open Gss
open Glr_utils
open Domain_types

let find_actions_for_top_nodes parse_table =
  Stack.(
    get
    >>= fun s ->
    (* Update top nodes with next_actions per stack, and filter the nodes with empty actions. *)
    let updated_top =
      NodeMap.map
        (fun top_node ->
           let next_actions =
             get_next_actions_for_node top_node.state s.next_token.token parse_table
           in
           { top_node with next_actions })
        s.top
      |> NodeMap.filter (fun _ top_node -> top_node.next_actions <> [])
    in
    put { s with top = updated_top } >>= fun _ -> get)
;;

let update_stack_monad_with_actions (c : glr_config) =
  Stack.(
    get
    >>= fun s ->
    let parse_table = get_parse_table c s in
    find_actions_for_top_nodes parse_table)
;;

(* ------------------------------------------ *)
(* Apply actions to stack *)
(* ------------------------------------------ *)

(* Assumptions -> Top nodes need to have actions that need to be resolved ?*)
(* How do you find nodes to merge ? -> If same state in top, then merge, since it implies literally added right now.*)
(*Remove old one*)
let apply_shift (top_node : gss_node) (x : node_state) =
  Stack.(
    get
    >>= fun s ->
    let existing_node_opt = find_opt (fun n _ -> n = x) s.top in
    let new_node =
      match existing_node_opt with
      | None ->
        let node, _ =
          create_and_add_node
            s
            ~state:x
            ~parents:(NodeIdSet.singleton top_node.id)
            ~edges:[]
            ~next_actions:[]
            ~blocked_reductions:[]
        in
        node
      | Some (_, existing_node) ->
        let node =
          { existing_node with parents = NodeIdSet.add top_node.id existing_node.parents }
        in
        Hashtbl.replace s.nodes node.id node;
        node
    in
    return { s with top = NodeMap.add new_node.state new_node s.top })
;;

let apply_goto (s : stack) (top_node : gss_node) (x : node_state) =
  (* (\* add a check here in s.top for same state nodes. if yes, merge. figure out how *\) *)
  let new_node =
    (* (\* Use Base package for this. has inbuilt funcs for it. *\) *)
    match find_opt (fun _ n -> n.state = x) s.top with
    | Some (_, existing_node) ->
      { existing_node with parents = NodeIdSet.add top_node.id existing_node.parents }
    | None ->
      let n, _n_id =
        create_node
          s.curr_id
          ~state:x
          ~parents:(NodeIdSet.singleton top_node.id)
          ~edges:[]
          ~next_actions:[]
          ~blocked_reductions:[]
      in
      n
  in
  Hashtbl.replace s.nodes new_node.id new_node;
  { s with top = NodeMap.add new_node.state new_node s.top }
;;

let find_matching_edge (parent : gss_node) (child : gss_node) (expected_sym : symbol) =
  List.find_opt
    (fun (edge_token, child_state) ->
       edge_token.token = expected_sym && child_state = child.state)
    parent.edges
;;

let collect_reduction_paths (s : stack) (top_node : gss_node) (pr : production_rule) =
  let rhs_symbols = List.rev pr.rhs in
  let rhs_length = List.length pr.rhs in
  let rec collect_paths
            (node : gss_node)
            (depth : int)
            (symbols : symbol list)
            (current_path : gss_node list)
    =
    match symbols with
    | [] -> [ List.rev current_path ]
    | expected_sym :: rest ->
      if depth <= 0
      then []
      else
        NodeIdSet.fold
          (fun parent_id acc ->
             let parent = Hashtbl.find s.nodes parent_id in
             match find_matching_edge parent node expected_sym with
             | Some _ ->
               let sub_paths =
                 collect_paths parent (depth - 1) rest (parent :: current_path)
               in
               sub_paths @ acc
             | None -> acc)
          node.parents
          []
  in
  collect_paths top_node rhs_length rhs_symbols [ top_node ]
;;

let can_reduce (s : stack) (top_node : gss_node) (pr : production_rule) =
  let rhs_symbols = List.rev pr.rhs in
  let rhs_length = List.length pr.rhs in
  let rec walk_back_all_symbols (node : gss_node) (depth : int) (symbols : symbol list) =
    match symbols with
    | [] -> true
    | expected_sym :: rest ->
      if depth <= 0
      then false
      else
        NodeIdSet.exists
          (fun x ->
             let parent = Hashtbl.find s.nodes x in
             let edge =
               List.find_opt
                 (fun (edge_token, child_state) ->
                    edge_token.token = expected_sym && child_state = node.state)
                 parent.edges
             in
             match edge with
             | None -> false
             | Some edge -> walk_back_all_symbols parent (depth - 1) rest)
          node.parents
  in
  walk_back_all_symbols top_node rhs_length rhs_symbols
;;

let apply_reduce (c : glr_config) (s : stack) (top_node : gss_node) (pr : production_rule)
  =
  let paths = collect_reduction_paths s top_node pr in
  List.fold_left
    (fun acc_stack path ->
       match path with
       | [] -> acc_stack (* shouldn't happen *)
       | path_start :: _ ->
         let parent_state = path_start.state in
         let parse_table =
           if s.direction = Forward
           then get_forward_parse_table c.parse_tables
           else get_backward_parse_table c.parse_tables
         in
         (match Hashtbl.find_opt parse_table (parent_state, pr.lhs) with
          | Some [ Goto target_state ] -> apply_goto acc_stack path_start target_state
          | _ -> acc_stack))
    s
    paths
;;
