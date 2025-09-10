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
(* TODO : How do you find nodes to merge ? -> If same state in top, then merge, since it implies literally added right now.*)
(*Remove old one*)
(* TODO :Interesting problem just discovered -> You're not adding the edge to the new parents of the child state and the transition state *)
(* No worries, stack has the current token. Just shift in the graph per token (or some other logic). you'll be fine. *)

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
            ~edges:EdgeSet.empty
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
    let updated_parent =
      { top_node with
        edges = EdgeSet.add (s.next_token.token, new_node.state) top_node.edges
      }
    in
    Hashtbl.replace s.nodes top_node.id updated_parent;
    return { s with top = NodeMap.add new_node.state new_node s.top })
;;

let apply_goto (top_node : gss_node) (x : node_state) = apply_shift top_node x
(*   (* (\* add a check here in s.top for same state nodes. if yes, merge. figure out how *\) *) *)
(*   let new_node = *)
(*     (* (\* Use Base package for this. has inbuilt funcs for it. *\) *) *)
(*     match find_opt (fun _ n -> n.state = x) s.top with *)
(*     | Some (_, existing_node) -> *)
(*       { existing_node with parents = NodeIdSet.add top_node.id existing_node.parents } *)
(*     | None -> *)
(*       let n, _n_id = *)
(*         create_node *)
(*           s.curr_id *)
(*           ~state:x *)
(*           ~parents:(NodeIdSet.singleton top_node.id) *)
(*           ~edges:[] *)
(*           ~next_actions:[] *)
(*           ~blocked_reductions:[] *)
(*       in *)
(*       n *)
(*   in *)
(*   Hashtbl.replace s.nodes new_node.id new_node; *)
(*   { s with top = NodeMap.add new_node.state new_node s.top } *)
(* ;; *)

let find_matching_edge
      (s : stack)
      (parent : gss_node)
      (child : gss_node)
      (expected_sym : symbol)
  =
  let child_node = Hashtbl.find s.nodes child.id in
  EdgeSet.find_opt
    (expected_sym, child_node.state)
    (* Can't have multiple edges since the children are unique*)
    parent.edges
;;

let collect_reduction_paths (s : stack) (top_node : gss_node) (pr : production_rule) =
  let rhs_symbols = List.rev pr.rhs in
  (* rhs symbols reversed since we go backwards *)
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
             (* Get parent using the id *)
             match find_matching_edge s parent node expected_sym with
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
             (*             let child_node = Hashtbl.find s.nodes child.id in *)
             (* EdgeSet.find_opt *)
             (*   (expected_sym, child_node.state) *)
             (*   (* Can't have multiple edges since the children are unique*) *)
             (*   parent.edges *)
             let edge = EdgeSet.find_opt (expected_sym, node.state) parent.edges in
             match edge with
             | None -> false
             | Some edge -> walk_back_all_symbols parent (depth - 1) rest)
          node.parents
  in
  walk_back_all_symbols top_node rhs_length rhs_symbols
;;

let apply_path_reduction (c : glr_config) (top_node : gss_node) (path : gss_node list) pr =
  Stack.(
    get
    >>= fun s ->
    match path with
    | [] -> return s
    | parent :: _ ->
      (match
         Hashtbl.find_opt
           (get_parse_table c s)
           ((fun (NodeState x) -> x) parent.state, pr.lhs)
       with
       | Some [ Goto target_state ] ->
         let s', _ = Stack.run_stack (apply_goto parent (NodeState target_state)) s in
         return s'
       | _ -> return s))
;;

(* List.fold_left *)
(*   (fun acc_stack path -> *)
(*      match path with *)
(*      | [] -> acc_stack (* shouldn't happen *) *)
(*      | path_start :: _ -> *)
(*        let parent_state = path_start.state in *)
(*        let parse_table = *)
(*          if s.direction = Forward *)
(*          then get_forward_parse_table c.parse_tables *)
(*          else get_backward_parse_table c.parse_tables *)
(*        in *)
(*        (match Hashtbl.find_opt parse_table (parent_state, pr.lhs) with *)
(*         | Some [ Goto target_state ] -> apply_goto acc_stack path_start target_state *)
(*         | _ -> acc_stack)) *)
(*   s *)
(*   paths in *)

let apply_paths_reduction
      (c : glr_config)
      (top_node : gss_node)
      (paths : gss_node list list)
      pr
  =
  Stack.(
    get
    >>= fun s ->
    match paths with
    | [] -> return s
    | path :: rest -> apply_path_reduction c top_node path pr >>= fun s' -> return s')
;;

let apply_reduce (c : glr_config) (top_node : gss_node) (pr : production_rule) =
  Stack.(
    get
    >>= fun s ->
    let paths = collect_reduction_paths s top_node pr in
    apply_paths_reduction c top_node paths pr >>= fun s -> return s)
;;
(* Top list should be filtered every time, though I guess we can do this later. *)
(* The idea here is checking if a path is possible is enough, since then the path itself will be reduced to the symbol *)
(* If the path is possible, all we need to do is find the goto state of the NonTerminal, and then add that to top nodes *)
(* We should also remove the child from the parent, so that further operations don't use this child, since it is now reduced. Or should it not be removed ? *)
(* Child likely has to be removed. It's a pop operation, though we're not treating it as such. It should not be available. Lots of questions. *)
(* Not putting the questions here. If I rediscover them, then sure. Keywords : Multiple reduce *)
