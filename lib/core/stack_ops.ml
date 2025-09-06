open Gss
open Domain_types
open Glr_utils
open Stack
open Stack_monad_ops

let initialise_stack direction next_token node =
  (* Set the root node with id = 0 *)
  let s : stack =
    { root = node
    ; curr_id = 1
    ; top = NodeSet.empty
    ; (* Edit : Fixed below*)
      (* Kinda wrong. *)
      (*We want to actually add the node.edge.y node here. children, basically *)
      next_token
    ; direction
    ; nodes = Hashtbl.create 100
    }
  in
  (* add root node to hashtbl *)
  Hashtbl.add s.nodes 0 node;
  (* Top will be the edges. You're using a fold left for threading through the id counter *)
  let top_list, final_id =
    List.fold_left
      (fun (top_acc, curr_id) (_, y) ->
         let n, new_id =
           create_and_add_node
             s
             ~state:y
             ~edges:[]
             ~parents:(NodeIdSet.singleton node.id)
             ~next_actions:[]
             ~blocked_reductions:[]
         in
         n :: top_acc, new_id)
      ([], 1)
      node.edges
  in
  { s with top = NodeSet.of_list top_list; curr_id = final_id }
;;

let update_stack_with_actions stack node_action_pairs =
  let updated_nodes =
    List.map
      (fun (node, actions) -> { node with next_actions = actions })
      node_action_pairs
  in
  List.iter (fun node -> Hashtbl.replace stack.nodes node.id node) updated_nodes;
  let updated_top = NodeSet.of_list updated_nodes in
  { stack with top = updated_top }
;;

let update_all_stacks_with_actions new_stacks next_actions =
  let updated_stacks = List.map2 update_stack_with_actions new_stacks next_actions in
  updated_stacks
;;

let all_blocked (stacks : stack list) =
  List.for_all
    (fun stack ->
       NodeSet.for_all
         (fun node ->
            List.for_all
              (fun action ->
                 match action with
                 | Reduce pr -> List.mem pr node.blocked_reductions
                 | _ -> false) (* Shift/Goto/Accept mean we should continue *)
              node.next_actions
            || node.next_actions = []) (* Empty actions also mean blocked *)
         stack.top)
    stacks
;;

let apply_goto (s : stack) (top_node : gss_node) (x : node_state) =
  (* (\* add a check here in s.top for same state nodes. if yes, merge. figure out how *\) *)
  let new_node =
    (* (\* Use Base package for this. has inbuilt funcs for it. *\) *)
    match find_opt (fun n -> n.state = x) s.top with
    | Some existing_node ->
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
  { s with top = NodeSet.add new_node s.top }
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

let apply_action (c : glr_config) (s : stack) (top_node : gss_node) (a : action) : stack =
  match a with
  | Shift x -> run_stack (apply_shift top_node x) s |> fst
  | Reduce pr -> apply_reduce c s top_node pr
  | Accept -> failwith "[2XX] Program finished ?"
  | Goto x -> apply_goto s top_node x
;;

let apply_actions
      (c : glr_config)
      (s : stack)
      (top_node : gss_node)
      (actions : action list)
  =
  List.fold_left (fun acc a -> apply_action c acc top_node a) s actions
;;

let apply_all_actions_to_stack
      (c : glr_config)
      (s : stack)
      (node_action_pairs : (gss_node * action list) list)
  =
  List.fold_left
    (fun acc_stack (node, actions) -> apply_actions c acc_stack node actions)
    s
    node_action_pairs
;;

let apply_actions_to_all_stacks c updated_stacks next_actions =
  let final_stacks =
    List.map2 (apply_all_actions_to_stack c) updated_stacks next_actions
  in
  final_stacks
;;
