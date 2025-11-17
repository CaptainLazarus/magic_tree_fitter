open Gss
open Domain_types
open Stack_monad_ops

let update_stack_with_actions (c : glr_config) (s : stack) =
  let s, _ = Stack.(run_stack (update_stack_with_actions_monad c) s) in
  s
;;

let initialise_stack direction next_token node =
  (* Set the root node with id = 0 *)
  let s : stack =
    { root = node
    ; curr_id = 1
    ; top = NodeMap.empty
    ; next_token
    ; direction
    ; nodes = HashtblCustom.create 100
    }
  in
  (* add root node to hashtbl *)
  HashtblCustom.add s.nodes (NodeId 0) node;
  (* Top will be the edges. You're using a fold for threading through the id counter *)
  let top_list, NodeId final_id =
    EdgeSet.fold
      (fun el acc ->
         let _, y = el in
         let top_acc, curr_id = acc in
         let n, new_id =
           create_and_add_node
             s
             ~state:y
             ~edges:EdgeSet.empty
             ~parents:(NodeIdSet.singleton node.id)
             ~next_actions:[]
             ~blocked_reductions:[]
         in
         (n.state, n) :: top_acc, increment_node_id curr_id)
      node.edges
      ([], NodeId 1)
  in
  { s with top = NodeMap.of_list top_list; curr_id = final_id }
;;

let all_blocked (stacks : stack list) =
  List.for_all
    (fun stack ->
       NodeMap.for_all
         (fun _ node ->
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

let update_stack_next_token (g : graph) (s : stack) =
  let is_blocked =
    NodeMap.fold
      (fun _ curr_node blocked -> curr_node.blocked_reductions <> [] || blocked)
      s.top
      false
  in
  if is_blocked
  then s
  else (
    match s.direction with
    | Forward ->
      if g.forward_tokens <> []
      then { s with next_token = List.hd g.forward_tokens }
      else s
    | Backward ->
      if g.reverse_tokens <> []
      then { s with next_token = List.hd g.reverse_tokens }
      else s)
;;

let consume_token = apply_actions_to_stack
