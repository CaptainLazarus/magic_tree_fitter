open Gss
open Stack
open Domain_types
open Stack_monad_ops

let update_stack (c : glr_config) (s : stack) =
  let s, _ = Stack.(run_stack (update_stack_monad_with_actions c) s) in
  s
;;

let initialise_stack direction next_token node =
  (* Set the root node with id = 0 *)
  let s : stack =
    { root = node
    ; curr_id = 1
    ; top = NodeMap.empty
    ; (* Edit : Fixed below*)
      (* Kinda wrong. *)
      (*We want to actually add the node.edge.y node here. children, basically *)
      next_token
    ; direction
    ; nodes = Hashtbl.create 100
    }
  in
  (* add root node to hashtbl *)
  Hashtbl.add s.nodes (NodeId 0) node;
  (* Top will be the edges. You're using a fold for threading through the id counter *)
  let top_list, NodeId final_id =
    EdgeSet.fold
      (fun el acc ->
         let sym, y = el in
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

let update_stack_with_actions stack node_action_pairs =
  let updated_nodes =
    List.map
      (fun (node, actions) -> node.state, { node with next_actions = actions })
      node_action_pairs
  in
  List.iter (fun (_, node) -> Hashtbl.replace stack.nodes node.id node) updated_nodes;
  let updated_top = NodeMap.of_list updated_nodes in
  { stack with top = updated_top }
;;

(* let update_all_stacks_with_actions new_stacks next_actions = *)
(*   let updated_stacks = List.map2 update_stack_with_actions new_stacks next_actions in *)
(*   updated_stacks *)
(* ;; *)

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

let apply_action (c : glr_config) (s : stack) (top_node : gss_node) (a : action) : stack =
  match a with
  | Shift x -> run_stack (apply_shift top_node (NodeState x)) s |> fst
  | Reduce pr -> run_stack (apply_reduce c top_node pr) s |> fst
  | Accept -> failwith "[2XX] Program finished ?"
  | Goto x -> run_stack (apply_goto top_node (NodeState x)) s |> fst
;;

let apply_node_actions (c : glr_config) (curr_stack : stack) top_node =
  (* we got the top_node. We have the stack. Now we have to List.map over options ? List.fold. We need to update and return the stack, basically.*)
  (* Individual ops can be a monad since stack is updated. stack -> stack *)
  List.fold_left (fun s a -> apply_action c s top_node a) curr_stack top_node.next_actions
;;

let apply_actions_to_stack (c : glr_config) =
  Stack.(
    get
    >>= fun s ->
    let updated_stack =
      NodeMap.fold (fun _ top_node s -> apply_node_actions c s top_node) s.top s
    in
    put updated_stack >>= fun _ -> get)
;;
