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
    ; (* Edit : Fixed below*)
      (* Kinda wrong. *)
      (*We want to actually add the node.edge.y node here. children, basically *)
      next_token
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

(* Apply the specific action. GOTO and shift are the same. Reduce leads to a goto and then ends. *)
(* After all the actions are done, remove the top node ? Only if not in nodes table *)

(* TODO : Add top_node removal only if nodes table mem check is false *)
(* NOTE: This is removing the node from the table. Interesting. Does this make sense ? Think through *)
(* If its a shift or goto, no removal. If its a reduce, then reduce should take care of that. *)

(* FIX : Should not be a remove here. Come here again after reduce *)

(* FIX : You should a. Check if the old and new top nodes are same and if they are, take a diff of the parents to see a. if shifted. If reduced, the parents will be a diff. So based on the action basically. Interesting*)

(* FIX: : Long story short, if shifted, parents added. If reduced, parentes deleted. Look at nodes table for source of truth ? *)

(* NOTE : Let's work this through. If there is a shift or multiple shifts, which result in the same top node, parents added. *)
(* NOTE : If shift + reduce, then parents will only be added from the shift. will be removed from the reduce. If multiple reduces, parents only removed + node itself fucks off. *)
(* NOTE : Anyway, long story. *)
(* Hashtbl.remove curr_stack.nodes top_node.id; *)

(* 1. Only shifts --> no parents change. edges increase. remove from top. stays in hashtbl *)
(* 2. Only reduce --> parents reduced. remove from hashtbl. *)
(* 3. Shift + reduce --> parents reduced. edges increase. remove from top. stays in hashtbl *)
(* 4. diff top node => shifts this state --> parents increased. stays in top. stays in hashtbl *)
(* 5. diff top node => reduce --> depends on change position. parent can either increase. stays in top and hashtbl. or parent doesn't change, but parent gets a new edge. still stays *)
(* 6. shift + diff top node => shift --> parents increased. still in top. stays in hashtbl. *)
(* 7. shift + diff top node => reduce --> p increase. still in top. *)
(* 8. reduce + diff top node => shift --> p increase. still in top *)
(* 9. reduce + diff top node => reduce --> p increase. still in top *)
(* 10. shift + reduce + diff top node => shift + reduce --> p increase. still in top *)

(* fml. so, either a. remove / keep in hashtbl b. remove / keep in top. You can also filter if no parents *)

(* let apply_top_node_actions (c : glr_config) (curr_stack : stack) top_node = *)
(*   let updated_stack = *)
(*     List.fold_left *)
(*       (fun s a -> apply_action c s top_node a) *)
(*       curr_stack *)
(*       top_node.next_actions *)
(*   in *)
(*   update_top_node top_node updated_stack *)
(* ;; *)

(* 1. Take each top node *)
(* 2. Apply all actions in that specific top node *)
(* 3. Remove the nodes that aren't in the nodes anymore --> If nodes not in the hashtbl. This runs at the end after all the actions are applied. *)

let consume_token = apply_actions_to_stack
