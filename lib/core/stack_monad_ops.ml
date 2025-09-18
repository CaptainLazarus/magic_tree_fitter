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
           let updated_node = { top_node with next_actions } in
           HashtblCustom.replace s.nodes top_node.id updated_node;
           updated_node)
        s.top
      |> NodeMap.filter (fun _ top_node -> top_node.next_actions <> [])
    in
    put { s with top = updated_top } >>= fun _ -> get)
;;

let update_stack_with_actions_monad (c : glr_config) =
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
(* TODO :Interesting problem just discovered -> You're not adding the edge to the new parents of the child state and the transition state -> Solved in a new patch. seems to be working *)
(* No worries, stack has the current token. Just shift in the graph per token (or some other logic). you'll be fine. *)

(* 1. Since state based, find out if target state in top_stack *)
(* 2. If in top stack, that means it's there. I said added right now. make sense ? top_stack could have x,y and LOOKUP(x,s) = y. Does this change anything ? *)
(* NOTE : If Top stack has a node that has state s, and we get state s, then we add the parents to this. If not, we create a node. If there are other nodes with state s, we don't care, since they're not top. Assumption. *)
let find_or_create_shifted_node target_state parent_id =
  Stack.(
    get
    >>= fun s ->
    let existing_node_opt = find_opt (fun n _ -> n = target_state) s.top in
    match existing_node_opt with
    | None ->
      let node, NodeId curr_id =
        create_and_add_node
          s
          ~state:target_state
          ~parents:(NodeIdSet.singleton parent_id)
          ~edges:EdgeSet.empty
          ~next_actions:[]
          ~blocked_reductions:[]
      in
      put { s with curr_id } >>= fun _ -> return node
    | Some (_, existing_node) ->
      let node =
        { existing_node with parents = NodeIdSet.add parent_id existing_node.parents }
      in
      HashtblCustom.replace s.nodes node.id node;
      put s >>= fun _ -> return node)
;;

let add_parent_edge parent_node transition_symbol child_node =
  Stack.(
    get
    >>= fun s ->
    let updated_parent =
      { parent_node with
        (* Check initalise_stacks for which token is being shifted. Should change this to current_token *)
        edges = EdgeSet.add (transition_symbol, child_node.state) parent_node.edges
      }
    in
    HashtblCustom.replace s.nodes parent_node.id updated_parent;
    put { s with top = NodeMap.add child_node.state child_node s.top } >>= fun _ -> get)
;;

(* 1. Find / Create a node *)
(* 2. Add the edge to the parent. *)
(* Things that should happen here --> *)
(* 1. Removed from top stack if no actions  --> This is not the place to do that. Where then ? *)
(* since top_stack is state based on NOT id based --> *)
(* a. Top stack node has shift action. new shift goes to different node. top_node still has actions --> stay *)
(* b. Top stack has no more actions, remove from top. *)
(* How do you determine if the top_stack node has actions ? Cannot be done here, since list of actions is streaming basically. is it ? *)
(* Wait, you have the top node right here. Check ? *)
(* NOTE : You may not need to check. The top nodes are an invariant list that are passed through, and the stack is updated throughout. *)
(* NOTE : So nodes are not mutably updated (the lookup table is). This means that new parents don't show up. Should we check this for if the nodes are added bak to top ? We know that LOOKUP(x,s) =/= x. *)
(* NOTE :  If yes, how do I check the new parents ? Copy list and then check double one level above ? *)
let apply_shift (top_node : gss_node) (x : node_state) =
  Stack.(
    get
    >>= fun s ->
    find_or_create_shifted_node x top_node.id
    >>= fun child_node ->
    add_parent_edge top_node s.next_token.token child_node >>= fun updated_stack -> get)
;;

(* let apply_goto (top_node : gss_node) (x : node_state) = apply_shift top_node x *)

let apply_goto (top_node : gss_node) (transition_symbol : symbol) (x : node_state) =
  Stack.(
    get
    >>= fun s ->
    find_or_create_shifted_node x top_node.id
    >>= fun child_node ->
    add_parent_edge top_node transition_symbol child_node >>= fun updated_stack -> get)
;;

let find_matching_edge
      (s : stack)
      (parent : gss_node)
      (child : gss_node)
      (expected_sym : symbol)
  =
  let child_node = HashtblCustom.find s.nodes child.id in
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
             let parent = HashtblCustom.find s.nodes parent_id in
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
             let parent = HashtblCustom.find s.nodes x in
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

(* 1. Removes parent id from child *)
(* 2. Add child to the stack top *)
(* NOTE : Removes edge from parent that led to path --> Does this break stuff ? If multiple reductions use the same path, sure. Question to be pondered over. Not sure if the edge has to be removed. Remove edge and decide ? Nah....let it stay. What can it do ?*)
let parent_cleanup path =
  Stack.(
    get
    >>= fun s ->
    let parent_node (* To be deleted from child's parent list *) = List.nth path 1 in
    let parent_id = parent_node.id in
    let child_node (* From whom the parent has to be deleted --> in top *) =
      List.hd path
    in
    let updated_child_node =
      { child_node with parents = NodeIdSet.remove parent_id child_node.parents }
    in
    HashtblCustom.replace s.nodes child_node.id child_node;
    put { s with top = NodeMap.add child_node.state updated_child_node s.top }
    >>= fun _ -> get)
;;

(* NOTE : I guess here's where you'll have to delete the parent. *)
(* Also the edge that's being replaced. Only in parent though. --> Check note above *)
let apply_path_reduction (c : glr_config) (top_node : gss_node) (path : gss_node list) pr =
  Stack.(
    get
    >>= fun s ->
    let rev_path = List.rev path in
    match rev_path with
    | [] -> return s
    | parent :: _ ->
      (match
         Hashtbl.find_opt
           (get_parse_table c s)
           ((fun (NodeState x) -> x) parent.state, pr.lhs)
       with
       | Some [ Goto target_state ] ->
         parent_cleanup path
         >>= fun s' ->
         put s'
         >>= fun _ ->
         apply_goto parent pr.lhs (NodeState target_state)
         >>= fun final_stack -> put final_stack >>= fun _ -> get
       | _ -> return s))
;;

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

(* TODO : So, read comments on apply shift. Mainly have to a. Update parents on reduction (remove dead parents). This will be needed for comparision later higher above for current graph.*)
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
