open Gss
open Glr_utils
open Domain_types
open Dump

let partition_actions acts =
  let rs, other =
    List.partition
      (function
        | Reduce _ -> true
        | _ -> false)
      acts
  in
  rs @ other
;;

let update_actions_for_top_node (top_node : gss_node) parse_table (s : stack) =
  let next_actions =
    get_next_actions_for_node top_node.state s.next_token.token parse_table
    |> partition_actions
  in
  let updated_node = { top_node with next_actions } in
  HashtblCustom.replace s.nodes top_node.id updated_node;
  updated_node
;;

let update_actions_for_top_nodes parse_table =
  Stack.(
    get
    >>= fun s ->
    (* Update top nodes with next_actions per stack, and filter the nodes with empty actions. *)
    let updated_top =
      NodeMap.map
        (fun top_node -> update_actions_for_top_node top_node parse_table s)
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
    update_actions_for_top_nodes parse_table)
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
    return { s with top = NodeMap.add child_node.state child_node s.top })
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
    >>= fun child_node -> add_parent_edge top_node s.next_token.token child_node)
;;

let apply_goto (top_node : gss_node) (transition_symbol : symbol) (x : node_state) =
  Stack.(
    get
    >>= fun s ->
    find_or_create_shifted_node x top_node.id
    >>= fun child_node -> add_parent_edge top_node transition_symbol child_node)
;;

let find_matching_edge
      (s : stack)
      (parent : gss_node)
      (child : gss_node)
      (expected_sym : symbol)
  =
  let child_node_opt = HashtblCustom.find_opt s.nodes child.id in
  match child_node_opt with
  | None ->
    dump_stack s;
    (* dump_nodes s; *)
    (* print_stack_top s; *)
    failwith "Node not found"
  | Some child_node ->
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
         >>= fun final_stack -> return final_stack
       | _ -> return s))
;;

let rec apply_paths_reduction
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
    | path :: rest ->
      apply_path_reduction c top_node path pr
      >>= fun updated_stack ->
      put updated_stack
      >>= fun _ ->
      apply_paths_reduction c top_node rest pr
      >>= fun final_stack -> put final_stack >>= fun _ -> get)
;;

(* TODO : So, read comments on apply shift. Mainly have to a. Update parents on reduction (remove dead parents). This will be needed for comparision later higher above for current graph.*)
let apply_reduce (c : glr_config) (top_node : gss_node) (pr : production_rule) =
  Stack.(
    get
    >>= fun s ->
    let paths = collect_reduction_paths s top_node pr in
    apply_paths_reduction c top_node paths pr
    >>= fun updated_stack -> put updated_stack >>= fun _ -> get)
;;

(* NOTE : Simple Routing func. Not bad *)
let apply_action (c : glr_config) (top_node : gss_node) (a : action) =
  Stack.(
    get
    >>= fun s ->
    match a with
    | Shift x ->
      apply_shift top_node (NodeState x) >>= fun updated_stack -> return updated_stack
    | Reduce pr ->
      apply_reduce c top_node pr >>= fun updated_stack -> return updated_stack
    | Accept -> failwith "[2XX] Program finished ?"
    | Goto x -> failwith "[3XX] GOTO should never be a node action - this is a bug")
;;

let update_top_node (top_node : gss_node) =
  Stack.(
    fun curr_stack ->
      let new_top_node = NodeMap.find top_node.state curr_stack.top in
      if NodeIdSet.is_empty new_top_node.parents
      then (
        HashtblCustom.remove curr_stack.nodes top_node.id;
        return { curr_stack with top = NodeMap.remove top_node.state curr_stack.top })
      else (
        let diff_a = NodeIdSet.diff new_top_node.parents top_node.parents in
        let diff_b = NodeIdSet.diff top_node.parents new_top_node.parents in
        return
          (match NodeIdSet.is_empty diff_a, NodeIdSet.is_empty diff_b with
           (* True a -> no new parents -> no top node got this ; True b -> no parents removed -> no reductions *)
           | true, true ->
             let updated_top = NodeMap.remove top_node.state curr_stack.top in
             { curr_stack with top = updated_top }
           | true, false ->
             HashtblCustom.remove curr_stack.nodes top_node.id;
             curr_stack
           | false, _ -> curr_stack)))
;;

let apply_top_node_actions (c : glr_config) top_node =
  Stack.(
    get
    >>= fun curr_stack ->
    let updated_stack =
      List.fold_left
        (fun s a -> run_stack (apply_action c top_node a) s |> fst)
        curr_stack
        top_node.next_actions
    in
    update_top_node top_node updated_stack
    >>= fun stack_with_updated_top_nodes -> put stack_with_updated_top_nodes)
;;

let apply_actions_to_stack (c : glr_config) =
  Stack.(
    get
    >>= fun curr_stack ->
    let updated_stack =
      NodeMap.fold
        (fun _ top_node s -> run_stack (apply_top_node_actions c top_node) s |> snd)
        curr_stack.top
        curr_stack
    in
    let cleaned_top =
      NodeMap.filter
        (fun state node -> HashtblCustom.mem updated_stack.nodes node.id)
        updated_stack.top
      (* TODO : Might wanna add the next actions here. Makes more sense logically imo. Actually, we don't have the tokens though. Do we ? Check once and update here.*)
    in
    put { updated_stack with top = cleaned_top } >>= fun _ -> get)
;;

(* This func requires me to refactor everything else, since I have no way of knowing which node got reduced. Fuck me. Seriously. *)
(* let rec apply_reduce_till_token_consumed *)
(*           (c : glr_config) *)
(*           (top_node : gss_node) *)
(*           (pr : production_rule) *)
(*   = *)
(*   Stack.( *)
(*     get *)
(*     >>= fun s -> *)
(*     apply_reduce c top_node pr *)
(*     >>= fun _ -> *)
(*     get *)
(*     >>= fun updated_stack -> *)
(*     (* let updated_node = update_actions_for_top_node (get_parse_table c updated_stack) in *) *)
(*     (* The problem here is I need a way of finding the "reduced" node and finding it's actions to apply recusively until it's a shift. Or even do shifts ?*) *)
(*     >>= fun updated_stack_with_actions -> apply_top_node_actions) *)
(* ;; *)
