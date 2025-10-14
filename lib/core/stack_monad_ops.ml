open Gss
open Glr_utils
open Domain_types
(* open Dump *)

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
    |> fun actions ->
    (* print_string (dump_token_info s.next_token); *)
    (* Printf.printf "\n"; *)
    (* dump_gss_node top_node; *)
    (* List.iter *)
    (*   (fun a -> *)
    (*      Printf.printf "\n"; *)
    (*      print_string (string_of_action a)) *)
    (*   actions; *)
    partition_actions actions
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

(* NOTE : If Top stack has a node that has state s, and we get state s, then we add the parents to this. If not, we create a node. If there are other nodes with state s, we don't care, since they're not top. Assumption. *)

(* 1. Find if a top node exists with a target state. *)
(* 2. If it doesn't, then create it. *)
(* 3. If it does, then fetch it.  *)
(* 3a. Update nodes hashtbl. *)
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

(* 1. Add edge to parent *)
(* 2. update hashtbl *)
(* 3. add child to top *)
let add_node_to_top parent_node transition_symbol child_node =
  Stack.(
    get
    >>= fun s ->
    let updated_parent =
      { parent_node with
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
let apply_shift (top_node : gss_node) (NodeState x : node_state) =
  Printf.printf "[4] Shifting %d state\n" x;
  (* dump_gss_node top_node; *)
  Stack.(
    get
    >>= fun s ->
    find_or_create_shifted_node (NodeState x) top_node.id
    >>= fun child_node ->
    add_node_to_top top_node s.next_token.token child_node
    >>= fun updated_stack -> put updated_stack)
;;

let apply_goto (top_node : gss_node) (transition_symbol : symbol) (x : node_state) =
  Stack.(
    get
    >>= fun s ->
    find_or_create_shifted_node x top_node.id
    >>= fun child_node ->
    add_node_to_top top_node transition_symbol child_node
    >>= fun updated_stack ->
    put updated_stack
    >>= fun _ ->
    (* dump_stack updated_stack; *)
    return x)
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
    (* dump_stack s; *)
    print_int (unpack_id child.id);
    (* dump_nodes s; *)
    (* print_stack_top s; *)
    failwith "[FIND MATCHING EDGE] Node not found"
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
(* HACK : WHY WAS I DOING THIS ? You shouldn't need to clean the parent up. Don't remove it from child. Let it be. Any other action can and could use this. Reduce just goes back and adds nodes to another previous node. why meddle with the top ? *)
(* NOTE : Removes edge from parent that led to path --> Does this break stuff ? If multiple reductions use the same path, sure. Question to be pondered over. Not sure if the edge has to be removed. Remove edge and decide ? Nah....let it stay. What can it do ?*)

(* let parent_cleanup path = *)
(*   (* Printf.printf "\n\n[XX] Parent Cleanup.\n\n"; *) *)
(*   Stack.( *)
(*     get *)
(*     >>= fun s -> *)
(*     let parent_node (* To be deleted from child's parent list *) = List.nth path 1 in *)
(*     let parent_id = parent_node.id in *)
(*     (* Why ? *) *)
(*     let child_node (* From whom the parent has to be deleted --> in top *) = *)
(*       List.hd path *)
(*     in *)
(*     let updated_child_node = *)
(*       { child_node with parents = NodeIdSet.remove parent_id child_node.parents } *)
(*     in *)
(*     (* dump_gss_node updated_child_node; *) *)
(*     HashtblCustom.replace s.nodes updated_child_node.id updated_child_node; *)
(*     put { s with top = NodeMap.add updated_child_node.state updated_child_node s.top }) *)
(* ;; *)
(**)
(* NOTE : I guess here's where you'll have to delete the parent. *)
(* Also the edge that's being replaced. Only in parent though. --> Check note above *)

(* Returns node state being shifted --> in this case only one is being shifted *)
let apply_path_reduction (c : glr_config) (top_node : gss_node) (path : gss_node list) pr =
  Printf.printf "[5.2] Applying Path Reduction\n";
  (* dump_rule pr; *)
  (* dump_path path; *)
  (* Printf.printf "\n"; *)
  (* dump_gss_node top_node; *)
  Stack.(
    get
    >>= fun s ->
    let rev_path = List.rev path in
    match rev_path with
    | [] -> return None
    | parent :: _ ->
      (match
         Hashtbl.find_opt
           (get_parse_table c s)
           ((fun (NodeState x) -> x) parent.state, pr.lhs)
       with
       | Some [ Goto target_state ] ->
         (* parent_cleanup path *)
         (* >>= fun _ -> *)
         apply_goto parent pr.lhs (NodeState target_state)
         >>= fun shifted_node_state -> return (Some shifted_node_state)
       | _ -> return None))
;;

let rec apply_paths_reduction
          (c : glr_config)
          (top_node : gss_node)
          (paths : gss_node list list)
          pr
          acc
  =
  Printf.printf "[5.1] Applying Path Reduction Recusively\n";
  Stack.(
    get
    >>= fun s ->
    match paths with
    | [] ->
      Printf.printf "[5.11] Path Reduction Recusion Completed\n";
      return acc
    | path :: rest ->
      apply_path_reduction c top_node path pr
      >>= fun shifted_node_state_opt ->
      (* could just replace with filtermap at the end *)
      let updated_acc =
        match shifted_node_state_opt with
        | Some ns -> ns :: acc
        | None -> acc
      in
      apply_paths_reduction c top_node rest pr updated_acc
      >>= fun final_acc ->
      Printf.printf "[5.12] Returning from this func\n";
      return final_acc)
;;

(* TODO : So, read comments on apply shift. Mainly have to a. Update parents on reduction (remove dead parents). This will be needed for comparision later higher above for current graph.*)
let apply_reduce (c : glr_config) (top_node : gss_node) (pr : production_rule) =
  Printf.printf "[5] Reducing ";
  (* dump_rule pr; *)
  (* dump_gss_node top_node; *)
  Stack.(
    get
    >>= fun s ->
    let paths = collect_reduction_paths s top_node pr in
    (* dump_paths paths; *)
    apply_paths_reduction c top_node paths pr []
    >>= fun reduced_top_nodes -> return reduced_top_nodes)
;;

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

let clear_top_node_actions (s : stack) (top_node : gss_node) =
  Printf.printf "[XX] Clear Top Node Actions";
  let top_node_opt = HashtblCustom.find_opt s.nodes top_node.id in
  match top_node_opt with
  | None -> failwith "[CLEAR TOP NODE ACTIONS] Node not found. What ?"
  | Some top_node ->
    let top_node = { top_node with next_actions = [] } in
    let new_top = NodeMap.add top_node.state top_node s.top in
    let s = { s with top = new_top } in
    HashtblCustom.replace s.nodes top_node.id top_node;
    top_node, s
;;

(* FIX : Audit this func *)
let update_top_node (node : gss_node) =
  Printf.printf "\n[XX] Updating top node\n";
  Stack.(
    get
    >>= fun s ->
    let top_node, curr_stack = clear_top_node_actions s node in
    (* dump_gss_node top_node; *)
    let new_top_node_opt = NodeMap.find_opt top_node.state curr_stack.top in
    match new_top_node_opt with
    | None -> failwith "\n[UPDATE TOP NODE] No top node found\n"
    | Some new_top_node ->
      (* top_node has no parents, remove from hashtbl and top *)
      (* dump_gss_node new_top_node; *)
      if NodeIdSet.is_empty new_top_node.parents
      then (
        Printf.printf "\n[XX] -----------------------\n";
        (* dump_nodes curr_stack; *)
        HashtblCustom.remove curr_stack.nodes top_node.id;
        (* dump_nodes curr_stack; *)
        return { curr_stack with top = NodeMap.remove top_node.state curr_stack.top })
      else (
        (* Basically, if a new parent exists, then it's still in top. otherwise remove *)
        let diff_a = NodeIdSet.diff new_top_node.parents top_node.parents in
        return
          (match NodeIdSet.is_empty diff_a with
           | true ->
             Printf.printf "\n++True++\n";
             let updated_top = NodeMap.remove top_node.state curr_stack.top in
             (* dump_stack { curr_stack with top = updated_top }; *)
             { curr_stack with top = updated_top }
           | false ->
             Printf.printf "\n++False++\n";
             curr_stack)))
;;

(* Split this func *)
let rec apply_reduce_till_token_consumed
          (c : glr_config)
          (top_node : gss_node)
          (pr : production_rule)
  =
  Stack.(
    apply_reduce c top_node pr
    >>= fun updated_top_nodes ->
    (* dump_node_states updated_top_nodes; *)
    get
    (* FIX : Update top node is a completely unweildy func. Rework yesterday *)
    >>= fun curr_stack ->
    Printf.printf "\n[5.01] Dumping Updated Stack without actions\n";
    (* dump_stack curr_stack; *)
    let top_node_states = NodeStateSet.of_seq (List.to_seq updated_top_nodes) in
    let updated_stacks_with_actions =
      NodeStateSet.fold
        (fun ns acc ->
           let top_node_with_actions =
             update_actions_for_top_node
               (NodeMap.find ns acc.top)
               (get_parse_table c acc)
               acc
           in
           { acc with top = NodeMap.add ns top_node_with_actions acc.top })
        top_node_states
        curr_stack
    in
    Printf.printf "\n[5.02] Dumping Updated Stack with actions\n";
    (* dump_stack updated_stacks_with_actions; *)
    put updated_stacks_with_actions
    >>= fun _ ->
    get
    >>= fun s' ->
    Printf.printf
      "\n[5.03] Now applying actions to the top_node ? Again ? Not the updated list\n";
    let recursive_top_node_list =
      NodeStateSet.fold
        (fun ns acc ->
           match NodeMap.find_opt ns s'.top with
           | None -> failwith "Node not found"
           | Some node -> node :: acc)
        top_node_states
        []
    in
    let updated_s' =
      List.fold_left
        (fun s1 curr_top_node ->
           List.fold_left
             (fun s2 a ->
                run_stack
                  (apply_action c curr_top_node a
                   >>= fun _ ->
                   update_top_node curr_top_node >>= fun final_stack -> put final_stack)
                  s2
                |> snd)
             s1
             curr_top_node.next_actions)
        s'
        recursive_top_node_list
    in
    put updated_s')

(* TODO : Use nodestate to pull the node from nodemap and then apply actions on that. Straightforward, since state is the key *)
(* let updated_node = update_actions_for_top_node (get_parse_table c updated_stack) in *)
(* The problem here is I need a way of finding the "reduced" node and finding it's actions to apply recusively until it's a shift. Or even do shifts ?*)

(* NOTE : Simple Routing func. Not bad *)
and apply_action (c : glr_config) (top_node : gss_node) (a : action) =
  Stack.(
    get
    >>= fun s ->
    Printf.printf "[3] Action routing\n";
    match a with
    | Shift x -> apply_shift top_node (NodeState x)
    | Reduce pr -> apply_reduce_till_token_consumed c top_node pr
    | Accept -> failwith "[2XX] Program finished ?"
    | Goto x -> failwith "[3XX] GOTO should never be a node action - this is a bug")
;;

let apply_top_node_actions (c : glr_config) top_node =
  Stack.(
    get
    >>= fun curr_stack ->
    Printf.printf "[2] Applying top node actions to stack\n";
    (* dump_gss_node top_node; *)
    let updated_stack =
      List.fold_left
        (fun s a -> run_stack (apply_action c top_node a) s |> snd)
        curr_stack
        top_node.next_actions
    in
    put updated_stack
    >>= fun _ ->
    update_top_node top_node
    >>= fun stack_with_updated_top_nodes -> put stack_with_updated_top_nodes)
;;

let apply_actions_to_stack (c : glr_config) =
  Stack.(
    get
    >>= fun curr_stack ->
    Printf.printf "[1] Applying actions to stack\n";
    (* print_stack_top curr_stack; *)
    let updated_stack =
      NodeMap.fold
        (fun _ top_node s -> run_stack (apply_top_node_actions c top_node) s |> snd)
        curr_stack.top
        curr_stack
    in
    (* this func is pointless. We're not removing any fucking nodes anymore *)
    let cleaned_top =
      NodeMap.filter
        (fun state node -> HashtblCustom.mem updated_stack.nodes node.id)
        updated_stack.top
      (* TODO : Might wanna add the next actions here. Makes more sense logically imo. Actually, we don't have the tokens though. Do we ? Check once and update here.*)
    in
    put { updated_stack with top = cleaned_top } >>= fun _ -> get)
;;
