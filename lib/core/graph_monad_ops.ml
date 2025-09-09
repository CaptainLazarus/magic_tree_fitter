open Gss
open Glr_utils
open Stack_ops
open Domain_types

let initialise_stacks_helper c g =
  let forward_anchor_nodes, backward_anchor_nodes =
    get_anchor_nodes c.parse_tables c.anchor_symbol
  in
  let forward_stacks =
    List.map (initialise_stack Forward (List.nth g.forward_tokens 0)) forward_anchor_nodes
  in
  let backward_stacks =
    List.map
      (initialise_stack Backward (List.nth g.reverse_tokens 0))
      backward_anchor_nodes
  in
  { g with stacks = forward_stacks @ backward_stacks }
;;

let initialise_stacks =
  Graph.(
    ask
    >>= fun c ->
    get
    >>= fun g ->
    match g.stacks with
    | [] -> put (initialise_stacks_helper c g) >>= fun _ -> ask
    | _ -> ask)
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

let rec construct_ast () =
  Graph.(
    ask
    >>= fun (c : glr_config) ->
    get
    >>= fun (g : graph) ->
    let updated_stacks =
      List.map (update_stack c) g.stacks
      |> List.filter (fun s -> not (NodeMap.is_empty s.top))
        (* Seems to work till here. 29 states -> 12 states*)
      |> List.map (fun s ->
        let s', _ = Stack.(run_stack (apply_actions_to_stack c) s) in
        s')
    in
    let g' = { g with stacks = updated_stacks } in
    put g >>= fun _ -> if all_blocked g'.stacks then return g' else construct_ast ())
;;
(* let stacks, node_action_pairs = get_all_actions c g.stacks in *)
(* let updated_stacks = update_all_stacks_with_actions stacks node_action_pairs in *)
(* let new_stacks = apply_actions_to_all_stacks c updated_stacks node_action_pairs in *)
(* let g' = { g with stacks = new_stacks } in *)
(* put g' >>= fun _ -> if all_blocked g'.stacks then return g' else construct_ast ()) *)
