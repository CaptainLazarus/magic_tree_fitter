open Gss
open Core_algo

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

let construct_ast (g : graph) =
  let max_iter = 100 in
  let rec aux iter g =
    if iter >= max_iter
    then (
      Printf.printf "RECURSION LIMIT REACHED\n%!";
      failwith "construct_ast: too many iterations");
    Gss_debug.debug_iteration_start (List.length g.stacks);
    (* Get actions *)
    let new_stacks, next_actions =
      List.map
        (fun s ->
           if s.direction = Forward
           then s, get_next_actions_for_stack (get_forward_parse_table g.parse_tables) s
           else s, get_next_actions_for_stack (get_backward_parse_table g.parse_tables) s)
        g.stacks
      |> List.filter (fun (_, node_action_pairs) ->
        List.exists (fun (_, actions) -> actions <> []) node_action_pairs)
      |> List.split
    in
    Gss_debug.debug_actions_found next_actions;
    (* Update stacks *)
    let updated_stacks = List.map2 update_stack_with_actions new_stacks next_actions in
    let g1 = { g with stacks = updated_stacks } in
    (* Apply actions *)
    let final_stacks =
      List.map2 (apply_all_actions_to_stack g1) updated_stacks next_actions
    in
    let g2 = { g1 with stacks = final_stacks } in
    Gss_debug.debug_blocked_check g2.stacks;
    Printf.printf "all_blocked check: %b\n%!" (all_blocked g2.stacks);
    Gss_debug.debug_actions_after_apply g2.stacks;
    if all_blocked g2.stacks then g2 else aux (iter + 1) g2
  in
  aux 0 g
;;
