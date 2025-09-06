open Gss
open Domain_types
open Glr_utils

let debug_iteration_start stacks_count =
  Printf.printf "construct_ast: processing %d stacks\n%!" stacks_count
;;

let get_next_action_for_node (state : int) (sym : symbol) parse_table =
  match Hashtbl.find_opt parse_table (state, sym) with
  | None -> []
  | Some s -> s
;;

let get_next_actions_for_stack parse_table (s : stack) =
  NodeSet.fold
    (fun e acc ->
       let actions = get_next_action_for_node e.state s.next_token.token parse_table in
       (e, actions) :: acc)
    s.top
    []
;;

let get_next_actions_for_stack_direction c stack =
  if stack.direction = Forward
  then get_next_actions_for_stack (get_forward_parse_table c.parse_tables) stack
  else get_next_actions_for_stack (get_backward_parse_table c.parse_tables) stack
;;

let next_action_for_stacks (c : glr_config) (g : graph) =
  List.map (fun s -> s, get_next_actions_for_stack_direction c s) g.stacks
;;

let filter_stacks_with_actions
      (stack_action_pairs : (stack * (gss_node * action list) list) list)
  =
  stack_action_pairs
  |>
  let filter_empty_action_lists =
    List.filter (fun (node, action_list) -> action_list <> [])
  in
  let filter_top_nodes_with_no_actions = List.map filter_empty_action_lists in
  List.filter (fun (s, top_nodes) -> top_nodes <> [])
;;

let get_all_actions (c : glr_config) (g : graph) =
  next_action_for_stacks c g |> filter_stacks_with_actions |> List.split
;;
