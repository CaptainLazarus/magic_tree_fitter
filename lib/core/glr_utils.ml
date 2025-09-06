open Gss
open Domain_types

(* Maunally verified that the lisp grammar forward states are working. Check backward ? And then assume this works. Will have to fix with automated tests *)
let initial_states_for_terminal
      (tables : (int * symbol, action list) Hashtbl.t list)
      (sym : symbol)
  : (int * int) list * (int * int) list
  =
  let extract_shift_states table =
    Hashtbl.fold
      (fun (state, symbol') actions acc ->
         match symbol', actions with
         | s, [ Shift x ] when s = sym -> (state, x) :: acc
         | _ -> acc)
      table
      []
  in
  match tables with
  | [ forward; reverse ] ->
    let ltr = extract_shift_states forward in
    let rtl = extract_shift_states reverse in
    ltr, rtl
  | _ -> failwith "Expected exactly two parse tables"
;;

let get_anchor_nodes parse_tables anchor =
  let create_anchor_node_from_list l =
    List.map
      (fun (x, y) ->
         { id = 0
         ; state = x
         ; edges = [ anchor, y ]
         ; parents = NodeIdSet.empty
         ; next_actions = []
         ; blocked_reductions = []
         })
      l
  in
  let forward_states, reverse_states =
    initial_states_for_terminal parse_tables anchor.token
  in
  let forward_anchor_nodes : gss_node list =
    create_anchor_node_from_list forward_states
  in
  let backward_anchor_nodes : gss_node list =
    create_anchor_node_from_list reverse_states
  in
  forward_anchor_nodes, backward_anchor_nodes
;;

let dump_parser_states xs ys =
  List.iter (fun (x, y) -> Printf.printf "\nForward States : %d %d\n" x y) xs;
  List.iter (fun (x, y) -> Printf.printf "\nBackward States : %d %d\n" x y) ys
;;

let get_forward_parse_table parse_tables = List.nth parse_tables 0
let get_backward_parse_table parse_tables = List.nth parse_tables 1

let find_opt predicate set =
  let filtered = NodeSet.filter predicate set in
  if NodeSet.is_empty filtered then None else Some (NodeSet.choose filtered)
;;
