open Domain_types
open Dump

(* let get_lhs_productions (g : grammar) (lhs : symbol) : production_rule list = *)
(*   List.filter (fun x -> x.lhs = lhs) g *)
(* ;; *)
(**)
let get_lhs_productions g lhs =
  let prods = List.filter (fun x -> x.lhs = lhs) g in
  (* Printf.printf "LHS: %s -> %d rules\n" (string_of_symbol lhs) (List.length prods); *)
  prods
;;

let get_symbol_after_dot (p, j, _) : symbol option = List.nth_opt p.rhs j

(* TODO : Write tests for this. No idea how correct *)
let rec first (g : grammar) (s : symbol list) : SymbolSet.t =
  let rec first_helper (g : grammar) (s : symbol list) (acc : SymbolSet.t) : SymbolSet.t =
    match s with
    | [] ->
      SymbolSet.add Epsilon acc
      (* failwith "Empty production. How ?" *)
      (*Little sus this one. Would you ever get an empty list ? 
      That means you never hit a terminal before. Or an epsilon. Or an EOF. 
      Very very sus. Failing for now*)
      (* If you send in a single NonTerminal that has Epsilon, 
         then you will get an empty list. Goddamn. Solved the above concern of the sus *)
    | Terminal x :: _ -> SymbolSet.add (Terminal x) acc
    | NonTerminal x :: xs ->
      (* Printf.printf "First lookup for NonTerminal: %s\n" x; *)
      let lhs_productions = get_lhs_productions g (NonTerminal x) in
      let rhs_productions = List.map (fun x -> x.rhs) lhs_productions in
      let first_list =
        rhs_productions
        |> List.map (fun rhs -> first g rhs)
        |> List.fold_left SymbolSet.union SymbolSet.empty
      in
      let acc' = SymbolSet.union acc first_list in
      if SymbolSet.mem Epsilon acc'
      then first_helper g xs (SymbolSet.remove Epsilon acc')
      else acc'
    | Epsilon :: _ -> SymbolSet.add Epsilon acc
    | EOF :: _ -> SymbolSet.add EOF acc
  in
  first_helper g s SymbolSet.empty
;;

let get_set_product (productions : production_rule list) (symbols : SymbolSet.t) =
  let symbols_list = SymbolSet.to_list symbols in
  List.map (fun a -> List.map (fun b -> a, 0, b) symbols_list) productions |> List.concat
;;

let rec closure_helper (g : grammar) (work_list : lr1_item Queue.t) (s : LR1ItemSet.t) =
  if Queue.is_empty work_list
  then s
  else (
    let p, j, a = Queue.take work_list in
    let sym = get_symbol_after_dot (p, j, a) in
    match sym with
    | Some current_symbol ->
      let lhs_productions = get_lhs_productions g current_symbol in
      let first_list = first g [ current_symbol; a ] in
      let lr1_items_found = get_set_product lhs_productions first_list in
      let filtered_seen_items =
        List.filter (fun x -> not (LR1ItemSet.mem x s)) lr1_items_found
      in
      let _ = Queue.add_seq work_list (List.to_seq filtered_seen_items) in
      let updated_state = LR1ItemSet.add_seq (List.to_seq filtered_seen_items) s in
      closure_helper g work_list updated_state
    | None -> closure_helper g work_list s)
;;

let closure (g : grammar) (item_set : LR1ItemSet.t) : LR1ItemSet.t =
  closure_helper g (Queue.of_seq (LR1ItemSet.to_seq item_set)) item_set
;;

let goto_items (s : LR1ItemSet.t) (x : symbol) : LR1ItemSet.t =
  List.fold_left
    (fun acc (p, j, a) ->
       match get_symbol_after_dot (p, j, a) with
       | None -> acc
       | Some sym ->
         if sym = x
         then
           (* dump_symbol sym; *)
           LR1ItemSet.add (p, j + 1, a) acc
         else acc)
    LR1ItemSet.empty
    (LR1ItemSet.to_list s)
;;

let rec const_states_helper
          (g : grammar)
          (work_list : LR1ItemSet.t Queue.t)
          (c : LR1ItemSetSet.t)
          (symbols : symbol list)
  : LR1ItemSetSet.t
  =
  if Queue.is_empty work_list
  then c
  else (
    let current_set = Queue.take work_list in
    let non_empty_sets =
      symbols
      |> List.map (fun x -> closure g (goto_items current_set x))
      |> List.filter (fun x -> not (LR1ItemSet.is_empty x))
    in
    let new_sets = List.filter (fun x -> not (LR1ItemSetSet.mem x c)) non_empty_sets in
    List.iter (fun x -> Queue.add x work_list) new_sets;
    let c' = LR1ItemSetSet.add_seq (List.to_seq new_sets) c in
    const_states_helper g work_list c' symbols)
;;

let const_states (g : grammar) : LR1ItemSetSet.t =
  let initial_item = List.hd g, 0, EOF in
  let initial_item_set = closure g (LR1ItemSet.add initial_item LR1ItemSet.empty) in
  let work_list = Queue.create () in
  let symbol_set =
    List.fold_left
      (fun acc { lhs; rhs } ->
         SymbolSet.add lhs acc
         |> fun acc' -> List.fold_left (fun acc sym -> SymbolSet.add sym acc) acc' rhs)
      SymbolSet.empty
      g
  in
  let _ = Queue.add initial_item_set work_list in
  const_states_helper
    g
    work_list
    (LR1ItemSetSet.add initial_item_set LR1ItemSetSet.empty)
    (SymbolSet.to_list symbol_set)
;;

(* let const_states (g:grammar) =  *)

(* Assuming EOF rule is at the top. This assumption is only for v1.0 *)
(* EOF Problem *)
(* 1. EOF not at the beginning -> C / CPP *)
(* 2. Multiple EOF -> Python -> Multiple entry points since multiple types of files to parse. Crazy. *)
let augment_grammar (g : grammar) : grammar =
  match g with
  | { lhs; rhs } :: rest ->
    let rhs' = List.rev (List.tl (List.rev rhs)) in
    { lhs = NonTerminal "S'"; rhs = [ lhs ] } :: { lhs; rhs = rhs' } :: rest
  | [] -> failwith "Empty Grammar"
;;

(* 1. Augment grammar first. Add rule {lhs: s' , rhs : s}. *)
(* : (int * symbol, action) Hashtbl.t *)
let create_parse_table (g : grammar) = g |> augment_grammar |> dump_grammar
