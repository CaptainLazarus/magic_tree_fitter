open Domain_types
open Grammar_reader_utils
(* open SymbolSet *)

let get_lhs_productions (g : grammar) (lhs : symbol) : production_rule list =
  List.filter (fun x -> x.lhs = lhs) g
;;

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

(* let rec closure (g : grammar) (l : LR1ItemSet.t) : LR1ItemSet.t = *)
(*   closure_helper g l LR1ItemSet.empty *)
(**)
(* and closure_helper (g : grammar) (l : LR1ItemSet.t) (acc : LR1ItemSet.t) = *)
(*   match l with *)
(*   | (p, j, a) :: xs -> *)
(*     let current_lhs = List.nth p.rhs j in *)
(*     let lhs_productions = get_lhs_productions g current_lhs in *)
(*     let first_set = first g in *)
(*     assert false *)
(* ;; *)
(**)
(* let const_states (g : grammar) : LR1ItemSetSet.t = *)
(*   let rec const_state_helper (g : grammar) (l : LR1ItemSet.t) acc = *)
(**)
(*   in *)
(*   let initial_item : lr1_item = List.hd g, 0, EOF in *)
(*   let initial_item_set = closure g (LR1ItemSet.add initial_item LR1ItemSet.empty) in *)
(*   let c = const_state_helper g initial_item_set LR1ItemSetSet.empty in *)
(*   c *)
(* ;; *)

(* Assuming EOF rule is at the top. This assumption is only for v1.0 *)
(* EOF Problem *)
(* 1. EOF not at the beginning -> C / CPP *)
(* 2. Multiple EOF -> Python -> Multiple entry points since multiple types of files to parse. Crazy. *)
let augment_grammar (g : grammar) : grammar =
  match g with
  | { lhs; rhs } :: rest ->
    let rhs' = List.rev (List.tl (List.rev rhs)) in
    { lhs = NonTerminal "S'"; rhs = [ lhs; EOF ] } :: { lhs; rhs = rhs' } :: rest
  | [] -> failwith "Empty Grammar"
;;

(* 1. Augment grammar first. Add rule {lhs: s' , rhs : s}. *)
(* : (int * symbol, action) Hashtbl.t *)
let create_parse_table (g : grammar) = g |> augment_grammar |> dump_grammar
