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

let get_remaining_symbols (p, j, _) =
  if j + 1 >= List.length p.rhs then [] else List.drop (j + 1) p.rhs
;;

(* TODO : Write tests for this. No idea how correct *)
let first (g : grammar) (s : symbol list) : SymbolSet.t =
  let rec first_helper
            (g : grammar)
            (s : symbol list)
            (seen : SymbolSet.t)
            (acc : SymbolSet.t)
    : SymbolSet.t
    =
    match s with
    | [] -> SymbolSet.add Epsilon acc
    (* failwith "Empty production. How ?" *)
    (*Little sus this one. Would you ever get an empty list ? 
      That means you never hit a terminal before. Or an epsilon. Or an EOF. 
      Very very sus. Failing for now*)
    (* If you send in a single NonTerminal that has Epsilon, 
         then you will get an empty list. Goddamn. Solved the above concern of the sus *)
    (* Changing this again. Making this acc. Don't need the epsilon rn*)
    | Terminal x :: _ -> SymbolSet.add (Terminal x) acc
    | NonTerminal x :: xs ->
      (* Printf.printf "First lookup for NonTerminal: %s\n" x; *)
      let lhs_productions = get_lhs_productions g (NonTerminal x) in
      let rhs_productions = List.map (fun x -> x.rhs) lhs_productions in
      if SymbolSet.mem (NonTerminal x) seen
      then
        if List.exists (fun x -> x = [ Epsilon ]) rhs_productions
        then first_helper g xs seen acc
        else acc
      else (
        let seen_updated = SymbolSet.add (NonTerminal x) seen in
        let first_list =
          rhs_productions
          |> List.map (fun rhs -> first_helper g rhs seen_updated acc)
          |> List.fold_left SymbolSet.union SymbolSet.empty
        in
        let acc' = SymbolSet.union acc first_list in
        if SymbolSet.mem Epsilon acc'
        then first_helper g xs seen_updated (SymbolSet.remove Epsilon acc')
        else acc')
    | Epsilon :: _ -> SymbolSet.add Epsilon acc
    | EOF :: _ -> SymbolSet.add EOF acc
  in
  (* Printf.printf "\n[5] First\n"; *)
  (* flush stdout; *)
  first_helper g s SymbolSet.empty SymbolSet.empty
;;

(* Redundant, but leave it in. will remove after confirming not useful at all *)
let first_for_lookahead g symbols = first g symbols |> fun x -> SymbolSet.remove Epsilon x

let get_set_product (productions : production_rule list) (symbols : SymbolSet.t) =
  let symbols_list = SymbolSet.to_list symbols in
  List.map (fun a -> List.map (fun b -> a, 0, b) symbols_list) productions |> List.concat
;;

let rec closure_helper (g : grammar) (work_list : lr1_item Queue.t) (s : LR1ItemSet.t) =
  (* Printf.printf *)
  (*   "\n================================================================================\n"; *)
  (* Printf.printf "\n[4] Current worklist:\n"; *)
  (* Queue.iter dump_lr1_item work_list; *)
  (* Printf.printf "\n[4] Current set:\n"; *)
  (* dump_lr1_set s; *)
  (* flush stdout; *)
  if Queue.is_empty work_list
  then
    (* Printf.printf "\n[4.1] Returned Set:\n"; *)
    (* dump_lr1_set s; *)
    (* flush stdout; *)
    s
  else (
    let p, j, a = Queue.take work_list in
    let sym = get_symbol_after_dot (p, j, a) in
    match sym with
    | Some current_symbol ->
      (* Printf.printf "\n[4.2] Found a symbol: %s\n" (string_of_symbol current_symbol); *)
      (* flush stdout; *)
      let lhs_productions = get_lhs_productions g current_symbol in
      (* Printf.printf "\n[4.3] Got LHS productions\n"; *)
      (* flush stdout; *)
      let remaining = get_remaining_symbols (p, j, a) in
      (* Printf.printf "\n[4.4] Remaining Symbols\n"; *)
      (* flush stdout; *)
      let first_list = first_for_lookahead g (remaining @ [ a ]) in
      (* Printf.printf "\n[4.5] First List\n"; *)
      (* flush stdout; *)
      let lr1_items_found = get_set_product lhs_productions first_list in
      (* Printf.printf "\n[4.6] Set product found \n"; *)
      (* flush stdout; *)
      let filtered_seen_items =
        List.filter (fun x -> not (LR1ItemSet.mem x s)) lr1_items_found
      in
      let filtered_seen_items =
        (* Printf.printf "Adding %d new items\n" (List.length filtered_seen_items); *)
        (* flush stdout; *)
        (* List.iter *)
        (*   (fun item -> *)
        (*      dump_lr1_item item; *)
        (*      flush stdout) *)
        (*   filtered_seen_items; *)
        filtered_seen_items
      in
      let _ = Queue.add_seq work_list (List.to_seq filtered_seen_items) in
      let updated_state = LR1ItemSet.add_seq (List.to_seq filtered_seen_items) s in
      closure_helper g work_list updated_state
    | None -> closure_helper g work_list s)
;;

let closure (g : grammar) (item_set : LR1ItemSet.t) : LR1ItemSet.t =
  (* print_string "\n[2] Reached Closure Table\n"; *)
  (* flush stdout; *)
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
  (* print_string "\n[1] Reached Const States\n"; *)
  (* flush stdout; *)
  let initial_item = List.hd g, 0, EOF in
  (* print_string "\n[1.1] Const States -> Closure\n"; *)
  (* flush stdout; *)
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

let is_accepting (g : grammar) (p : production_rule) : bool =
  match get_lhs_productions g (NonTerminal "S'") with
  | top :: _ -> p = top
  | [] -> false
;;

let get_next_state g (current : LR1ItemSet.t) (sym : symbol) (states : LR1ItemSet.t list)
  : int option
  =
  (* let next = goto_items current sym in *)
  (* print_string "\n[3] Get Next State -> Closure\n"; *)
  (* flush stdout; *)
  let next = closure g (goto_items current sym) in
  List.find_index (fun s -> LR1ItemSet.equal s next) states
;;

let add_action
      (tbl : (int * symbol, action list) Hashtbl.t)
      (state : int)
      (sym : symbol)
      (act : action)
  : unit
  =
  let key = state, sym in
  let existing = Hashtbl.find_opt tbl key |> Option.value ~default:[] in
  if List.mem act existing then () else Hashtbl.replace tbl key (act :: existing)
;;

let const_table_helper_debug
      (g : grammar)
      (state_index : int)
      ((p, dot_pos, lookahead) : lr1_item)
      (tbl : (int * symbol, action list) Hashtbl.t)
      (states : LR1ItemSet.t list)
  =
  print_endline "\n[const_table_helper]";
  (* Printf.printf "  State index: %d\n" state_index; *)
  (* Printf.printf "  Dot position: %d\n" dot_pos; *)
  (* Printf.printf "  Lookahead: %s\n" (string_of_symbol lookahead); *)
  (* Printf.printf *)
  (*   "  Production: %s -> %s\n" *)
  (*   (string_of_symbol p.lhs) *)
  (*   (String.concat " " (List.map string_of_symbol p.rhs)); *)
  (* Printf.printf "  Table size: %d\n" (Hashtbl.length tbl); *)
  (* Printf.printf "  Total states: %d\n" (List.length states); *)
  let current_state = List.nth states state_index in
  match get_symbol_after_dot (p, dot_pos, lookahead) with
  | None ->
    (* Printf.printf "  Dot at end. "; *)
    if is_accepting g p
    then
      (* Printf.printf "Inserting [Accept] action.\n"; *)
      add_action tbl state_index EOF Accept
    else
      (* Printf.printf "Inserting [Reduce] for lookahead %s\n" (string_of_symbol lookahead); *)
      add_action tbl state_index lookahead (Reduce p)
  | Some Epsilon -> Printf.printf "  [Skip] Dot before Epsilon — skipping\n"
  | Some sym ->
    (* Printf.printf "  Dot before symbol: %s — computing GOTO...\n" (string_of_symbol sym); *)
    let next_set = goto_items current_state sym in
    if LR1ItemSet.is_empty next_set
    then Printf.printf "  [Skip] GOTO(%d, %s) = ∅\n" state_index (string_of_symbol sym)
    else (
      let next_state = get_next_state g current_state sym states in
      match next_state with
      | None ->
        Printf.printf
          "  [404] GOTO(%d, %s) not in canonical states!\n"
          state_index
          (string_of_symbol sym);
        (* Printf.printf "  Dumping computed next_set:\n"; *)
        (* dump_lr1_set next_set; *)
        (* Printf.printf "  Dumping all canonical states:\n"; *)
        List.iteri
          (fun i st ->
             Printf.printf "  --- State %d ---\n" i;
             dump_lr1_set st)
          states;
        failwith "[404] State not found"
      | Some next ->
        Printf.printf "  GOTO leads to state %d. Inserting action...\n" next;
        (match sym with
         | NonTerminal _ ->
           Printf.printf "  Inserting [Goto %d]\n" next;
           add_action tbl state_index sym (Goto next)
         | Terminal _ ->
           Printf.printf "  Inserting [Shift %d]\n" next;
           add_action tbl state_index sym (Shift next)
         | Epsilon | EOF -> failwith "Unexpected Epsilon or EOF in shift/goto"))
;;

let const_table_helper
      (g : grammar)
      (state_index : int)
      ((p, dot_pos, lookahead) : lr1_item)
      (tbl : (int * symbol, action list) Hashtbl.t)
      (states : LR1ItemSet.t list)
  =
  let current_state = List.nth states state_index in
  match get_symbol_after_dot (p, dot_pos, lookahead) with
  | None ->
    if is_accepting g p
    then add_action tbl state_index EOF Accept
    else add_action tbl state_index lookahead (Reduce p)
  | Some Epsilon -> ()
  | Some sym ->
    let next_set = goto_items current_state sym in
    if not (LR1ItemSet.is_empty next_set)
    then (
      match get_next_state g current_state sym states with
      | None -> failwith "[404] State not found"
      | Some next ->
        (match sym with
         | NonTerminal _ -> add_action tbl state_index sym (Goto next)
         | Terminal _ -> add_action tbl state_index sym (Shift next)
         | Epsilon | EOF -> failwith "Unexpected Epsilon or EOF in shift/goto"))
;;

(* I think you can with epsilon, but I don't think so with bloody EOF. I literally remove it. *)

let const_table (g : grammar) : (int * symbol, action list) Hashtbl.t =
  (* print_string "\n[0] Reached Const Table\n"; *)
  let states = g |> const_states |> LR1ItemSetSet.to_list in
  let tbl = Hashtbl.create ~random:false 0 in
  List.iteri
    (fun i state ->
       LR1ItemSet.iter (fun item -> const_table_helper g i item tbl states) state)
    states;
  tbl
;;

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

let reverse_grammar (g : grammar) : grammar =
  List.map (fun { lhs; rhs } -> { lhs; rhs = List.rev rhs }) g
;;

(* 1. Augment grammar first. Add rule {lhs: s' , rhs : s}. *)
(* : (int * symbol, action) Hashtbl.t *)
let create_parse_table (g : grammar) (* : (int * symbol, action list) Hashtbl.t list  *) =
  g
  |> augment_grammar
  |> const_table
  |> fun x ->
  dump_parse_table_to_file x ("parse_table_normal" ^ ".txt");
  x
;;

let create_parse_table_r (g : grammar) =
  g
  |> augment_grammar
  |> reverse_grammar
  |> const_table
  |> fun x ->
  dump_parse_table_to_file x ("parse_table_normal" ^ ".txt");
  x
;;

let create_parse_tables (g : grammar) (* : (int * symbol, action list) Hashtbl.t list  *) =
  g
  |> augment_grammar
  |> fun x ->
  [ x; reverse_grammar x ]
  (* |> List.map dump_grammar *)
  |> List.map const_table
  |> List.mapi (fun i x ->
    dump_parse_table_to_file x ("parse_table_" ^ string_of_int i ^ ".txt");
    x)
;;
