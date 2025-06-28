open Alcotest
open Magic_tree_fitter.Parse_table_constructor
open Magic_tree_fitter.Domain_types
open Magic_tree_fitter.Dump
open Test_utils
(* open Magic_tree_fitter.Symbol_table *)

let test_first_of_terminal () =
  let x = [] in
  let expected =
    List.fold_left (fun acc elt -> SymbolSet.add elt acc) SymbolSet.empty [ Terminal "(" ]
  in
  let msg = "checks if first symbol is correct" in
  let actual = first x [ Terminal "("; NonTerminal "s" ] in
  check bool msg true (SymbolSet.equal actual expected)
;;

let test_first_of_non_terminal () =
  let x = grammar |> dump_grammar in
  let expected =
    List.fold_left (fun acc elt -> SymbolSet.add elt acc) SymbolSet.empty [ Terminal "(" ]
  in
  let msg = "checks if first set is correct for list -> (s_expression+)" in
  let actual = first x [ NonTerminal "list" ] in
  dump_symbol_set expected;
  dump_symbol_set actual;
  check bool msg true (SymbolSet.equal actual expected)
;;

let test_if_epsilon_causes_fallthrough_to_next_symbol () =
  let x = grammar |> dump_grammar in
  let expected =
    List.fold_left
      (fun acc elt -> SymbolSet.add elt acc)
      SymbolSet.empty
      [ Terminal "("; Terminal "ATOMIC_SYMBOL"; EOF ]
  in
  let msg = "checks if first set is correct for (s_expression* EOF) " in
  let actual = first x [ NonTerminal "s_expression*"; EOF ] in
  dump_symbol_set expected;
  dump_symbol_set actual;
  check bool msg true (SymbolSet.equal actual expected)
;;

let test_if_epsilon_is_added_to_first_set () =
  let x = grammar |> dump_grammar in
  let expected =
    List.fold_left
      (fun acc elt -> SymbolSet.add elt acc)
      SymbolSet.empty
      [ Terminal "("; Terminal "ATOMIC_SYMBOL"; Epsilon ]
  in
  let msg = "checks if first set is correct for (s_expression*) " in
  let actual = first x [ NonTerminal "s_expression*" ] in
  dump_symbol_set expected;
  dump_symbol_set actual;
  check bool msg true (SymbolSet.equal actual expected)
;;

let test_closure_of_initial_item_set () =
  let x = grammar in
  let initial_item : lr1_item = List.hd x, 0, EOF in
  let initial_item_set = closure x (LR1ItemSet.add initial_item LR1ItemSet.empty) in
  let expected = LR1ItemSet.empty in
  let msg = "checks if closure is correct for s0 of the augmented production" in
  let actual = closure x initial_item_set in
  dump_lr1_set expected;
  dump_lr1_set actual;
  check bool msg true (LR1ItemSet.equal actual expected)
;;

let test_const_states_generation () =
  let x = min_grammar |> augment_grammar |> dump_grammar in
  let expected = LR1ItemSetSet.empty in
  let msg = "checks if const_states is generated correctly" in
  let actual = const_states x in
  dump_const_states expected;
  dump_const_states actual;
  check bool msg true (LR1ItemSetSet.equal actual expected)
;;

let test_const_table () =
  let x = min_grammar |> augment_grammar |> dump_grammar in
  (* let expected = Hashtbl.create 32 in *)
  let msg = "checks if const_table is generated correctly" in
  let actual = const_table x in
  dump_parse_table_to_file actual "output.txt";
  check bool msg true false
;;

let test_is_accepting () =
  let g = min_grammar |> augment_grammar in
  let top =
    match get_lhs_productions g (NonTerminal "S'") with
    | x :: _ -> x
    | [] -> failwith "Missing augmented production"
  in
  check bool "is_accepting returns true for top rule" true (is_accepting g top)
;;

let test_add_action_no_dup () =
  let tbl = Hashtbl.create 4 in
  let key = 0, Terminal "id" in
  add_action tbl 0 (Terminal "id") (Shift 1);
  add_action tbl 0 (Terminal "id") (Shift 1);
  (* should not duplicate *)
  match Hashtbl.find_opt tbl key with
  | Some [ Shift 1 ] -> () (* OK *)
  | Some acts ->
    failwith ("Unexpected: " ^ String.concat "," (List.map string_of_action acts))
  | None -> failwith "No entry in table"
;;

let test_get_next_state () =
  let g = min_grammar |> augment_grammar in
  let states = const_states g |> LR1ItemSetSet.to_list in
  let s0 = List.nth states 0 in
  match get_symbol_after_dot (List.hd (LR1ItemSet.elements s0)) with
  | Some sym ->
    let i = get_next_state g s0 sym states in
    check bool "goto result is in state list" true (Option.is_some i)
  | None -> ()
;;

let test_epsilon_via_desugared_plus () =
  let g = min_grammar_epsilon |> augment_grammar |> dump_grammar in
  let a_star_first = first g [ NonTerminal "a*" ] in
  let a_star_eof_first = first g [ NonTerminal "a*"; EOF ] in
  check bool "a* first includes B" true (SymbolSet.mem (Terminal "B") a_star_first);
  check bool "a* first includes ε" true (SymbolSet.mem Epsilon a_star_first);
  check
    bool
    "first(a* EOF) includes B and EOF"
    true
    (SymbolSet.equal a_star_eof_first (SymbolSet.of_list [ Terminal "B"; EOF ]))
;;

let test_closure_expands_lookaheads () =
  let g = min_grammar_epsilon |> augment_grammar |> dump_grammar in
  let initial_item = { lhs = NonTerminal "S'"; rhs = [ NonTerminal "s" ] }, 0, EOF in
  let item_set = closure g (LR1ItemSet.singleton initial_item) in
  dump_lr1_set item_set;
  let expected =
    LR1ItemSet.exists
      (fun (p, _, la) ->
         p.lhs = NonTerminal "a"
         && (match p.rhs with
             | Terminal "B" :: _ -> true
             | _ -> false)
         && symbol_compare la (Terminal "B") = 0)
      item_set
  in
  check bool "closure contains a → B a a* , B" true expected
;;

let test_goto_items () =
  let g = min_grammar_epsilon |> augment_grammar in
  let s0 =
    closure
      g
      (LR1ItemSet.singleton
         ({ lhs = NonTerminal "S'"; rhs = [ NonTerminal "s" ] }, 0, EOF))
  in
  let after = goto_items s0 (NonTerminal "s") in
  (* after should contain item with dot advanced past s *)
  let contains_advanced =
    LR1ItemSet.exists (fun (p, j, _) -> p.lhs = NonTerminal "S'" && j = 1) after
  in
  check bool "goto_items advances dot" true contains_advanced
;;

let test_parse_table_accept () =
  let g = min_grammar_epsilon |> augment_grammar |> dump_grammar in
  let tbl = const_table g in
  dump_parse_table_to_file tbl "accept_debug.txt";
  let accept_found =
    Hashtbl.to_seq tbl
    |> Seq.filter (fun ((_, sym), _) -> sym = EOF)
    |> Seq.map snd
    |> Seq.exists
         (List.exists (function
            | Accept -> true
            | _ -> false))
  in
  check bool "parse table has Accept action under EOF" true accept_found
;;

let test_debug_const_states () =
  let g = min_grammar_epsilon |> augment_grammar in
  let states = const_states g in
  dump_const_states states;
  assert false
;;

let suite =
  [ "Test First of Terminal Symbol", test_first_of_terminal
  ; "Test First of NonTerminal Symbol", test_first_of_non_terminal
  ; ( "Test first of mutli symbol list with an epsilon fallthrough"
    , test_if_epsilon_causes_fallthrough_to_next_symbol )
  ; "Test if epsilon is added to first set", test_if_epsilon_is_added_to_first_set
    (* ; "Test if closure works", test_closure_of_initial_item_set *)
    (* ; "Test if goto works", test_goto_of_s0_item_set *)
    (* ; "Test const_states", test_const_states_generation *)
    (* ; "Test const_table", test_const_table *)
  ; "Test is_accepting", test_is_accepting
  ; "Test add_action no duplicate", test_add_action_no_dup
  ; "Test get_next_state", test_get_next_state
  ; "Test epsilon via desugared plus", test_epsilon_via_desugared_plus
  ; "Test closure expands lookaheads", test_closure_expands_lookaheads
  ; "Test goto_items advances dot", test_goto_items
    (* ; "Test parse table includes Accept on EOF", test_parse_table_accept *)
  ; "Find const_states", test_debug_const_states
  ]
;;
