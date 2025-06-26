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

let suite =
  [ "Test First of Terminal Symbol", test_first_of_terminal
  ; "Test First of NonTerminal Symbol", test_first_of_non_terminal
  ; ( "Test first of mutli symbol list with an epsilon fallthrough"
    , test_if_epsilon_causes_fallthrough_to_next_symbol )
  ; "Test if epsilon is added to first set", test_if_epsilon_is_added_to_first_set
    (* ; "Test if closure works", test_closure_of_initial_item_set *)
    (* ; "Test if goto works", test_goto_of_s0_item_set *)
  ; "Test const_states", test_const_states_generation
  ]
;;
