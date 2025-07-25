open Alcotest
open Magic_tree_fitter.Parse_table_constructor
open Magic_tree_fitter.Domain_types
open Magic_tree_fitter.Dump
open Test_utils

let symbol_set = SymbolSet.of_list

(* FIRST TESTS *)

let test_first_empty_list () =
  let g = grammar in
  let result = first g [] in
  let expected = symbol_set [ Epsilon ] in
  check bool "first of empty list = {ε}" true (SymbolSet.equal result expected)
;;

let test_first_of_terminal () =
  let expected = symbol_set [ Terminal "(" ] in
  let actual = first [] [ Terminal "("; NonTerminal "s" ] in
  check bool "first of terminal symbol" true (SymbolSet.equal actual expected)
;;

let test_first_of_non_terminal () =
  let g = dump_grammar grammar in
  let expected = symbol_set [ Terminal "(" ] in
  let actual = first g [ NonTerminal "list" ] in
  check bool "first of list" true (SymbolSet.equal actual expected)
;;

let test_first_with_epsilon_fallthrough () =
  let g = dump_grammar grammar in
  let expected = symbol_set [ Terminal "("; Terminal "ATOMIC_SYMBOL"; EOF ] in
  let actual = first g [ NonTerminal "s_expression*"; EOF ] in
  check bool "first with epsilon and EOF" true (SymbolSet.equal actual expected)
;;

let test_first_adds_epsilon () =
  let g = dump_grammar grammar in
  let expected = symbol_set [ Terminal "("; Terminal "ATOMIC_SYMBOL"; Epsilon ] in
  let actual = first g [ NonTerminal "s_expression*" ] in
  check bool "first includes epsilon" true (SymbolSet.equal actual expected)
;;

let test_epsilon_via_desugared_plus () =
  let g = min_grammar_epsilon |> dump_grammar in
  let a_star_first = first g [ NonTerminal "a*" ] in
  let a_star_eof_first = first g [ NonTerminal "a*"; EOF ] in
  check bool "a* first includes B" true (SymbolSet.mem (Terminal "B") a_star_first);
  check bool "a* first includes epsilon" true (SymbolSet.mem Epsilon a_star_first);
  check
    bool
    "first(a* EOF) includes B and EOF"
    true
    (SymbolSet.equal a_star_eof_first (symbol_set [ Terminal "B"; EOF ]))
;;

(* CLOSURE TESTS *)
let test_closure_empty_set_returns_empty () =
  let g = min_grammar_epsilon in
  let item_set = closure g LR1ItemSet.empty in
  check bool "closure on ∅ = ∅" true (LR1ItemSet.is_empty item_set)
;;

let test_closure_ignores_terminal_after_dot () =
  let g = min_grammar_epsilon in
  let item =
    { lhs = NonTerminal "a"; rhs = [ Terminal "B"; NonTerminal "a*" ] }, 0, Terminal "B"
  in
  let item_set = closure g (LR1ItemSet.singleton item) in
  (* Should contain only the original item *)
  check bool "closure on terminal doesn't expand" true (LR1ItemSet.cardinal item_set = 1)
;;

let test_closure_chains_indirect_nonterminals () =
  let g = min_grammar_epsilon |> dump_grammar in
  let item = { lhs = NonTerminal "S'"; rhs = [ NonTerminal "s" ] }, 0, EOF in
  let item_set = closure g (LR1ItemSet.singleton item) in
  let has_indirect =
    LR1ItemSet.exists (fun (p, _, _) -> p.lhs = NonTerminal "a") item_set
  in
  dump_lr1_set item_set;
  check bool "closure includes indirect productions" true has_indirect
;;

let test_closure_adds_epsilon_production () =
  let g = min_grammar_epsilon in
  let item = { lhs = NonTerminal "s"; rhs = [ NonTerminal "a*" ] }, 0, EOF in
  let item_set = closure g (LR1ItemSet.singleton item) in
  let found =
    LR1ItemSet.exists
      (fun (p, _, _) -> p.lhs = NonTerminal "a*" && p.rhs = [ Epsilon ])
      item_set
  in
  check bool "closure includes epsilon production for a*" true found
;;

let test_closure_expands_lookaheads () =
  let g = min_grammar_epsilon in
  let initial_item = { lhs = NonTerminal "S'"; rhs = [ NonTerminal "s" ] }, 0, EOF in
  let item_set = closure g (LR1ItemSet.singleton initial_item) in
  let expected =
    LR1ItemSet.exists
      (fun (p, _, la) ->
         p.lhs = NonTerminal "a"
         && (match p.rhs with
             | Terminal "B" :: _ -> true
             | _ -> false)
         && symbol_compare la EOF = 0) (* Changed from Terminal "B" to EOF *)
      item_set
  in
  check bool "closure contains a → B a a* , $" true expected
;;

(* Sus test. Ok-ing for now, but dont assume this is right. Need to think this one through. Might let some cases passthrough that shouldn't*)
let test_closure_is_idempotent_for_initial_item_set () =
  let x = min_grammar_epsilon in
  let initial_item : lr1_item = List.hd x, 0, EOF in
  let initial_item_set = closure x (LR1ItemSet.add initial_item LR1ItemSet.empty) in
  let expected = initial_item_set in
  let actual = closure x initial_item_set in
  let msg = "checks if closure is correct for s0 of the augmented production" in
  dump_lr1_item initial_item;
  dump_lr1_set expected;
  dump_lr1_set actual;
  check bool msg true (LR1ItemSet.equal actual expected)
;;

(* TODO : How the absolute fuck is the test not passing ? Running this on main you get the right grammar. Fuckin hell. Find out cause and fix this. State due to seen symbols ?*)
let test_closure_multiple_lookaheads () =
  (* Grammar: 
     S' → s
     s → a a* b b*
     a → "A" a
     b → "B" b
     b* → b b*
     b* → ε
  *)
  let g = two_star_grammar |> dump_grammar in
  (* Dump the original grammar for verification *)
  print_endline "\n=== Original Grammar ===";
  let item =
    ( { lhs = NonTerminal "s"
      ; rhs = [ NonTerminal "a"; NonTerminal "a*"; NonTerminal "b"; NonTerminal "b*" ]
      }
    , 0
    , EOF )
  in
  print_endline "\n=== Initial Item ===";
  dump_lr1_item item;
  let closed = closure g (LR1ItemSet.singleton item) in
  (* Dump the full closure set *)
  print_endline "\n=== Full Closure Set ===";
  dump_lr1_set closed;
  (* Focus on a* items *)
  let astar_items =
    LR1ItemSet.filter (fun (p, _, _) -> p.lhs = NonTerminal "a*") closed
  in
  print_endline "\n=== a* Items ===";
  dump_lr1_set astar_items;
  (* Verify the ε production has both "B" and EOF as lookaheads *)
  let has_b =
    LR1ItemSet.exists
      (fun (p, dot, la) -> p.lhs = NonTerminal "a*" && dot = 0 && la = Terminal "B")
      astar_items
  in
  let has_eof =
    LR1ItemSet.exists
      (fun (p, dot, la) -> p.lhs = NonTerminal "a*" && dot = 0 && la = EOF)
      astar_items
  in
  print_endline ("\nHas B lookahead: " ^ string_of_bool has_b);
  print_endline ("Has EOF lookahead: " ^ string_of_bool has_eof);
  (* Also check the FIRST sets for debugging *)
  print_endline "\n=== FIRST(a* b b* EOF) ===";
  let first_set = first g [ NonTerminal "a*"; NonTerminal "b"; NonTerminal "b*"; EOF ] in
  dump_symbol_set first_set;
  check bool "Multiple lookaheads for ε in a*" true (has_b && has_eof)
;;

let test_const_states_generation () =
  let x = min_grammar |> dump_grammar in
  let expected = LR1ItemSetSet.empty in
  let msg = "checks if const_states is generated correctly" in
  let actual = const_states x in
  dump_const_states expected;
  dump_const_states actual;
  check bool msg true (LR1ItemSetSet.equal actual expected)
;;

let test_const_table () =
  let x = min_grammar |> dump_grammar in
  (* let expected = Hashtbl.create 32 in *)
  let msg = "checks if const_table is generated correctly" in
  let actual = const_table x in
  dump_parse_table_to_file actual "output.txt";
  check bool msg true false
;;

let test_is_accepting () =
  let g = min_grammar in
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
  let g = min_grammar in
  let states = const_states g |> LR1ItemSetSet.to_list in
  let s0 = List.nth states 0 in
  match get_symbol_after_dot (List.hd (LR1ItemSet.elements s0)) with
  | Some sym ->
    let i = get_next_state g s0 sym states in
    check bool "goto result is in state list" true (Option.is_some i)
  | None -> ()
;;

let test_goto_items () =
  let g = min_grammar_epsilon in
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
  let g = min_grammar_epsilon |> dump_grammar in
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
  let g = min_grammar_epsilon in
  let states = const_states g in
  dump_const_states states;
  assert false
;;

(* let first = [] *)
(* let closure = [] *)

let suite =
  [ "First of terminal", test_first_of_terminal
  ; "First of empty list raises", test_first_empty_list
  ; "First of nonterminal", test_first_of_non_terminal
  ; "First set with epsilon fallthrough", test_first_with_epsilon_fallthrough
  ; "First set includes epsilon", test_first_adds_epsilon
  ; "desugared plus handles epsilon", test_epsilon_via_desugared_plus
  ; "closure ignores terminal after dot", test_closure_ignores_terminal_after_dot
  ; "closure chains indirect expansions", test_closure_chains_indirect_nonterminals
  ; "closure includes epsilon productions", test_closure_adds_epsilon_production
  ; "Test closure expands lookaheads", test_closure_expands_lookaheads
  ; "Test if closure is idempotent", test_closure_is_idempotent_for_initial_item_set
  ; "Test deepseek", test_closure_multiple_lookaheads
    (* ; "Test if goto works", test_goto_of_s0_item_set *)
    (* ; "Test const_states", test_const_states_generation *)
    (* ; "Test const_table", test_const_table *)
    (* ; "Test is_accepting", test_is_accepting *)
    (* ; "Test add_action no duplicate", test_add_action_no_dup *)
    (* ; "Test get_next_state", test_get_next_state *)
    (* ; "Test epsilon via desugared plus", test_epsilon_via_desugared_plus *)
    (* ; "Test goto_items advances dot", test_goto_items *)
    (* ; "Test parse table includes Accept on EOF", test_parse_table_accept *)
    (* ; "Find const_states", test_debug_const_states *)
  ]
;;
