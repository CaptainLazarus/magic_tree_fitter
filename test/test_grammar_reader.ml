open Alcotest
open Magic_tree_fitter.Grammar_reader
open Magic_tree_fitter.Domain_types
open Magic_tree_fitter.Grammar_reader_utils
open Test_utils

let test_remove_comments () =
  let cleaned = remove_comments content in
  check bool "keeps rules" true (String.contains cleaned 'l');
  check bool "removes // comments" false (String.contains cleaned '/')
;;

let test_read_file () =
  (* print_string content; *)
  check bool "starts with grammar" true (String.starts_with ~prefix:"grammar" content)
;;

let test_first_word () =
  check string "first word is hello" "Hello" (first_word "Hello World")
;;

let test_is_uppercase () =
  check bool "checks if string is uppercase" true (is_uppercase "TEST")
;;

let test_is_not_uppercase () =
  check bool "checks if string is not uppercase" false (is_uppercase "test")
;;

(* TODO : Revise this test if antlr LHS productions can have mixed case *)
let test_is_not_completely_uppercase () =
  check bool "checks if string is not completely uppercase" true (is_uppercase "Test")
;;

let test_is_parse_rule () =
  let rule =
    {|
    lisp_
    : s_expression+ EOF
    ;
    |}
  in
  check bool "checks if rule is a parse rule" true (is_parse_rule rule)
;;

let test_is_not_parse_rule () =
  let rules =
    {|
    grammar lisp;

    ATOMIC_SYMBOL
        : LETTER ATOM_PART?
        ;

    fragment ATOM_PART
        : (LETTER | NUMBER) ATOM_PART
        ;

    |}
  in
  let result = not (List.exists is_parse_rule (filter_content rules)) in
  check bool "there are no parse rules" true result
;;

let test_split_rules () =
  let x = content |> filter_content in
  (* List.iter print_string x; *)
  check bool "number of lisp rules are 3" true (List.length x = 3)
;;

let test_convert_to_nonterminal_symbol () =
  let x = "a" in
  check bool "a is a Nonterminal" true (NonTerminal "a" = convert_to_symbol x)
;;

let test_convert_to_terminal_symbol () =
  let xs =
    [ "A", Terminal "A"; "AA", Terminal "AA"; "AA_", Terminal "AA_"; "'x'", Terminal "x" ]
  in
  List.iter
    (fun (input, expected) ->
       let msg = Printf.sprintf "check if %s symbol is converted" input in
       let actual = convert_to_symbol input in
       check symbol_testable msg expected actual)
    xs
;;

let test_convert_to_productions () =
  let test_cases =
    [ ( "'(' s_expression '.' s_expression ')'"
      , [ Terminal "("
        ; NonTerminal "s_expression"
        ; Terminal "."
        ; NonTerminal "s_expression"
        ; Terminal ")"
        ] )
      (* Add more (input, expected_production) pairs here *)
    ]
  in
  List.iter
    (fun (input, expected) ->
       let msg = Printf.sprintf "convert_to_production: %s" input in
       let actual = convert_to_production input in
       check production_testable msg expected actual)
    test_cases
;;

let suite =
  [ "Removes comments", test_remove_comments
  ; "Reads grammar file", test_read_file
  ; "Gets first word from string", test_first_word
  ; "Checks uppercase", test_is_uppercase
  ; "Checks if not uppercase", test_is_not_uppercase
  ; "Checks if not completely uppercase", test_is_not_completely_uppercase
  ; "Checks parse rule", test_is_parse_rule
  ; "Checks if no parse rules", test_is_not_parse_rule
  ; "Split Rules", test_split_rules
  ; "Checks if symbol is converted to a nonterminal", test_convert_to_nonterminal_symbol
  ; "Checks if symbol is converted to a terminal", test_convert_to_terminal_symbol
  ; ( "Checks if production string is converted to a production type"
    , test_convert_to_productions )
  ]
;;
