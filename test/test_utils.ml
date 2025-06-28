open Alcotest
open Magic_tree_fitter.Grammar_reader
open Magic_tree_fitter.Domain_types

type suite = string * (unit -> unit)

let create_test ?(test_type = `Quick) name f = test_case name test_type f
let create_test_suite (s : suite list) = List.map (fun (name, f) -> create_test name f) s
let fixture_path = "../grammars/lisp.g4"
let content = read_file fixture_path |> remove_comments
let grammar = fixture_path |> extract_grammar
let min_grammar = "../grammars/min_grammar.g4" |> extract_grammar
let min_grammar_epsilon = "../grammars/min_epsilon_grammar.g4" |> extract_grammar

(* Testables and pp *)
let pp_symbol fmt = function
  | Terminal t -> Format.fprintf fmt "Terminal(%s)" t
  | NonTerminal nt -> Format.fprintf fmt "NonTerminal(%S)" nt
  | Epsilon -> Format.fprintf fmt "Epsilon"
  | EOF -> Format.fprintf fmt "EOF"
;;

let symbol_testable = testable pp_symbol ( = )
let production_testable = list symbol_testable
let production_list_testable = list production_testable

let rule_testable =
  testable
    (fun fmt { lhs; rhs } ->
       Format.fprintf
         fmt
         "{ lhs = %a; rhs = %a }"
         pp_symbol
         lhs
         (pp production_testable)
         rhs)
    ( = )
;;
