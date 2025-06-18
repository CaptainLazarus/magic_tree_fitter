open Magic_tree_fitter.Grammar_reader
open Magic_tree_fitter.Parse_table_constructor

let () =
  let _grammar = "grammars/lisp.g4" |> extract_grammar |> create_parse_table in
  print_string "--------\n"
;;
