open Magic_tree_fitter.Grammar_reader

let () =
  let _grammar = extract_grammar "grammars/lisp.g4" in
  print_string "--------\n"
;;
