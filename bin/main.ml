open Magic_tree_fitter.Grammar_reader

let () =
  let cleaned_grammar = read_file "grammars/lisp.g4" |> remove_comments in
  print_string cleaned_grammar
