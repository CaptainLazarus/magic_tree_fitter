open Magic_tree_fitter.Grammar_reader
open Magic_tree_fitter.Parse_table_constructor

let () =
  Printexc.record_backtrace true;
  try
    let _grammar = "grammars/lisp.g4" |> extract_grammar |> create_parse_tables in
    print_string "--------\n"
  with
  | exn ->
    Printf.eprintf
      "Unhandled exception: %s\n%s\n"
      (Printexc.to_string exn)
      (Printexc.get_backtrace ())
;;
