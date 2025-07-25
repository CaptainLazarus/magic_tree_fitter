open Magic_tree_fitter.Grammar_reader
open Magic_tree_fitter.Parse_table_constructor
open Magic_tree_fitter.Core_algo

let () =
  Printexc.record_backtrace true;
  try
    let _grammar =
      let parse_tables = "grammars/lisp.g4" |> extract_grammar |> create_parse_tables in
      let _input = run_java_and_read_output () |> dump_token_list in
      get_ast parse_tables
    in
    print_string "--------\n"
  with
  | exn ->
    Printf.eprintf
      "Unhandled exception: %s\n%s\n"
      (Printexc.to_string exn)
      (Printexc.get_backtrace ())
;;
