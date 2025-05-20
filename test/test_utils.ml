open Alcotest
open Magic_tree_fitter.Grammar_reader

type suite = string * (unit -> unit)

let create_test ?(test_type = `Quick) name f = test_case name test_type f

let create_test_suite (s : suite list) =
  List.map (fun (name, f) -> create_test name f) s

let fixture_path = "../grammars/lisp.g4"
let content = read_file fixture_path |> remove_comments
