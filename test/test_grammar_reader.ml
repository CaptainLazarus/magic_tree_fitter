open Alcotest
open Magic_tree_fitter.Grammar_reader
open Test_utils

let test_remove_comments () =
  let cleaned = remove_comments content in
  check bool "keeps rules" (String.contains cleaned 'l') true;
  check bool "removes // comments" (String.contains cleaned '/') false

let test_read_file () =
  print_string content;
  check bool "starts with grammar"
    (String.starts_with ~prefix:"grammar" content)
    true

let suite =
  [
    ("Removes comments", test_remove_comments);
    ("Reads grammar file", test_read_file);
  ]
