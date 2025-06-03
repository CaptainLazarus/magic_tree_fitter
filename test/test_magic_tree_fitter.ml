open Test_utils

let () =
  Alcotest.run "All tests" [ "File Reading", create_test_suite Test_grammar_reader.suite ]
;;
