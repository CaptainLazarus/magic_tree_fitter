open Test_utils

let () =
  Alcotest.run
    "All tests"
    [ "Grammar Parsing", create_test_suite Test_grammar_reader.suite
    ; "Parse Table Construction", create_test_suite Test_parse_table_construction.suite
    ]
;;
