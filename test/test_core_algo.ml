open Alcotest
open Magic_tree_fitter.Core_algo
open Magic_tree_fitter.Domain_types

let test_most_common_terminal_single () =
  let jsons =
    [ `Assoc [ "token", `String "ATOM"; "lexeme", `String "x" ]
    ; `Assoc [ "token", `String "ATOM"; "lexeme", `String "42" ]
    ; `Assoc [ "token", `String "DOT"; "lexeme", `String "." ]
    ]
  in
  let tokens = List.map token_info_of_json jsons in
  let actual =
    match most_common_terminal tokens with
    | Some { token = Terminal s; _ } -> s
    | _ -> "NONE"
  in
  check bool "most common is DOT or ATOM" true (actual = "DOT" || actual = "ATOM")
;;

let test_most_common_terminal_tie () =
  let jsons =
    [ `Assoc [ "token", `String "DOT"; "lexeme", `String "." ]
    ; `Assoc [ "token", `String "LPAREN"; "lexeme", `String "(" ]
    ; `Assoc [ "token", `String "DOT"; "lexeme", `String "." ]
    ; `Assoc [ "token", `String "LPAREN"; "lexeme", `String "(" ]
    ]
  in
  let tokens = List.map token_info_of_json jsons in
  let actual =
    match most_common_terminal tokens with
    | Some { token = Terminal s; _ } -> s
    | _ -> "NONE"
  in
  check bool "most common is DOT or LPAREN" true (actual = "DOT" || actual = "LPAREN")
;;

let test_most_common_terminal_none () =
  let jsons =
    [ `Assoc [ "token", `String "expr"; "lexeme", `String "x" ]
    ; `Assoc [ "token", `String "stmt"; "lexeme", `String "y" ]
    ]
  in
  let tokens = List.map token_info_of_json jsons in
  let expected = None in
  let actual =
    match most_common_terminal tokens with
    | Some { token = Terminal s; _ } -> Some s
    | _ -> None
  in
  check (option string) "no terminal symbols" expected actual
;;

(* Helper to create a mock table with some shift actions *)
let create_mock_table entries =
  let table = Hashtbl.create 10 in
  List.iter (fun (state, sym, action) -> Hashtbl.add table (state, sym) action) entries;
  table
;;

let suite =
  [ "most common terminal (single)", test_most_common_terminal_single
  ; "most common terminal (tie)", test_most_common_terminal_tie
  ; "most common terminal (none)", test_most_common_terminal_none
  ]
;;
