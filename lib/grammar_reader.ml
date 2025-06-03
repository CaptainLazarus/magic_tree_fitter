open Domain_types

(* FILE READING *)
let read_file path =
  let ic = open_in path in
  let len = in_channel_length ic in
  let content = really_input_string ic len in
  close_in ic;
  content
;;

(* Also trims the final string. *)
let remove_comments (input : string) : string =
  let re_block = Str.regexp "/\\*\\(.\\|\n\\)*?\\*/" in
  let re_line = Str.regexp "//.*" in
  input |> Str.global_replace re_block "" |> Str.global_replace re_line "" |> String.trim
;;

(* RULE READER *)
let first_word (line : string) =
  line
  |> String.trim
  |> String.split_on_char ' '
  |> List.find_opt (fun token -> token <> "")
  |> Option.value ~default:""
;;

(* This only checks if the first character is uppercase. 
  Assumption : ANTLR grammar files only have no mixed case LHS productions *)
let is_uppercase (s : string) : bool =
  String.length s > 0 && Char.uppercase_ascii s.[0] = s.[0]
;;

let starts_with_single_quote (s : string) : bool = String.length s > 0 && s.[0] = '\''

let starts_with_single_quote_or_is_uppercase (s : string) : bool =
  List.exists (fun f -> f s) [ is_uppercase; starts_with_single_quote ]
;;

(* Skip lines until a lone semicolon is found *)
let rec discard_rule (xs : string list) : string list =
  match xs with
  | [] -> []
  | x :: xs' -> if x |> String.trim <> ";" then discard_rule xs' else xs'
;;

let extract_production (_s : string) : production = failwith "not implemented"

let rec save_rule_helper (current_rule : rule) (xs : string list) : rule * string list =
  match xs with
  | [] -> current_rule, []
  | x :: xs ->
    let updated_current_rule =
      { current_rule with rhs = extract_production x :: current_rule.rhs }
    in
    save_rule_helper updated_current_rule xs
;;

(*
   basically, these are the lines for which it's guaranteed to start with a non terminal.
    So take first line, make that as part of the lhs, and then rhs has to be filled in.
*)
let save_rule (xs : string list) : rule * string list =
  match xs with
  | [] -> failwith "tf?"
  | x :: xs -> save_rule_helper { lhs = NonTerminal x; rhs = [] } xs
;;

(*
   based on g4 file semantics. grammar, fragment and lexer lines are skipped. Only parser rules matter
*)
let is_parse_rule (s : string) : bool =
  let word = first_word s in
  match word with
  | "" | " " | "grammar" | "fragment" -> false
  | _ -> not (is_uppercase word)
;;

let convert_to_symbol (s : string) : symbol =
  if starts_with_single_quote_or_is_uppercase s
  then
    if starts_with_single_quote s
    then Terminal (String.sub s 1 (String.length s - 2))
    else Terminal s
  else NonTerminal s
;;

let convert_to_production (prod : string) : symbol list =
  String.split_on_char ' ' prod |> List.map (fun s -> convert_to_symbol s)
;;

let convert_to_productions (rhs : string) : production list =
  String.split_on_char '|' rhs |> List.map (fun prod -> convert_to_production prod)
;;

let convert_to_rules (parse_rules : string list) : rule list =
  parse_rules
  |> List.map (fun x ->
    match String.split_on_char ':' x with
    | [ lhs_string; rhs_string ] ->
      let lhs = NonTerminal (String.trim lhs_string) in
      let rhs = convert_to_productions rhs_string in
      { lhs; rhs }
    | _ -> failwith "Invalid Rule Format")
;;

let filter_content (content : string) : string list =
  content |> String.split_on_char ';' |> List.filter is_parse_rule
;;

(* |> List.map (fun x ->
    match (String.split_on_char ':' x) with
    | [lhs_string; rhs_string] -> 
      let lhs = NonTerminal (String.trim lhs_string) in
      let rhs = (String.split_on_char '|' rhs_string)
      |> List.map (fun (prod) -> 
        String.split_on_char ' ' prod |> List.map (fun s -> NonTerminal s)
        ) in
        {lhs ; rhs}
    | _ -> failwith "Invalid Rule Format"
    ) *)

let extract_grammar_from_string (content : string) : grammar =
  content |> filter_content |> convert_to_rules
;;

(* List.iter print_string ;
  [] *)

let extract_grammar (file : string) : grammar =
  read_file file |> remove_comments |> extract_grammar_from_string
;;
