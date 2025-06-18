open Domain_types
open Symbol_table
open Grammar_reader_utils

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

let expand_production (production_rules : (string * string list) list) =
  let rec expand_rhs_helper lhs rhs acc =
    match rhs with
    | [] -> acc
    | x :: xs (* x = Aa *) ->
      expand_rhs_helper
        lhs
        xs
        ((lhs, String.split_on_char ' ' x |> List.map String.trim) :: acc)
  in
  let expand_rhs (production_rule : string * string list) acc =
    match production_rule with
    | lhs, rhs (* rhs = [Aa ; Bb ; etc] *) -> expand_rhs_helper lhs rhs acc
  in
  let rec expand_production_helper (production_rules : (string * string list) list) acc =
    match production_rules with
    | [] -> List.rev acc
    | x :: xs -> expand_production_helper xs (expand_rhs x acc)
  in
  expand_production_helper production_rules []
;;

let convert_to_symbol (s : string) : symbol =
  if starts_with_single_quote_or_is_uppercase s
  then
    if starts_with_single_quote s
    then Terminal (String.sub s 1 (String.length s - 2))
    else Terminal s
  else if s = "epsilon"
  then Epsilon
  else if s = "EOF"
  then EOF
  else NonTerminal s
;;

let convert_to_production (prod : string) : symbol list =
  String.split_on_char ' ' prod |> List.map (fun s -> convert_to_symbol s)
;;

let filter_content (content : string) : string list =
  content |> String.split_on_char ';' |> List.filter is_parse_rule
;;

let split_rules (parse_rules : string list) : (string * string) list =
  parse_rules
  |> List.map (fun x -> String.split_on_char ':' x)
  |> List.map (fun x -> List.nth x 0, List.nth x 1)
;;

let split_rhs (production_rules : (string * string) list) : (string * string list) list =
  production_rules
  |> List.map (fun x ->
    String.trim (fst x), String.split_on_char '|' (snd x) |> List.map String.trim)
;;

let convert_plus_to_star (q : (string * string list) Queue.t) (s : string) : string list =
  let base = String.sub s 0 (String.length s - 1) in
  let base_star = base ^ "*" in
  if not (has_seen base_star)
  then (
    mark_seen base_star;
    let new_rule_1 = base_star, [ base; base_star ] in
    let new_rule_2 = base_star, [ "epsilon" ] in
    Queue.add new_rule_1 q;
    Queue.add new_rule_2 q)
  else ();
  [ base; base ^ "*" ]
;;

let desugar_rhs (q : (string * string list) Queue.t) (rhs : string list) : symbol list =
  let rec desugar_rhs_helper
            (q : (string * string list) Queue.t)
            (rhs : string list)
            (acc : string list)
    : string list
    =
    match rhs with
    | [] -> List.rev acc
    | x :: xs ->
      let expanded = if ends_with_plus x then convert_plus_to_star q x else [ x ] in
      desugar_rhs_helper q xs (List.rev_append expanded acc)
  in
  desugar_rhs_helper q rhs [] |> List.map convert_to_symbol
;;

let rec process_queue
          (q : (string * string list) Queue.t)
          (acc : (symbol * symbol list) list)
  =
  (* dump_queue q; *)
  if Queue.is_empty q
  then List.rev acc
  else (
    let lhs, rhs = Queue.take q in
    let prod = convert_to_symbol lhs, desugar_rhs q rhs in
    process_queue q (prod :: acc))
;;

let desugar_production_strings (production_tuples : (string * string list) list)
  : (symbol * symbol list) list
  =
  let q = Queue.create () in
  Queue.add_seq q (List.to_seq production_tuples);
  process_queue q []
;;

let convert_to_grammar (xs : (symbol * symbol list) list) : grammar =
  xs |> List.map (fun (lhs, rhs) -> { lhs; rhs })
;;

(* Currentyl reading as a string -> list. Should go from string -> graph. Is muchh safer and easier*)

let extract_grammar_from_string (content : string) =
  content
  |> filter_content
  |> split_rules
  |> split_rhs
  |> expand_production
  |> fun x ->
  (* dump x ;*)
  desugar_production_strings x |> convert_to_grammar
;;

let extract_grammar (file : string) =
  read_file file |> remove_comments |> extract_grammar_from_string
;;
