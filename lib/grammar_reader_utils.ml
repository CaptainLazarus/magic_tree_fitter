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

(*
   based on g4 file semantics. grammar, fragment and lexer lines are skipped. Only parser rules matter
*)
let is_parse_rule (s : string) : bool =
  let word = first_word s in
  match word with
  | "" | " " | "grammar" | "fragment" -> false
  | _ -> not (is_uppercase word)
;;

let ends_with_plus s = String.length s > 0 && String.get s (String.length s - 1) = '+'
