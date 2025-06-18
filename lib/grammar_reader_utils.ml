open Domain_types

let dump_single x =
  print_string ("\n" ^ fst x);
  print_string " -> ";
  print_endline (String.concat " " (snd x))
;;

let rec dump (s : (string * string list) list) =
  match s with
  | [] -> ()
  | x :: xs ->
    dump_single x;
    dump xs
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

let dump_queue (q : (string * string list) Queue.t) =
  Printf.printf "Queue state:\n";
  Queue.iter (fun (lhs, rhs) -> Printf.printf "%s -> %s\n" lhs (String.concat " " rhs)) q;
  Printf.printf "------\n%!"
;;

let string_of_symbol = function
  | Terminal s -> "\"" ^ s ^ "\""
  | NonTerminal s -> s
  | Epsilon -> "ε"
  | EOF -> "$"
;;

let string_of_production = function
  | [] -> "ε"
  | symbols -> String.concat " " (List.map string_of_symbol symbols)
;;

let dump_rules (rules : (symbol * symbol list) list) =
  print_endline "\nRules : ---------------\n";
  List.iter
    (fun (lhs, rhs) ->
       let lhs_str = string_of_symbol lhs in
       let rhs_str = string_of_production rhs in
       Printf.printf "%s → %s\n" lhs_str rhs_str)
    rules;
  rules
;;

let dump_grammar (grammar : grammar) : grammar =
  print_endline "\nGrammar : ===============\n";
  List.iter
    (fun { lhs; rhs } ->
       let lhs_str = string_of_symbol lhs in
       let rhs_str = string_of_production rhs in
       Printf.printf "%s → %s\n" lhs_str rhs_str)
    grammar;
  grammar
;;
