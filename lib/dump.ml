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

let dump_symbol x = string_of_symbol x |> print_string

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

let dump_symbol_set (s : SymbolSet.t) : unit =
  let elems = SymbolSet.elements s in
  let strs = List.map string_of_symbol elems in
  let out = String.concat "; " strs in
  print_endline ("{ " ^ out ^ " }")
;;

let dump_lr1_item ((p, j, a) : lr1_item) : unit =
  let lhs_str = string_of_symbol p.lhs in
  let rhs_symbols =
    List.mapi
      (fun idx sym ->
         if idx = j then "• " ^ string_of_symbol sym else string_of_symbol sym)
      p.rhs
  in
  let rhs_str =
    if j >= List.length p.rhs
    then String.concat " " (rhs_symbols @ [ "•" ])
    else String.concat " " rhs_symbols
  in
  Printf.printf "%s → %s , %s\n" lhs_str rhs_str (string_of_symbol a)
;;

let dump_lr1_set (s : LR1ItemSet.t) : unit =
  print_endline "\nLR(1) Item Set: ---------\n";
  LR1ItemSet.iter dump_lr1_item s
;;

let dump_const_states (states : LR1ItemSetSet.t) : unit =
  print_endline "\nCanonical Collection of LR(1) Item Sets:\n";
  let idx = ref 0 in
  LR1ItemSetSet.iter
    (fun state ->
       Printf.printf "State %d:\n" !idx;
       dump_lr1_set state;
       incr idx;
       print_endline "")
    states
;;
