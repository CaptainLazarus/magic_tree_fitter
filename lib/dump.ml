open Domain_types
open Gss

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

let dump_rule (rule : production_rule) =
  let lhs_str = string_of_symbol rule.lhs in
  let rhs_str = string_of_production rule.rhs in
  Printf.printf "%s → %s\n" lhs_str rhs_str
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
  flush stdout;
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

let collect_symbols (tbl : (int * symbol, action list) Hashtbl.t) : symbol list =
  Hashtbl.fold (fun (_, sym) _ acc -> SymbolSet.add sym acc) tbl SymbolSet.empty
  |> SymbolSet.elements
;;

module IntSet = Set.Make (Int)

let collect_states (tbl : (int * symbol, action list) Hashtbl.t) : int list =
  Hashtbl.fold (fun (state, _) _ acc -> IntSet.add state acc) tbl IntSet.empty
  |> IntSet.elements
;;

let string_of_action = function
  | Shift n -> "S" ^ string_of_int n
  | Reduce r ->
    Printf.sprintf "R(%s→%s)" (string_of_symbol r.lhs) (string_of_production r.rhs)
  | Accept -> "Acc"
  | Goto n -> "G" ^ string_of_int n
;;

let string_of_action_list acts =
  match acts with
  | [] -> ""
  | [ a ] -> string_of_action a
  | _ ->
    let inner = List.map string_of_action acts |> String.concat ", " in
    "[" ^ inner ^ "]"
;;

let dump_parse_table_to_file
      (tbl : (int * symbol, action list) Hashtbl.t)
      (filename : string)
  : unit
  =
  let oc = open_out filename in
  let symbols = collect_symbols tbl in
  let states = collect_states tbl in
  let col_width = 20 in
  let pad s = Printf.sprintf "%-*s" col_width s in
  let fprintf = Printf.fprintf in
  fprintf oc "%s" (pad "State");
  List.iter (fun sym -> fprintf oc "%s" (pad (string_of_symbol sym))) symbols;
  fprintf oc "\n";
  List.iter
    (fun state ->
       fprintf oc "%s" (pad (string_of_int state));
       List.iter
         (fun sym ->
            let entry =
              match Hashtbl.find_opt tbl (state, sym) with
              | Some actions -> string_of_action_list actions
              | None -> ""
            in
            fprintf oc "%s" (pad entry))
         symbols;
       fprintf oc "\n")
    states;
  close_out oc;
  print_endline "Dump complete"
;;

let dump_token_info { token; lexeme } =
  Printf.sprintf "{ token = %s; lexeme = \"%s\" }" (string_of_symbol token) lexeme
;;

let dump_token_list xs =
  List.iter
    (fun x ->
       Printf.printf "{ token = %s; lexeme = \"%s\" }" (string_of_symbol x.token) x.lexeme)
    xs
;;

let dump_edgeset edges =
  let edge_strings =
    EdgeSet.elements edges
    |> List.map (fun (symbol, target_state) ->
      let (NodeState state_val) = target_state in
      Printf.sprintf "%s -> %d" (string_of_symbol symbol) state_val)
  in
  Printf.sprintf "[%s]" (String.concat "; " edge_strings)
;;

let dump_edgeset_verbose edges =
  Printf.printf "EdgeSet (%d edges):\n" (EdgeSet.cardinal edges);
  EdgeSet.iter
    (fun (symbol, target_state) ->
       let (NodeState state_val) = target_state in
       Printf.printf "  %s -> state %d\n" (string_of_symbol symbol) state_val)
    edges;
  Printf.printf "\n%!"
;;

let dump_nodes stack =
  Printf.printf "\nAll nodes in stack (%d total):\n" (HashtblCustom.length stack.nodes);
  HashtblCustom.iter
    (fun node_id node ->
       let (NodeId id_val) = node_id in
       let (NodeId actual_id) = node.id in
       let (NodeState state_val) = node.state in
       Printf.printf "  Node[key=%d, id=%d, state=%d]\n" id_val actual_id state_val;
       Printf.printf "    edges: %s\n" (dump_edgeset node.edges);
       Printf.printf
         "    parents: {%s}\n"
         (String.concat
            ", "
            (List.map
               (fun parent_id ->
                  let (NodeId pid) = parent_id in
                  string_of_int pid)
               (NodeIdSet.elements node.parents)));
       Printf.printf
         "    next_actions: [%s]\n"
         (String.concat "; " (List.map string_of_action node.next_actions));
       Printf.printf
         "    blocked_reductions: [%s]\n"
         (String.concat
            "; "
            (List.map
               (fun r ->
                  Printf.sprintf
                    "%s→%s"
                    (string_of_symbol r.lhs)
                    (string_of_production r.rhs))
               node.blocked_reductions));
       Printf.printf "\n")
    stack.nodes;
  Printf.printf "------\n%!"
;;

let print_stack_top stack =
  Printf.printf "\nStack.top (%d nodes):\n" (NodeMap.cardinal stack.top);
  NodeMap.iter
    (fun _ node ->
       let (NodeId node_id) = node.id in
       let (NodeState node_state) = node.state in
       Printf.printf "  Node[id=%d, state=%d]\n" node_id node_state;
       Printf.printf
         "    edges: [%s]\n"
         (String.concat
            "; "
            (List.map
               (fun (symbol, target_state) ->
                  let (NodeState state_val) = target_state in
                  Printf.sprintf "%s -> %d" (string_of_symbol symbol) state_val)
               (EdgeSet.elements node.edges)));
       Printf.printf
         "    parents: {%s}\n"
         (String.concat
            ", "
            (List.map
               (fun parent_id ->
                  let (NodeId id_val) = parent_id in
                  string_of_int id_val)
               (NodeIdSet.elements node.parents)));
       Printf.printf
         "    next_actions: [%s]\n"
         (String.concat "; " (List.map string_of_action node.next_actions));
       Printf.printf
         "    blocked_reductions: [%s]\n"
         (String.concat
            "; "
            (List.map
               (fun r ->
                  Printf.sprintf
                    "%s→%s"
                    (string_of_symbol r.lhs)
                    (string_of_production r.rhs))
               node.blocked_reductions));
       Printf.printf "\n")
    stack.top;
  Printf.printf "------\n%!"
;;

(* ------------------------------------------------------------------ *)
(* pretty-print one gss_node                                          *)
(* ------------------------------------------------------------------ *)
let dump_gss_node (n : gss_node) : unit =
  let (NodeId id_val) = n.id in
  let (NodeState st_val) = n.state in
  Printf.printf "Node[id=%d, state=%d]\n" id_val st_val;
  (* edges *)
  let es =
    EdgeSet.fold
      (fun (sym, NodeState s) acc ->
         let sym_str =
           match sym with
           | Terminal t -> "\"" ^ t ^ "\""
           | NonTerminal nt -> nt
           | Epsilon -> "ε"
           | EOF -> "$"
         in
         Printf.sprintf "%s -> %d" sym_str s :: acc)
      n.edges
      []
    |> String.concat "; "
  in
  Printf.printf "  edges: [%s]\n" es;
  (* parents *)
  let ps =
    NodeIdSet.fold (fun (NodeId p) acc -> string_of_int p :: acc) n.parents []
    |> String.concat ", "
  in
  Printf.printf "  parents: {%s}\n" ps;
  (* next_actions *)
  let acts =
    List.map
      (function
        | Shift s -> Printf.sprintf "S%d" s
        | Reduce pr ->
          let lhs = string_of_symbol pr.lhs in
          let rhs = string_of_production pr.rhs in
          Printf.sprintf "R(%s→%s)" lhs rhs
        | Accept -> "Acc"
        | Goto s -> Printf.sprintf "G%d" s)
      n.next_actions
    |> String.concat "; "
  in
  Printf.printf "  next_actions: [%s]\n" acts;
  (* blocked reductions *)
  let blocked =
    List.map
      (fun pr ->
         let lhs =
           match pr.lhs with
           | Terminal t -> t
           | NonTerminal nt -> nt
           | _ -> "?"
         in
         Printf.sprintf "%s→..." lhs)
      n.blocked_reductions
    |> String.concat "; "
  in
  Printf.printf "  blocked_reductions: [%s]\n" blocked;
  print_endline ""
;;

(* ------------------------------------------------------------------ *)
(* dump a single stack                                                *)
(* ------------------------------------------------------------------ *)
let dump_stack (s : stack) : unit =
  Printf.printf
    "=== STACK %s ===\n"
    (match s.direction with
     | Forward -> "Forward"
     | Backward -> "Backward");
  Printf.printf "curr_id = %d\n" s.curr_id;
  Printf.printf
    "next_token = %s\n"
    (match s.next_token.token with
     | Terminal t -> "\"" ^ t ^ "\""
     | NonTerminal nt -> nt
     | Epsilon -> "ε"
     | EOF -> "$");
  Printf.printf "root: ";
  dump_gss_node s.root;
  Printf.printf "TOP nodes (%d total):\n" (NodeMap.cardinal s.top);
  NodeMap.iter (fun _ node -> dump_gss_node node) s.top;
  Printf.printf "ALL nodes in hashtbl (%d total):\n" (HashtblCustom.length s.nodes);
  HashtblCustom.iter (fun _ node -> dump_gss_node node) s.nodes;
  print_endline "------"
;;

(* ------------------------------------------------------------------ *)
(* dump every stack in a graph                                        *)
(* ------------------------------------------------------------------ *)
let dump_stacks (g : graph) : unit =
  Printf.printf
    "\n\n ==========================Dumping Stacks============================\n";
  List.iter dump_stack g.stacks
;;

let dump_node_states = List.iter (fun x -> Printf.printf " %d " (unpack_state x))
let dump_path = List.iter (fun x -> Printf.printf " %d " (unpack_state x.state))

let dump_paths =
  List.iter (fun path ->
    Printf.printf "Path -> ";
    dump_path path;
    Printf.printf "\n")
;;
