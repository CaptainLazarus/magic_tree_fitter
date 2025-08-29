open Domain_types
open Grammar_reader
open Yojson.Basic.Util
open Gss_parser

(* open Dump *)
open Gss

let run_java_and_read_output () =
  let ic =
    Unix.open_process_in
      "java -cp \"./grammars:./grammars/antlr-4.13.1-complete.jar\" Main"
  in
  let rec read_all acc =
    try
      let line = input_line ic in
      let json = Yojson.Basic.from_string line in
      read_all (json :: acc)
    with
    | End_of_file -> List.rev acc
  in
  let output = read_all [] in
  close_in ic;
  (* print_string "\n\nStart\n\n"; *)
  output
;;

let dump_token_list (tokens : Yojson.Basic.t list) : Yojson.Basic.t list =
  tokens |> List.map Yojson.Basic.to_string |> String.concat "\n" |> print_string;
  tokens
;;

let token_info_of_json (x : Yojson.Basic.t) : token_info =
  let open Yojson.Basic.Util in
  { token = x |> member "token" |> to_string |> convert_to_symbol
  ; lexeme = x |> member "lexeme" |> to_string
  }
;;

let most_common_terminal (tokens : token_info list) : token_info option =
  let terminals =
    List.filter
      (fun { token; _ } ->
         match token with
         | Terminal _ -> true
         | _ -> false)
      tokens
  in
  let counts =
    List.fold_left
      (fun acc tok ->
         let count =
           match List.assoc_opt tok.token acc with
           | Some n -> n + 1
           | None -> 1
         in
         (tok.token, count) :: List.remove_assoc tok.token acc)
      []
      terminals
  in
  match counts with
  | [] -> None
  | _ ->
    let most_common_token =
      fst (List.hd (List.sort (fun (_, a) (_, b) -> compare b a) counts))
    in
    List.find_opt (fun t -> t.token = most_common_token) terminals
;;

(* Maunally verified that the lisp grammar forward states are working. Check backward ? And then assume this works. Will have to fix with automated tests *)
let initial_states_for_terminal
      (tables : (int * symbol, action list) Hashtbl.t list)
      (sym : symbol)
  : (int * int) list * (int * int) list
  =
  let extract_shift_states table =
    Hashtbl.fold
      (fun (state, symbol') actions acc ->
         match symbol', actions with
         | s, [ Shift x ] when s = sym -> (state, x) :: acc
         | _ -> acc)
      table
      []
  in
  match tables with
  | [ forward; reverse ] ->
    let ltr = extract_shift_states forward in
    let rtl = extract_shift_states reverse in
    ltr, rtl
  | _ -> failwith "Expected exactly two parse tables"
;;

let dump_parser_states xs ys =
  List.iter (fun (x, y) -> Printf.printf "\nForward States : %d %d\n" x y) xs;
  List.iter (fun (x, y) -> Printf.printf "\nBackward States : %d %d\n" x y) ys
;;

(* [x ; y ; A ; z] --> ([y ; x] , [z]) *)
let rec bisect_list selected_token token_list acc =
  match token_list with
  | [] -> acc, []
  | x :: xs when x = selected_token -> acc, xs
  | x :: xs -> bisect_list selected_token xs (x :: acc)
;;

(* Here we have a list of either empty or action nodes.
   If the list is empty, that means that edge is useless. Remove from stack ? *)
(* let next_actions = *)
(*   fun parse_table next_sym root_node -> find_next_actions root_node next_sym parse_table *)
(* ;; *)

let get_tokens =
  let tokens = run_java_and_read_output () in
  List.map
    (fun (x : Yojson.Basic.t) ->
       { token = x |> member "token" |> to_string |> convert_to_symbol
       ; lexeme = x |> member "lexeme" |> to_string
       })
    tokens
;;

let select_anchor token_info_list =
  let selected_token : token_info option = most_common_terminal token_info_list in
  match selected_token with
  | None -> failwith "[413] No token selected"
  | Some t -> t
;;

let get_anchor_nodes parse_tables anchor =
  let create_anchor_node_from_list l =
    List.map
      (fun (x, y) ->
         { id = 0
         ; state = x
         ; edges = [ anchor, y ]
         ; parents = NodeIdSet.empty
         ; next_actions = []
         ; blocked_reductions = []
         })
      l
  in
  let forward_states, reverse_states =
    initial_states_for_terminal parse_tables anchor.token
  in
  let forward_anchor_nodes : gss_node list =
    create_anchor_node_from_list forward_states
  in
  let backward_anchor_nodes : gss_node list =
    create_anchor_node_from_list reverse_states
  in
  forward_anchor_nodes, backward_anchor_nodes
;;

let initialise_stack direction next_token node =
  let s : stack =
    { root = node
    ; next_id = 1
    ; top = NodeSet.empty
    ; (* Edit : Fixed below*)
      (* Kinda wrong. *)
      (*We want to actually add the node.edge.y node here. children, basically *)
      next_token
    ; direction
    ; nodes = Hashtbl.create 100
    }
  in
  Hashtbl.add s.nodes 0 node;
  { s with
    top =
      NodeSet.of_seq
        (List.map
           (fun (_, y) ->
              let n =
                create_node
                  s
                  ~state:y
                  ~edges:[]
                  ~parents:(NodeIdSet.singleton node.id)
                  ~next_actions:[]
                  ~blocked_reductions:[]
              in
              Hashtbl.add s.nodes n.id n;
              n)
           node.edges
         |> List.to_seq)
  }
;;

let initialise_stacks (g : graph) =
  let forward_anchor_nodes, backward_anchor_nodes =
    get_anchor_nodes g.parse_tables g.anchor_symbol
  in
  let forward_stacks =
    List.map (initialise_stack Forward (List.nth g.forward_tokens 0)) forward_anchor_nodes
  in
  let backward_stacks =
    List.map
      (initialise_stack Backward (List.nth g.reverse_tokens 0))
      backward_anchor_nodes
  in
  { g with stacks = forward_stacks @ backward_stacks }
;;

(* file -> JSON -> get X -> run GLR from parse tables ->  *)
let get_ast parse_tables =
  let token_info_list = get_tokens in
  let selected_anchor = select_anchor token_info_list in
  let reverse_tokens, forward_tokens = bisect_list selected_anchor token_info_list [] in
  let g : graph =
    { stacks = []
    ; parse_tables
    ; anchor_symbol = selected_anchor
    ; token_list = token_info_list
    ; forward_tokens
    ; reverse_tokens
    }
    |> initialise_stacks
  in
  construct_ast g
;;
(* List.map construct_ast (forward_anchor_nodes @ backward_anchor_nodes) *)

(* Monad for non determinism -> phil wadler monads ->  *)
