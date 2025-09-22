open Domain_types
open Grammar_reader
open Yojson.Basic.Util
open Graph
open Graph_monad_ops

(* (\* open Dump *\) *)
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
  output
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

(* [x ; y ; A ; z] --> ([y ; x] , [z]) *)
let rec bisect_list selected_token token_list acc =
  match token_list with
  | [] -> acc, []
  | x :: xs when x = selected_token -> acc, xs
  | x :: xs -> bisect_list selected_token xs (x :: acc)
;;

(* (\* Here we have a list of either empty or action nodes. *)
(*    If the list is empty, that means that edge is useless. Remove from stack ? *\) *)
(* (\* let next_actions = *\) *)
(* (\*   fun parse_table next_sym root_node -> find_next_actions root_node next_sym parse_table *\) *)
(* (\* ;; *\) *)

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

(* file -> JSON -> get X -> run GLR from parse tables ->  *)
let setup_glr parse_tables =
  let token_info_list = get_tokens in
  let selected_anchor = select_anchor token_info_list in
  let reverse_tokens, forward_tokens = bisect_list selected_anchor token_info_list [] in
  let config =
    { parse_tables; anchor_symbol = selected_anchor; token_list = token_info_list }
  in
  let g : graph = { stacks = []; forward_tokens; reverse_tokens } in
  config, g
;;

let get_ast parse_tables =
  let config, initial_graph = setup_glr parse_tables in
  (* Run the monadic computation with the setup *)
  run_glr initialise_stacks config initial_graph
  |> fun (c, g) -> run_glr construct_ast () c g
;;
