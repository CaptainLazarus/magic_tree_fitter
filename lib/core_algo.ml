(* open Yojson.Basic *)
open Domain_types
open Grammar_reader
open Yojson.Basic.Util
open Dump
open Glr_algo_data_structures

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

let add_to_gss _ = ()
let add_to_sppf _ = ()

let construct_ast
      (_gss : (gss_edge * gss_edge list) list)
      (sppf : sppf_node list)
      _parse_tables
      (token_info_list : token_info list)
      inital_token
  =
  ignore (dump_token_info inital_token);
  let split_at_anchor ~anchor lst =
    let rec loop before = function
      | [] -> List.rev before, []
      | x :: xs when x = anchor -> List.rev before, xs
      | x :: xs -> loop (x :: before) xs
    in
    loop [] lst
  in
  let before, after = split_at_anchor ~anchor:inital_token token_info_list in
  (* before = [1; 2], after = [4; 5] *)
  List.iter (fun x -> print_string (dump_token_info x)) before;
  print_string "\n=====================\n";
  List.iter (fun x -> print_string (dump_token_info x)) after;
  match token_info_list with
  | [] -> sppf
  (* | _ -> *)
  | _ -> failwith "[3XX] Intentional"
;;

let run_core_algo
      (forward_states : (int * int) list)
      (reverse_states : (int * int) list)
      (initial_token : token_info)
      (parse_tables : (int * symbol, action list) Hashtbl.t list)
      (token_info_list : token_info list)
  =
  let inital_sppf_node : sppf_node = { meta = initial_token; children = None } in
  let (root_edge : gss_edge) =
    { meta = initial_token; forward = forward_states; backward = reverse_states }
  in
  construct_ast
    [ root_edge, [] ]
    [ inital_sppf_node ]
    parse_tables
    token_info_list
    initial_token
;;

(* file -> JSON -> get X -> run GLR from parse tables ->  *)
let get_ast parse_tables =
  let tokens = run_java_and_read_output () in
  let token_info_list : token_info list =
    List.map
      (fun (x : Yojson.Basic.t) ->
         { token = x |> member "token" |> to_string |> convert_to_symbol
         ; lexeme = x |> member "lexeme" |> to_string
         })
      tokens
  in
  let selected_token : token_info option = most_common_terminal token_info_list in
  match selected_token with
  | None -> failwith "\n[413] No terminal selected as anchor symbol\n"
  | Some t ->
    print_string ("\nSelected Terminal : " ^ dump_token_info t ^ "\n");
    let forward_states, reverse_states =
      initial_states_for_terminal parse_tables t.token
    in
    List.iter
      (fun (x, y) -> Printf.printf "\nForward States : %d %d\n" x y)
      forward_states;
    List.iter
      (fun (x, y) -> Printf.printf "\nBackward States : %d %d\n" x y)
      reverse_states;
    run_core_algo forward_states reverse_states t parse_tables token_info_list
;;
