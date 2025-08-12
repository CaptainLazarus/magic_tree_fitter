open Domain_types
open Grammar_reader
open Yojson.Basic.Util

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

(* let find_next_actions node sym parse_table = *)
(*   let find_next_actions_helper *)
(*         (state : int) *)
(*         (sym : symbol) *)
(*         (parse_table : (int * symbol, action list) Hashtbl.t) *)
(*     = *)
(*     match Hashtbl.find_opt parse_table (state, sym) with *)
(*     | None -> [] *)
(*     | Some s -> s *)
(*   in *)
(*   node.edges *)
(*   |> List.map (fun (x, y) -> find_next_actions_helper y sym parse_table, (x, y)) *)
(* ;; *)

let get_next_action_for_node (state : int) (sym : symbol) parse_table =
  match Hashtbl.find_opt parse_table (state, sym) with
  | None -> []
  | Some s -> s
;;

let get_next_actions_for_stack parse_table (s : stack) =
  NodeSet.fold
    (fun e acc ->
       let actions = get_next_action_for_node e.state s.next_token.token parse_table in
       (e, actions) :: acc)
    s.top
    []
;;

let get_forward_parse_table parse_tables = List.nth parse_tables 0
let get_backward_parse_table parse_tables = List.nth parse_tables 1

let find_opt predicate set =
  let filtered = NodeSet.filter predicate set in
  if NodeSet.is_empty filtered then None else Some (NodeSet.choose filtered)
;;

(* Assumptions -> Top nodes need to have actions that need to be resolved ?*)
(* How do you find nodes to merge ? -> If same state in top, then merge, since it implies literally added right now.*)
let apply_shift (s : stack) (top_node : gss_node) (x : node_state) =
  (* add a check here in s.top for same state nodes. if yes, merge. figure out how *)
  let new_node =
    (* Use Base package for this. has inbuilt funcs for it. *)
    match find_opt (fun n -> n.state = x) s.top with
    | Some existing_node ->
      { existing_node with parents = NodeIdSet.add top_node.id existing_node.parents }
    | None ->
      create_node
        s
        ~state:x
        ~parents:(NodeIdSet.singleton top_node.id)
        ~edges:[]
        ~next_actions:[]
        ~blocked_reductions:[]
  in
  Hashtbl.replace s.nodes new_node.id new_node;
  { s with top = NodeSet.add new_node s.top }
;;

let apply_goto (s : stack) (top_node : gss_node) (x : node_state) =
  (* add a check here in s.top for same state nodes. if yes, merge. figure out how *)
  let new_node =
    (* Use Base package for this. has inbuilt funcs for it. *)
    match find_opt (fun n -> n.state = x) s.top with
    | Some existing_node ->
      { existing_node with parents = NodeIdSet.add top_node.id existing_node.parents }
    | None ->
      create_node
        s
        ~state:x
        ~parents:(NodeIdSet.singleton top_node.id)
        ~edges:[]
        ~next_actions:[]
        ~blocked_reductions:[]
  in
  Hashtbl.replace s.nodes new_node.id new_node;
  { s with top = NodeSet.add new_node s.top }
;;

let find_matching_edge (parent : gss_node) (child : gss_node) (expected_sym : symbol) =
  List.find_opt
    (fun (edge_token, child_state) ->
       edge_token.token = expected_sym && child_state = child.state)
    parent.edges
;;

let collect_reduction_paths (s : stack) (top_node : gss_node) (pr : production_rule) =
  let rhs_symbols = List.rev pr.rhs in
  let rhs_length = List.length pr.rhs in
  let rec collect_paths
            (node : gss_node)
            (depth : int)
            (symbols : symbol list)
            (current_path : gss_node list)
    =
    match symbols with
    | [] -> [ List.rev current_path ]
    | expected_sym :: rest ->
      if depth <= 0
      then []
      else
        NodeIdSet.fold
          (fun parent_id acc ->
             let parent = Hashtbl.find s.nodes parent_id in
             match find_matching_edge parent node expected_sym with
             | Some _ ->
               let sub_paths =
                 collect_paths parent (depth - 1) rest (parent :: current_path)
               in
               sub_paths @ acc
             | None -> acc)
          node.parents
          []
  in
  collect_paths top_node rhs_length rhs_symbols [ top_node ]
;;

let can_reduce (s : stack) (top_node : gss_node) (pr : production_rule) =
  let rhs_symbols = List.rev pr.rhs in
  let rhs_length = List.length pr.rhs in
  let rec walk_back_all_symbols (node : gss_node) (depth : int) (symbols : symbol list) =
    match symbols with
    | [] -> true
    | expected_sym :: rest ->
      if depth <= 0
      then false
      else
        NodeIdSet.exists
          (fun x ->
             let parent = Hashtbl.find s.nodes x in
             let edge =
               List.find_opt
                 (fun (edge_token, child_state) ->
                    edge_token.token = expected_sym && child_state = node.state)
                 parent.edges
             in
             match edge with
             | None -> false
             | Some edge -> walk_back_all_symbols parent (depth - 1) rest)
          node.parents
  in
  walk_back_all_symbols top_node rhs_length rhs_symbols
;;

let apply_reduce (g : graph) (s : stack) (top_node : gss_node) (pr : production_rule) =
  let paths = collect_reduction_paths s top_node pr in
  List.fold_left
    (fun acc_stack path ->
       match path with
       | [] -> acc_stack (* shouldn't happen *)
       | path_start :: _ ->
         let parent_state = path_start.state in
         let parse_table =
           if s.direction = Forward
           then get_forward_parse_table g.parse_tables
           else get_backward_parse_table g.parse_tables
         in
         (match Hashtbl.find_opt parse_table (parent_state, pr.lhs) with
          | Some [ Goto target_state ] -> apply_goto acc_stack path_start target_state
          | _ -> acc_stack))
    s
    paths
;;

let apply_action (g : graph) (s : stack) (top_node : gss_node) (a : action) : stack =
  match a with
  | Shift x -> apply_shift s top_node x
  | Reduce pr -> apply_reduce g s top_node pr
  | Accept -> failwith "[2XX] Program finished ?"
  | Goto x -> apply_goto s top_node x
;;

let apply_actions (g : graph) (s : stack) (top_node : gss_node) (actions : action list) =
  List.fold_left (fun acc a -> apply_action g acc top_node a) s actions
;;

let apply_all_actions_to_stack
      (g : graph)
      (s : stack)
      (node_action_pairs : (gss_node * action list) list)
  =
  List.fold_left
    (fun acc_stack (node, actions) -> apply_actions g acc_stack node actions)
    s
    node_action_pairs
;;

let all_blocked (stacks : stack list) =
  List.for_all
    (fun stack ->
       NodeSet.for_all
         (fun node ->
            List.for_all
              (fun action ->
                 match action with
                 | Reduce pr -> List.mem pr node.blocked_reductions
                 | _ -> false) (* Shift/Goto/Accept mean we should continue *)
              node.next_actions
            || node.next_actions = []) (* Empty actions also mean blocked *)
         stack.top)
    stacks
;;

(* I have all the anchor nodes. Now, there's 2 things to do. One, for each anchor, apply the GSS. For now *)
(* I have all the anchor nodes. Now, there's 2 things to do. One, for each anchor, apply the GSS. For now *)
let construct_ast (g : graph) =
  let max_iter = 100 in
  let rec aux iter g =
    if iter >= max_iter
    then (
      Printf.printf "RECURSION LIMIT REACHED\n%!";
      failwith "construct_ast: too many iterations");
    Printf.printf "construct_ast: processing %d stacks\n%!" (List.length g.stacks);
    (* 1 -> Get the next actions per stack. *)
    let new_stacks, next_actions =
      List.map
        (fun s ->
           if s.direction = Forward
           then s, get_next_actions_for_stack (get_forward_parse_table g.parse_tables) s
           else s, get_next_actions_for_stack (get_backward_parse_table g.parse_tables) s)
        g.stacks
      |> List.filter (fun (_, node_action_pairs) ->
        List.exists (fun (_, actions) -> actions <> []) node_action_pairs)
      |> List.split
    in
    (* Debug: actions found *)
    Printf.printf
      "Total actions found: %d\n%!"
      (List.fold_left ( + ) 0 (List.map List.length next_actions));
    (* After getting next_actions, add this: *)
    Printf.printf "Actions: ";
    List.iteri
      (fun i node_action_pairs ->
         Printf.printf
           "S%d:[%s] "
           i
           (String.concat
              ","
              (List.map
                 (fun (_, acts) -> string_of_int (List.length acts))
                 node_action_pairs)))
      next_actions;
    Printf.printf "\n%!";
    (* 2 -> Update nodes with their next_actions *)
    let update_stack_with_actions stack node_action_pairs =
      let updated_nodes =
        List.map
          (fun (node, actions) -> { node with next_actions = actions })
          node_action_pairs
      in
      List.iter (fun node -> Hashtbl.replace stack.nodes node.id node) updated_nodes;
      let updated_top = NodeSet.of_list updated_nodes in
      { stack with top = updated_top }
    in
    let updated_stacks = List.map2 update_stack_with_actions new_stacks next_actions in
    let g1 = { g with stacks = updated_stacks } in
    (* 3 -> Apply actions *)
    let final_stacks =
      List.map2 (apply_all_actions_to_stack g1) updated_stacks next_actions
    in
    let g2 = { g1 with stacks = final_stacks } in
    (* Debug: stack info before blocked check *)
    Printf.printf "Checking if blocked... ";
    List.iteri
      (fun i stack -> Printf.printf "Stack%d:%d " i (NodeSet.cardinal stack.top))
      g2.stacks;
    Printf.printf "\n%!";
    Printf.printf "all_blocked check: %b\n%!" (all_blocked g2.stacks);
    (* Before the recursive call *)
    Printf.printf "Actions after apply: ";
    List.iteri
      (fun i stack ->
         let total_actions =
           NodeSet.fold (fun node acc -> acc + List.length node.next_actions) stack.top 0
         in
         Printf.printf "S%d:%d " i total_actions)
      g2.stacks;
    Printf.printf "\n%!";
    if all_blocked g2.stacks then g2 else aux (iter + 1) g2
  in
  aux 0 g
;;

(* I have to discard all the empty stacks now. Just filter ? *)

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
    ; (* Kinda wrong. *)
      (*We want to actually add the node.edge.y node here. children, basically *)
      (* Edit : Fixed *)
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
