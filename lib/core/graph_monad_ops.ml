open Gss
open Glr_utils
open Stack_ops

(* open Dump *)
open Domain_types

let initialise_stacks_helper c g =
  let forward_anchor_nodes, backward_anchor_nodes =
    get_anchor_nodes c.parse_tables c.anchor_symbol
  in
  let forward_stacks =
    List.map (initialise_stack Forward c.anchor_symbol) forward_anchor_nodes
  in
  let backward_stacks =
    List.map (initialise_stack Backward c.anchor_symbol) backward_anchor_nodes
  in
  { g with stacks = forward_stacks @ backward_stacks }
;;

let initialise_stacks =
  Graph.(
    ask
    >>= fun c ->
    get
    >>= fun g ->
    match g.stacks with
    | [] ->
      put (initialise_stacks_helper c g)
      >>= fun _ ->
      get
      >>= fun g' ->
      let updated_stacks =
        List.map (update_stack_with_actions c) g'.stacks
        |> List.filter (fun s -> not (NodeMap.is_empty s.top))
      in
      put { g' with stacks = updated_stacks } >>= fun _ -> ask
    | _ -> ask)
;;

let all_blocked (g : graph) =
  if g.forward_tokens = [] || g.reverse_tokens = []
  then true
  else
    List.for_all
      (fun stack ->
         NodeMap.for_all
           (fun _ node ->
              List.for_all
                (fun action ->
                   match action with
                   | Reduce pr -> List.mem pr node.blocked_reductions
                   | _ -> false) (* Shift/Goto/Accept mean we should continue *)
                node.next_actions)
           (* || node.next_actions = []) (* Empty actions also mean blocked *) *)
           (* This is commented out since the empty action lists get filtered out later.*)
           stack.top)
      g.stacks
;;

let rec construct_ast () =
  (* 1. Run actions on stacks *)
  (* 2. Update next token *)
  (* 3. If blocked, return. If not, goto 1 *)
  Graph.(
    ask
    >>= fun (c : glr_config) ->
    get
    >>= fun (g : graph) ->
    let updated_stacks =
      List.map
        (fun s ->
           let s', _ = Stack.(run_stack (apply_actions_to_stack c) s) in
           (* Printf.printf "After apply_actions_to_stack:\n"; *)
           (* dump_nodes s'; *)
           (* print_stack_top s'; *)
           s')
        g.stacks
      (* |> (fun sl -> *)
      (* if g.forward_tokens = [] || g.reverse_tokens = [] *)
      (* then sl *)
      (* else ( *)
      (*   let curr_forward_token = List.hd g.forward_tokens in *)
      (*   let curr_backward_token = List.hd g.reverse_tokens in *)
      (*   List.map *)
      (*     (fun s -> *)
      (*        { s with *)
      (*          next_token = *)
      (*            (if s.direction = Forward *)
      (*             then curr_forward_token *)
      (*             else curr_backward_token) *)
      (*        }) *)
      (*     sl)) *)
      |> List.map (update_stack_with_actions c)
      |> List.filter (fun s -> not (NodeMap.is_empty s.top))
    in
    let g' =
      { stacks = updated_stacks
      ; forward_tokens = List.tl g.forward_tokens
      ; reverse_tokens = List.tl g.reverse_tokens
      }
    in
    put g' >>= fun _ -> if all_blocked g' then return g' else construct_ast ())
;;

let ( >>+ ) xs f = List.concat_map f xs
let return_m x = [ x ]

let combine_stacks () =
  Graph.(
    ask
    >>= fun c ->
    get
    >>= fun g ->
    let forward_stacks, backward_stacks =
      List.partition (fun s -> s.direction = Forward) g.stacks
    in
    let x' =
      forward_stacks
      >>+ fun x ->
      backward_stacks
      >>+ fun y ->
      (* Have to individually check for each top_node *)
      let top_actions_forward =
        NodeMap.fold (fun _ top_node acc -> top_node.next_actions :: acc) x.top []
      in
      let top_actions_backward =
        NodeMap.fold (fun _ top_node acc -> top_node.next_actions :: acc) y.top []
      in
      let has_common_element =
        List.exists
          (fun action -> List.mem action top_actions_backward)
          top_actions_forward
      in
      if has_common_element then return_m [ x, y ] else return_m []
    in
    return g)
;;
