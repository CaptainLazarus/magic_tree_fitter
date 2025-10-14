open Gss
open Glr_utils
open Stack_ops
open Dump
open Domain_types

let initialise_stacks_helper c g =
  let forward_anchor_nodes, backward_anchor_nodes =
    get_anchor_nodes c.parse_tables c.anchor_symbol
  in
  let forward_stacks =
    List.map
      (initialise_stack
         Forward
         (* HACK : Asssumes non empty list initally. Might be a problem. Check *)
         (List.hd g.forward_tokens))
      forward_anchor_nodes
  in
  let backward_stacks =
    List.map
      (initialise_stack
         Backward
         (* HACK : Asssumes non empty list initally. Might be a problem. Check *)
         (List.hd g.reverse_tokens))
      backward_anchor_nodes
  in
  { stacks = forward_stacks @ backward_stacks
  ; forward_tokens = List.tl g.forward_tokens
  ; reverse_tokens = List.tl g.reverse_tokens
  }
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
  (* if g.forward_tokens = [] || g.reverse_tokens = [] *)
  (* then *)
  (* dump_token_list g.forward_tokens; *)
  (* dump_token_list g.reverse_tokens; *)
  (*   true *)
  (* else *)
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

let rec construct_ast (n : int) =
  (* 1. Run actions on stacks *)
  (* 2. Update next token *)
  (* 3. If blocked, return. If not, goto 1 *)
  Graph.(
    ask
    >>= fun (c : glr_config) ->
    get
    >>= fun (g : graph) ->
    if n > 1000
    then return g
    else (
      (* Consume token -> Update top nodes with actions -> filter top nodes with empty action lists *)
      dump_stacks g;
      let updated_stacks =
        List.map
          (fun s ->
             let s', _ = Stack.(run_stack (consume_token c) s) in
             s')
          g.stacks
        (* FIX : I need to advance the token here. Updating here makes no sense *)
        (* |> List.map (update_stack_next_token g) *)
        |> List.map (update_stack_with_actions c)
        |> List.filter (fun s -> not (NodeMap.is_empty s.top))
      in
      (*
         So...couple of things here.
    1. If there's a blocked reduction, then don't advance the token ?
    2. If no shifts occured, then all blocked (using the new definition of reduce -> recursive reduce till something else). In which case, no point of advancement.
    3. If a single shift occurs, dump the other stacks ? Depends. If they're blocked, then advance only that stack. advance global token otherwise. That reduce func needs to be checked.
    3a. Flip side is globally advacne for atleast one shift, since blocked reductions don't advacne anyway.
    
    All of this is really stupid. either the stack consumed the input, which is the default assumption, or it has a blocked reduction. There's literally no in-between. So just check for a blocked reduction. What am I missing.
      *)
      let g' =
        { stacks = updated_stacks
        ; forward_tokens =
            (if g.forward_tokens = [] then [] else List.tl g.forward_tokens)
        ; reverse_tokens =
            (if g.reverse_tokens = [] then [] else List.tl g.reverse_tokens)
        }
      in
      (* dump_token_list g.reverse_tokens; *)
      (* dump_token_list g.forward_tokens; *)
      put g'
      >>= fun _ ->
      if all_blocked g'
      then
        (* dump_stacks g'; *)
        return g'
      else construct_ast (n + 1)))
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
