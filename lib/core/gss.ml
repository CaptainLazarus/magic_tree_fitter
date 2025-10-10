open Domain_types

type node_state = NodeState of int
type node_id = NodeId of int

let unpack_state (NodeState x) = x
let unpack_id (NodeId x) = x
let increment_node_id (NodeId x) = NodeId (x + 1)

type direction_t =
  | Forward
  | Backward

module NodeIdSet = Set.Make (struct
    type t = node_id

    let compare = compare
  end)

module NodeStateSet = Set.Make (struct
    type t = node_state

    let compare = compare
  end)

let node_state_compare (NodeState i1) (NodeState i2) = Int.compare i1 i2

module EdgeSet = Set.Make (struct
    type t = symbol * node_state

    let compare (t1, s1) (t2, s2) =
      let c = symbol_compare t1 t2 in
      if c = 0 then node_state_compare s1 s2 else c
    ;;
  end)

type gss_node =
  { id : node_id
  ; state : node_state
  ; edges : EdgeSet.t
  ; parents : NodeIdSet.t
    (*node_id*)
    (* ; children : int list *)
    (* Basically `List.map (fun (sym, s) -> s) edges` since edges leading out lead to children *)
    (* Update : This is incorrect. The edge is holding node_state. Need to do a manual lookup for which children have that state. Since if same state, the nodes get merged, especially wit hthe same parents *)
  ; next_actions : action list
  ; blocked_reductions : production_rule list
  }

module NodeMap = Map.Make (struct
    type t = node_state

    let compare = node_state_compare
  end)

let node_id_compare_bool (NodeId id1) (NodeId id2) =
  if Int.compare id1 id2 = 0 then true else false
;;

module HashtblCustom = Hashtbl.Make (struct
    type t = node_id

    let equal = node_id_compare_bool
    let hash (NodeId i) = i
  end)

type stack =
  { root : gss_node
  ; top : gss_node NodeMap.t
  ; next_token : token_info
  ; direction : direction_t
  ; nodes : gss_node HashtblCustom.t
  ; curr_id : int
  }

let create_node
      (current_id : node_id)
      ~state
      ~parents
      ~edges
      ~next_actions
      ~blocked_reductions
  : gss_node * node_id
  =
  let (NodeId x) = current_id in
  let node =
    { id = current_id; state; parents; edges; next_actions; blocked_reductions }
  in
  node, NodeId (x + 1)
;;

let create_and_add_node s ~state ~parents ~edges ~next_actions ~blocked_reductions =
  let new_node, NodeId next_id =
    create_node
      (NodeId s.curr_id)
      ~state
      ~parents
      ~edges
      ~next_actions
      ~blocked_reductions
  in
  HashtblCustom.add s.nodes new_node.id new_node;
  new_node, NodeId next_id
;;

type glr_config =
  { parse_tables : (int * symbol, action list) Hashtbl.t list
  ; anchor_symbol : token_info
  ; token_list : token_info list
  }

type graph =
  { stacks : stack list
  ; forward_tokens : token_info list
  ; reverse_tokens : token_info list
  }

(* Interesting thing here. Graph is an entity, graph node is one too. There's either one above a graph, maybe something like a mega-graph something but need better terrminology. It's there because the graphs are actually disconnected and you need an entity to link them.*)
(* Think puddle of slime as an electricity conduit. Everythings in a pool and that's why. think of that as the context. All the *)
(* Edit : Node -> Stack -> Graph *)

(*
   f1 -> take the graph -> stacks + graph data
f2 -> stack -> top_nodes + stack_data
f3 -> nodes + actions -> R

Reader
*)
