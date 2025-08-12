open Domain_types

type node_id = int
type node_state = int

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

type gss_node =
  { id : node_id
  ; state : node_state
  ; edges : (token_info * node_state) list
  ; parents : NodeIdSet.t
    (*node_id*)
    (* ; children : int list *)
    (* Basically `List.map (fun (sym, s) -> s) edges` since edges leading out lead to children *)
  ; next_actions : action list
  ; blocked_reductions : production_rule list
  }

module NodeSet = Set.Make (struct
    type t = gss_node

    let compare a b =
      let c = compare a.state b.state in
      if c = 0 then compare a.id b.id else c
    ;;
  end)

type stack =
  { root : gss_node
  ; top : NodeSet.t
  ; next_token : token_info
  ; direction : direction_t
  ; nodes : (int, gss_node) Hashtbl.t
  ; mutable next_id : int
  }

let create_node stack ~state ~parents ~edges ~next_actions ~blocked_reductions =
  let id = stack.next_id in
  stack.next_id <- id + 1;
  { id; state; parents; edges; next_actions; blocked_reductions }
;;

type graph =
  { stacks : stack list
  ; parse_tables : (int * symbol, action list) Hashtbl.t list
  ; anchor_symbol : token_info
  ; token_list : token_info list
  ; forward_tokens : token_info list
  ; reverse_tokens : token_info list
  }

(* Interesting thing here. Graph is an entity, graph node is one too. There's either one above a graph, maybe something like a mega-graph something but need better terrminology. It's there because the graphs are actually disconnected and you need an entity to link them.*)
(* Think puddle of slime as an electricity conduit. Everythings in a pool and that's why. think of that as the context. All the *)
(* Edit : Node -> Stack -> Graph *)
