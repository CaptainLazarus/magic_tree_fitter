open Domain_types

type direction_t =
  | Forward
  | Backward

type gss_node =
  { state : int
  ; edges : (token_info * int) list
  ; parents : int list
    (* ; children : int list *)
    (* Basically `List.map (fun (sym, s) -> s) edges` since edges leading out lead to children *)
  ; next_actions : action list
  }

type stack =
  { root : gss_node
  ; top : gss_node list
  ; next_token : token_info
  ; direction : direction_t
  }

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
