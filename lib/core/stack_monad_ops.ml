open Gss
open Glr_utils

(* Assumptions -> Top nodes need to have actions that need to be resolved ?*)
(* How do you find nodes to merge ? -> If same state in top, then merge, since it implies literally added right now.*)
(*Remove old one*)
let apply_shift (top_node : gss_node) (x : node_state) =
  Stack.(
    get
    >>= fun s ->
    let existing_node_opt = find_opt (fun n -> n.state = x) s.top in
    let new_node =
      match existing_node_opt with
      | None ->
        let node, _ =
          create_and_add_node
            s
            ~state:x
            ~parents:(NodeIdSet.singleton top_node.id)
            ~edges:[]
            ~next_actions:[]
            ~blocked_reductions:[]
        in
        node
      | Some existing_node ->
        let node =
          { existing_node with parents = NodeIdSet.add top_node.id existing_node.parents }
        in
        Hashtbl.replace s.nodes node.id node;
        node
    in
    return { s with top = NodeSet.add new_node s.top })
;;
