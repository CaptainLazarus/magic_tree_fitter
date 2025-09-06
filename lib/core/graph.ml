open Gss

type 'a graph_state = glr_config -> graph -> 'a * graph

let return x = fun _config state -> x, state

let ( >>= ) m f =
  fun config state ->
  let a, state' = m config state in
  let m' = f a in
  m' config state'
;;

let ask = fun config state -> config, state
let get = fun _config state -> state, state
let put new_state = fun _config _state -> (), new_state
let run_glr m config initial_state = m config initial_state
