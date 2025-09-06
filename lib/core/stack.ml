open Gss

type 'a stack_state = stack -> 'a * stack

let return x = fun s -> x, s
let get = fun s -> s, s
let put s = fun _ -> (), s

let ( >>= ) m f =
  fun s ->
  let a, s' = m s in
  (f a) s'
;;

let run_stack m s = m s

let next_id =
  get
  >>= fun (s : stack) ->
  put { s with curr_id = s.curr_id + 1 }
  >>= fun _ -> get >>= fun { curr_id; _ } -> return (curr_id + 1)
;;

(* let create_node stack ~state ~parents ~edges ~next_actions ~blocked_reductions = *)
(*   let id = stack.next_id in *)
(*   stack.next_id <- id + 1; *)
(*   { id; state; parents; edges; next_actions; blocked_reductions } *)
