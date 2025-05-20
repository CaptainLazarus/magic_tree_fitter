let read_file path =
  let ic = open_in path in
  let len = in_channel_length ic in
  let content = really_input_string ic len in
  close_in ic;
  content

(* Also trims the final string. *)
let remove_comments (input : string) : string =
  let re_block = Str.regexp "/\\*\\(.\\|\n\\)*?\\*/" in
  let re_line = Str.regexp "//.*" in
  input
  |> Str.global_replace re_block ""
  |> Str.global_replace re_line ""
  |> String.trim
