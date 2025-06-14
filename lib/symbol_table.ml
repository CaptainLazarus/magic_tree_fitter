module StringSet = Set.Make (String)

let seen = ref StringSet.empty
let has_seen s = StringSet.mem s !seen
let mark_seen s = seen := StringSet.add s !seen
let reset () = seen := StringSet.empty
