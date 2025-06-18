type symbol =
  | Terminal of string
  | NonTerminal of string
  | Epsilon
  | EOF

let symbol_order = function
  | NonTerminal _ -> 3
  | Terminal _ -> 2
  | Epsilon -> 1
  | EOF -> 0
;;

module SymbolOrd = struct
  type t = symbol

  let compare a b = compare (symbol_order a) (symbol_order b)
end

module SymbolSet = Set.Make (SymbolOrd)

type production = symbol list

let rec production_order a b =
  match a, b with
  | x :: xs, y :: ys ->
    let k = compare (symbol_order x) (symbol_order y) in
    if k = 0 then production_order xs ys else k
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
;;

type production_rule =
  { lhs : symbol
  ; rhs : production
  }

type grammar = production_rule list

type action =
  | Shift of int
  | Reduce of int

type lr1_item = production_rule * int * symbol
