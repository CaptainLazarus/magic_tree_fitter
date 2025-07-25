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

let symbol_compare a b =
  match a, b with
  | EOF, EOF -> 0
  | Epsilon, Epsilon -> 0
  | Terminal x, Terminal y -> String.compare x y
  | NonTerminal x, NonTerminal y -> String.compare x y
  | _ -> compare (symbol_order a) (symbol_order b)
;;

module SymbolOrd = struct
  type t = symbol

  let compare = symbol_compare
end

module SymbolSet = Set.Make (SymbolOrd)

type production = symbol list

let rec production_order a b =
  match a, b with
  | x :: xs, y :: ys ->
    let k = symbol_compare x y in
    if k = 0 then production_order xs ys else k
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
;;

type production_rule =
  { lhs : symbol
  ; rhs : production
  }

let production_rule_order a b =
  let k = symbol_compare a.lhs b.lhs in
  if k = 0 then production_order a.rhs b.rhs else k
;;

type grammar = production_rule list

type action =
  | Shift of int
  | Reduce of production_rule
  | Accept
  | Goto of int

type lr1_item = production_rule * int * symbol

let lr1_item_order (p1, i1, s1) (p2, i2, s2) =
  let k = production_rule_order p1 p2 in
  if k <> 0
  then k
  else (
    let k1 = compare i1 i2 in
    if k1 <> 0 then k1 else symbol_compare s1 s2)
;;

module LR1ItemOrd = struct
  type t = lr1_item

  let compare = lr1_item_order
end

module LR1ItemSet = Set.Make (LR1ItemOrd)

module ItemSetOrd = struct
  type t = LR1ItemSet.t

  let compare = LR1ItemSet.compare
end

module LR1ItemSetSet = Set.Make (ItemSetOrd)

type token_info =
  { token : symbol
  ; lexeme : string
  }
