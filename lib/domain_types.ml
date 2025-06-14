type symbol =
  | Terminal of string
  | NonTerminal of string
  | Epsilon

type production = symbol list

type production_rule =
  { lhs : symbol
  ; rhs : production
  }

type grammar = production_rule list
