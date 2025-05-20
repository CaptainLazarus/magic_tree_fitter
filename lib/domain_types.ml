type symbol = Terminal of string | NonTerminal of string
type production = symbol list
type rule = { lhs : symbol; rhs : production }
type grammar = rule list
