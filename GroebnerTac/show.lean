import Qq open Qq Lean

-- Construct an expression
def a : Expr := q([42 + 1])

-- Construct a typed expression
def b : Q(List Nat) := q([42 + 1])

#eval a
