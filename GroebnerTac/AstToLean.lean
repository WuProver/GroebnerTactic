import Lean
import Mathlib
import GroebnerTac.AST

open Lean Meta

partial def astToLean (ast : MathAST) : String :=
  match ast with
  -- nat
  | .nat n => toString n

  -- variable
  | .polyVar var => var

  -- constant
  | .polyConst value => astToLean value

  -- monomial
  | .polyMonomial var degree coeff =>
    let coeffStr := astToLean coeff
    match degree with
    | 0 => coeffStr
    | 1 =>
      if coeffStr == "1" then var
      else if coeffStr == "(-1)" then s!"-{var}"
      else s!"({coeffStr} * {var})"
    | _ =>
      if coeffStr == "1" then s!"({var} ^ {degree})"
      else if coeffStr == "(-1)" then s!"-({var} ^ {degree})"
      else s!"({coeffStr} * {var} ^ {degree})"

  -- add
  | .polyAdd left right => s!"({astToLean left} + {astToLean right})"

  -- mul
  | .polyMul left right => s!"({astToLean left} * {astToLean right})"

  -- sub
  | .polySub left right => s!"({astToLean left} - {astToLean right})"

  

  | _ => "sorry"
