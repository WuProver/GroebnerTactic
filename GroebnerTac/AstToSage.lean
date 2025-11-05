import Lean
import Mathlib
import GroebnerTac.AST

open Lean Meta

partial def astToSage (ast : MathAST) : String :=
  match ast with
  -- variable
  | .polyVar var => var

  -- constant
  | .polyConst value => astToSage value

  -- monomial
  | .polyMonomial var degree coeff =>
    let coeffStr := astToSage coeff
    match degree with
    | 0 => coeffStr
    | 1 =>
      if coeffStr == "1" then var
      else if coeffStr == "-1" then s!"-{var}"
      else s!"{coeffStr}*{var}"
    | _ =>
      if coeffStr == "1" then s!"{var}^{degree}"
      else if coeffStr == "-1" then s!"-{var}^{degree}"
      else s!"{coeffStr}*{var}^{degree}"

  -- add
  | .polyAdd left right =>
    s!"({astToSage left} + {astToSage right})"

  -- mul
  | .polyMul left right =>
    s!"({astToSage left} * {astToSage right})"

  -- sub
  | .polySub left right =>
    s!"({astToSage left} - {astToSage right})"

  -- nat
  | .nat n => s!"{n}"

  -- otherwise
  | _ => "unknown_ast"


