import Lean
import Mathlib

open Lean Meta

inductive MathAST where
  | nat (n : Nat)
  | int (n : Int)
  | string (s : String)

  | hypothesis (proposition : MathAST)

  | var (name : String) (type : String)
  | bool (b : Bool)

  | polyVar (var : String)
  | polyConst (value : MathAST)
  | polyMonomial (var : String) (degree : Nat) (coeff : MathAST)
  | polyAdd (left : MathAST) (right : MathAST)
  | polyMul (left : MathAST) (right : MathAST)
  | polySub (left : MathAST) (right : MathAST)

  -- Comparison and logic
  | eq (lhs rhs : MathAST)
  | lt (lhs rhs : MathAST)
  | le (lhs rhs : MathAST)
  | gt (lhs rhs : MathAST)
  | ge (lhs rhs : MathAST)
  | and (args : List MathAST)
  | or (args : List MathAST)
  | not (arg : MathAST)

  -- calculations
  | add (args : List MathAST)
  | sub (lhs rhs : MathAST)
  | mul (args : List MathAST)
  | div (lhs rhs : MathAST)
  | pow (base exponent : MathAST)
  | neg (arg : MathAST)

  -- Functions
  | func (name : String) (args : List MathAST)
  | apply (func : MathAST) (args : List MathAST)

  -- Quantifiers
  | exists (vars : List (String × MathAST)) (body : MathAST)
  | lambda (var : String) (varType : MathAST) (body : MathAST)


  | list (elems : List MathAST)

  deriving Repr, BEq, Inhabited
