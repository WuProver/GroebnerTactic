import Mathlib

import Mathlib.Tactic
import Lean

import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
import Lean.Meta.Tactic.TryThis

open Lean Elab Tactic Meta Term
open Meta Ring Qq PrettyPrinter
open MvPolynomial MonomialOrder

namespace Poly
open Lean

syntax (name := GBSolve) "inequal" : tactic
@[tactic GBSolve]
def inEquality : Tactic := fun stx => do
  evalTactic (← `(tactic|
    focus
      try simp [*]
      try norm_num
      first | done | ring | linarith
  ))
