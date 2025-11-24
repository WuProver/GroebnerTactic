
import Mathlib
import Qq
import Lean

open Qq

open Lean Elab Tactic Meta Term
open Meta Ring Qq PrettyPrinter

/-!
In this file we show some examples of using the GroebnerTac library.

-/

section
open MvPolynomial

set_option linter.style.missingEnd false
set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)


def my_set : Set  (MvPolynomial (Fin 2) ℚ):= {X 0 ^ 2 + X 1, 3*X 1}

def parsePoly (e : Expr) : Lean.MetaM String := do
  let e ← checkTypeQ e q(MvPolynomial (Fin 2) ℚ)
  match e with
  | none => pure s!"unknown"
  | some expr =>
    match expr with
    | ~q($a + $b) =>
      let a  ← parsePoly a
      let b  ← parsePoly b
      pure s!"({a} + {b})"

    | ~q($a * $b) =>
      let left ← parsePoly a
      let right ← parsePoly b
      pure s!"({left} * {right})"

    | ~q($a ^ ($n : ℕ)) =>
      let baseStr ← parsePoly a
      let n ← try
        let .isNat _ n _ ← NormNum.derive (α := q(ℕ)) n | failure
        pure n.natLit!
      catch _ =>
        pure n.natLit!
      -- dbg_trace "FOUND POW: {baseStr}^{n}"
      pure s!"{baseStr}^{n}"
      -- dbg_trace "FOUND POW: {baseStr}^{n}"
    | ~q(MvPolynomial.X $idx) =>
      match idx with
      -- | ~q(@OfNat.ofNat _ _ $n) => pure s!"X_{n}"
      -- | ~q(@OfNat.ofNat _ _ $n) => dbg_trace "FOUND VAR INDEX {n}"; pure s!"X_{n}"
      -- | _ => pure s!"X_{idx}"
      | ~q(@OfNat.ofNat _ _ $var) =>
        match var with
        | .app (.app (.app (.const `Fin.instOfNat _) _) _) n => pure s!"X_{n}"
        | _ => pure s!"X_{idx}"
    | ~q(@OfNat.ofNat _ _ $n) =>
      pure s!"{n}"
    | ~q(@Zero.toOfNat0 _ $z) =>
      -- logInfo m!"[DEBUG] Found zero constant{z}"
      -- dbg_trace s!"[DEBUG] Found zero constant {z}"
      pure "0"
    | _ =>
      pure s!"{e}"


def parseVars (e : Q(Set (MvPolynomial (Fin 2) ℚ))) : Lean.MetaM (List String) := do
  -- let e ← checkTypeQ e q(Set (MvPolynomial $σ $R))
  match e with
  -- | none => pure []
  -- | some expr =>
  --   match expr with
  | ~q(Insert.insert (γ:=Set _) $a $b) =>
    let VarA ← parsePoly a
    let VarB ← parseVars b
    -- logInfo m!"[DEBUG] View A: {a}"
    -- logInfo m!"[DEBUG] View B: {b}"
    logInfo m!"[DEBUG] VarA: {VarA}"
    logInfo m!"[DEBUG] VarB: {VarB}"
    -- dbg_trace s!"View A: {a}"
    -- dbg_trace s!"View B: {b}"
    pure (VarA :: VarB)
  | ~q((∅: Set (MvPolynomial _ _))) => pure []
  | ~q(Set.singleton $v) =>
    let vStr ← parsePoly v
    -- logInfo m!"[DEBUG] Singleton var: {vStr}"
    pure [vStr]
  | ~q(singleton $v) =>
    let vStr ← parsePoly v
    -- logInfo m!"[DEBUG] Single var: {vStr}"
    pure [vStr]
  | _ => unreachable!

      -- let parsedPoly ← parsePoly poly
      -- let varsList ← parseVars vars
      -- let parsedR ← parsePoly r


