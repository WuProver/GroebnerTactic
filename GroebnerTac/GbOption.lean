import Lean

open Lean

inductive GroebnerTacticBackend
  | sage_api : GroebnerTacticBackend
  | sage_local : GroebnerTacticBackend
  | sympy : GroebnerTacticBackend
deriving Hashable, Repr, Inhabited

def GroebnerTacticBackend.ofDataValue? : DataValue → Option GroebnerTacticBackend
  | .ofNat 0 => some .sage_local
  | .ofNat 1 => some .sage_api
  | .ofNat 2 => some .sympy
  | _           => panic! "`0`, `1`, or `2` should be passed"

def GroebnerTacticBackend.toDataValue : GroebnerTacticBackend → DataValue
  | .sage_local => .ofNat 0
  | .sage_api => .ofNat 1
  | .sympy => .ofNat 2

instance : KVMap.Value GroebnerTacticBackend where
  toDataValue := GroebnerTacticBackend.toDataValue
  ofDataValue? := GroebnerTacticBackend.ofDataValue?

register_option gb_tactic.backend : GroebnerTacticBackend := {
  defValue := .sympy
  descr := "backend used on `gb_tactic`, `0` for Sage API, `1` for Sage, and `2` for sympy"
}
