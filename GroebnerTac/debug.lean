import MonomialOrderedPolynomial
import Groebner.Groebner
import Groebner.ToMathlib.List

import GroebnerTac.Tactic

/-
In this file we show some templates of using those problem.
-/

section
open MvPolynomial MonomialOrder

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in


open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]

example :
  lex.IsGroebnerBasis
  ({X 0 - 1, X 1^2} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0^2 + X 1^2 - 1, X 0 - 1} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  gb_solve


example : lex.IsGroebnerBasis ({X 0, X 1} :
 Set (MvPolynomial (Fin 3) ℚ)) (Ideal.span {X 0, X 0 + X 1}) := by
  add_gb_hyp h ({X 0, X 0 + X 1} : Set (MvPolynomial (Fin 3) ℚ))
  sorry
--   sorry
  -- simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, C_1, Fin.isValue, pow_one, one_mul,
  --   zero_add] at h
  -- exact h

example :
  lex.IsGroebnerBasis
  ({X 0 + X 1, X 1 ^ 2 + 1} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0 + X 1, X 0 * X 1 - 1} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  add_gb_hyp h ({X 0 + X 1, X 0 * X 1 - 1} : Set (MvPolynomial (Fin 2) ℚ))
  simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, C_1, Fin.isValue, pow_one, one_mul,
    zero_add] at h
  exact h
