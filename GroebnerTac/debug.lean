import Groebner.Basic
import Groebner.List

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

import GroebnerTac.Tactic

section
open MvPolynomial MonomialOrder

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in


open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]


example : 1 ∉ Ideal.span  ({X 0 + X 1, 1 - X 0*X 3} : Set <| MvPolynomial (Fin 4) ℚ) := by
   ideal_membership

-- example : 1 ∉ Ideal.span ({(1 - (X 3 * X 1)), X 0} : Set <| MvPolynomial (Fin 4) ℚ) := by
--    ideal_membership

example : (X 1 - C 2 : MvPolynomial (Fin 2) ℚ) = (X 1 - 2 : MvPolynomial (Fin 2) ℚ) := by
  exact rfl

example : lex.IsGroebnerBasis ({0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 1 * X 3 ^ 1 + C ↑(↑(-2) / ↑1)}
 : Set (MvPolynomial (Fin 4) ℚ)) (Ideal.span {0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 1 * X 3 ^ 1 + C ↑(↑(-2) / ↑1)}) := by
  simp only [_root_.ne_eq, _root_.one_ne_zero, _root_.not_false_eq_true, _root_.div_self, MvPolynomial.C_1, Fin.isValue, _root_.pow_one, _root_.one_mul,
    _root_.zero_add, _root_.div_one, MvPolynomial.C_neg, ← _root_.sub_eq_add_neg]


--   norm_num

--   conv =>
--     rw [← sub_eq_add_neg]
  basis

example : lex.IsGroebnerBasis ({X 0, X 1 * X 3 - C ↑(↑1 / ↑2)}
 : Set (MvPolynomial (Fin 4) ℚ)) (Ideal.span {X 0, X 1 * X 3 - C ↑(↑1 / ↑2)}) := by
  simp only [← sub_eq_add_neg]
  basis



-- example : 1 ∉ Ideal.span  ({X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ) := by
--   --  ideal_membership
--   have h_gb : letI basis := ( {X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ)
--     lex.IsGroebnerBasis basis (Ideal.span basis) := by
--       basis
--   have l_ideal : Ideal.span ({X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ) =
--   Ideal.span ( {X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ) := by
--     simp
--   have h_gb' : letI basis := ({X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ)
--     lex.IsGroebnerBasis basis (Ideal.span ({X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ):
--     ) := by
--     rw [l_ideal]
--     exact h_gb
--   have h_rm : lex.IsRemainder (1: MvPolynomial (Fin 4) ℚ)
--     {X 1*X 3 + 1, X 0 + X 1} (1) := by
--     remainder
--   by_contra h_mem
--   have eq : 1 = (0 : MvPolynomial (Fin 4) ℚ ):= by
--     exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h_gb' h_rm).mpr h_mem
--   have neq : 1 ≠ (0 : MvPolynomial (Fin 4) ℚ) := by
--     decide +kernel
--   contradiction
