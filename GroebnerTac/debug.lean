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
