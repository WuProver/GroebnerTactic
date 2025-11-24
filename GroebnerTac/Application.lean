import Mathlib

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


#check isRemainder_zero_iff_mem_ideal_of_isGroebner'
#check existsUnique_isRemainder_of_isGroebnerBasis

lemma aux {f g r : MvPolynomial σ k} {G : Set (MvPolynomial σ k)} (h : r ∈ Ideal.span G) : r + f * g ∈ Ideal.span (insert g G) := by
  have h₁ : f * g ∈ Ideal.span (insert g G) := by
    rw [Ideal.span_insert]
    refine Submodule.mem_sup_left (show f * g ∈ Ideal.span {g} from ?_)
    apply Ideal.mul_mem_left
    exact Ideal.mem_span_singleton_self g
  have h₂ : r ∈ Ideal.span (insert g G) := by
    rw [Ideal.span_insert]
    exact Submodule.mem_sup_right h
  exact (Submodule.add_mem_iff_right (Ideal.span (insert g G)) h₂).mpr h₁


/-这里有个问题 这两个中间的结论要做成什么样子 需要用户自己传什么东西吗-/
/-需要改一下groebner这个tactic的证明-/
/-Ideal Membership problem-/
example (f : MvPolynomial (Fin 2) ℚ):
  X 0 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
    have h₁ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis ) := by
      basis
    have h₂ : lex.IsRemainder (X 0: MvPolynomial (Fin 2) ℚ)
      {X 0 , X 1^2} 0 := by
      remainder
    -- have h₃ : lex.IsRemainder (X 0: MvPolynomial (Fin 2) ℚ)
    --   ({X 0 , X 1^2}: Finset (MvPolynomial (Fin 2) ℚ)) 0 := by
    --   norm_cast
    have h₄: Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) = Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
      apply le_antisymm
      · rw [Ideal.span_le]
        intro x hx
        simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl|rfl)
        ·
          sorry
        ·
          sorry
      · rw [Ideal.span_le]
        intro x hx
        simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl|rfl)
        · sorry
        · sorry
      --   · convert_to 1 * X 0 + 1 * X 1 ^2 ∈ _
      --     · sorry
      --     repeat
      --       conv in _ ∈ Ideal.span (insert _ _) => {}
      --       apply aux

      --     sorry
      --   ·
      --     sorry
      -- · sorry
    have h₅ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) ) := by
      rw [h₄]
      norm_cast at h₁
    apply (isRemainder_zero_iff_mem_ideal_of_isGroebner' h₅).mp h₂



#check existsUnique_isRemainder_of_isGroebnerBasis₀

  -- get_basis
example:
   X 2 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    have h₁ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis
    have l₁ : Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) = Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
      sorry
    have l₂ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) ) := by
      rw [l₁]
      norm_cast at h₁
      -- norm_cast at h₁
    have h₂ : lex.IsRemainder (X 2: MvPolynomial (Fin 3) ℚ)
      {X 0, X 1^2} (X 2) := by
      remainder'
    by_contra h₄
    have h₅ : lex.IsRemainder (X 2: MvPolynomial (Fin 3) ℚ)
      ({X 0 , X 1^2}: Set (MvPolynomial (Fin 3) ℚ)) (0) := by
      apply (isRemainder_zero_iff_mem_ideal_of_isGroebner' l₂).mpr h₄
    have h₆ : X 2 = (0 : MvPolynomial (Fin 3) ℚ ):= by
      exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' l₂ h₂).mpr h₄
    have neq : X 2 ≠ (0 : MvPolynomial (Fin 3) ℚ) := by
      exact X_ne_zero 2
    contradiction

/-Radical Ideal Membership problem-/
example :
  X 0 * X 1 ∈ (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) ℚ))).radical:= by
   have h₁ : letI basis := ({X 0, X 1} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      sorry
   sorry

example :
  X 3 ∉ (Ideal.span ({X 0 ^ 2 - X 1, 3 * X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical := by

  sorry

/-Intersection of Ideals-/
example :
    (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
    ⊓
    Ideal.span ({X 1 ^ 3 - X 0 * X 1} : Set (MvPolynomial (Fin 2) ℚ))
    =
    Ideal.span {X 1 ^ 3 - X 0 * X 1} := by
    have h₁ : letI basis := ({X 1 ^ 3 - X 0 * X 1} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      sorry
    have h₂ : (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
    ⊓
    Ideal.span ({X 1 ^ 3 - X 0 * X 1} : Set (MvPolynomial (Fin 2) ℚ)) = Ideal.span {X 1 ^ 3 - X 0 * X 1} := by
      sorry
    exact h₂

example :
    (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
    ⊓
    Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ))
    ≠
    Ideal.span {X 0 ^ 4 - X 1} := by
    have h₁ : letI basis := ({X 0 ^ 4 - X 1} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      sorry
    have h₂ : letI basis := ({X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      sorry
    have h₃ :(Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ)) ⊓ Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ)) = Ideal.span {X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3} := by
      sorry
    have h₄ : ((Ideal.span {X 0 ^4 - X 1}):Ideal (MvPolynomial (Fin 2) ℚ)) = Ideal.span {X 0 ^4 - X 1} := by
      sorry





    sorry





end
