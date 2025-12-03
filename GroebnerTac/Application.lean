import Mathlib

import Groebner.Basic
import Groebner.List

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

import GroebnerTac.Tactic
import GroebnerTac.Ideal
section
open MvPolynomial MonomialOrder Ideal

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]


/-Ideal Membership problem-/
example :
  X 0 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
    have h₁ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis ) := by
      basis
    have h₂ : lex.IsRemainder (X 0: MvPolynomial (Fin 2) ℚ)
      {X 0 , X 1^2} 0 := by
      remainder
    have h₄: Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) =
      Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
      ideal
    have h₅ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}
    : Set (MvPolynomial (Fin 2) ℚ)) ) := by
      rw [h₄]
      norm_cast at h₁
    apply (isRemainder_zero_iff_mem_ideal_of_isGroebner' h₅).mp h₂

example (f : MvPolynomial (Fin 2) ℚ):
  X 0 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
  submodule_span [1, -1]
  decide +kernel


example:
   X 2 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    have h₁ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis
    have l₁ : Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) =
    Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
      ideal
    have l₂ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
      lex.IsGroebnerBasis basis (Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} :
      Set (MvPolynomial (Fin 3) ℚ)) ) := by
      rw [l₁]
      norm_cast at h₁
      -- norm_cast at h₁
    have h₂ : lex.IsRemainder (X 2: MvPolynomial (Fin 3) ℚ)
      {X 0, X 1^2} (X 2) := by
      remainder'
    by_contra h₄
    have h₆ : X 2 = (0 : MvPolynomial (Fin 3) ℚ ):= by
      exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' l₂ h₂).mpr h₄
    have neq : X 2 ≠ (0 : MvPolynomial (Fin 3) ℚ) := by
      exact X_ne_zero 2
    contradiction

/-Radical Ideal Membership problem-/
example :
  X 0 * X 1 ∈ (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical:= by
    sorry

example :
  X 2 ∉ (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical := by
  by_contra h
  rw [Ideal.mem_radical_iff] at h
  rcases h with ⟨n, hn⟩
  have h₁: (1: MvPolynomial (Fin 3) ℚ) = X 2 ^ n + (1 - X 2^n) := by
    -- decide +kernel
    simp
  have h₂: ((1 - X 2): MvPolynomial (Fin 3) ℚ) ∣ (1 - X 2^n) := by
    exact one_sub_dvd_one_sub_pow (X 2) n
  have h₃: 1 ∈ Ideal.span ({X 0, X 1, 1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    rcases h₂ with ⟨p, hp⟩
    rw [hp] at h₁
    have l₁ : X 2 ^ n ∈ Ideal.span ({X 0, X 1, 1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
      have t₁: Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) ≤ Ideal.span ({X 0, X 1, 1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
        apply Ideal.span_mono
        simp
      exact t₁ hn
    have l₂ : (1 - X 2) * p ∈ Ideal.span ({X 0, X 1, 1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
      apply Ideal.mul_mem_right
      have t₁: Ideal.span ({1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) ≤ Ideal.span ({X 0, X 1, 1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
        apply Ideal.span_mono
        simp
      have t₂: (1 - X 2) ∈ Ideal.span ({1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
        exact Ideal.mem_span_singleton_self (1 - X 2)
      exact t₁ t₂
    rw [h₁]
    apply Ideal.add_mem _ l₁ l₂
    rw [← h₁]
    refine ⟨Ideal.span {X 0, X 1, 1 - X 2}, ?_⟩
    ext x
    constructor
    · intro h
      simp at h
      have l: ({X 0, X 1, 1 - X 2} : Set (MvPolynomial (Fin 3) ℚ)) ⊆ (Ideal.span ({X 0, X 1, 1 - X 2} : Set (MvPolynomial (Fin 3) ℚ))) := by
        exact Ideal.subset_span
      exact h l
    · intro h
      simp
      intro a
      simp at h
      exact h
  have h₄ : lex.IsRemainder (1: MvPolynomial (Fin 3) ℚ)
      {X 0, X 1, 1 - X 2} 1 := by
    remainder'
  have h₅ : letI basis := ({X 0, X 1, 1 - X 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    basis
  have h₆ : (1: MvPolynomial (Fin 3) ℚ) = 0 := by
     exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h₅ h₄).mpr h₃
  simp at h₆

/-Intersection of Ideals-/
example :
    (Ideal.span ({X 0 ^ 3* X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
    ⊓
    Ideal.span ({X 0 * X 1^2} : Set (MvPolynomial (Fin 2) ℚ))
    =
    Ideal.span {X 0 ^3 * X 1} := by
    have h₁ : letI basis := ({X 1 ^ 3 - X 0 * X 1} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis
    have h₂ : (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
    ⊓
    Ideal.span ({X 1 ^ 3 - X 0 * X 1} : Set (MvPolynomial (Fin 2) ℚ)) = Ideal.span {X 1 ^ 3 - X 0 * X 1} := by

      sorry
    sorry

/-这里有个问题 要证明两个理想不相等-/
example :
    (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
    ⊓
    Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ))
    ≠
    Ideal.span {X 0 ^ 4 - X 1} := by
    have h₁ : letI basis := ({X 0 ^ 4 - X 1} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis
    have h₂ : letI basis := ({X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis
    have h₃ :(Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ)) ⊓ Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ)) = Ideal.span {X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3} := by

      sorry
    have h₄ : ((Ideal.span {X 0 ^4 - X 1}):Ideal (MvPolynomial (Fin 2) ℚ)) = Ideal.span {X 0 ^4 - X 1} := by
      exact rfl
    have h₅ :  letI basis := ({X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis ((Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ)) ⊓ Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ))) := by
      rw[h₃]
      exact h₂
    have h₆ : (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
    ⊓
    Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ)) = Ideal.span {X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3}  := by
      exact h₃
    rw [h₄]
    rw [h₆]
    sorry

example :
  (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 3) ℚ)) : Ideal (MvPolynomial (Fin 3) ℚ))
      ⊓
      Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 3) ℚ))
      ≠
      Ideal.span {X 0 ^ 4 - X 1} := by
    have h₁ : letI basis := ({X 0 ^ 4 - X 1} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis
    have h₂ : letI basis := ({X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis
    have h₃ : Ideal.span ({X 2 * (X 0 ^ 2 - X 1), (1 - X 2)*(X 1 ^ 2 - X 0)} : Set <| MvPolynomial (Fin 3) ℚ) = Ideal.span ({X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3, X 0 ^2 * X 2 - X 1 * X 2, X 1^2 * X 2 - X 0 * X 2 - X 1 ^2 + X 0} : Set <| MvPolynomial (Fin 3) ℚ) := by
      ideal
    have h₄ : Ideal.span ({X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3, X 0 ^2 * X 2 - X 1 * X 2, X 1^2 * X 2 - X 0 * X 2 - X 1 ^2 + X 0} : Set <| MvPolynomial (Fin 3) ℚ) ⊓ Ideal.span ({X 0, X 1}: Set <| MvPolynomial (Fin 3) ℚ) = Ideal.span ({X 0^3 - X 0^2*X 1^2 - X 0*X 1 + X 1^3} : Set <| MvPolynomial (Fin 3) ℚ) := by
      apply le_antisymm
      ·

        sorry
      ·
        sorry
    rw [←h₃] at h₄
    have h₅:  Ideal.span {X 2 * (X 0 ^ 2 - X 1), (1 - X 2) * (X 1 ^ 2 - X 0)} ⊓ Ideal.span {X 0, X 1} = (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 3) ℚ)) : Ideal (MvPolynomial (Fin 3) ℚ))
      ⊓
      Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 3) ℚ)) := by
       sorry
    rw [← h₅]
    rw [h₄]
    have h₆ : (X 0 ^ 3 - X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 + X 1 ^ 3 : (MvPolynomial (Fin 3) ℚ)) ∉  Ideal.span {X 0 ^ 4 - X 1} := by
      by_contra l
      have l₁ : lex.IsRemainder (X 0 ^ 3 - X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 + X 1 ^ 3 : (MvPolynomial (Fin 3) ℚ)) {X 0 ^ 4 - X 1} (X 0 ^ 3 - X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 + X 1 ^ 3 : (MvPolynomial (Fin 3) ℚ))  := by
        remainder'
      have l₂ : (X 0 ^ 3 - X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 + X 1 ^ 3 : (MvPolynomial (Fin 3) ℚ)) = 0 := by
        exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h₁ l₁).mpr l
      have l₃ : (X 0 ^ 3 - X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 + X 1 ^ 3 : (MvPolynomial (Fin 3) ℚ)) ≠ 0 := by
        decide +kernel
      exact l₃ l₂
    have h₇ : (X 0 ^ 3 - X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 + X 1 ^ 3 : (MvPolynomial (Fin 3) ℚ)) ∈   Ideal.span {X 0 ^ 3 - X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 + X 1 ^ 3 } := by
      exact mem_span_singleton_self (X 0 ^ 3 - X 0 ^ 2 * X 1 ^ 2 - X 0 * X 1 + X 1 ^ 3)
    exact ne_of_mem_of_not_mem' h₇ h₆
    -- have h₁: (Ideal.span ({X 3 *(X 0 ^ 2 - X 1), (1 - X 3)*(X 1^2 - X 0)} : Set (MvPolynomial (Fin 3) ℚ)) : Ideal (MvPolynomial (Fin 3) ℚ))
    --   ⊆ (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 3) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))⊓
    --   Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 3) ℚ)) := by
    --   sorry
    -- have h₂ : letI basis := ({X 3 *(X 0 ^ 2 - X 1), (1 - X 3)*(X 1^2 - X 0)} : Set <| MvPolynomial (Fin 3) ℚ)
    -- lex.IsGroebnerBasis basis (Ideal.span basis) := by


end
