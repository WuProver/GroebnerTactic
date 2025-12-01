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
/-这里这么做算不算做复杂了 但是证不等于的时候确实需要这么一个充要条件-/
/-Ideal Membership problem-/
example (f : MvPolynomial (Fin 2) ℚ):
  X 0 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
    have h₁ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis ) := by
      basis
    have h₂ : lex.IsRemainder (X 0: MvPolynomial (Fin 2) ℚ)
      {X 0 , X 1^2} 0 := by
      remainder
    have h₄: Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) = Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
      ideal
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
      ideal
    have l₂ : letI basis := ({X 0, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) ) := by
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
/-这里是不是做成系数表示会更好-/
example :
  X 0 * X 1 ∈ (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical:= by
    sorry
    -- rw [Ideal.mem_radical_iff]
    -- have h₁ : (Ideal.span ({X 0, X 1, 1 - X 0*X 1} : Set (MvPolynomial (Fin 3) ℚ))) = Ideal.span {1} := by
    --   sorry
    -- have h₂ : (1: MvPolynomial (Fin 2) ℚ) = X 0 * X 1 + (1 - X 0*X 1) := by
    --   decide +kernel

    -- sorry

/-算出典范的Groebner基之后要证明他们不相等-/
/-这里同样要用一个典范的groebner基？-/
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
    
    sorry
    -- have h₁: (Ideal.span ({X 3 *(X 0 ^ 2 - X 1), (1 - X 3)*(X 1^2 - X 0)} : Set (MvPolynomial (Fin 3) ℚ)) : Ideal (MvPolynomial (Fin 3) ℚ))
    --   ⊆ (Ideal.span ({X 0 ^ 2 - X 1} : Set (MvPolynomial (Fin 3) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))⊓
    --   Ideal.span ({X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 3) ℚ)) := by
    --   sorry
    -- have h₂ : letI basis := ({X 3 *(X 0 ^ 2 - X 1), (1 - X 3)*(X 1^2 - X 0)} : Set <| MvPolynomial (Fin 3) ℚ)
    -- lex.IsGroebnerBasis basis (Ideal.span basis) := by


end
