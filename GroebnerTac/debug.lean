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

example :
  Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) = Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    ideal


    sorry


example :
  Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) = Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    apply le_antisymm
    {
    focus
      rw [Ideal.span_le]
      intro x hx
      simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl|rfl)
      focus
        apply (iff_of_eq <| congrArg (a₂ :=  C ↑(↑1 / ↑1) * X 1 ^ 2 + C ↑(↑1 / ↑1) * X 0 ^ 1 ) (· ∈ _) (by decide +kernel)).mpr
        change _ ∈ (_ : Ideal _)
        repeat
          conv in _ ∈ Ideal.span (insert _ _) => {}
          apply aux
        apply Ideal.mul_mem_left
        apply Ideal.mem_span_singleton_self
        
        sorry
      focus
        apply (iff_of_eq <| congrArg (a₂ := 1 * X 1 ^ 2 + 0 * X 0 ) (· ∈ _) (by decide +kernel)).mpr
        change _ ∈ (_ : Ideal _)
        repeat
          conv in _ ∈ Ideal.span (insert _ _) => {}
          apply aux
        apply Ideal.mul_mem_left
        apply Ideal.mem_span_singleton_self
      }
    {
    focus
      rw [Ideal.span_le]
      intro x hx
      simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl|rfl)
      focus
        apply (iff_of_eq <| congrArg (a₂ := (- 1) * X 1 ^ 2 + 1 * (X 0 + X 1 ^ 2)) (· ∈ (_ : Ideal _)) (by decide +kernel)).mpr
        -- change _ ∈ (_ : Ideal _)
        repeat
          conv in _ ∈ Ideal.span (insert _ _) => {}
          apply aux
        apply Ideal.mul_mem_left
        apply Ideal.mem_span_singleton_self
      focus
        apply (iff_of_eq <| congrArg (a₂ := 1 * X 1 ^ 2 + 0 * (X 0 + X 1 ^ 2)) (· ∈ (_ : Ideal _)) (by decide +kernel)).mpr
        -- change _ ∈ (_ : Ideal _)
        repeat
          conv in _ ∈ Ideal.span (insert _ _) => {}
          apply aux
        apply Ideal.mul_mem_left
        apply Ideal.mem_span_singleton_self
    }
