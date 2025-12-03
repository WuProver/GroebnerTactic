import Groebner.Basic
import Groebner.List

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

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
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [isRemainder_range_fin, ← exists_and_right]
  use [X 0, X 1 ^ 2, X 2 ^ 3, X 3 ^ 4].get
  split_ands
  focus
    simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
    all_goals decide +kernel-- PIT, proof by reflection
  focus
    intro i
    fin_cases i
    all_goals {
        -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
        simp only [List.get, Fin.isValue]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
      }
  simp

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
    simp only [← Set.range_get_singleton, ← Set.range_get_cons_list]
    -- use index
    rw [isRemainder_range_fin, ← exists_and_right]
    use [X 3 ^ 4, 0].get
    split_ands
    focus
      simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      try grind-- PIT, we will rely on reflection
    focus
      intro i
      fin_cases i
      all_goals {
        -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
        simp only [List.get, Fin.isValue]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
      }
    focus
      rw [Function.Surjective.forall (AddEquiv.surjective (SortedFinsupp.lexAddEquiv compare))]
      simp only [MvPolynomial.SortedRepr.support_eq, Finset.mem_map_equiv,
        Fin.isValue, List.length_nil, List.length_cons,
        EquivLike.coe_symm_apply_apply, List.mem_toFinset]
      intro x h i
      fin_cases i
      all_goals
        simp only [List.get]
        rw [← tsub_eq_zero_iff_le, MvPolynomial.SortedRepr.lex_degree_eq]
        convert_to _ → ¬ SortedFinsupp.toFinsupp _ - SortedFinsupp.toFinsupp x = 0
        rw [← SortedFinsupp.toFinsupp_tsub, SortedFinsupp.toFinsupp_eq_zero_iff]
        decide +kernel +revert

example :
    letI basis := ({X 0 + X 1 ^ 2, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
  rw [buchberger_criterion]
  simp only [Fin.isValue, Subtype.forall, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, sPolynomial_self]
  simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  simp_rw [isRemainder_range_fin]
  split_ands
  ·
    focus
      use [0, 0].get -- spoly f0 f0
      split_ands
      · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
        all_goals decide +kernel-- PIT by reflection
      · intro i
        fin_cases i
        all_goals {
          -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
          simp only [List.get, Fin.isValue]
          all_goals {
            rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
              SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
              ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
            decide +kernel
          }
        }
  · simp
  · use [0, X 1 ^ 2].get -- spoly f0 f1
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get]
      all_goals decide +kernel-- PIT by reflection
    · intro i
      fin_cases i
      all_goals {
        -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
        simp only [List.get, Fin.isValue]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
      }
  · simp
  · use [0, - X 1 ^ 2].get -- spoly f1 f0
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      all_goals decide +kernel
    · intro i
      fin_cases i
      all_goals {
        -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
        simp only [List.get, Fin.isValue]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
      }
  · simp
  · use [0, 0].get -- spoly f1 f1
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      all_goals decide +kernel-- PIT by reflection
    · intro i
      fin_cases i
      all_goals {
        -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
        simp only [List.get, Fin.isValue]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
      }
  · simp


lemma aux {f g r : MvPolynomial σ k} {G : Set (MvPolynomial σ k)} (h : r ∈ Ideal.span G) : r + f * g ∈ Ideal.span (insert g G):= by
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
    apply le_antisymm
    focus
      rw [Ideal.span_le]
      intro x hx
      simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl|rfl)
      focus
        apply (iff_of_eq <| congrArg (a₂ := 1 * X 1 ^ 2 + 1 * X 0 ) (· ∈ _) (by decide +kernel)).mpr
        change _ ∈ (_ : Ideal _)
        repeat
          conv in _ ∈ Ideal.span (insert _ _) => {}
          apply aux
        apply Ideal.mul_mem_left
        apply Ideal.mem_span_singleton_self
      focus
        apply (iff_of_eq <| congrArg (a₂ := 1 * X 1 ^ 2 + 0 * X 0 ) (· ∈ _) (by decide +kernel)).mpr
        change _ ∈ (_ : Ideal _)
        repeat
          conv in _ ∈ Ideal.span (insert _ _) => {}
          apply aux
        apply Ideal.mul_mem_left
        apply Ideal.mem_span_singleton_self
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

example (a b c d : Int) : 5 * d + 1 * a + 3 * c + 2 * b  ∈ Ideal.span {a, b, c, d} := by
  submodule_span [1, 2, 3, 5]
  ring


open MvPolynomial MonomialOrder

example :  X 0^2 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
  submodule_span [X 0, -X 0]
  ring

example :
  Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) = Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl|rfl)
    ·
      change _ ∈ (_ : Ideal _)
      submodule_span [1, 1]
      decide +kernel
    ·
      change _ ∈ (_ : Ideal _)
      submodule_span [0, 1]
      decide +kernel
  · rw [Ideal.span_le]
    intro x hx
    simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl|rfl)
    ·
      change _ ∈ (_ : Ideal _)
      submodule_span [1, -1]
      ring
    ·
      change _ ∈ (_ : Ideal _)
      submodule_span [0, 1]
      decide +kernel
      
end
