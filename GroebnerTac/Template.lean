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

/- The template of the remainder equals to `0` -/
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
    -- all_goals decide +kernel-- PIT, proof by reflection
    all_goals {
      exact MvPolynomial.SortedRepr.eq_iff'.mpr (by decide +kernel)
    }
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

/- The templaye of the remainder does not equal to `0` -/
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

/- The template of `G` is the groebner basis of `Ideal.span G` -/
example :
    letI basis := ({X 0 + X 1 ^ 2, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
  rw [buchberger_criterion]
  simp only [Fin.isValue, Subtype.forall, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, sPolynomial_self]
  simp only [← Set.range_get_singleton, ← Set.range_get_cons_list]
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
      all_goals {
        exact MvPolynomial.SortedRepr.eq_iff'.mpr (by decide +kernel)
      }-- PIT by reflection
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


/- The template of `G` is the groebner basis of `Ideal.span F` -/
set_option maxHeartbeats 20000000 in
example:
  lex.IsGroebnerBasis ({X 1^3 - X 2^2, X 0^2 - X 1, X 0*X 1 - X 2, X 0*X 2 - X 1^2} : Set <| MvPolynomial (Fin 3) ℚ)  (Ideal.span ({X 0^2 - X 1, X 0^3 - X 2} : Set <| MvPolynomial (Fin 3) ℚ)):= by
    have h_gb : let basis : Set (MvPolynomial (Fin 3) ℚ) := {X 1^3 - X 2^2, X 0^2 - X 1, X 0*X 1 - X 2, X 0*X 2 - X 1^2}
          lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis
    have h_ideal : Ideal.span ({X 1^3 - X 2^2, X 0^2 - X 1, X 0*X 1 - X 2, X 0*X 2 - X 1^2} : Set <| MvPolynomial (Fin 3) ℚ) = Ideal.span ({X 0^2 - X 1, X 0^3 - X 2} : Set <| MvPolynomial (Fin 3) ℚ) := by
      ideal
    simp [h_ideal] at h_gb
    exact h_gb

/- A lemma help prove f ∈ I -/
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

open MvPolynomial MonomialOrder

/- Help prove `f` in `Ideal.span G` -/
example :  X 0^2 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
  submodule_span [X 0, -X 0]
  ring

/- `Ideal.span G1` = `Ideal.span G2` -/
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

/-Ideal Membership Problem-/
example :
  X 0 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
    have h_rm : lex.IsRemainder (X 0: MvPolynomial (Fin 2) ℚ)
      {0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2} 0 := by
      simp
      remainder
      -- remainder
    have h_gb : letI basis := ({0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis ) := by
      simp
      basis
    have h_ideal : Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) =
      Ideal.span ({0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
      simp
      ideal
    have h_gb' : letI basis := ({0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2} : Set <| MvPolynomial (Fin 2) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}
    : Set (MvPolynomial (Fin 2) ℚ)) ) := by
      rw [h_ideal]
      exact h_gb
    apply (isRemainder_zero_iff_mem_ideal_of_isGroebner' h_gb').mp h_rm


example:
   X 2 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    have h_gb : letI basis := ( {0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      simp
      basis
    have l_ideal : Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) =
    Ideal.span ( {0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
      simp
      ideal
    have h_gb' : letI basis := ( {0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
      lex.IsGroebnerBasis basis (Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} :
      Set (MvPolynomial (Fin 3) ℚ)) ) := by
      rw [l_ideal]
      exact h_gb
      -- norm_cast at h₁
    have h_rm : lex.IsRemainder (X 2: MvPolynomial (Fin 3) ℚ)
      {0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2} (X 2) := by
      simp
      remainder
    by_contra h_mem
    have eq : X 2 = (0 : MvPolynomial (Fin 3) ℚ ):= by
      exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h_gb' h_rm).mpr h_mem
    have neq : X 2 ≠ (0 : MvPolynomial (Fin 3) ℚ) := by
      decide +kernel
    contradiction

example (f : MvPolynomial (Fin 2) ℚ):
  X 0 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
  submodule_span [1, -1]
  decide +kernel

/-Radical Ideal Membership-/
example :
  X 0 * X 1 ∈ (Ideal.span ({X 0 ^ 5, X 1 ^ 5} : Set (MvPolynomial (Fin 3) ℚ))).radical:= by
    rw [Ideal.mem_radical_iff]
    use 5
    ideal_membership

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
  have h₃: 1 ∈ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
    rcases h₂ with ⟨p, hp⟩
    rw [hp] at h₁
    have l₁ : X 2 ^ n ∈ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
      have t₁: Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) ≤ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
        apply Ideal.span_mono
        simp
      exact t₁ hn
    have l₂ : (1 - X 2) * p ∈ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
      apply Ideal.mul_mem_right
      have t₁: Ideal.span ({1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) ≤ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
        apply Ideal.span_mono
        simp
      have t₂: (1 - X 2) ∈ Ideal.span ({1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
        exact Ideal.mem_span_singleton_self (1 - X 2)
      exact t₁ t₂
    rw [h₁]
    apply Ideal.add_mem _ l₁ l₂
    rw [← h₁]
    refine ⟨Ideal.span {1 - X 2, X 0, X 1}, ?_⟩
    ext x
    constructor
    · intro h
      simp at h
      have l: ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) ⊆ (Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ))) := by
        exact Ideal.subset_span
      exact h l
    · intro h
      simp
      intro a
      simp at h
      exact h
  have h₄ : lex.IsRemainder (1: MvPolynomial (Fin 3) ℚ)
      {1 - X 2, X 0, X 1} 1 := by
    remainder
  have h₅ : letI basis := ({1 - X 2, X 0, X 1} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    basis
  have h₆ : (1: MvPolynomial (Fin 3) ℚ) = 0 := by
     exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h₅ h₄).mpr h₃
  simp at h₆

end
