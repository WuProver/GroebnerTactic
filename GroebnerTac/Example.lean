import Groebner.Basic
import Groebner.List

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

import GroebnerTac.Tactic


/-!
In this file we show some examples of using the GroebnerTac library.

-/

section
open MvPolynomial MonomialOrder

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)

#check Set.range_get_nil
#check Set.range_get_singleton

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [isRemainder_range_fin]
  split_ands
  · use [X 0, X 1 ^ 2, X 2 ^ 3, X 3 ^ 4].get
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      all_goals decide +kernel-- PIT, proof by reflection
    · intro i
      fin_cases i
      all_goals {
        simp [-List.get_eq_getElem, List.get]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
      }
  · simp

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
    -- showGoal
    sorry

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [isRemainder_range_fin]
  split_ands
  · use [X 3 ^ 4, 0].get
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get]
      -- rw [Polynomial.PolyRepr.eq_iff']
      -- all_goals decide+kernerl-- PIT by reflection
      all_goals grind-- PIT by reflection
    · intro i
      fin_cases i
      · simp [-List.get_eq_getElem, List.get]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
    --     rw [MvPolynomial.PolyRepr.lex_degree_eq', MvPolynomial.PolyRepr.lex_degree_eq',
    -- SortedFinsupp.orderIsoFinsupp.le_iff_le, ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
    --     decide +kernel-- compare degree by reflection
      · simp [-List.get_eq_getElem, List.get]
  · simp only [Fin.isValue, mem_support_iff, coeff_add, ne_eq, List.length_cons, List.length_nil,
    Nat.reduceAdd, List.get_eq_getElem]
    intro a h₁ h₂ h₃
    fin_cases h₂
    · simp
      sorry
    · sorry

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
      showGoal

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

example :
    letI basis := ({X 0 + X 1 ^ 2, X 1 ^ 2} : Finset <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
  rw [buchberger_criterion]
  simp only [Fin.isValue, Finset.coe_insert, Finset.coe_singleton, Subtype.forall,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  simp_rw [isRemainder_range_fin]
  split_ands
  · use [0, 0].get -- spoly f0 f0
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      all_goals decide +kernel-- PIT by reflection
    · intro i
      fin_cases i
      all_goals {
        simp [-List.get_eq_getElem, List.get]
        all_goals decide +kernel -- compare degree by reflection
      }
  · simp
  · use [0, X 1 ^ 2].get -- spoly f0 f1
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get]
        -- convert sum to add
      sorry
      -- all_goals decide +kernel-- PIT by reflection
    · intro i
      fin_cases i
      · simp [-List.get_eq_getElem, List.get]
      · simp [-List.get_eq_getElem, List.get]
        sorry
      -- all_goals {
      --   simp [-List.get_eq_getElem, List.get]
      --   all_goals sorry-- compare degree by reflection
      -- }
  · simp
  · use [0, - X 1 ^ 2].get -- spoly f1 f0
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      sorry
    · intro i
      fin_cases i
      · simp [-List.get_eq_getElem, List.get]
      · simp [-List.get_eq_getElem, List.get]
        sorry
  · simp
  · use [0, 0].get -- spoly f1 f1
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      all_goals decide +kernel-- PIT by reflection
    · intro i
      fin_cases i
      all_goals {
        simp [-List.get_eq_getElem, List.get]
        all_goals decide +kernel -- compare degree by reflection
      }
  · simp
example :
    letI basis := ({X 0 + X 1 ^ 2, X 1 ^ 2} : Finset <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    sorry
    -- groebner
end


#check MvPolynomial.X
