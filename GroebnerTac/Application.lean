import Mathlib

import Groebner.Basic
import Groebner.List
-- import Groebner.Lemma

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

import GroebnerTac.Tactic

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
  X 0 ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) ℚ)) := by
    ideal_membership

example :
   X 2 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    ideal_membership

example :
   X 1 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    ideal_membership

example :
   X 0 + X 1 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    ideal_membership

example :
  X 0 + 2 * X 1^2 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
    ideal_membership

example :
  X 0 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
    ideal_membership

example : 1 ∉ Ideal.span  ({X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ) := by
   ideal_membership


example : 1 ∉ Ideal.span  ({X 0 + X 1, 1 - X 0*X 3} : Set <| MvPolynomial (Fin 4) ℚ) := by
   ideal_membership

example : 1 ∉ Ideal.span  ({X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ) := by
   ideal_membership

example : 1 ∈ Ideal.span ({X 0, X 1, 1 - X 3 * X 0} : Set <| MvPolynomial (Fin 4) ℚ) := by

  ideal_membership

-- example : 1



/-Radical Ideal Membership problem-/
example :
  X 0 * X 1 ∈ (Ideal.span ({X 0 ^ 5, X 1 ^ 5} : Set (MvPolynomial (Fin 3) ℚ))).radical:= by
    radical_membership

example :
  X 2 ∉ (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical := by
  radical_membership


example :
  X 0 ∉ (Ideal.span ({X 0 + X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical := by
  radical_membership



end
