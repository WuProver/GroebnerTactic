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
open MvPolynomial MonomialOrder

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]


variable {R : Type*} [CommRing R] {I : Ideal R} {a : R} {B : Set R}

lemma Ideal.insert_le_of_mem_of_le:
    a ∈ I → Ideal.span B ≤ I → Ideal.span (insert a B) ≤ I := by
    intro ha hB
    rw [Ideal.span_insert]
    simp
    constructor
    · exact (Ideal.span_singleton_le_iff_mem I).mpr ha
    · exact hB

example : Ideal.span ({X 2 * X 0 ^ 2 - X 2 * X 1, (1 - X 2)*(X 1 ^ 2 - X 0)} : Set <| MvPolynomial (Fin 3) ℚ) = Ideal.span ({X 0^2*X 1^2 - X 0^3 - X 1^3 + X 0*X 1, X 0 ^2 * X 2 - X 1 * X 2, X 1^2 * X 2 - X 0 * X 2 - X 1 ^2 + X 0} : Set <| MvPolynomial (Fin 3) ℚ) := by
  ideal


