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

set_option maxHeartbeats 200000000 in
set_option synthInstance.maxSize 2000000 in
-- set_option trace.profiler true in
example :
  (X 1^2 + C 3 * X 1 * X 4 + C 2 * X 3^6 * X 4 + C 6 * X 3^5 * X 4^2 + X 3^4 * X 4^3 - C 2 * X 3^3 * X 4^4 + X 3^2 -
  C (566/275 : ℚ) * X 3 * X 4^11 - C (6273/25 : ℚ) * X 3 * X 4^6 + C (69019/275 : ℚ) * X 3 * X 4 -
  C (1467/275 : ℚ) * X 4^12 - C (16271/25 : ℚ) * X 4^7 + C (179073/275 : ℚ) * X 4^2)
  ∈ (Ideal.span ({X 0 + X 1 + X 2 + X 3 + X 4,
    X 0*X 1 + X 0*X 2 + X 0*X 3 + X 0*X 4 + X 1*X 2 + X 1*X 3 + X 1*X 4 + X 2*X 3 + X 2*X 4 + X 3*X 4,
    X 0*X 1*X 2 + X 0*X 1*X 3 + X 0*X 1*X 4 + X 0*X 2*X 3 + X 0*X 2*X 4 + X 0*X 3*X 4 +
    X 1*X 2*X 3 + X 1*X 2*X 4 + X 1*X 3*X 4 + X 2*X 3*X 4,
    X 0*X 1*X 2*X 3 + X 0*X 1*X 2*X 4 + X 0*X 1*X 3*X 4 + X 0*X 2*X 3*X 4 +
    X 1*X 2*X 3*X 4,
    X 0*X 1*X 2*X 3*X 4 - 1} : Set (MvPolynomial (Fin 5) ℚ))).radical := by
    radical_membership
