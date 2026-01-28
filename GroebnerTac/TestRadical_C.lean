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


--cyclic-1
set_option trace.profiler true in
example :
  (X 0 - 1) ∈ (Ideal.span ({X 0-1} : Set (MvPolynomial (Fin 2) ℚ))).radical := by
    radical_membership

--cyclic-2
set_option trace.profiler true in
example :
  (X 1^2 + 1) ∈ (Ideal.span ({X 0 + X 1, X 0*X 1 - 1} : Set (MvPolynomial (Fin 2) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
example :
  (X 0 + X 1) ∈ (Ideal.span ({X 0 + X 1, X 0*X 1 - 1} : Set (MvPolynomial (Fin 2) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
example :
  (X 0*X 1 - 1) ∈ (Ideal.span ({X 0 + X 1, X 0*X 1 - 1} : Set (MvPolynomial (Fin 2) ℚ))).radical := by
    radical_membership

--cyclic-3
set_option trace.profiler true in
example :
  (X 0 + X 1 + X 2) ∈ (Ideal.span ({X 0 + X 1 + X 2, X 0*X 1 + X 0*X 2 + X 1*X 2, X 0*X 1*X 2 - 1} :
    Set (MvPolynomial (Fin 3) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
example :
  (X 1^2 + X 1*X 2 + X 2^2) ∈ (Ideal.span ({X 0 + X 1 + X 2, X 0*X 1 + X 0*X 2 + X 1*X 2, X 0*X 1*X 2 - 1} :
    Set (MvPolynomial (Fin 3) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
example :
  (X 2^3 - 1) ∈ (Ideal.span ({X 0 + X 1 + X 2, X 0*X 1 + X 0*X 2 + X 1*X 2, X 0*X 1*X 2 - 1} :
    Set (MvPolynomial (Fin 3) ℚ))).radical := by
    radical_membership

--cyclic-4
set_option trace.profiler true in
example :
  (X 0 + X 1 + X 2 + X 3) ∈ (Ideal.span ({X 0 + X 1 + X 2 + X 3,
    X 0*X 1 + X 0*X 3 + X 1*X 2 + X 2*X 3,
    X 0*X 1*X 2 + X 0*X 1*X 3 + X 0*X 2*X 3 + X 1*X 2*X 3,
    X 0*X 1*X 2*X 3 - 1} : Set (MvPolynomial (Fin 4) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
example :
  (X 1^2 + 2*X 1*X 3 + X 3^2) ∈ (Ideal.span ({X 0 + X 1 + X 2 + X 3,
    X 0*X 1 + X 0*X 3 + X 1*X 2 + X 2*X 3,
    X 0*X 1*X 2 + X 0*X 1*X 3 + X 0*X 2*X 3 + X 1*X 2*X 3,
    X 0*X 1*X 2*X 3 - 1} : Set (MvPolynomial (Fin 4) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
set_option maxHeartbeats 200000000 in
set_option synthInstance.maxSize 2000000 in
example :
  (X 1*X 2 - X 1*X 3 + X 2^2*X 3^4 + X 2*X 3 - 2*X 3^2) ∈ (Ideal.span ({X 0 + X 1 + X 2 + X 3,
    X 0*X 1 + X 0*X 3 + X 1*X 2 + X 2*X 3,
    X 0*X 1*X 2 + X 0*X 1*X 3 + X 0*X 2*X 3 + X 1*X 2*X 3,
    X 0*X 1*X 2*X 3 - 1} : Set (MvPolynomial (Fin 4) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
example :
  (X 1*X 3^4 - X 1 + X 3^5 - X 3) ∈ (Ideal.span ({X 0 + X 1 + X 2 + X 3,
    X 0*X 1 + X 0*X 3 + X 1*X 2 + X 2*X 3,
    X 0*X 1*X 2 + X 0*X 1*X 3 + X 0*X 2*X 3 + X 1*X 2*X 3,
    X 0*X 1*X 2*X 3 - 1} : Set (MvPolynomial (Fin 4) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
example :
  (X 2^3*X 3^2 + X 2^2*X 3^3 - X 2 - X 3) ∈ (Ideal.span ({X 0 + X 1 + X 2 + X 3,
    X 0*X 1 + X 0*X 3 + X 1*X 2 + X 2*X 3,
    X 0*X 1*X 2 + X 0*X 1*X 3 + X 0*X 2*X 3 + X 1*X 2*X 3,
    X 0*X 1*X 2*X 3 - 1} : Set (MvPolynomial (Fin 4) ℚ))).radical := by
    radical_membership

--cyclic-5
set_option trace.profiler true in
set_option maxHeartbeats 200000000 in
set_option synthInstance.maxSize 2000000 in
example :
  (X 0 + X 1 + X 2 + X 3 + X 4) ∈ (Ideal.span ({X 0 + X 1 + X 2 + X 3 + X 4,
    X 0*X 1 + X 0*X 2 + X 0*X 3 + X 0*X 4 + X 1*X 2 + X 1*X 3 + X 1*X 4 + X 2*X 3 + X 2*X 4 + X 3*X 4,
    X 0*X 1*X 2 + X 0*X 1*X 3 + X 0*X 1*X 4 + X 0*X 2*X 3 + X 0*X 2*X 4 + X 0*X 3*X 4 +
    X 1*X 2*X 3 + X 1*X 2*X 4 + X 1*X 3*X 4 + X 2*X 3*X 4,
    X 0*X 1*X 2*X 3 + X 0*X 1*X 2*X 4 + X 0*X 1*X 3*X 4 + X 0*X 2*X 3*X 4 +
    X 1*X 2*X 3*X 4,
    X 0*X 1*X 2*X 3*X 4 - 1} : Set (MvPolynomial (Fin 5) ℚ))).radical := by
    radical_membership


-- example : x1^2 + 3*x1*x4 + 2*x3^6*x4 + 6*x3^5*x4^2 + x3^4*x4^3 - 2*x3^3*x4^4 + x3^2 -
--   (566/275)*x3*x4^11 - (6273/25)*x3*x4^6 + (69019/275)*x3*x4 -
--   (1467/275)*x4^12 - (16271/25)*x4^7 + (179073/275)*x4^2 = 0 := by grind

-- set_option maxHeartbeats 200000000 in
-- set_option synthInstance.maxSize 2000000 in
-- -- set_option trace.profiler true in
-- example :
--   (X 1^2 + C 3 * X 1 * X 4 + C 2 * X 3^6 * X 4 + C 6 * X 3^5 * X 4^2 + X 3^4 * X 4^3 - C 2 * X 3^3 * X 4^4 + X 3^2 -
--   C (566/275 : ℚ) * X 3 * X 4^11 - C (6273/25 : ℚ) * X 3 * X 4^6 + C (69019/275 : ℚ) * X 3 * X 4 -
--   C (1467/275 : ℚ) * X 4^12 - C (16271/25 : ℚ) * X 4^7 + C (179073/275 : ℚ) * X 4^2)
--   ∈ (Ideal.span ({X 0 + X 1 + X 2 + X 3 + X 4,
--     X 0*X 1 + X 0*X 2 + X 0*X 3 + X 0*X 4 + X 1*X 2 + X 1*X 3 + X 1*X 4 + X 2*X 3 + X 2*X 4 + X 3*X 4,
--     X 0*X 1*X 2 + X 0*X 1*X 3 + X 0*X 1*X 4 + X 0*X 2*X 3 + X 0*X 2*X 4 + X 0*X 3*X 4 +
--     X 1*X 2*X 3 + X 1*X 2*X 4 + X 1*X 3*X 4 + X 2*X 3*X 4,
--     X 0*X 1*X 2*X 3 + X 0*X 1*X 2*X 4 + X 0*X 1*X 3*X 4 + X 0*X 2*X 3*X 4 +
--     X 1*X 2*X 3*X 4,
--     X 0*X 1*X 2*X 3*X 4 - 1} : Set (MvPolynomial (Fin 5) ℚ))).radical := by
--     radical_membership
--     -- radical_membership
