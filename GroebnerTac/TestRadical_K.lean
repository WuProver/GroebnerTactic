import Mathlib


import MonomialOrderedPolynomial
import Groebner.Groebner
import Groebner.ToMathlib.List

import GroebnerTac.Tactic

section
open MvPolynomial MonomialOrder Ideal

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]

--kasura-1
-- polys : [x0 + 2*x1 - 1, x0^2 - x0 + 2*x1^2]
-- gb : [x0 + 2*x1 - 1, x1^2 - 1/3*x1]
set_option trace.profiler true in
example :
  (X 1^2 - C (1/3 : ℚ) * X 1) ∈ (Ideal.span ({X 0 + C 2 * X 1 - C 1,
    X 0^2 - X 0 + C 2 * X 1^2} : Set (MvPolynomial (Fin 2) ℚ))).radical := by
    radical_membership

set_option trace.profiler true in
example :
  (X 0 + C 2 * X 1 - C 1) ∈ (Ideal.span ({X 0 + C 2 * X 1 - C 1,
    X 0^2 - X 0 + C 2 * X 1^2} : Set (MvPolynomial (Fin 2) ℚ))).radical := by
    radical_membership
