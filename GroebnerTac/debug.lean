import MonomialOrderedPolynomial.MvPolynomial
import Groebner.Groebner
import Groebner.ToMathlib.List
import GroebnerTac.Tactic

/-!
In this file we show some examples of using our tactic.
-/

section
open MvPolynomial MonomialOrder

example :
  X 0 * X 1 ∈ (Ideal.span ({C (1/2 : ℚ) * (X 0 + X 1), C (1/2 : ℚ) * (X 0 - X 1)} :
   Set (MvPolynomial (Fin 2) ℚ))).radical := by
   gb_solve
