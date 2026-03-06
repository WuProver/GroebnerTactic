import MonomialOrderedPolynomial.MvPolynomial
import Groebner.Groebner
import Groebner.ToMathlib.List
import GroebnerTac.Tactic

/-!
In this file we show some examples of using our tactic.
-/

section
open MvPolynomial MonomialOrder

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

set_option synthInstance.maxSize 100000000

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)

/-The test example that verify mvpolynomial `f` is a remainder with respect to a set `G`-/
example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
  gb_solve

/-The test example that verify a set is groebner basis-/
example :
    letI basis := ({X 0 + X 1 ^ 2, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    gb_solve

/-The test example that verify ideal membership problem-/
example :
  X 0 ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) ℚ)) := by
  gb_solve

example :
   X 2 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
  gb_solve

/-The test example that verify radical membership problem-/
example :
  X 0 * X 1 ∈ (Ideal.span ({C (1/2 : ℚ) * (X 0 + X 1), C (1/2 : ℚ) * (X 0 - X 1)} :
   Set (MvPolynomial (Fin 2) ℚ))).radical := by
  gb_solve

example :
  X 0 ∉ (Ideal.span ({X 0 + X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical := by
  gb_solve
