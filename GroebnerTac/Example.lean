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


example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
      remainder[0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2, 0 + C ↑(↑1 / ↑1) * X 2 ^ 3,
        0 + C ↑(↑1 / ↑1) * X 3 ^ 4]
  -- -- remainder?
  --  remainder[X 0, X 1^2, X 2^3,X 3^4]

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
    remainder [X 0, X 1^2, X 2^3, X 3^4]

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
    remainder

example :
    lex.IsRemainder (X 0 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
    remainder

example :
    lex.IsRemainder (X 0 + X 1 ^ 3 + X 2 ^ 4 : MvPolynomial (Fin 3) ℚ)
      {X 0, X 1, X 2} 0 := by
    remainder

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
    remainder

example :
    lex.IsRemainder (1: MvPolynomial (Fin 3) ℚ)
      {X 0, X 1, 2 - X 3} (1) := by
    remainder
      -- sorry

example :
    letI basis := ({X 0 + X 1 ^ 2, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    basis

example :
    letI basis := ({X 0 ^ 4 - X 1} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis

example :
  Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) =
    Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
   ideal


example :
  Ideal.span ({X 0 + X 1^2, X 1 }) =
    Ideal.span ({X 0, X 1 } : Set (MvPolynomial (Fin 3) ℚ)) := by
   ideal



end
