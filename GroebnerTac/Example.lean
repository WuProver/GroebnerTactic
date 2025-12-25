import Groebner.Basic
import Groebner.List

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

import GroebnerTac.Tactic

/-!
In this file we show some examples of using our tactic.
-/

section
open MvPolynomial MonomialOrder

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)

/- The test example of `remainder` -/
example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
      remainder[0 + C ↑(↑1 / ↑1) * X 0 ^ 1, 0 + C ↑(↑1 / ↑1) * X 1 ^ 2, 0 + C ↑(↑1 / ↑1) * X 2 ^ 3,
        0 + C ↑(↑1 / ↑1) * X 3 ^ 4]

example :
    lex.IsRemainder (X 0 ^ 2 - X 1 : MvPolynomial (Fin 3) ℚ)
      {X 0 ^ 2 - X 1} 0 := by
    remainder

example :
    lex.IsRemainder (X 0 ^ 5 + X 1 * X 2 + 100 : MvPolynomial (Fin 3) ℚ)
      {1} 0 := by
    remainder


example :
    lex.IsRemainder (X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) ℚ)
      {X 0 * X 1 - 1} (X 0 + X 1) := by
    remainder


example :
    lex.IsRemainder (X 0 : MvPolynomial (Fin 3) ℚ)
      {2 * X 0 - 1} (C (1/2 : ℚ)) := by
    remainder


example :
    lex.IsRemainder (X 0 * X 1 : MvPolynomial (Fin 3) ℚ)
      {2 * X 0 - X 1}
      (C (1/2 : ℚ) * X 1 ^ 2) := by
    remainder


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


example :
    lex.IsRemainder (C (2/3 : ℚ) * X 0 * X 1 : MvPolynomial (Fin 3) ℚ)
      {3 * X 0 + 1}
      (- C (2/9 : ℚ) * X 1) := by
    remainder


example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 3) ℚ)
      {X 0 + C (1/2 : ℚ) * X 1}
      (C (5/4 : ℚ) * X 1 ^ 2) := by
    remainder


/- The test example of basis -/
example :
    letI basis := ({X 0 + X 1 ^ 2, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    basis

example :
    letI basis := ({X 0 ^ 4 - X 1} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
      basis

example :
    letI basis := ({X 0} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    basis


/- The test example of basis'-/
set_option maxHeartbeats 20000000 in
example:
  lex.IsGroebnerBasis
  ({X 1^3 - X 2^2, X 0^2 - X 1, X 0*X 1 - X 2, X 0*X 2 - X 1^2} :
    Set <| MvPolynomial (Fin 3) ℚ)
  (Ideal.span ({X 0^2 - X 1, X 0^3 - X 2} :
    Set <| MvPolynomial (Fin 3) ℚ)):= by
    basis'


example :
  lex.IsGroebnerBasis
  ({X 0 - 1, X 1^2} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0^2 + X 1^2 - 1, X 0 - 1} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  basis'

example :
  lex.IsGroebnerBasis
  ({1} : Set <| MvPolynomial (Fin 3) ℚ)
  (Ideal.span ({X 0, 1 - X 0} : Set <| MvPolynomial (Fin 3) ℚ)) := by
  basis'

example :
  lex.IsGroebnerBasis
  ({X 0 ^ 2 - 1} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0 ^ 2 - 1, (X 0 ^ 2 - 1) * (X 1 + 1)} :
    Set <| MvPolynomial (Fin 2) ℚ)) := by
    basis'

set_option maxHeartbeats 20000000 in
example :
  lex.IsGroebnerBasis
  ({X 0 - X 3, X 1 - X 3, X 2 - X 3} : Set <| MvPolynomial (Fin 4) ℚ)
  (Ideal.span ({X 0 - X 1, X 1 - X 2, X 2 - X 3} :
    Set <| MvPolynomial (Fin 4) ℚ)) := by
    basis'

example :
  lex.IsGroebnerBasis
  ({X 0 - C (1/2 : ℚ)} : Set <| MvPolynomial (Fin 1) ℚ)
  (Ideal.span ({2 * X 0 - 1} : Set <| MvPolynomial (Fin 1) ℚ)) := by
  basis'

example :
  lex.IsGroebnerBasis
  ({X 1 + 6} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({C (2/3 : ℚ) * X 1 + 4} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  basis'


example : lex.IsGroebnerBasis ({X 0, X 1} :
 Set (MvPolynomial (Fin 3) ℚ)) (Ideal.span {X 0, X 0 + X 1}) := by
  add_gb_hyp h ({X 0, X 0 + X 1} : Set (MvPolynomial (Fin 3) ℚ))
  simp at h
  exact h


example :
  lex.IsGroebnerBasis
  ({X 0 + X 1, X 1 ^ 2 + 1} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0 + X 1, X 0 * X 1 - 1} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  add_gb_hyp h ({X 0 + X 1, X 0 * X 1 - 1} : Set (MvPolynomial (Fin 2) ℚ))
  simp at h
  exact h

set_option maxHeartbeats 20000000 in
example :
    letI inputs := ({X 0 + X 1 + X 2,
                     X 0 * X 1 + X 1 * X 2 + X 2 * X 0,
                     X 0 * X 1 * X 2 - 1} : Set <| MvPolynomial (Fin 3) ℚ)
    ∃ (G : Set <| MvPolynomial (Fin 3) ℚ),
    lex.IsGroebnerBasis G (Ideal.span inputs) := by
    add_gb_hyp h ({X 0 + X 1 + X 2,
                     X 0 * X 1 + X 1 * X 2 + X 2 * X 0,
                     X 0 * X 1 * X 2 - 1} : Set <| MvPolynomial (Fin 3) ℚ)
    exact
      Exists.intro
        {0 + C (1 / 1) * X 0 ^ 1 + C (1 / 1) * X 1 ^ 1 + C (1 / 1) * X 2 ^ 1,
          0 + C (1 / 1) * X 1 ^ 2 + C (1 / 1) * X 1 ^ 1 * X 2 ^ 1 + C (1 / 1) * X 2 ^ 2,
          0 + C (1 / 1) * X 2 ^ 3 + C (-1 / 1)}
        h

example :
  letI inputs := ({X 0 - C (2/3 : ℚ), X 1 + C (4/5 : ℚ)}: Set <| MvPolynomial (Fin 2) ℚ)
    ∃ (G : Set <| MvPolynomial (Fin 2) ℚ),
    lex.IsGroebnerBasis G (Ideal.span inputs) := by
    add_gb_hyp h ({X 0 - C (2/3 : ℚ), X 1 + C (4/5 : ℚ)} : Set <| MvPolynomial (Fin 2) ℚ)
    exact
      Exists.intro
        {0 + C (1 / 1) * X 0 ^ 1 + C (-2 / 3), 0 + C (1 / 1) * X 1 ^ 1 + C (4 / 5)} h

/-! a failed example-/
-- set_option maxHeartbeats 20000000 in
-- example :
--     letI inputs := ({
--         X 0 + 2 * X 1 + 2 * X 2 - 1,
--         X 0 ^ 2 + 2 * X 1 ^ 2 + 2 * X 2 ^ 2 - X 0,
--         2 * X 0 * X 1 + 2 * X 1 * X 2 - X 1
--       } : Set <| MvPolynomial (Fin 3) ℚ)
--     ∃ (G : Set <| MvPolynomial (Fin 3) ℚ),
--     lex.IsGroebnerBasis G (Ideal.span inputs) := by
--     add_gb_hyp h ({
--         X 0 + 2 * X 1 + 2 * X 2 - 1,
--         X 0 ^ 2 + 2 * X 1 ^ 2 + 2 * X 2 ^ 2 - X 0,
--         2 * X 0 * X 1 + 2 * X 1 * X 2 - X 1
--       } : Set <| MvPolynomial (Fin 3) ℚ)
--     exact Exists.intro _ h

x


end
