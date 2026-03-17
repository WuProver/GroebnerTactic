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


variable {σ : Type*} (m : MonomialOrder σ)

/-The test example that verify mvpolynomial `f` is a remainder with respect to a set `G`-/
example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
  gb_solve

example :
    lex.IsRemainder (X 0 ^ 2 - X 1 : MvPolynomial (Fin 3) ℚ)
      {X 0 ^ 2 - X 1} 0 := by
  gb_solve

example :
    lex.IsRemainder (X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) ℚ)
      {X 0 * X 1 - 1} (X 0 + X 1) := by
  gb_solve

example :
    lex.IsRemainder (X 0 * X 1 : MvPolynomial (Fin 3) ℚ)
      {2 * X 0 - X 1}
      (C (1/2 : ℚ) * X 1 ^ 2) := by
  gb_solve

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
  gb_solve

example :
    lex.IsRemainder (C (2/3 : ℚ) * X 0 * X 1 : MvPolynomial (Fin 3) ℚ)
      {3 * X 0 + 1}
      (- C (2/9 : ℚ) * X 1) := by
  gb_solve

example :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 3) ℚ)
      {X 0 + C (1/2 : ℚ) * X 1}
      (C (5/4 : ℚ) * X 1 ^ 2) := by
  gb_solve

/-The test example that verify a set is groebner basis-/
example :
    letI basis := ({X 0 + X 1 ^ 2, X 1 ^ 2} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by

    gb_solve

example :
    letI basis := ({X 0 ^ 4 - X 1} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    gb_solve

example :
    letI basis := ({X 0} : Set <| MvPolynomial (Fin 3) ℚ)
    lex.IsGroebnerBasis basis (Ideal.span basis) := by
    gb_solve

example :
  lex.IsGroebnerBasis
  ({X 0 - 1, X 1^2} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0^2 + X 1^2 - 1, X 0 - 1} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  gb_solve

example :
  lex.IsGroebnerBasis
  ({1} : Set <| MvPolynomial (Fin 3) ℚ)
  (Ideal.span ({X 0, 1 - X 0} : Set <| MvPolynomial (Fin 3) ℚ)) := by
  gb_solve

example :
  lex.IsGroebnerBasis
  ({X 0 ^ 2 - 1} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0 ^ 2 - 1, (X 0 ^ 2 - 1) * (X 1 + 1)} :
    Set <| MvPolynomial (Fin 2) ℚ)) := by
  gb_solve

example :
  lex.IsGroebnerBasis
  ({X 0 - C (1/2 : ℚ)} : Set <| MvPolynomial (Fin 1) ℚ)
  (Ideal.span ({2 * X 0 - 1} : Set <| MvPolynomial (Fin 1) ℚ)) := by
  gb_solve

example :
  lex.IsGroebnerBasis
  ({X 1 + 6} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({C (2/3 : ℚ) * X 1 + 4} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  gb_solve

-- set_option maxHeartbeats 2000000 in
-- example :
--   lex.IsGroebnerBasis
--   ({X 1^3 - X 2^2, X 0^2 - X 1, X 0*X 1 - X 2, X 0*X 2 - X 1^2} :
--     Set <| MvPolynomial (Fin 3) ℚ)
--   (Ideal.span ({X 0^2 - X 1, X 0^3 - X 2} :
--     Set <| MvPolynomial (Fin 3) ℚ)):= by
--     gb_solve

/-The test example that verify ideal membership problem-/
example :
  X 0 ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) ℚ)) := by
  gb_solve

example :
   X 2 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
  gb_solve

example :
   X 1 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
  gb_solve

example :
   X 0 + X 1 ∉ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
  gb_solve

example :
  X 0 + 2 * X 1^2 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
  gb_solve

example :
  X 0 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
  gb_solve

example : 1 ∉ Ideal.span  ({X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ) := by
  gb_solve

example : 1 ∉ Ideal.span  ({X 0 + X 1, 1 - X 0*X 3} : Set <| MvPolynomial (Fin 4) ℚ) := by
  gb_solve

example : 1 ∉ Ideal.span  ({X 1*X 3 + 1, X 0 + X 1} : Set <| MvPolynomial (Fin 4) ℚ) := by
  gb_solve

example : 1 ∈ Ideal.span ({X 0, X 1, 1 - X 3 * X 0} : Set <| MvPolynomial (Fin 4) ℚ) := by
  gb_solve

example :
  X 0 ^ 3 - X 0 ∈ Ideal.span ({X 0 ^ 2 - 1} : Set (MvPolynomial (Fin 1) ℚ)) := by
  gb_solve


/-The test example that verify radical membership problem-/
example :
  X 0 * X 1 ∈ (Ideal.span ({C (1/2 : ℚ) * (X 0 + X 1), C (1/2 : ℚ) * (X 0 - X 1)} :
   Set (MvPolynomial (Fin 2) ℚ))).radical := by
  gb_solve

example :
  C (1/2 : ℚ) * X 0 + C (2/3 : ℚ) * X 1 ∈
    (Ideal.span ({C (1/4 : ℚ) * X 0^2, C (4/9 : ℚ) * X 1^2} :
    Set (MvPolynomial (Fin 2) ℚ))).radical := by
  gb_solve

example :
  C (1/2 : ℚ) * X 0 + C (1/3 : ℚ) * X 1 ∈
  (Ideal.span ({C (1/4 : ℚ) * X 0^2 + C (1/3 : ℚ) * X 0 * X 1 + C (1/9 : ℚ) * X 1^2}
  : Set (MvPolynomial (Fin 2) ℚ))).radical := by
  gb_solve

example :
  X 0 ∈ (Ideal.span ({X 0 + C (3/5 : ℚ) * X 1, C (3/5 : ℚ) * X 1}
  : Set (MvPolynomial (Fin 2) ℚ))).radical := by
  gb_solve

example :
  X 0 * X 1 ∈ (Ideal.span ({C (1/2 : ℚ) * (X 0 + X 1), C (1/2 : ℚ) * (X 0 - X 1)} :
   Set (MvPolynomial (Fin 2) ℚ))).radical := by
  gb_solve

example :
  X 2 ∉ (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical := by
  gb_solve

example :
  X 0 ∉ (Ideal.span ({X 0 + X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical := by
  gb_solve

example :
  (X 0 - X 1) * (X 0 + X 1) ∈
    (Ideal.span ({X 0^2, X 1^2} : Set (MvPolynomial (Fin 2) ℚ))).radical := by
  gb_solve

example :
  C (1/2 : ℚ) * X 0 ∈
    (Ideal.span ({C (1/4 : ℚ) * X 0} : Set (MvPolynomial (Fin 1) ℚ))).radical := by
  gb_solve

example :
  X 0 ∈ (Ideal.span ({X 0 + C (2/3 : ℚ) * X 1, C (1/5 : ℚ) * X 1}
    : Set (MvPolynomial (Fin 2) ℚ))).radical := by
  gb_solve

/- Some examples that compute the GB and provide a hypothesis in cases where the GB is not known -/
example : lex.IsGroebnerBasis ({X 0, X 1} :
 Set (MvPolynomial (Fin 3) ℚ)) (Ideal.span {X 0, X 0 + X 1}) := by
  add_gb_hyp h ({X 0, X 0 + X 1} : Set (MvPolynomial (Fin 3) ℚ))
  simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, C_1, Fin.isValue, pow_one, one_mul,
    zero_add] at h
  exact h

example :
  lex.IsGroebnerBasis
  ({X 0 + X 1, X 1 ^ 2 + 1} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0 + X 1, X 0 * X 1 - 1} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  add_gb_hyp h ({X 0 + X 1, X 0 * X 1 - 1} : Set (MvPolynomial (Fin 2) ℚ))
  simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, C_1, Fin.isValue, pow_one, one_mul,
    zero_add] at h
  exact h

/-Some examples that verify two ideals are equal-/
example :
  Ideal.span ({X 0 + X 1^2, X 1 }) =
    Ideal.span ({X 0, X 1 } : Set (MvPolynomial (Fin 3) ℚ)) := by
   ideal

example :
  Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2}) =
    Ideal.span ({X 0, X 1 ^ 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
    ideal

example :
  Ideal.span ({2 * X 0 - 1} : Set (MvPolynomial (Fin 3) ℚ)) =
  Ideal.span ({X 0 - C (1/2 : ℚ)}) := by
  ideal

example :
  Ideal.span ({C (1/3 : ℚ) * X 0 + C (2/3 : ℚ)} : Set (MvPolynomial (Fin 3) ℚ)) =
  Ideal.span ({X 0 + 2}) := by
  ideal

example :
  Ideal.span ({X 0 ^ 2 - C (1/4 : ℚ), X 0 - C (1/2 : ℚ)} : Set (MvPolynomial (Fin 3) ℚ)) =
  Ideal.span ({X 0 - C (1/2 : ℚ)}) := by
  ideal

example :
  Ideal.span ({C (1/2 : ℚ) * X 0 + C (1/2 : ℚ), C (1/2 : ℚ) * X 0 - C (1/2 : ℚ)} : Set (MvPolynomial (Fin 3) ℚ)) =
  Ideal.span ({1}) := by
  ideal

example :
  Ideal.span ({
    X 0 + X 1 + X 2,
    X 0 * X 1 + X 1 * X 2 + X 2 * X 0,
    X 0 * X 1 * X 2 - 1
  } : Set (MvPolynomial (Fin 3) ℚ)) =
  Ideal.span ({
    X 0 + X 1 + X 2,
    X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2,
    X 0 * X 1 * X 2 - 1
  } : Set (MvPolynomial (Fin 3) ℚ)) := by
  ideal

end
