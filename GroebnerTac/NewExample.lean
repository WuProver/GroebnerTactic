import MonomialOrderedPolynomial
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

/- The test example of basis -/
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


/- The test example of basis'-/
set_option maxHeartbeats 20000000 in
example :
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

-- cyclic-2
example :
  lex.IsGroebnerBasis
  ({X 0 + X 1, X 1 ^ 2 + 1} : Set <| MvPolynomial (Fin 2) ℚ)
  (Ideal.span ({X 0 + X 1, X 0 * X 1 - 1} : Set <| MvPolynomial (Fin 2) ℚ)) := by
  add_gb_hyp h ({X 0 + X 1, X 0 * X 1 - 1} : Set (MvPolynomial (Fin 2) ℚ))
  simp at h
  exact h

-- cyclic-3
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
      Exists.intro _ h

-- cyclic-4
set_option maxHeartbeats 200000000 in
example :
    letI inputs := ({X 0 + X 1 + X 2 + X 3,
                     X 0*X 1 + X 1*X 2 + X 2*X 3 + X 3*X 0,
                     X 0*X 1*X 2 + X 1*X 2*X 3 + X 2*X 3*X 0 + X 3*X 0*X 1,
                     X 0*X 1*X 2*X 3 - 1} : Set <| MvPolynomial (Fin 4) ℚ)
    ∃ (G : Set <| MvPolynomial (Fin 4) ℚ),
    lex.IsGroebnerBasis G (Ideal.span inputs) := by
    set_option synthInstance.maxSize 1024 in add_gb_hyp h ({X 0 + X 1 + X 2 + X 3,
                   X 0*X 1 + X 1*X 2 + X 2*X 3 + X 3*X 0,
                   X 0*X 1*X 2 + X 1*X 2*X 3 + X 2*X 3*X 0 + X 3*X 0*X 1,
                   X 0*X 1*X 2*X 3 - 1} : Set <| MvPolynomial (Fin 4) ℚ)
    exact
      Exists.intro _ h

-- cyclic-5
-- set_option maxHeartbeats 5000000000 in
-- set_option maxRecDepth 500000000 in
-- lemma cyclic5:
--     letI inputs := ({
--       X 0 + X 1 + X 2 + X 3 + X 4,
--       X 0*X 1 + X 1*X 2 + X 2*X 3 + X 3*X 4 + X 4*X 0,
--       X 0*X 1*X 2 + X 1*X 2*X 3 + X 2*X 3*X 4 + X 3*X 4*X 0 + X 4*X 0*X 1,
--       X 0*X 1*X 2*X 3 + X 1*X 2*X 3*X 4 + X 2*X 3*X 4*X 0 + X 3*X 4*X 0*X 1 + X 4*X 0*X 1*X 2,
--       X 0*X 1*X 2*X 3*X 4 - 1
--     } : Set <| MvPolynomial (Fin 5) ℚ)
--     ∃ (G : Set <| MvPolynomial (Fin 5) ℚ),
--     lex.IsGroebnerBasis G (Ideal.span inputs) := by
--     set_option synthInstance.maxSize 1024 in add_gb_hyp h ({
--       X 0 + X 1 + X 2 + X 3 + X 4,
--       X 0*X 1 + X 1*X 2 + X 2*X 3 + X 3*X 4 + X 4*X 0,
--       X 0*X 1*X 2 + X 1*X 2*X 3 + X 2*X 3*X 4 + X 3*X 4*X 0 + X 4*X 0*X 1,
--       X 0*X 1*X 2*X 3 + X 1*X 2*X 3*X 4 + X 2*X 3*X 4*X 0 + X 3*X 4*X 0*X 1 + X 4*X 0*X 1*X 2,
--       X 0*X 1*X 2*X 3*X 4 - 1
--     } : Set <| MvPolynomial (Fin 5) ℚ)
--     exact
--       Exists.intro _ h

-- #print axioms cyclic5

example :
  letI inputs := ({X 0 - C (2/3 : ℚ), X 1 + C (4/5 : ℚ)}: Set <| MvPolynomial (Fin 2) ℚ)
    ∃ (G : Set <| MvPolynomial (Fin 2) ℚ),
    lex.IsGroebnerBasis G (Ideal.span inputs) := by
    add_gb_hyp h ({X 0 - C (2/3 : ℚ), X 1 + C (4/5 : ℚ)} : Set <| MvPolynomial (Fin 2) ℚ)
    exact
      Exists.intro
        {0 + C (1 / 1) * X 0 ^ 1 + C (-2 / 3), 0 + C (1 / 1) * X 1 ^ 1 + C (4 / 5)} h

-- Katsura-1
example :
    letI inputs := ({
      X 0 + 2 * X 1 - 1,
      X 0^2 - X 0 + 2 * X 1^ 2
    } : Set <| MvPolynomial (Fin 2) ℚ)
    ∃ (G : Set <| MvPolynomial (Fin 2) ℚ),
    lex.IsGroebnerBasis G (Ideal.span inputs) := by

    set_option synthInstance.maxSize 1024 in add_gb_hyp h ({
      X 0 + 2 * X 1 - 1,
      X 0^2 - X 0 + 2 * X 1^ 2
    } : Set <| MvPolynomial (Fin 2) ℚ)
    exact
      Exists.intro _ h



-- Katsura-2
set_option maxHeartbeats 2000000 in
example :
    letI inputs := ({
      X 0 + 2 * X 1 + 2 * X 2 - 1,
      X 0^2 + 2 * X 1^2 + 2 * X 2^2 - X 0,
      2 * X 0 * X 1 + 2 * X 1 * X 2 - X 1
    } : Set <| MvPolynomial (Fin 3) ℚ)
    ∃ (G : Set <| MvPolynomial (Fin 3) ℚ),
    lex.IsGroebnerBasis G (Ideal.span inputs) := by

    set_option synthInstance.maxSize 1024 in add_gb_hyp h ({
      X 0 + 2 * X 1 + 2 * X 2 - 1,
      X 0^2 + 2 * X 1^2 + 2 * X 2^2 - X 0,
      2 * X 0 * X 1 + 2 * X 1 * X 2 - X 1
    } : Set <| MvPolynomial (Fin 3) ℚ)
    exact
      Exists.intro _ h

-- Katsura-3
set_option maxHeartbeats 2000000 in
example :
    letI inputs := ({
      X 0 + 2 * X 1 + 2 * X 2 + 2 * X 3 - 1,
      X 0^2 - X 0 + 2 * X 1^2 + 2 * X 2^2 + 2* X 3^2,
      2 * X 0 * X 1 + 2 * X 1 * X 2 - X 1 + 2 * X 2 * X 3,
      2*X 0*X 2 + X 1^2 + 2*X 1*X 3 - X 2
    } : Set <| MvPolynomial (Fin 3) ℚ)
    ∃ (G : Set <| MvPolynomial (Fin 3) ℚ),
    lex.IsGroebnerBasis G (Ideal.span inputs) := by

    set_option synthInstance.maxSize 1024 in add_gb_hyp h ({
      X 0 + 2 * X 1 + 2 * X 2 + 2 * X 3 - 1,
      X 0^2 - X 0 + 2 * X 1^2 + 2 * X 2^2 + 2* X 3^2,
      2 * X 0 * X 1 + 2 * X 1 * X 2 - X 1 + 2 * X 2 * X 3,
      2*X 0*X 2 + X 1^2 + 2*X 1*X 3 - X 2
    } : Set <| MvPolynomial (Fin 3) ℚ)
    exact
      Exists.intro _ h

-- Katsura-4
set_option maxHeartbeats 5000000 in
example :
    letI inputs := ({
      X 0 + 2 * X 1 + 2 * X 2 + 2 * X 3 + 2 * X 4 - 1,
      X 0^2 - X 0 + 2 * X 1^2 + 2 * X 2^2 + 2 * X 3^2 + 2 * X 4^2,
      2 * X 0 * X 1 + 2 * X 1 * X 2 - X 1 + 2 * X 2 * X 3 + 2 * X 3 * X 4,
      2 * X 0 * X 2 + X 1^2 + 2 * X 1 * X 3 + 2 * X 2 * X 4 - X 2,
      2 * X 0 * X 3 + 2 * X 1 * X 2 + 2 * X 1 * X 4 - X 3
    } : Set <| MvPolynomial (Fin 5) ℚ)
    ∃ (G : Set <| MvPolynomial (Fin 5) ℚ),
    lex.IsGroebnerBasis G (Ideal.span inputs) := by

    set_option synthInstance.maxSize 1024 in add_gb_hyp h ({
      X 0 + 2 * X 1 + 2 * X 2 + 2 * X 3 + 2 * X 4 - 1,
      X 0^2 - X 0 + 2 * X 1^2 + 2 * X 2^2 + 2 * X 3^2 + 2 * X 4^2,
      2 * X 0 * X 1 + 2 * X 1 * X 2 - X 1 + 2 * X 2 * X 3 + 2 * X 3 * X 4,
      2 * X 0 * X 2 + X 1^2 + 2 * X 1 * X 3 + 2 * X 2 * X 4 - X 2,
      2 * X 0 * X 3 + 2 * X 1 * X 2 + 2 * X 1 * X 4 - X 3
    } : Set <| MvPolynomial (Fin 5) ℚ)

    exact
      Exists.intro _ h

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
