import Groebner.Basic
import Groebner.List

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

import GroebnerTac.Tactic

open MvPolynomial MonomialOrder

-- set_option maxRecDepth 5000000

-- set_option maxHeartbeats 5000000 in
-- example :
--   letI inputs := ({
--     X 0 ^ 2 + X 1 ^ 2 - C 1,
--     X 2 ^ 2 + X 3 ^ 2 - C 1,
--     X 4 * X 1 ^ 3 + X 5 * X 3 ^ 3 - C (6/5 : ℚ),
--     X 4 * X 0 ^ 3 + X 5 * X 2 ^ 3 - C (6/5 : ℚ),
--     X 4 * X 1 ^ 2 * X 0 + X 5 * X 3 ^ 2 * X 2 - C (7/10 : ℚ),
--     X 4 * X 1 * X 0 ^ 2 + X 5 * X 3 * X 2 ^ 2 - C (7/10 : ℚ)
--   } : Set <| MvPolynomial (Fin 6) ℚ)

--   ∃ (G : Set <| MvPolynomial (Fin 6) ℚ),
--   lex.IsGroebnerBasis G (Ideal.span inputs) := by
--   set_option synthInstance.maxSize 1024 in add_gb_hyp h ({
--     X 0 ^ 2 + X 1 ^ 2 - C 1,
--     X 2 ^ 2 + X 3 ^ 2 - C 1,
--     X 4 * X 1 ^ 3 + X 5 * X 3 ^ 3 - C (6/5 : ℚ),
--     X 4 * X 0 ^ 3 + X 5 * X 2 ^ 3 - C (6/5 : ℚ),
--     X 4 * X 1 ^ 2 * X 0 + X 5 * X 3 ^ 2 * X 2 - C (7/10 : ℚ),
--     X 4 * X 1 * X 0 ^ 2 + X 5 * X 3 * X 2 ^ 2 - C (7/10 : ℚ)
--   } : Set <| MvPolynomial (Fin 6) ℚ)

--   exact
--     Exists.intro _ h
