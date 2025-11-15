-- import Mathlib

-- set_option trace.grind.simp true
-- set_option trace.grind.ring.simp true
-- set_option trace.grind.debug.ring.simp true
-- set_option trace.grind.debug.ring.basis true
-- set_option trace.grind.debug.ring.simpBasis true
-- set_option trace.grind.debug.ring.rabinowitsch true
-- set_option trace.grind.ring.superpose true

-- example (x : ℝ) :
--     x^4 - 6*x^2 + 12*x - 8 = 0 → 2*x^3 - 10*x^2 + 16*x - 8 = 0 →
--     x^2 - 4*x + 4 = 0 := by
--   grobner

-- -- theorem exm1 (x y : ℝ)
-- --     (ha : x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 = 0) :
-- --     x ^ 2 + 2 * x * y + y ^ 2 = 0 := by
-- --   grobner

-- theorem exm2 (x y : ℝ)
--     (ha : x ^ 2 + y ^ 2 = 0) : x = 0 := by
--    sorry

-- example : ∃ (x : ℕ ), x + 1 = 2 := by
--   use 1

import Mathlib

example (x y : ℝ) : x^2 + y^2 = 0 → x = 0 := by
  intro h
  
