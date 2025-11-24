import Mathlib

theorem ex (x y : ℝ)
    (h₁ : x * y ^ 2 + 2 * y^2 = 0) (h₂: x^4 -2 * x^2 +1 = 0):
    y - x ^ 2 + 1 = 0 := by
  grind
