import Mathlib

set_option trace.grind.simp true
set_option trace.grind.ring.simp true
set_option trace.grind.debug.ring.simp true
set_option trace.grind.debug.ring.basis true
set_option trace.grind.debug.ring.simpBasis true
set_option trace.grind.debug.ring.rabinowitsch true
set_option trace.grind.ring.superpose true

/- Here we test cyclic-n -/

--cyclic-1
set_option trace.profiler true in
example (x0 : Nat) (h : x0 - 1 = 0) : x0 - 1 = 0 := by
  grind

set_option trace.profiler true in
example (x0 : ℕ) (h : x0 - 1 = 0) : x0 - 1 = 0 := by
  grind

set_option trace.profiler true in
example (x0 : ℝ) (h : x0 - 1 = 0) : x0 - 1 = 0 := by
  grind


--cyclic-2
--polys: [x0 + x1, x0*x1 - 1]
--gb: [x0 + x1, x1^2 + 1]
--involve ℂ ▸ can't colve
set_option trace.profiler true in
example (x0 x1 : ℝ) (h₁ : x0 + x1 = 0) (h₂ : x0*x1 - 1 = 0)  : x1^2 + 1= 0 := by
  grind

set_option trace.profiler true in
example (x0 x1 : ℕ) (h₁ : x0 + x1 = 0) (h₂ : x0*x1 - 1 = 0)  : x0 + x1 = 0 := by
  grind

set_option trace.profiler true in
example (x0 x1 : Nat) (h₁ : x0 + x1 = 0) (h₂ : x0*x1 - 1 = 0)  : x0 + x1 = 0 := by
  grind

--cyclic-3
--polys: [x0 + x1 + x2, x0*x1 + x0*x2 + x1*x2, x0*x1*x2 - 1]
--gb: [x0 + x1 + x2, x1^2 + x1*x2 + x2^2, x2^3 - 1]
set_option trace.profiler true in
example (x0 x1 x2 : ℕ) (h₁ : x0 + x1 + x2 = 0) (h₂ : x0*x1 + x0*x2 + x1*x2 = 0)
  (h₃ : x0*x1*x2 - 1=0) : x0 + x1 + x2 = 0 := by
  grind

set_option trace.profiler true in
example (x0 x1 x2 : ℕ) (h₁ : x0 + x1 + x2 = 0) (h₂ : x0*x1 + x0*x2 + x1*x2 = 0)
  (h₃ : x0*x1*x2 - 1=0) : x1^2 + x1*x2 + x2^2 = 0 := by
  grind

set_option trace.profiler true in
example (x0 x1 x2 : ℕ) (h₁ : x0 + x1 + x2 = 0) (h₂ : x0*x1 + x0*x2 + x1*x2 = 0)
  (h₃ : x0*x1*x2 - 1=0) : x2^3 - 1 = 0 := by
  grind

--cyclic-4
--polys: [x0 + x1 + x2 + x3, x0*x1 + x0*x3 + x1*x2 + x2*x3, x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3, x0*x1*x2*x3 - 1]
--gb: [x0 + x1 + x2 + x3, x1^2 + 2*x1*x3 + x3^2, x1*x2 - x1*x3 + x2^2*x3^4 + x2*x3 - 2*x3^2, x1*x3^4 - x1 + x3^5 - x3, x2^3*x3^2 + x2^2*x3^3 - x2 - x3, x2^2*x3^6 - x2^2*x3^2 - x3^4 + 1]
set_option trace.profiler true in
example (x0 x1 x2 x3: ℕ) (h₁ : x0 + x1 + x2 + x3 = 0)
  (h₂ : x0*x1 + x0*x3 + x1*x2 + x2*x3 = 0)
  (h₃ : x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3=0)
  (h₄ : x0*x1*x2*x3 - 1 = 0) : x0 + x1 + x2 + x3 = 0 := by
  grind

set_option trace.profiler true in
example (x0 x1 x2 x3: ℕ) (h₁ : x0 + x1 + x2 + x3 = 0)
  (h₂ : x0*x1 + x0*x3 + x1*x2 + x2*x3 = 0)
  (h₃ : x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3=0)
  (h₄ : x0*x1*x2*x3 - 1 = 0) : x1^2 + 2*x1*x3 + x3^2 = 0 := by
  grind

set_option trace.profiler true in
example (x0 x1 x2 x3: ℕ) (h₁ : x0 + x1 + x2 + x3 = 0)
  (h₂ : x0*x1 + x0*x3 + x1*x2 + x2*x3 = 0)
  (h₃ : x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3=0)
  (h₄ : x0*x1*x2*x3 - 1 = 0) : x1*x2 - x1*x3 + x2^2*x3^4 + x2*x3 - 2*x3^2 = 0 := by
  grind

set_option trace.profiler true in
example (x0 x1 x2 x3: ℕ) (h₁ : x0 + x1 + x2 + x3 = 0)
  (h₂ : x0*x1 + x0*x3 + x1*x2 + x2*x3 = 0)
  (h₃ : x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3=0)
  (h₄ : x0*x1*x2*x3 - 1 = 0) : x1*x3^4 - x1 + x3^5 - x3 = 0 := by
  grind

set_option trace.profiler true in
example (x0 x1 x2 x3: ℕ) (h₁ : x0 + x1 + x2 + x3 = 0)
  (h₂ : x0*x1 + x0*x3 + x1*x2 + x2*x3 = 0)
  (h₃ : x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3=0)
  (h₄ : x0*x1*x2*x3 - 1 = 0) : x2^3*x3^2 + x2^2*x3^3 - x2 - x3 = 0:= by
  grind

set_option trace.profiler true in
example (x0 x1 x2 x3: ℝ) (h₁ : x0 + x1 + x2 + x3 = 0)
  (h₂ : x0*x1 + x0*x3 + x1*x2 + x2*x3 = 0)
  (h₃ : x0*x1*x2 + x0*x1*x3 + x0*x2*x3 + x1*x2*x3=0)
  (h₄ : x0*x1*x2*x3 - 1 = 0) : x2^2*x3^6 - x2^2*x3^2 - x3^4 + 1 = 0:= by
  grind

--cyclic-5
--polys: [x0 + x1 + x2 + x3 + x4, x0*x1 + x0*x4 + x1*x2 + x2*x3 + x3*x4, x0*x1*x2 + x0*x1*x4 + x0*x3*x4 + x1*x2*x3 + x2*x3*x4, x0*x1*x2*x3 + x0*x1*x2*x4 + x0*x1*x3*x4 + x0*x2*x3*x4 + x1*x2*x3*x4, x0*x1*x2*x3*x4 - 1]
--gb: [x0 + x1 + x2 + x3 + x4, x1^2 + 3*x1*x4 + 2*x3^6*x4 + 6*x3^5*x4^2 + x3^4*x4^3 - 2*x3^3*x4^4 + x3^2 - 566/275*x3*x4^11 - 6273/25*x3*x4^6 + 69019/275*x3*x4 - 1467/275*x4^12 - 16271/25*x4^7 + 179073/275*x4^2, x1*x2 - x1*x4 + x2^2 + 2*x2*x4 - 6/5*x3^6*x4 - 19/5*x3^5*x4^2 - x3^4*x4^3 + x3^3*x4^4 - 2*x3^2 + 334/275*x3*x4^11 + 3702/25*x3*x4^6 - 40726/275*x3*x4 + 867/275*x4^12 + 9616/25*x4^7 - 105873/275*x4^2,x1*x3 - x1*x4 - 2/5*x3^6*x4 - 8/5*x3^5*x4^2 - x3^4*x4^3 + x3^3*x4^4 + 124/275*x3*x4^11 + 1372/25*x3*x4^6 - 15106/275*x3*x4 + 346/275*x4^12 + 3838/25*x4^7 - 42124/275*x4^2, x1*x4^5 - x1 + 1/55*x4^11 + 13/5*x4^6 - 144/55*x4, x2^3 + 2*x2^2*x4 - 2*x2*x4^2 + x3^6*x4^2 + 2*x3^5*x4^3 - 2*x3^4*x4^4 + 2*x3^2*x4 - 232/275*x3*x4^12 - 2576/25*x3*x4^7 + 28018/275*x3*x4^2 - 568/275*x4^13 - 6299/25*x4^8 + 69307/275*x4^3, x2*x3 - x2*x4 + 8/5*x3^6*x4 + 22/5*x3^5*x4^2 - x3^3*x4^4 + x3^2 - 442/275*x3*x4^11 - 4901/25*x3*x4^6 + 53913/275*x3*x4 - 1121/275*x4^12 - 12433/25*x4^7 + 136674/275*x4^2, x2*x4^5 - x2 + 1/55*x4^11 + 13/5*x4^6 - 144/55*x4, x3^7 + 3*x3^6*x4 + x3^5*x4^2 - x3^2 - 398/55*x3*x4^11 - 4414/5*x3*x4^6 + 48787/55*x3*x4 - 1042/55*x4^12 - 11556/5*x4^7 + 128103/55*x4^2, x3^2*x4^5 - x3^2 - 2/55*x3*x4^11 - 21/5*x3*x4^6 + 233/55*x3*x4 - 8/55*x4^12 - 89/5*x4^7 + 987/55*x4^2,x4^15 + 122*x4^10 - 122*x4^5 - 1]

variable (x0 x1 x2 x3 x4 : ℂ)
variable (h1 : x0 + x1 + x2 + x3 + x4 = 0)
variable (h2 : x0*x1 + x0*x4 + x1*x2 + x2*x3 + x3*x4 = 0)
variable (h3 : x0*x1*x2 + x0*x1*x4 + x0*x3*x4 + x1*x2*x3 + x2*x3*x4 = 0)
variable (h4 : x0*x1*x2*x3 + x0*x1*x2*x4 + x0*x1*x3*x4 + x0*x2*x3*x4 + x1*x2*x3*x4 = 0)
variable (h5 : x0*x1*x2*x3*x4 - 1 = 0)

set_option trace.profiler true in
example : x0 + x1 + x2 + x3 + x4 = 0 := by grind

-- example : x1^2 + 3*x1*x4 + 2*x3^6*x4 + 6*x3^5*x4^2 + x3^4*x4^3 - 2*x3^3*x4^4 + x3^2 -
--   (566/275)*x3*x4^11 - (6273/25)*x3*x4^6 + (69019/275)*x3*x4 -
--   (1467/275)*x4^12 - (16271/25)*x4^7 + (179073/275)*x4^2 = 0 := by grind

-- example : x1*x2 - x1*x4 + x2^2 + 2*x2*x4 - (6/5)*x3^6*x4 - (19/5)*x3^5*x4^2 -
--   x3^4*x4^3 + x3^3*x4^4 - 2*x3^2 + (334/275)*x3*x4^11 + (3702/25)*x3*x4^6 -
--   (40726/275)*x3*x4 + (867/275)*x4^12 + (9616/25)*x4^7 - (105873/275)*x4^2 = 0 := by grind

-- example : x1*x3 - x1*x4 - (2/5)*x3^6*x4 - (8/5)*x3^5*x4^2 - x3^4*x4^3 + x3^3*x4^4 +
--   (124/275)*x3*x4^11 + (1372/25)*x3*x4^6 - (15106/275)*x3*x4 +
--   (346/275)*x4^12 + (3838/25)*x4^7 - (42124/275)*x4^2 = 0 := by grind

-- example : x1*x4^5 - x1 + (1/55)*x4^11 + (13/5)*x4^6 - (144/55)*x4 = 0 := by grind

-- example : x2^3 + 2*x2^2*x4 - 2*x2*x4^2 + x3^6*x4^2 + 2*x3^5*x4^3 - 2*x3^4*x4^4 +
--   2*x3^2*x4 - (232/275)*x3*x4^12 - (2576/25)*x3*x4^7 + (28018/275)*x3*x4^2 -
--   (568/275)*x4^13 - (6299/25)*x4^8 + (69307/275)*x4^3 = 0 := by grind


-- example : x2*x3 - x2*x4 + (8/5)*x3^6*x4 + (22/5)*x3^5*x4^2 - x3^3*x4^4 + x3^2 -
--   (442/275)*x3*x4^11 - (4901/25)*x3*x4^6 + (53913/275)*x3*x4 -
--   (1121/275)*x4^12 - (12433/25)*x4^7 + (136674/275)*x4^2 = 0 := by grind

-- example : x2*x4^5 - x2 + (1/55)*x4^11 + (13/5)*x4^6 - (144/55)*x4 = 0 := by grind

-- example : x3^7 + 3*x3^6*x4 + x3^5*x4^2 - x3^2 - (398/55)*x3*x4^11 - (4414/5)*x3*x4^6 +
--   (48787/55)*x3*x4 - (1042/55)*x4^12 - (11556/5)*x4^7 + (128103/55)*x4^2 = 0 := by grind

-- example : x3^2*x4^5 - x3^2 - (2/55)*x3*x4^11 - (21/5)*x3*x4^6 + (233/55)*x3*x4 -
--   (8/55)*x4^12 - (89/5)*x4^7 + (987/55)*x4^2 = 0 := by grind

-- set_option maxHeartbeats 100000000 in
-- example : x4^15 + 122*x4^10 - 122*x4^5 - 1 = 0 := by grind (ringSteps := 100000)
