import Mathlib

open Ideal
open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]

example :
  (Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
      ⊓
  Ideal.span ({X 1} : Set (MvPolynomial (Fin 2) ℚ))
      =
  Ideal.span {X 0 * X 1} := by
    have h₁ :  Ideal.span ({X 2 * X 0, (1 - X 2) * X 1} : Set (MvPolynomial (Fin 2) ℚ)) ⊓ Ideal.span {X 0, X 1} = Ideal.span {X 0 * X 1} := by
      sorry
    sorry


/-
我查了一下文档 根据我的理解Fin n是 Z/nZ
-/
example : (0 : Fin 2) = (2 : Fin 2) := rfl

-- example : (0 : Fin 2) = (0 : Fin 3) := rfl

example : (0 : Fin 2).val = (0 : Fin 3).val := rfl

/-
我想问的问题是：
现在用户输入了一个多项式f,他的变元是X_0,...X_n-1，我在证明的时候需要引入一个新变元t，但是我引入这个新变元t的时候我必须把这个变元的定义变到Fin n+1上，这个时候就会出现不匹配的问题了，我有办法让他们匹配吗，我目前只会norm_cast，但好像从statement写都会出错？Lean中这两个类型就是不同的，不能比较。然后我还想了一种思路，详见Lemma.lean（没有证完）

但是如果我要走这条路的话，我还要整一个ι，这样整个证明似乎会变得很复杂，想问一下张老师有没有什么简单的方法能解决这个问题。
-/

example :
  (Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) ℚ)) : Ideal (MvPolynomial (Fin 2) ℚ))
      ⊓
  Ideal.span ({X 1} : Set (MvPolynomial (Fin 2) ℚ))
      =
  Ideal.span {X 0 * X 1} := by

  have h₁ : Ideal.span ({X none * X (some 0), (1 - X none) * X (some 1)} : Set (MvPolynomial (Option (Fin 2)) ℚ))
            ⊓
            (Ideal.span {X 0, X 1}).map (rename some)
            =
            (Ideal.span {X 0 * X 1}).map (rename some) := by
    sorry

  sorry
