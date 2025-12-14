import Mathlib

import Groebner.Basic
import Groebner.List
import GroebnerTac.Tactic

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

open MvPolynomial

section Ideal
open MvPolynomial MonomialOrder Ideal

variable {R : Type*} [CommRing R] {σ : Type*}
variable {K : Type*} [Field K] {σ : Type*}

#check lex.IsGroebnerBasis

set_option maxHeartbeats 2000000 in
theorem Rabinovich_method (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    f ∈ I.radical ↔
    1 ∈
      I.map (rename Option.some) ⊔
      Ideal.span {1 - (X none) * (rename Option.some f) } := by
  let R := MvPolynomial σ K
  let R_t := MvPolynomial (Option σ) K
  constructor
  ·
    intro h
    rcases h with ⟨n, hn⟩
    have eq : (1 : MvPolynomial (Option σ) K) =
    (1 - ((X none) * (rename Option.some f)) ^ n) +
    ((X none) * (rename Option.some f)) ^ n := by
      ring
    nth_rw 2 [eq]
    apply Ideal.add_mem
    · apply Ideal.mem_sup_right
      have l₁: 1 - (X none) * (rename Option.some f) ∣ 1 - (X none * (rename some) f) ^ n := by
        exact one_sub_dvd_one_sub_pow (X none * (rename some) f) n
      rcases l₁ with ⟨p, hp⟩
      rw [hp]
      apply Ideal.mul_mem_right
      exact Ideal.mem_span_singleton_self (1 - X none * (rename some) f)
    · apply Ideal.mem_sup_left
      rw [mul_pow]
      apply Ideal.mul_mem_left
      rw [← map_pow]
      exact Ideal.mem_map_of_mem (rename some) hn
  ·
    intro h
    let R_f := Localization.Away f
    let inv_f : R_f := IsLocalization.mk' R_f 1 ⟨f, Submonoid.mem_powers _⟩

    let φ : R_t →+* R_f := (aeval (fun o => match o with
      | some i => algebraMap R R_f (X i)
      | none   => inv_f
    )).toRingHom

    have kill_gen : φ (1 - X none * rename Option.some f) = 0 := by
      simp only [map_sub, map_one, map_mul]

      have val_t : φ (X none) = inv_f := by
        simp [φ]
        rw [aeval_X]

      have val_f : φ (rename Option.some f) = algebraMap R R_f f := by
        dsimp [φ]
        rw [MvPolynomial.aeval_rename]
        have h₁ : ((fun o ↦
          match o with
          | some i => (algebraMap R R_f) (X i)
          | none => inv_f) ∘ some) = fun i ↦ (algebraMap R R_f) (X i) := by
          ext i
          simp
        rw [h₁]
        suffices ∀ g : MvPolynomial σ K,
        (aeval fun i ↦ algebraMap R R_f (X i)) g = algebraMap R R_f g by
          apply this
        intro g
        apply MvPolynomial.induction_on g
        · intro c
          simp [AlgHom.commutes]
          exact rfl
        ·
          intro p q hp hq
          simp [map_add, hp, hq]
        ·
          intro p i hp
          simp [map_mul, hp]

      rw [val_t, val_f]
      rw [IsLocalization.mk'_spec]
      simp

    have h_image : (1 : R_f) ∈ I.map (algebraMap R R_f) := by
      rw [← map_one φ]
      have step := Ideal.mem_map_of_mem φ h
      rw [Ideal.map_sup, Ideal.map_span] at step
      rw [Set.image_singleton, kill_gen, Ideal.span_singleton_zero, sup_bot_eq] at step
      convert step using 1
      symm
      erw [Ideal.map_map]
      congr 1
      apply RingHom.ext
      intro x
      apply MvPolynomial.induction_on x
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply]
        erw [MvPolynomial.rename_C]
        simp [φ]
        rw [MvPolynomial.aeval_C]
        exact rfl

      · intro p q hp hq
        simp
        erw [hp, hq]
      ·
        intro p hp hq
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply, map_mul]
        erw [hq]
        congr 1
        dsimp
        change φ (rename some (X hp)) = _
        rw [MvPolynomial.rename_X]
        simp [φ]
        rw [MvPolynomial.aeval_X]
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) R_f] at h_image
    rcases h_image with ⟨⟨g, ⟨l, hl⟩⟩, hg⟩
    rw [one_mul] at hg
    rw [IsLocalization.eq_iff_exists (Submonoid.powers f) R_f] at hg
    obtain ⟨c, h_and⟩ := hg
    dsimp at h_and
    have h_mul_pow : ↑c * l ∈ Submonoid.powers f := Submonoid.mul_mem _ c.2 hl
    obtain ⟨n, hn⟩ := h_mul_pow
    use n
    dsimp at hn
    rw [hn, h_and]
    exact Ideal.mul_mem_left I (↑c) g.2

variable {T : Type*} [DecidableEq T]
set_option maxHeartbeats 2000000 in
theorem Rabinovich_method'
    (g : σ → T) (t : T)
    (h_disj : ∀ a, g a ≠ t)
    (h_inj : Function.Injective g)
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    f ∈ I.radical ↔
    1 ∈
      I.map (rename g) ⊔
      Ideal.span {1 - (X t) * (rename g f) } := by
  classical
  let R := MvPolynomial σ K
  let R_t := MvPolynomial T K
  constructor
  ·
    intro h
    rcases h with ⟨n, hn⟩
    have eq : (1 : R_t) =
      (1 - ((X t) * (rename g f)) ^ n) +
      ((X t) * (rename g f)) ^ n := by
      ring
    nth_rw 2 [eq]
    apply Ideal.add_mem
    ·
      apply Ideal.mem_sup_right
      have l₁: 1 - (X t) * (rename g f) ∣ 1 - (X t * (rename g) f) ^ n := by
        exact one_sub_dvd_one_sub_pow (X t * (rename g) f) n
      rcases l₁ with ⟨p, hp⟩
      rw [hp]
      apply Ideal.mul_mem_right
      exact Ideal.mem_span_singleton_self (1 - X t * (rename g) f)
    ·
      apply Ideal.mem_sup_left
      rw [mul_pow]
      apply Ideal.mem_map_of_mem (rename g) at hn
      rw [map_pow] at hn
      apply Ideal.mul_mem_left
      convert hn using 1

  ·
    intro h
    let R_f := Localization.Away f
    let inv_f : R_f := IsLocalization.mk' R_f 1 ⟨f, Submonoid.mem_powers _⟩

    let φ_func : T → R_f := fun x ↦
      if h_eq : x = t then inv_f
      else
        if h_ran : x ∈ Set.range g then algebraMap R R_f (X (Classical.choose h_ran))
        else 0

    let φ : R_t →+* R_f := (aeval φ_func).toRingHom
    have kill_gen : φ (1 - X t * rename g f) = 0 := by
      simp only [map_sub, map_one, map_mul]
      have val_t : φ (X t) = inv_f := by
        dsimp [φ, φ_func]
        rw [aeval_X]
        simp only [if_true]

      have val_f : φ (rename g f) = algebraMap R R_f f := by
        dsimp [φ]
        rw [MvPolynomial.aeval_rename]
        have h_comp : φ_func ∘ g = fun i ↦ (algebraMap R R_f) (X i) := by
          ext i
          dsimp [φ_func]
          split_ifs with h1 h2
          ·
            exfalso
            exact h_disj i h1
          ·
            congr
            apply h_inj
            exact Classical.choose_spec h2
          ·
            exfalso
            exact h2 (Set.mem_range_self i)
        rw [h_comp]
        change (MvPolynomial.aeval (fun i ↦ algebraMap R R_f (X i))).toRingHom f = (algebraMap R R_f) f
        congr 1
        simp
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
          exact rfl
        · intro i
          simp
          exact rfl
      rw [val_t, val_f]
      rw [IsLocalization.mk'_spec]
      simp

    have h_image : (1 : R_f) ∈ I.map (algebraMap R R_f) := by
      rw [← map_one φ]
      have step := Ideal.mem_map_of_mem φ h
      rw [Ideal.map_sup, Ideal.map_span] at step
      rw [Set.image_singleton, kill_gen, Ideal.span_singleton_zero, sup_bot_eq] at step
      convert step using 1
      symm
      erw [Ideal.map_map]
      congr 1
      apply RingHom.ext
      intro x
      apply MvPolynomial.induction_on x
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply]
        erw [MvPolynomial.rename_C]
        dsimp [φ]
        rw [MvPolynomial.aeval_C]
        exact rfl
      · intro p q hp hq
        simp
        erw [hp, hq]
      · intro p i hp
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply, map_mul]
        erw [hp]
        congr 1
        dsimp [φ]
        dsimp [φ_func]
        erw [MvPolynomial.rename_X]
        rw [MvPolynomial.aeval_X]
        rw [if_neg (h_disj i)]
        have h_ran : g i ∈ Set.range g := Set.mem_range_self i
        rw [dif_pos h_ran]
        congr 1
        congr 1
        apply h_inj
        exact Classical.choose_spec h_ran

    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) R_f] at h_image
    rcases h_image with ⟨⟨g_val, ⟨l, hl⟩⟩, hg⟩

    rw [one_mul] at hg
    rw [IsLocalization.eq_iff_exists (Submonoid.powers f) R_f] at hg
    obtain ⟨c, h_and⟩ := hg
    dsimp at h_and
    have h_mul_pow : ↑c * l ∈ Submonoid.powers f := Submonoid.mul_mem _ c.2 hl
    obtain ⟨n, hn⟩ := h_mul_pow
    use n
    dsimp at hn
    rw [hn, h_and]
    exact Ideal.mul_mem_left I (↑c) g_val.2


example :
  X 0 ∉ (Ideal.span ({X 0 + X 1} : Set (MvPolynomial (Fin 3) ℚ))).radical := by
  let g : Fin 3 → Fin 4 := Fin.castSucc
  let t : Fin 4 := Fin.last 3

  by_contra h
  rw [Rabinovich_method' g t Fin.castSucc_ne_last (Fin.castSucc_injective 3)] at h
  rw [Ideal.map_span] at h
  rw [← Ideal.span_union] at h
  rw [Set.image_singleton, Set.singleton_union] at h
  simp only [rename_X,  t] at h
  dsimp [g, t] at h
  simp at h
  have h₁ : 1 ∉ Ideal.span  ({X 0 + X 1, 1 - X (Fin.last 3) * (rename Fin.castSucc) (X 0)} : Set <| MvPolynomial (Fin 4) ℚ) := by
    simp
    ideal_membership
  simp at h₁
  exact h₁ h

end Ideal
