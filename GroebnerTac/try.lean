import Mathlib

open MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*}

section IntersectionIdeal

noncomputable def t : MvPolynomial (Option σ) R := X none

noncomputable def ι : MvPolynomial σ R →+* MvPolynomial (Option σ) R :=
  (rename Option.some).toRingHom

noncomputable def eval_t (val : MvPolynomial σ R) : MvPolynomial (Option σ) R →+* MvPolynomial σ R :=
  (aeval (fun o => match o with
    | none => val
    | some i => X i
  )).toRingHom

theorem intersection_eq_elimination (I J : Ideal (MvPolynomial σ R)) (f : MvPolynomial σ R) :
    f ∈ I ⊓ J ↔ ι f ∈ Ideal.span {t} * I.map ι ⊔ Ideal.span {1 - t} * J.map ι := by

  let K := Ideal.span {t} * I.map ι ⊔ Ideal.span {1 - t} * J.map ι

  apply Iff.intro
  -- 方向 1 (⇒): 如果 f ∈ I 且 f ∈ J，那么 ι(f) ∈ K
  · intro h
    cases h with
    | intro hI hJ =>
      have eq_split : ι f = t * ι f + (1 - t) * ι f := by
        simp [t]
        ring
      rw [eq_split]

      apply Ideal.add_mem (Ideal.span {t} * I.map ι ⊔ Ideal.span {1 - t} * J.map ι)
      ·
        apply Ideal.mem_sup_left
        apply Ideal.mul_mem_mul
        · apply Ideal.mem_span_singleton_self
        · apply Ideal.mem_map_of_mem _ hI
      ·
        apply Ideal.mem_sup_right
        apply Ideal.mul_mem_mul
        · apply Ideal.mem_span_singleton_self
        · apply Ideal.mem_map_of_mem _ hJ

  -- 方向 2 (⇐): 如果 ι(f) ∈ K，那么 f ∈ I 且 f ∈ J
  · intro h_in_K
    constructor
    ·
      have h1 : eval_t 1 (ι f) = f := by
        change ((eval_t 1).comp ι) f = (RingHom.id _) f
        congr 1
        
        sorry
      rw [← h1]
      apply Ideal.mem_map_of_mem (eval_t 1) at h_in_K
      sorry

    ·
      have h0 : eval_t 0 (ι f) = f := by
        sorry
      rw [← h0]
      apply Ideal.mem_map_of_mem (eval_t 0) at h_in_K
      sorry

end IntersectionIdeal
