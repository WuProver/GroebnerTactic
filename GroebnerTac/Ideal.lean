import Mathlib

namespace Tactic.Submodule

open Qq Lean Elab Tactic Term

lemma aux_add_smul (R : Type*) {M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (g : R) (r f : M)
    (s : Set M) (h : r ∈ Submodule.span R s) :
    g • f + r ∈ Submodule.span R (insert f s) := by
  simp [Submodule.span_insert]
  apply Submodule.add_mem
  · apply Submodule.mem_sup_left
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact Submodule.mem_sup_right h

lemma aux_smul (R : Type*) {M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (g : R) (f : M):
    g • f ∈ Submodule.span R {f} :=
  Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

elab "submodule_span" "[" coeffs:term,* "]" : tactic => do
  let goal ← getMainTarget
  let some goal ← Qq.checkTypeQ goal q(Prop) | throwError "goal isn't a prop"
  let ⟨_, R, _, M, smul, member, basesSet, _, _, _⟩ ←
    show TacticM <|
      (u_1 : Level) × (R : Q(Type $u_1)) ×
      (u_2 : Level) × (M : Q(Type $u_2)) ×
      -- mul (*) or smul (•),    member,  set of bases
      (Q($R) → Q($M) → Q($M)) × Q($M) × Q(Set $M) ×
      -- instances
      (_ : Q(Semiring $R)) × (_ : Q(AddCommMonoid $M)) × Q(_root_.Module $R $M) from
    match goal with
    | ~q($member ∈ @Ideal.span $α $instSemiring $s) =>
      pure ⟨u_1, α, u_1, α, fun x y ↦ q($x * $y), member, s,
        instSemiring, q(inferInstance), q(inferInstance)⟩
    | ~q($member ∈ @Submodule.span $R $M $instSemiring $instMonoid $instModule $s) =>
      pure ⟨u_2, R, u_1, M, fun x y ↦ q($x • $y), member, s,
        instSemiring, instMonoid, instModule⟩
    | _ => throwError "unsupported goal"
  let rec getObjectsOfSet (s : Q(Set $M)) (old : Array Q($M) := #[]) :
      TacticM <| Option <| Array Q($M) := do
    match s with
    | ~q(insert $a $s) => getObjectsOfSet s (old ++ #[a])
    | ~q({$a}) => pure <| .some <| old ++ #[a]
    | ~q({}) => pure <| .some old
    | _ => pure <| .none
  let bases := (← getObjectsOfSet basesSet).getD #[]
  let coeffs ← coeffs.getElems.mapM (do withSynthesize <| elabTermEnsuringTypeQ · R)
  if bases.size != coeffs.size then
    throwError
      s!"unmatched numbers of coefficients ({coeffs.size}) with numbers of bases ({bases.size})"

  -- `let sum` lead to error on the `q(...)` on `(← getMainGoal).assign` sentence?
  have sum :=
    if coeffs.size != 0 then
      (coeffs.zip bases)[0:coeffs.size-1].foldr
      (fun x y ↦ q($(smul x.1 x.2) + «$y»))
      (smul coeffs.back! bases.back!)
    else q(0)

  let sumMemSpan : Q($sum ∈ Submodule.span $R $s) ←
    match coeffs.size with
    | 0 => pure <| show Q($sum ∈ Submodule.span $R $basesSet) from
      show Q(0 ∈ Submodule.span $R $basesSet) from
      q(Submodule.zero_mem (R := $R) (module_M := inferInstance) _)
    | _ =>
      let g := coeffs.back!
      let f := bases.back!
      let init ← instantiateMVarsQ q(aux_smul $R (M := $M) $g $f)
      let proof : (sum_ : Q($M)) × (s_ : Q(Set $M)) × Q($sum_ ∈ Submodule.span $R $s_) ←
        (coeffs.zip bases)[0:coeffs.size-1].foldrM
          (fun x ⟨sum_, s_, mem_⟩ ↦ do
            let g := x.1
            let f := x.2
            pure ⟨q($g • $f + $sum_), q(insert $f $s_),
              ← instantiateMVarsQ q(aux_add_smul $R (M := $M) $g $sum_ $f $s_ $mem_)⟩)
          ⟨q($g • $f), q({$f}), init⟩
      pure proof.2.2
  let mvarIdEq : Q(($member = $sum)) ← mkFreshExprMVarQ q($member = $sum) (userName := `eq)

  (← getMainGoal).assign
    <| q((iff_of_eq <|
      congrArg (a₁ := $member) (a₂ := $sum)
      (· ∈ Submodule.span $R (M := $M) $basesSet) $mvarIdEq).mpr $sumMemSpan)

  replaceMainGoal [mvarIdEq.mvarId!]

example (a b c d : Int) : 5 * d + 1 * a + 3 * c + 2 * b  ∈ Ideal.span {a, b, c, d} := by
  submodule_span [1, 2, 3, 5]
  ring


open MvPolynomial MonomialOrder

example :  X 0^2 ∈ Ideal.span ({X 0 + X 1^ 2, X 1 ^ 2} : Set (MvPolynomial (Fin 2) ℚ)) := by
  submodule_span [X 0, -X 0]
  ring
