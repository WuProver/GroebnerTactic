import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly

import Groebner.Basic
import Groebner.List

import Mathlib.Tactic
import Lean


namespace Mathlib.Tactic.IsRemainder
open Lean Elab Tactic Meta Term
open Meta Ring Qq PrettyPrinter AtomM
open MvPolynomial MonomialOrder

namespace Poly
open Lean

variable {m : Type → Type} [Monad m] [MonadQuotation m] [MonadRef m]

/-
In this section, we define the structure to represent
a multivariate polynomial with rational coefficients,
-/

/-Define a structure `V` to represent the (index, exponent) pair of a MvPolynomial-/
def V := Nat × Nat
deriving FromJson, ToJson, Repr


/-`V.mkQ` constructs a `Expr` from a V pair,-/
def V.mkQ {u u' : Lean.Level} (v : V) (σ : Q(Type $u))
    (instOfNat : Q((n : Nat) → OfNat $σ n))
    (R : Q(Type $u'))
    (instField : Q(Field $R)) : Q(MvPolynomial $σ $R) :=
  let i : Q(Nat) := mkRawNatLit v.1
  let e : Q(Nat) := mkRawNatLit v.2
  q(MvPolynomial.X ($instOfNat $i).ofNat ^ $e)


/-`V.mkQ` constructs a `Term` from a V pair,-/
def V.mkTerm (v : V) : m Term :=
  let v' := Syntax.mkNumLit (toString v.1)
  if v.2 ≠ 1 then
    let e := Syntax.mkNumLit (toString v.2)
    `(term| MvPolynomial.X $v':num ^ $e:num)
  else
    `(term| MvPolynomial.X $v':num)


/-Define a structure `Q` to represent the coeff of a MvPolynomial-/
def Q := Int × Nat
deriving FromJson, ToJson, Repr

/-`Q.mkQ` constructs a `Expr` from a Q pair,-/
def Q.mkQ (q : Q) : Q(ℚ) :=
  let n : Q(Int) := mkIntLit q.1
  let d : Q(Nat) := mkNatLit q.2
  q($n / $d)

/-`Q.mkTerm` constructs a `Term` from a Q pair,-/
def Q.mkTerm (q : Q) : m Term :=
  let n := Syntax.mkNumLit (toString q.1)
  if q.2 = 1 then
    `(term| $n:num)
  else
    `(term| ($n:num / $(Syntax.mkNumLit (toString q.2))))

/-Define a structure `Mon` to represent a monomial of a MvPolynomial-/
structure Mon where
  c : Q
  e : Array V
deriving FromJson, ToJson, Repr


/-`Mon.mkQ` constructs a `Expr` from a Mon structure,-/
def Mon.mkQ {u v : Lean.Level} (m : Mon) (σ : Q(Type u))
    (instOfNat : Q((n : Nat) → OfNat $σ n))
    (R : Q(Type v))
    (instField : Q(Field $R)) : Q(MvPolynomial $σ $R) :=
  let c := m.c.mkQ
  m.e.foldl (β := Q(MvPolynomial $σ $R)) (init := q(MvPolynomial.C $c))
    (fun p m ↦
      let m := m.mkQ σ instOfNat R instField
      q($p * $m))

/-Define a structure `Polynomial` to represent a MvPolynomial-/
def Polynomial := List Poly.Mon
deriving FromJson, ToJson, Repr


/-`Polynomial.mkQ` constructs a `Expr` from a Polynomial structure,-/
def Polynomial.mkQ {u v : Lean.Level} (p : Polynomial) (σ : Q(Type $u))
    (instOfNat : Q((n : Nat) → OfNat $σ n))
    (R : Q(Type $v))
    (instField : Q(Field $R)) : Q(MvPolynomial $σ $R) :=
  p.foldl (α := Q(MvPolynomial $σ $R)) (init := q(0))
    (fun p m ↦
      let m := m.mkQ σ instOfNat R instField
      q($p + $m))

end Poly

/-Here's some example to test the sturcture to `Expr` defined before-/
#eval do
  Lean.fromJson? (α := List Poly.Mon)
    (← Lean.Json.parse
      "[{\"c\" : [1, 2], \"e\": [[0, 2], [2, 3]]}, {\"c\" : [3, 5], \"e\": [[4, 1]]}]")


#eval do
  Lean.fromJson? (α := Poly.Polynomial)
    (← Lean.Json.parse
      "[{\"c\" : [1, 2], \"e\": [[0, 2], [2, 3]]}, {\"c\" : [3, 5], \"e\": [[4, 1]]}]")


#eval do
  Lean.fromJson? (α := Poly.Polynomial)
    (← Lean.Json.parse
      "[{\"c\" : [1, 2], \"e\": [[0, 2], [2, 3]]}, {\"c\" : [3, 5], \"e\": [[4, 1]]}]")

#check Lean.MetaM Unit

open Qq in
#eval do
  let Except.ok parsed := Lean.Json.parse
      "[{\"c\" : [1, 2], \"e\": [[0, 2], [2, 3]]}, {\"c\" : [3, 5], \"e\": [[4, 1]]}]" | failure
  logInfo m!"{parsed}"
  let Except.ok p := Lean.fromJson? (α := Poly.Polynomial) parsed | failure
  let instOfNat ← Qq.synthInstanceQ q((n : Nat) → OfNat Nat n)
  let instField ← Qq.synthInstanceQ q(Field ℚ)
  let p := p.mkQ q(Nat) instOfNat q(ℚ) instField
  Lean.logInfo p


/-
In this section, we define the function to run Sage scripts
-/
inductive SageTask where
  | remainder (poly remainder : String)
  | basis (set : String)
  | ideal (genI genJ : String)


def runSage (task : SageTask) : IO String := do

  let (scriptName, scriptArgs) := match task with
    | .remainder poly rem => ("Remainder.sage", #["-p", poly, "-d", rem])
    | .basis set          => ("Basis.sage",     #["-s", set])
    | .ideal genI genJ    => ("Ideal.sage",     #["-I", genI, "-J", genJ])

  let cwd ← IO.currentDir
  let path := cwd / "Sage" / scriptName

  -- check if the file exists
  if not (← path.pathExists) then
    dbg_trace f!"There does not exist {path}"
    throw <| IO.userError s!"could not find sage script {scriptName}"

  -- runsage
  let child ← IO.Process.spawn {
    cmd := "sage"
    args := #[path.toString] ++ scriptArgs
    stdout := .piped,
    stderr := .piped
  }

  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait

  if !stderr.isEmpty then
    IO.println s!"Sage stderr: {stderr}"

  if exitCode != 0 then
    IO.println s!"Sage exit code: {exitCode}"

  return stdout

def testRemainder : IO String :=
  runSage (.remainder "X_0*X_1" "[X_0^2-X_1, 3*X_1]")

#eval testRemainder


/-
In this section, we define the functions to parse the Sage output
-/
def stringToJson (s : String) : Except String Json :=
  Json.parse s

#eval stringToJson "[{\"coeffs\": [\"1\"], \"power\": [[1, 0, 0, 0]]}, {\"coeffs\": [\"1\"], \"power\": [[0, 2, 0, 0]]}]"



def parseJson (result : Except String Json) : Lean.MetaM (Json) := do
  match result with
  | .ok sage_json_result => return sage_json_result
  | .error e => IO.throwServerError <|
  s!"Could not parse SageMath output : {result}\n Error : {e}"

def parseResult (result : Except String Poly.Polynomial) : Lean.MetaM (Option (Poly.Polynomial)) := do
  match result with
  | .ok parsed_result => return parsed_result
  | .error e => IO.throwServerError <|
  s!"Error when convert result to polynomial structure Error: {e}"

def processElement (jsonElement : Json) : MetaM Expr := do
  let mon_result := Lean.fromJson? (α := Poly.Polynomial) jsonElement
  let mon ← parseResult mon_result
  match mon with
      | none => IO.throwServerError "There is not any result be parsed"
      | some p =>
        let instOfNat ← Qq.synthInstanceQ q((n : Nat) → OfNat Nat n)
        let instField ← Qq.synthInstanceQ q(Field ℚ)
        let p := p.mkQ q(Nat) instOfNat q(ℚ) instField
        Lean.logInfo p
        pure p

def exprListToSyntaxArray (es : List Expr) : MetaM (Array Syntax) := do
  es.toArray.mapM fun e => do
    PrettyPrinter.delab e

def liftListQ (xs : List (Q(MvPolynomial ℕ ℚ))) : Q(List (MvPolynomial ℕ ℚ)) :=
  match xs with
  | [] => q([])
  | x :: xs =>
      let xs : Q(List (MvPolynomial ℕ ℚ)) := liftListQ xs
      q($x :: $xs)

def parseCoeff (a : Json) : TacticM Term := do
  let Except.ok b:= a.getArr? | failure
  let process_a:= b.mapM processElement
  let resultArray ←  process_a
  let xs := resultArray.toList
  let get : Q((xs : List (MvPolynomial ℕ ℚ)) -> Fin xs.length -> MvPolynomial ℕ ℚ) := q(List.get)
  let xs : Q(List (MvPolynomial ℕ ℚ)) := liftListQ xs
  let xs_get := q($get $xs)
  let xs_get <- Lean.PrettyPrinter.delab xs_get
  pure xs_get

def parseCoeff' (a : Json) : TacticM Term := do
  let Except.ok b:= a.getArr? | failure
  let process_a:= b.mapM processElement
  let resultArray ←  process_a
  let xs := resultArray.toList
  let get : Q((xs : List (MvPolynomial ℕ ℚ)) -> Fin xs.length -> MvPolynomial ℕ ℚ) := q(List.get)
  let xs : Q(List (MvPolynomial ℕ ℚ)) := liftListQ xs
  let xs <- Lean.PrettyPrinter.delab xs
  pure xs

/-
In this section, we define the some functions to parse `Expr` in Lean
-/

/-`parsePoly` parses a `MvPolynomial σ R` expression into a `String`-/
partial def parsePoly {u v: Lean.Level}{σ : Q(Type $u)}{R : Q(Type $v)}{r : Q(CommSemiring $R)} (e : Q(MvPolynomial $σ $R)) : MetaM String := do
  match e with
  | ~q($a + $b) =>
    let a  ← parsePoly a
    let b  ← parsePoly b
    pure s!"({a} + {b})"

  | ~q(@HSub.hSub (MvPolynomial «$σ» «$R») (MvPolynomial «$σ» «$R») (MvPolynomial «$σ» «$R») $commring $a $b) => do
            let a ← parsePoly a
            let b ← parsePoly b
            pure s!"({a} - {b})"

  | ~q($a * $b) =>
    let left ← parsePoly a
    let right ← parsePoly b
    pure s!"({left} * {right})"

  | ~q($a ^ ($n : ℕ)) =>
    let baseStr ← parsePoly a
    let n ← try
      let .isNat _ n _ ← NormNum.derive (α := q(ℕ)) n | failure
      pure n.natLit!
    catch _ =>
      pure n.natLit!
    pure s!"{baseStr}^{n}"

  | ~q(MvPolynomial.X $idx) =>
    match idx with
    | ~q(@OfNat.ofNat _ _ $var) =>
      match var with
      | .app (.app (.app (.const `Fin.instOfNat _) _) _) n => pure s!"X_{n}"
      | _ => pure s!"X_{idx}"

  | ~q(@OfNat.ofNat _ $b $n) =>
    logInfo "go to this branch"
    pure s!"{b}"

  | _ =>
    pure s!"{e}"

#eval parsePoly q(1: MvPolynomial Nat Nat)

/-`parseVars` parses a `Set (MvPolynomial σ R)` expression into a `List String`-/
partial def parseSet {u v : Level} {σ : Q(Type u)} {R : Q(Type v)} {r : Q(CommSemiring $R)}
    (e : Q(Set (MvPolynomial $σ $R))) : MetaM (List String) := do
  match e with
  | ~q(Insert.insert (γ:=Set _) $a $b) =>

    let VarA ← parsePoly (σ := σ) (R := R) (r := r) a
    let VarB ← parseSet (σ := σ) (R := R) (r := r) b

    -- logInfo m!"[DEBUG] VarA: {VarA}"
    -- logInfo m!"[DEBUG] VarB: {VarB}"

    pure (VarA :: VarB)
  | ~q((∅: Set (MvPolynomial _ _))) => pure []
  | ~q(Set.singleton $v) =>

    let vStr ← parsePoly (σ := σ) (R := R) (r := r) v
    pure [vStr]
  | ~q(singleton $v) =>

    let vStr ← parsePoly (σ := σ) (R := R) (r := r) v
    pure [vStr]
  | _ => unreachable!

/-
In this section, we define the tactics to call Sage to prove some algebraic facts
-/

elab "remainder" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder _ $R $instCommSemiring $poly $vars $r) =>

      let parsedPoly ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
      let varsList ← parseSet (σ := σ) (R := R) (r := instCommSemiring) vars
      let parsedR ← parsePoly r

      let sage_result ← runSage (.remainder parsedPoly s!"{varsList}")

      let result := Json.parse s!"{sage_result}"
      logInfo m!"[DEBUG] sage_json_result: {result}"
      let sage_json_result ← parseJson result
      logInfo m!"[DEBUG] sage_json_result after parsing: {sage_json_result}"
      let Except.ok arr := sage_json_result.getArr? | failure
      logInfo m!"Arr: {arr[0]!}"

      let processList := arr.mapM processElement
      let resultArray ← processList
      let xs := resultArray.toList
      let get : Q((xs : List (MvPolynomial ℕ ℚ)) -> Fin xs.length -> MvPolynomial ℕ ℚ) := q(List.get)
      let xs : Q(List (MvPolynomial ℕ ℚ)) := liftListQ xs
      let xs_get := q($get $xs)
      let xs_get <- Lean.PrettyPrinter.delab xs_get

      let runUse := fun x => do Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]
      evalTactic (← `(tactic|
         simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
      ))
      evalTactic (← `(tactic|
         rw [isRemainder_range_fin, ← exists_and_right]
      ))
      runUse xs_get
      evalTactic (← `(tactic|
        split_ands
      ))
      evalTactic (← `(tactic|
        focus
          simp [Fin.univ_succ, -List.get_eq_getElem, List.get]
          all_goals decide +kernel-- PIT, proof by reflection
      ))
      evalTactic (← `(tactic|
        focus
          intro i
          fin_cases i
          all_goals {
            -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
            simp only [List.get, Fin.isValue]
            all_goals {
              rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
                SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
                ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
              decide +kernel
            }
          }
      ))
      evalTactic (← `(tactic| simp))
    | _ =>
      dbg_trace "not a lex.IsRemainder"


elab "remainder'" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder _ $R $instCommSemiring $poly $vars $r) =>
      logInfo m!"[DEBUG] vars = {vars}"

      let parsedPoly ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
      let varsList ← parseSet (σ := σ) (R := R) (r := instCommSemiring) vars
      let parsedR ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) r

      logInfo m!"parsed vars: {varsList}"
      logInfo m!"parsed polynomial: {parsedPoly}"

      let sage_result ← runSage (.remainder parsedPoly s!"{varsList}")

      logInfo m!"[DEBUG] check sage_result 11_26: {sage_result}"


      let result := Json.parse s!"{sage_result}"
      -- logInfo m!"[DEBUG] sage_json_result: {result}"
      let sage_json_result ← parseJson result
      -- logInfo m!"[DEBUG] sage_json_result after parsing: {sage_json_result}"
      let Except.ok arr := sage_json_result.getArr? | failure

      let processList := arr.mapM processElement
      let resultArray ← processList
      let xs := resultArray.toList
      let get : Q((xs : List (MvPolynomial ℕ ℚ)) -> Fin xs.length -> MvPolynomial ℕ ℚ) := q(List.get)
      let xs : Q(List (MvPolynomial ℕ ℚ)) := liftListQ xs
      -- logInfo m!"[DEBUG] {xs}"
      let xs_get := q($get $xs)
      -- logInfo m!"[DEBUG] {xs_get}"
      let xs_get <- Lean.PrettyPrinter.delab xs_get
      -- logInfo m!"[CHECK {xs_get}]"
      let runUse := fun x => do Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]
      evalTactic (← `(tactic|
        simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
      ))
      evalTactic (← `(tactic|
        rw [isRemainder_range_fin, ← exists_and_right]
      ))
      runUse xs_get
      evalTactic (← `(tactic|
        split_ands
      ))
      evalTactic (← `(tactic|
        focus
          simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
          try grind-- PIT, we will rely on reflection
      ))
      evalTactic (← `(tactic|
        focus
          intro i
          fin_cases i
          all_goals {
            -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
            simp only [List.get, Fin.isValue]
            all_goals {
              rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
                SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
                ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
              decide +kernel
            }
          }
      ))
      evalTactic (← `(tactic|
        focus
          rw [Function.Surjective.forall (AddEquiv.surjective (SortedFinsupp.lexAddEquiv compare))]
          simp only [MvPolynomial.SortedRepr.support_eq, Finset.mem_map_equiv,
            Fin.isValue, List.length_nil, List.length_cons,
            EquivLike.coe_symm_apply_apply, List.mem_toFinset]
          intro x h i
          fin_cases i
          all_goals
            simp only [List.get]
            rw [← tsub_eq_zero_iff_le, MvPolynomial.SortedRepr.lex_degree_eq]
            convert_to _ → ¬ SortedFinsupp.toFinsupp _ - SortedFinsupp.toFinsupp x = 0
            rw [← SortedFinsupp.toFinsupp_tsub, SortedFinsupp.toFinsupp_eq_zero_iff]
            decide +kernel +revert
      ))
    | _ =>
      dbg_trace "not a lex.IsRemainder"

/-`basis` helps prove if a Set is Groebner Basis-/
elab "basis" : tactic  => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsGroebnerBasis _ $R $instCommSemiring $basis $ideal) =>

      let basislist <- parseSet basis
      dbg_trace "parsed basis: {basislist}"

      let sage_result ← runSage (.basis s!"{basislist}")
      logInfo m!"[DEBUG] check sage_result basis 11_26: {sage_result}"
      let result := Json.parse s!"{sage_result}"
      let sage_json_result ← parseJson result

      let Except.ok arr := sage_json_result.getArr? | failure
      -- logInfo m!"Arr: {arr}"
      -- logInfo m!"Arr[0]: {arr[0]!}"
      let parsedTermsArray ← arr.mapM parseCoeff
      evalTactic (← `(tactic|
        rw [buchberger_criterion]
      ))
      evalTactic (← `(tactic|
        simp only [Fin.isValue, Subtype.forall, Set.mem_insert_iff, Set.mem_singleton_iff,
          forall_eq_or_imp, forall_eq, sPolynomial_self]
      ))
      evalTactic (← `(tactic|
        simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
      ))
      evalTactic (← `(tactic|
        simp_rw [isRemainder_range_fin]
      ))
      evalTactic (← `(tactic|
        split_ands
      ))
      for i in parsedTermsArray do
        logInfo m!"[DEBUG Basis] check {i}"
        evalTactic (← `(tactic|
        focus
          use $i:term
        ))
        evalTactic (← `(tactic|
          split_ands
        ))
        evalTactic (← `(tactic|
          focus
            simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
            all_goals decide +kernel-- PIT by reflection
        ))
        evalTactic (← `(tactic|
          focus
            intro i
            fin_cases i
            all_goals {
              simp only [List.get]
              rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
                SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
                ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
              decide +kernel
            }
        ))
        evalTactic (← `(tactic|
        · simp))


open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]

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

variable {R : Type*} [CommRing R] {I : Ideal R} {a : R} {B : Set R}

lemma Ideal.insert_le_of_mem_of_le:
    a ∈ I → Ideal.span B ≤ I → Ideal.span (insert a B) ≤ I := by
    intro ha hB
    rw [Ideal.span_insert]
    simp
    constructor
    · exact (Ideal.span_singleton_le_iff_mem I).mpr ha
    · exact hB

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

elab "ideal" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goalType ← goal.getType
  let goalType ← checkTypeQ goalType q(Prop)
  match goalType with
  | none => return
  | some expr =>
    match expr with
    | ~q( ($I : @Ideal (@MvPolynomial $σ $R $i) $ring) = $J )  =>
      -- let (LHS : Q(Ideal MvPolynomial «σ» «R»)) := a
      let LHS := I
      let RHS := J

      match LHS, RHS with
      | ~q(Ideal.span $I_gens), ~q(Ideal.span $J_gens) =>
        let I_gens_list ←  parseSet I_gens
        let J_gens_list ←  parseSet J_gens
        let sage_result ← runSage (.ideal s!"{I_gens_list}" s!"{J_gens_list}")

        let result := Json.parse s!"{sage_result}"
        let sage_json_result ← parseJson result
        let Except.ok poly_arr := sage_json_result.getArr? | failure

        evalTactic (← `(tactic|
          apply le_antisymm
        ))

        for poly_json in poly_arr do
          let Except.ok arr := poly_json.getArr? | failure
          evalTactic (← `(tactic|
            focus
              nth_rw 1 [Set.singleton_def]
              ))
          for poly in arr do
            let coeff_json := Json.parse s!"{poly}"
            let coeff_json ← parseJson coeff_json
            let Except.ok coeff_arr := coeff_json.getArr? | failure

            let termsArray : Array Term ← coeff_arr.mapM fun coeff => do
              let termExpr ← processElement coeff
              Lean.PrettyPrinter.delab termExpr

            logInfo m!"[DEBUG Ideal] poly to use : {termsArray}"
            evalTactic (← `(tactic|
              apply Ideal.insert_le_of_mem_of_le
              ))
            evalTactic (← `(tactic|
              focus
                submodule_span [$termsArray:term,*]
                with_unfolding_all decide
                -- decide +kernel
              ))
          evalTactic (← `(tactic|
            focus
              simp only [Ideal.span_empty, Fin.isValue, bot_le]
            ))
      | _ =>
        dbg_trace "The left side is not an Ideal.span"


    | _ =>
      logError "Error: Goal is not an equality (Eq.eq) structure."



end IsRemainder



namespace Mathlib.Tactic.IsGroebner

end IsGroebner

end Tactic

end Mathlib
