import Mathlib

import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial

import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
import Lean.Meta.Tactic.TryThis

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

/-`Mon.mkTerm` constructs a `Term` from a Mon structure,-/
def Mon.mkTerm (m' : Mon) : m Term := do
  let c : Term ← `(term| MvPolynomial.C $(← m'.c.mkTerm))
  m'.e.foldlM (fun p m ↦ do `(term| $p * $(← m.mkTerm))) c


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

/-`Polynomial.mkTerm` constructs a `Term` from a Polynomial structure,-/
def Polynomial.mkTerm (p : Polynomial) : m Term := do
  p.foldlM (fun p m ↦ do `(term| $p + $(← m.mkTerm))) (← `(0))

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
  | GBasis (set : String)
  | GRemainder (poly set : String)
  | radical (poly set : String)
  | Idealmem (poly set : String)


def runSage (task : SageTask) : IO String := do

  let (scriptName, scriptArgs) := match task with
    | .remainder poly rem  => ("Remainder.sage", #["-p", poly, "-d", rem])
    | .basis set           => ("Basis.sage",     #["-s", set])
    | .ideal genI genJ     => ("Ideal.sage",     #["-I", genI, "-J", genJ])
    | .GBasis set          => ("GBasis.sage",    #["-s", set])
    | .GRemainder poly set => ("GRemainder.sage", #["-p", poly, "-s", set])
    | .radical poly set    => ("Radical.sage",  #["-p", poly, "-s", set])
    | .Idealmem poly set   => ("Idealmem.sage", #["-p", poly, "-s", set])

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
def parseJson (result : Except String Json) : Lean.MetaM (Json) := do
  match result with
  | .ok sage_json_result => return sage_json_result
  | .error e => IO.throwServerError <|
  s!"Could not parse SageMath output : {result}\n Error : {e}"

def parseResult (result : Except String Poly.Polynomial)
  : Lean.MetaM (Option (Poly.Polynomial)) := do
  match result with
  | .ok parsed_result => return parsed_result
  | .error e => IO.throwServerError <|
  s!"Error when convert result to polynomial structure Error: {e}"

/-`mkPolyExpr` convert `Json` returned by sage to `Expr` -/
def mkPolyExpr (jsonElement : Json) : MetaM Expr := do
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

/-`mkPolyTerm` convert `Json` returned by sage to `Term` -/
def mkPolyTerm (jsonElement : Json) : MetaM Term := do
  let poly_result := Lean.fromJson? (α := Poly.Polynomial) jsonElement
  let poly ← parseResult poly_result
  match poly with
  | none => IO.throwServerError "There is not any result be parsed"
  | some p =>
    let p ← p.mkTerm
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

/-`mkPolyListTerm` convert `Json` to the `Expr` of a list of MvPolynomial using `mkPolyExpr` -/
def mkPolyListTerm (jsonInput : Json) : TacticM Term := do
  let Except.ok jsonArray:= jsonInput.getArr? | failure
  let polyExprsArray := jsonArray.mapM mkPolyExpr

  let resultArray ←  polyExprsArray
  let polyExprList := resultArray.toList
  let get : Q((polyExprList : List (MvPolynomial ℕ ℚ)) ->
              Fin polyExprList.length -> MvPolynomial ℕ ℚ) := q(List.get)
  let polyExprList : Q(List (MvPolynomial ℕ ℚ)) := liftListQ polyExprList
  let polyListExpr := q($get $polyExprList)
  let polyListExpr <- Lean.PrettyPrinter.delab polyListExpr

  pure polyListExpr

/-
In this section, we define some functions to parse `Expr` in Lean
-/
/-`parsePoly` parses a `MvPolynomial σ R` expression into a `String`-/
partial def parsePoly {u v: Lean.Level}
  {σ : Q(Type $u)}{R : Q(Type $v)}
  {r : Q(CommSemiring $R)} (e : Q(MvPolynomial $σ $R)) : MetaM String := do
  match e with
  | ~q($a + $b) =>
    let a  ← parsePoly a
    let b  ← parsePoly b
    pure s!"({a} + {b})"

  | ~q(@HSub.hSub (MvPolynomial «$σ» «$R»)
    (MvPolynomial «$σ» «$R») (MvPolynomial «$σ» «$R») $commring $a $b) => do
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

  | ~q(MvPolynomial.C $val) =>
      let r ← Mathlib.Meta.NormNum.derive val
      pure s!"{r.toRat.get!}"
    -- match val with
    -- | ~q(@HDiv.hDiv («$R»)
    --   («$R») («$R») $commring $a $b) =>
    --   -- pure s!"{a}/{b}"
    --   match a, b with
    --   | ~q(@OfNat.ofNat _ _ $n1),  ~q(@OfNat.ofNat _ _ $n2) =>
    --     match n1, n2 with
    --     | ~q(@Rat.instOfNat $n1),  ~q(@Rat.instOfNat $n2)
    --       pure s!"{n1}/{n2}"
    --     | _ =>
    --       pure s!"{n1}/{n2}"
    -- | _ =>

  | ~q(@OfNat.ofNat _ $b $n) =>
    logInfo "go to this branch"
    pure s!"{b}"

  | _ =>
    pure s!"{e}"

#eval parsePoly q(1: MvPolynomial Nat Nat)
#eval parsePoly q(X 1 - C (1 / 2): MvPolynomial (Fin 2) ℚ)
#eval parsePoly q(X 1 - C (1): MvPolynomial (Fin 2) ℚ)

run_meta do
  let r ← Mathlib.Meta.NormNum.derive q(1 + 3*2 + 3/4 : ℚ)
  Lean.logInfo <| repr r.toRat

/-`parseSet` parses a `Set (MvPolynomial σ R)` expression into a `List String`-/
partial def parseSet {u v : Level} {σ : Q(Type u)} {R : Q(Type v)} {r : Q(CommSemiring $R)}
    (e : Q(Set (MvPolynomial $σ $R))) : MetaM (List String) := do
  match e with
  | ~q(Insert.insert (γ:=Set _) $a $b) =>

    let VarA ← parsePoly (σ := σ) (R := R) (r := r) a
    let VarB ← parseSet (σ := σ) (R := R) (r := r) b

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
def verifyRemainderLogic (witness : Term) (isZeroTarget : Bool) : TacticM Unit := do
  let runUse := fun x => do Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]

  evalTactic (← `(tactic|
     simp only [← Set.range_get_singleton, ← Set.range_get_cons_list]
  ))
  evalTactic (← `(tactic|
     rw [isRemainder_range_fin, ← exists_and_right]
  ))

  runUse witness

  evalTactic (← `(tactic| split_ands ))

  evalTactic (← `(tactic|
    focus
      simp [Fin.univ_succ, -List.get_eq_getElem, List.get]
      all_goals decide +kernel
  ))

  evalTactic (← `(tactic|
    focus
      intro i
      fin_cases i
      all_goals {
        simp only [List.get, Fin.isValue]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
      }
  ))

  if isZeroTarget then
    evalTactic (← `(tactic| simp))
  else
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

syntax (name := checkRemainder) "remainder" "[" term,* "]" : tactic

@[tactic checkRemainder]
def evalCheckRemainder : Tactic := fun stx => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder
       _ $R $instCommSemiring $poly $vars $r) =>

      let isZeroTarget ← isDefEq r q(0)

      match stx with

      | `(tactic| remainder [ $args,* ]) => do

        let witness : Term ← `([ $args,* ])

        verifyRemainderLogic witness isZeroTarget

      | _ => throwUnsupportedSyntax


open Lean.Meta.Tactic.TryThis

syntax (name := remainderTry) "remainder?" : tactic

@[tactic remainderTry]
def evalRemainderTry : Tactic := fun stx => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)

  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder
      _ $R $instCommSemiring $poly $vars $r) =>

      let isZeroTarget ← isDefEq r q(0)
      let parsedPoly ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
      let varsList ← parseSet (σ := σ) (R := R) (r := instCommSemiring) vars

      let sage_result ← runSage (.remainder parsedPoly s!"{varsList}")
      let result := Json.parse s!"{sage_result}"
      let sage_json_result ← parseJson result
      let Except.ok arr := sage_json_result.getArr? | failure

      let processList := arr.mapM mkPolyExpr
      let exprList ←  processList
      let exprList := exprList.toList

      let args : Array Term ← exprList.toArray.mapM fun e => do
        Lean.PrettyPrinter.delab e

      let suggestion : TSyntax `tactic ← `(tactic| remainder [ $args,* ])
      addSuggestion stx suggestion

      let listQ : Q(List (MvPolynomial ℕ ℚ)) := liftListQ exprList

      let getQ : Q((xs : List (MvPolynomial ℕ ℚ)) -> Fin xs.length
         -> MvPolynomial ℕ ℚ) := q(List.get)
      let witnessQ := q($getQ $listQ)

      let witnessTerm : Term ← Lean.PrettyPrinter.delab witnessQ

      verifyRemainderLogic witnessTerm isZeroTarget

    | _ =>
      dbg_trace "Goal is not a `lex.IsRemainder` proposition."
      throwUnsupportedSyntax

-- syntax (name := remainderTactic) "remainder" ("?")? (ppSpace "[" term,* "]")? : tactic
syntax (name := remainderNormal) "remainder" (ppSpace "[" term,* "]")? : tactic
-- syntax (name := remainderTry) "remainder?" (ppSpace "[" term,* "]")? : tactic

@[tactic remainderNormal, tactic remainderTry]
def evalRemainderTactic : Tactic := fun stx => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)

  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder
      _ $R $instCommSemiring $poly $vars $r) =>

      let isZeroTarget ← isDefEq r q(0)

      let hasQuestionMark := !stx[1].isNone

      let userArgs? : Option (Array Syntax) :=
        if stx[2].isNone then none
        else some stx[2][1].getSepArgs

      let (witnessSyntax, shouldSuggest, suggestionArgs) ← match userArgs? with
        | some args =>
          let argsTerms : Array (TSyntax `term) := args.map fun s => ⟨s⟩
          let listSyntax ← `([$argsTerms,*])

          pure (listSyntax, false, argsTerms)

        | none => do
          let parsedPoly ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
          let varsList ← parseSet (σ := σ) (R := R) (r := instCommSemiring) vars

          let varsStr := s!"{varsList}"
          let sage_result ← runSage (.remainder parsedPoly varsStr)
          logInfo m!"[DEBUG Remainder parsedPoly] : {parsedPoly}"
          logInfo m!"[DEBUG Remainder varsList] :{varsList}"
          logInfo m!"[DEBUG Remainder sage_result] :{sage_result}"

          let result := Json.parse sage_result
          let sage_json_result ← parseJson result
          let Except.ok arr := sage_json_result.getArr? | failure

          let processList := arr.mapM mkPolyExpr
          let exprList ← processList
          let exprList := exprList.toList

          let listQ : Q(List (MvPolynomial ℕ ℚ)) := liftListQ exprList
          let listSyntax : Term ← Lean.PrettyPrinter.delab listQ

          let argsTerms : Array Term ← exprList.toArray.mapM fun e => do
             Lean.PrettyPrinter.delab e

          pure (listSyntax, hasQuestionMark, argsTerms)

      let witness : Term ← `(List.get $witnessSyntax)
      verifyRemainderLogic witness isZeroTarget

      if shouldSuggest then

        let suggestion : TSyntax `tactic ← `(tactic| remainder [ $suggestionArgs,* ])
        addSuggestion stx suggestion

    | _ => throwUnsupportedSyntax

-- @[tactic remainderNormal, tactic remainderTry]
-- def evalRemainderTactic : Tactic := fun stx => do
--   let goal ← Lean.Elab.Tactic.getMainGoal
--   let t ← goal.getType
--   let t ← checkTypeQ t q(Prop)

--   match t with
--   | none => return
--   | some expr =>
--     match expr with
--     | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder
--        _ $R $instCommSemiring $poly $vars $r) =>

--       let isZeroTarget ← isDefEq r q(0)

--       let hasQuestionMark := !stx[1].isNone

--       let userArgs? : Option (Array Syntax) :=
--         if stx[2].isNone then
--           none
--         else
--           some stx[2][1].getSepArgs

--       let (witnessSyntax, shouldSuggest) ← match userArgs? with
--         | some args =>
--           -- user provide: remainder [h1, h2, ...]
--           let argsTerms : Array (TSyntax `term) := args.map fun s => ⟨s⟩

--           let listSyntax ← `([$argsTerms,*])

--           pure (listSyntax, false)

--         | none => do
--           -- user don't provide
--           let parsedPoly ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
--           let varsList ← parseSet (σ := σ) (R := R) (r := instCommSemiring) vars

--           let varsStr := s!"{varsList}"
--           let sage_result ← runSage (.remainder parsedPoly varsStr)


--           let result := Json.parse sage_result
--           let sage_json_result ← parseJson result
--           let Except.ok arr := sage_json_result.getArr? | failure


--           let processList := arr.mapM mkPolyExpr
--           let exprList ← processList
--           let exprList := exprList.toList

--           let listQ : Q(List (MvPolynomial ℕ ℚ)) := liftListQ exprList
--           let listSyntax : Term ← Lean.PrettyPrinter.delab listQ

--           pure (listSyntax, hasQuestionMark)

--       let witness : Term ← `(List.get $witnessSyntax)

--       verifyRemainderLogic witness isZeroTarget

--       if shouldSuggest then
--         let suggestion : TSyntax `tactic ← `(tactic| remainder [ $args,* ])
--         addSuggestion stx suggestion
--         -- let suggestion : TSyntax `tactic ← `(tactic| remainder $witnessSyntax)
--         -- addSuggestion stx suggestion

--     | _ =>
--       throwError "Goal is not a `lex.IsRemainder` proposition."
-- @[tactic remainderTactic]
-- def evalRemainderTactic : Tactic := fun stx => do
--   let goal ← Lean.Elab.Tactic.getMainGoal
--   let t ← goal.getType
--   let t ← checkTypeQ t q(Prop)

--   match t with
--   | none => return
--   | some expr =>
--     match expr with
--     | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder
--       _ $R $instCommSemiring $poly $vars $r) =>

--       let isZeroTarget ← isDefEq r q(0)
--       let isTry := !stx[1].isNone

--       let userTerm? : Option Term :=
--         if stx[2].isNone then none
--         else some ⟨stx[2][0]⟩

--       let ((witnessSyntax, shouldSuggest) : (Term × Bool)) ← match userTerm? with
--         | some userList =>
--           pure (userList, false)

--         | none => do

--           let parsedPoly ←  parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
--           let varsList ←  parseSet (σ := σ) (R := R) (r := instCommSemiring) vars

--           let sage_result ← runSage (.remainder parsedPoly s!"{varsList}")
--           let result := Json.parse s!"{sage_result}"
--           let sage_json_result ← parseJson result
--           let Except.ok arr := sage_json_result.getArr? | failure

--           let processList := arr.mapM mkPolyExpr
--           let exprList ←  processList
--           let exprList := exprList.toList
--           let listQ : Q(List (MvPolynomial ℕ ℚ)) := liftListQ exprList
--           let listSyntax : Term ← Lean.PrettyPrinter.delab listQ

--           pure (listSyntax, isTry)

--       let witness : Term ← `(List.get $witnessSyntax)

--       verifyRemainderLogic witness isZeroTarget

--       if shouldSuggest then
--         let suggestion : TSyntax `tactic ← `(tactic| remainder $witnessSyntax)
--         addSuggestion stx suggestion

--     | _ =>
--       throwError "Goal is not a `lex.IsRemainder` proposition."




elab "remainder_zero" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder
      _ $R $instCommSemiring $poly $vars $r) =>

      let parsedPoly ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
      let varsList ← parseSet (σ := σ) (R := R) (r := instCommSemiring) vars
      -- let parsedR ← parsePoly r

      let sage_result ← runSage (.remainder parsedPoly s!"{varsList}")

      let result := Json.parse s!"{sage_result}"
      logInfo m!"[DEBUG] sage_json_result: {result}"
      let sage_json_result ← parseJson result
      logInfo m!"[DEBUG] sage_json_result after parsing: {sage_json_result}"
      let Except.ok arr := sage_json_result.getArr? | failure
      logInfo m!"Arr: {arr[0]!}"

      let processList := arr.mapM mkPolyTerm
      let resultArray : Array Term ← processList
      let xs : Term ← `(term| [$resultArray:term,*].get)


      let runUse := fun x => do
        Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]

      evalTactic (← `(tactic|
         simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
      ))
      evalTactic (← `(tactic|
         rw [isRemainder_range_fin, ← exists_and_right]
      ))
      runUse xs
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


elab "remainder_neq_zero" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder
      _ $R $instCommSemiring $poly $vars $r) =>
      logInfo m!"[DEBUG] vars = {vars}"

      let parsedPoly ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
      let varsList ← parseSet (σ := σ) (R := R) (r := instCommSemiring) vars
      -- let parsedR ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) r

      logInfo m!"parsed vars: {varsList}"
      logInfo m!"parsed polynomial: {parsedPoly}"

      let sage_result ← runSage (.remainder parsedPoly s!"{varsList}")

      logInfo m!"[DEBUG] check sage_result 11_26: {sage_result}"


      let result := Json.parse s!"{sage_result}"
      let sage_json_result ← parseJson result
      let Except.ok arr := sage_json_result.getArr? | failure

      let processList := arr.mapM mkPolyExpr
      let resultArray ← processList
      let xs := resultArray.toList
      let get : Q((xs : List (MvPolynomial ℕ ℚ)) ->
        Fin xs.length -> MvPolynomial ℕ ℚ) := q(List.get)
      let xs : Q(List (MvPolynomial ℕ ℚ)) := liftListQ xs
      let xs_get := q($get $xs)

      let xs_get <- Lean.PrettyPrinter.delab xs_get
      let runUse := fun x => do
        Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]

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

elab "basis" : tactic  => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  logInfo m!"[DEBUG `basis` Goal] : {goal}"
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsGroebnerBasis
      _ $R $instCommSemiring $basis $ideal) =>

      let basislist <- parseSet basis
      logInfo m!"[DEBUG `basis`] : {basislist}"
      -- dbg_trace "parsed basis: {basislist}"

      let sage_result ← runSage (.basis s!"{basislist}")
      logInfo m!"[Sage Result] {sage_result}"
      let result := Json.parse s!"{sage_result}"
      let sage_json_result ← parseJson result

      let Except.ok arr := sage_json_result.getArr? | failure

      let parsedTermsArray ← arr.mapM mkPolyListTerm
      logInfo m!"[DEBUG Basis] parsedTermsArray: {parsedTermsArray}"

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
        -- logInfo m!"[DEBUG Basis] check {i}"
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
            -- with_unfolding_all decide
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
    (g : R) (f : M) :
    g • f ∈ Submodule.span R {f} :=
  Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

variable {R : Type*} [CommRing R] {I : Ideal R} {a : R} {B : Set R}

lemma Ideal.insert_le_of_mem_of_le :
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

        logInfo m!"{I_gens_list}"
        logInfo m!"{J_gens_list}"

        let sage_result ← runSage (.ideal s!"{I_gens_list}" s!"{J_gens_list}")
        logInfo m!"[DEBUG `ideal` sage result] : {sage_result}"
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
              let termExpr ← mkPolyExpr coeff
              Lean.PrettyPrinter.delab termExpr

            -- logInfo m!"[DEBUG Ideal] coeff_arr : {coeff_arr}"
            -- let termsArray : Array Term ← coeff_arr.mapM fun coeff => do
            --   mkPolyTerm coeff

            -- logInfo m!"[DEBUG Ideal] poly to use : {termsArray}"
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


elab "basis'" : tactic  => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  logInfo m!"[DEBUG `basis` Goal] : {goal}"
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsGroebnerBasis
      _ $R $instCommSemiring $basis $ideal) =>
      let basis_term ← Lean.PrettyPrinter.delab basis
      let ideal_term ← Lean.PrettyPrinter.delab ideal

      let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)

      logInfo m!"[DEBUG] basis {basis_term}"
      logInfo m!"[DBEUG] ideal {ideal_term}"
      logInfo m!"[DEBUG] polyType : {polyType}"

      evalTactic (← `(tactic|
        have h_gb :
        letI basis := ($basis_term : Set $polyType)
        lex.IsGroebnerBasis basis (Ideal.span basis) := by
          basis
      ))

      evalTactic (← `(tactic|
        have h_ideal : Ideal.span ($basis_term) = $ideal_term := by
          ideal
      ))

      evalTactic (← `(tactic|
        simp [h_ideal] at h_gb
      ))

      evalTactic (← `(tactic|
        exact h_gb
      ))




def mkSetSyntaxFromTerms (terms : Array Term) : MetaM Term := do
  if terms.isEmpty then
    `(∅)
  else
    let termStrs ← terms.mapM fun t => do
      let fmt ← Lean.PrettyPrinter.ppTerm t
      return fmt.pretty

    let setStr := "{" ++ String.intercalate ", " termStrs.toList ++ "}"

    let env ← getEnv
    match Lean.Parser.runParserCategory env `term setStr with
    | Except.ok stx => return ⟨stx⟩
    | Except.error e => throwError s!"Failed to create set syntax: {e}"

syntax (name := groebnerMembership) "ideal_membership" : tactic
@[tactic groebnerMembership]
def evalGroebnerMembership : Tactic := fun stx => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)

  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q($f ∈ ($I : @Ideal (@MvPolynomial $σ $R $i) $ring)) =>

      match I with
      | ~q(Ideal.span $I_gens) =>
        let I_gens_list ←  parseSet I_gens
        let f_str ← parsePoly f

        let sage_coeff ← runSage (.Idealmem f_str s!"{I_gens_list}")

        let coeff_list := Json.parse s!"{sage_coeff}"
        let coeff_list ← parseJson coeff_list
        let Except.ok coeff_arr := coeff_list.getArr? | failure
        let coeff_expr_list := coeff_arr.mapM mkPolyExpr

        let coeff_expr_list ← coeff_expr_list
        let coeff_expr_list := coeff_expr_list.toList

        let coeff_terms : Array Term ← coeff_expr_list.toArray.mapM fun e => do
          Lean.PrettyPrinter.delab e

        evalTactic (← `(tactic|
          submodule_span [ $coeff_terms,* ]
        ))

        evalTactic (← `(tactic|
          decide +kernel
        ))


        -- for coeff in coeff_arr do
        --   logInfo m!"[DEBUG] : {coeff}"

        -- let sage_gb ← runSage (.GBasis s!"{I_gens_list}")

        -- let gb := Json.parse s!"{sage_gb}"
        -- let gb ← parseJson gb
        -- let Except.ok gb_arr := gb.getArr? | failure

        -- let exprArray ← gb_arr.mapM fun jsonElem => mkPolyExpr jsonElem

        -- let argsTerms : Array Term ← exprArray.mapM fun e => Lean.PrettyPrinter.delab e
        -- let f_term ← Lean.PrettyPrinter.delab f
        -- let I_term ← Lean.PrettyPrinter.delab I

        -- -- logInfo m!"f_term : {f_term}"
        -- -- logInfo m!"I_term : {I_term}"

        -- let setSyntax ← mkSetSyntaxFromTerms argsTerms
        -- -- logInfo m!"setSyntax {setSyntax}"

        -- let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)


        -- evalTactic (← `(tactic|

        --   have h_gb : lex.IsGroebnerBasis ($setSyntax : Set $polyType) (Ideal.span $setSyntax) := by
        --     simp only [_root_.ne_eq, _root_.one_ne_zero,
        --     _root_.not_false_eq_true,
        --     _root_.div_self, MvPolynomial.C_1,
        --     Fin.isValue, _root_.pow_one, _root_.one_mul,
        --     _root_.zero_add, _root_.div_one,
        --     MvPolynomial.C_neg, ← _root_.sub_eq_add_neg]
        --     basis
        -- ))

        -- evalTactic (← `(tactic|
        --   have h_rm : lex.IsRemainder ($f_term) ($setSyntax : Set $polyType) 0 := by
        --     simp
        --     remainder
        -- ))

        -- evalTactic (← `(tactic|
        --   have h_ideal : $I_term = Ideal.span ($setSyntax : Set $polyType) := by
        --     simp
        --     first | done | ideal
        -- ))

        -- evalTactic (← `(tactic|
        --   have h_gb' : lex.IsGroebnerBasis ($setSyntax : Set $polyType) $I_term := by
        --     rw [h_ideal]
        --     exact h_gb
        -- ))

        -- evalTactic (← `(tactic|
        --   apply (isRemainder_zero_iff_mem_ideal_of_isGroebner' h_gb').mp h_rm
        -- ))
      | _ => throwError "Expect Ideal.span, but got {I}"

    | ~q(¬($f ∈ ($I : @Ideal (@MvPolynomial $σ $R $i) $ring))) =>

      match I with
      | ~q(Ideal.span $I_gens) =>
        let f_str ←  parsePoly f

        let I_gens_list ←  parseSet I_gens

        logInfo m!"[DBEUG I GENS LIST]{I_gens_list}"
        let sage_gb ← runSage (.GBasis s!"{I_gens_list}")
        logInfo m!"[GB SAGE RESULT] : {sage_gb}"
        let gb := Json.parse s!"{sage_gb}"
        let gb ← parseJson gb
        let Except.ok gb_arr := gb.getArr? | failure

        let exprArray ← gb_arr.mapM fun jsonElem => mkPolyExpr jsonElem

        let argsTerms : Array Term ← exprArray.mapM fun e => Lean.PrettyPrinter.delab e

        let sage_rm ← runSage (.GRemainder f_str s!"{I_gens_list}")
        -- logInfo m!"[REMAINDER SAGE RESULT] : {sage_rm}"

        let Except.ok parsed := Lean.Json.parse sage_rm | failure
        let Except.ok p := Lean.fromJson? (α := Poly.Polynomial) parsed | failure
        let instOfNat ← Qq.synthInstanceQ q((n : Nat) → OfNat Nat n)
        let instField ← Qq.synthInstanceQ q(Field ℚ)
        let rm := p.mkQ q(Nat) instOfNat q(ℚ) instField

        let f_term ← Lean.PrettyPrinter.delab f
        let I_term ← Lean.PrettyPrinter.delab I
        let rm_term ← Lean.PrettyPrinter.delab rm
        logInfo m!"[DEBUG f_term] : {f_term}"
        logInfo m!"[DEBUG I_term] : {I_term}"
        logInfo m!"[DEBUG rm_term] : {rm_term}"

        let setSyntax ← mkSetSyntaxFromTerms argsTerms

        logInfo m!"[DEBUG `setSyntax`] : {setSyntax}"

        let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)

        logInfo m!"[DEBUG `polyType`] : {polyType}"
        evalTactic (← `(tactic|
          have h_gb : lex.IsGroebnerBasis ($setSyntax : Set $polyType) (Ideal.span $setSyntax) := by
            simp only [_root_.ne_eq, _root_.one_ne_zero,
                  _root_.not_false_eq_true,
                  _root_.div_self, MvPolynomial.C_1,
                  Fin.isValue, _root_.pow_one, _root_.one_mul,
                  _root_.zero_add, _root_.div_one,
                  MvPolynomial.C_neg, ← _root_.sub_eq_add_neg]
            basis
        ))

        logInfo m!"[I Term] {I_term}"
        logInfo m!"[setSyntax] {setSyntax}"
        logInfo m!"[polyType] {polyType}"

        evalTactic (← `(tactic|
          have h_ideal : $I_term = Ideal.span ($setSyntax : Set $polyType) := by
            simp only [_root_.ne_eq, _root_.one_ne_zero,
                  _root_.not_false_eq_true,
                  _root_.div_self, MvPolynomial.C_1,
                  Fin.isValue, _root_.pow_one, _root_.one_mul,
                  _root_.zero_add, _root_.div_one,
                  MvPolynomial.C_neg, ← _root_.sub_eq_add_neg]
            first | done | ideal
        ))

        evalTactic (← `(tactic|
          have h_gb' : lex.IsGroebnerBasis ($setSyntax : Set $polyType) $I_term := by
            rw [h_ideal]
            exact h_gb
        ))

        evalTactic (← `(tactic|
         have h_rm : lex.IsRemainder ($f_term : $polyType)
         ($setSyntax : Set $polyType) ($rm_term : $polyType ) := by
            simp only [_root_.ne_eq, _root_.one_ne_zero,
                  _root_.not_false_eq_true,
                  _root_.div_self, MvPolynomial.C_1,
                  Fin.isValue, _root_.pow_one, _root_.one_mul,
                  _root_.zero_add, _root_.div_one,
                  MvPolynomial.C_neg, ← _root_.sub_eq_add_neg]
            remainder
        ))

        evalTactic (← `(tactic|
          by_contra h_mem
        ))

        evalTactic (← `(tactic|
          have neq : ($rm_term : $polyType) ≠ (0 : $polyType) := by
            decide +kernel
        ))

        evalTactic (← `(tactic|
          have eq : ($rm_term : $polyType) = (0 : $polyType) := by
            exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h_gb' h_rm).mpr h_mem
        ))

        evalTactic (← `(tactic|
          contradiction
        ))
      | _ => throwError "Expect Ideal.span, but got {I}"

    | _ => throwError "Goal must be of form `f ∈ Ideal.span S` or form of `f ∉ Ideal.span S`"


def insertPolyToSetExpr {u v : Level} {σ : Q(Type u)} {R : Q(Type v)}
    {r : Q(CommSemiring $R)}
    (poly : Q(MvPolynomial $σ $R))
    (set : Q(Set (MvPolynomial $σ $R))) : MetaM Q(Set (MvPolynomial $σ $R)) := do

  return q(Insert.insert $poly $set)

partial def appendPolyToSetExpr {u v : Level} {σ : Q(Type u)} {R : Q(Type v)}
    {r : Q(CommSemiring $R)}
    (poly : Q(MvPolynomial $σ $R))
    (set : Q(Set (MvPolynomial $σ $R))) : MetaM Q(Set (MvPolynomial $σ $R)) := do

  match set with
  | ~q(∅) =>
      return q(Insert.insert $poly ∅)

  | ~q(Insert.insert $head $tail) =>
      let newTail ← appendPolyToSetExpr (r := r) poly tail
      return q(Insert.insert $head $newTail)

  | _ =>
      return q(Insert.insert $poly $set)

partial def liftPolySet {u : Level} (n : Q(Nat)) (R : Q(Type u))
    (instR : Q(CommSemiring $R))
    (set : Q(Set (MvPolynomial (Fin $n) $R))) : MetaM Q(Set (MvPolynomial (Fin ($n + 1)) $R)) := do
  match set with
  | ~q(∅) =>
      return q(∅ : Set (MvPolynomial (Fin ($n + 1)) $R))

  | ~q(Insert.insert $head $tail) =>
      let head_lifted : Q(MvPolynomial (Fin ($n + 1)) $R) :=
        q(@MvPolynomial.rename (Fin $n) (Fin ($n + 1)) $R $instR Fin.castSucc $head)

      let tail_lifted ← liftPolySet n R instR tail
      return q(Insert.insert $head_lifted $tail_lifted)

  | _ =>
      return q(Set.image (@MvPolynomial.rename (Fin $n) (Fin ($n + 1)) $R $instR Fin.castSucc) $set)


open MvPolynomial MonomialOrder Ideal

variable {K : Type*} [Field K] {σ : Type*}
variable {T : Type*} [DecidableEq T]
variable {R : Type*} [CommRing R] {σ : Type*}


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
      rw [_root_.mul_pow]
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

    rw [_root_.one_mul] at hg
    rw [IsLocalization.eq_iff_exists (Submonoid.powers f) R_f] at hg
    obtain ⟨c, h_and⟩ := hg
    dsimp at h_and
    have h_mul_pow : ↑c * l ∈ Submonoid.powers f := Submonoid.mul_mem _ c.2 hl
    obtain ⟨n, hn⟩ := h_mul_pow
    use n
    dsimp at hn
    rw [hn, h_and]
    exact Ideal.mul_mem_left I (↑c) g_val.2


syntax (name := radicalMembership) "radical_membership" : tactic
@[tactic radicalMembership]
def evalradicalMembership : Tactic := fun stx => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)

  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q($f ∈ @Ideal.radical
            (@MvPolynomial $σ $R $i)
            $ring
            (@Ideal.span
              (@MvPolynomial $σ $R $i)
              (@CommSemiring.toSemiring
                 (@MvPolynomial $σ $R $i)
                 $ring)
              $I_gens)) =>
      let f_str ←  parsePoly f
      let I_gens_list ←  parseSet I_gens



      let n ← runSage (.radical f_str s!"{I_gens_list}")

      let n_val : Nat := n.trim.toNat!
      let n_expr := mkNatLit n_val
      let n_term ← Lean.PrettyPrinter.delab n_expr


      evalTactic (← `(tactic|
          rw [Ideal.mem_radical_iff]
        ))

      evalTactic (← `(tactic|
          use $n_term:term
        ))

      evalTactic (← `(tactic|
          ideal_membership
        ))

      logInfo m!"{n}"

      pure 0

    | ~q(¬ ($f ∈ @Ideal.radical
          (@MvPolynomial (Fin $n) $R $i)
          $ring
          (@Ideal.span
            (@MvPolynomial (Fin $n) $R $i)
            (@CommSemiring.toSemiring
                (@MvPolynomial (Fin $n) $R $i)
                $ring)
            $I_gens))) =>
      let u_level : Level ← getLevel R

      let σ_new : Q(Type) := q(Fin ($n + 1))

      let n_term : Term ← Lean.PrettyPrinter.delab n
      let f_term ← Lean.PrettyPrinter.delab f
      let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial (Fin ($n + 1)) $R)

      let _inst_R ← synthInstanceQ q(CommRing (MvPolynomial (Fin ($n + 1)) $R))

      let one_sub_tf_expr := q(
        (1 : MvPolynomial (Fin ($n + 1)) $R) -
         (MvPolynomial.X (Fin.last $n) * (MvPolynomial.rename Fin.castSucc $f))
      )

      let one_sub_tf_term : Term ← Lean.PrettyPrinter.delab one_sub_tf_expr

      let I_gens_lifted ← liftPolySet n R i I_gens
      let new_set_expr ← @insertPolyToSetExpr
          Level.zero
          u_level
          σ_new
          R
          i
          one_sub_tf_expr
          I_gens_lifted

      let new_set_term : Term ← Lean.PrettyPrinter.delab new_set_expr

      logInfo m!"[DEBUG NEW SET TERM] : {new_set_term} "

      evalTactic (← `(tactic|
      let g : Fin $n_term → Fin ($n_term + 1) := Fin.castSucc
      ))

      evalTactic (← `(tactic|
      let t : Fin ($n_term + 1) := Fin.last $n_term
      ))

      evalTactic (← `(tactic|
      by_contra h
      ))

      evalTactic (← `(tactic|
      rw [Rabinovich_method' g t Fin.castSucc_ne_last (Fin.castSucc_injective $n_term)] at h
      ))

      evalTactic (← `(tactic|
      rw [Ideal.map_span] at h
      ))

      evalTactic (← `(tactic|
      rw [← Ideal.span_union] at h
      ))

      -- evalTactic (← `(tactic|
      -- rw [Set.image_singleton, Set.singleton_union] at h
      -- ))

      -- evalTactic (← `(tactic|
      -- simp only [rename_X,  t] at h
      -- ))

      evalTactic (← `(tactic|
      conv at h =>
        repeat rw [Set.image_insert_eq]
        try rw [Set.image_singleton]
        try rw [Set.union_singleton]
      ))

      evalTactic (← `(tactic|
      dsimp [g, t] at h
      ))

      evalTactic (← `(tactic|
      simp only [Fin.isValue, map_add, rename_X, Fin.reduceCastSucc, map_one,
              Fin.castSucc_zero, Fin.castSucc_one, Fin.castSucc_succ] at h
      ))

      evalTactic (← `(tactic|
      have h₁ : 1 ∉ Ideal.span  ($new_set_term : Set <| MvPolynomial (Fin ($n_term + 1)) ℚ) := by
        conv =>
          repeat rw [Set.image_insert_eq]
          try rw [Set.image_singleton]
          try rw [Set.union_singleton]
        simp
        ideal_membership
      ))

      logInfo m!"{new_set_term}"

      evalTactic (← `(tactic|
      simp at h₁
      ))

      evalTactic (← `(tactic|
      exact h₁ h
      ))


    | _ => throwError "Goal must be of form `f ∈ (Ideal.span S).
    radical` or form of `f ∉ (Ideal.span S).radical`"




end IsRemainder


open MvPolynomial MonomialOrder

set_option maxHeartbeats 2000000 in
example:
  lex.IsGroebnerBasis ({X 1^3 - X 2^2, X 0^2 - X 1, X 0*X 1 - X 2, X 0*X 2 - X 1^2} : Set <| MvPolynomial (Fin 3) ℚ)  (Ideal.span ({X 0^2 - X 1, X 0^3 - X 2} : Set <| MvPolynomial (Fin 3) ℚ)):= by
   basis'


namespace Mathlib.Tactic.IsGroebner

end IsGroebner

end Tactic

end Mathlib
