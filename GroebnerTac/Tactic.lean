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


def runSage (task : SageTask) : IO String := do

  let (scriptName, scriptArgs) := match task with
    | .remainder poly rem  => ("Remainder.sage", #["-p", poly, "-d", rem])
    | .basis set           => ("Basis.sage",     #["-s", set])
    | .ideal genI genJ     => ("Ideal.sage",     #["-I", genI, "-J", genJ])
    | .GBasis set          => ("GBasis.sage",    #["-s", set])
    | .GRemainder poly set => ("GRemainder.sage", #["-p", poly, "-s", set])
    | .radical poly set    => ("Radical.sage",  #["-p", poly, "-s", set])

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
In this section, we define the some functions to parse `Expr` in Lean
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

  | ~q(@OfNat.ofNat _ $b $n) =>
    logInfo "go to this branch"
    pure s!"{b}"

  | _ =>
    pure s!"{e}"

#eval parsePoly q(1: MvPolynomial Nat Nat)

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

  -- [Common Step] Goal 2: Prove the degree condition
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
          logInfo m!"{parsedPoly}"
          logInfo m!"{varsList}"
          logInfo m!"{sage_result}"

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
      -- logInfo m!"[DEBUG] {xs}"
      let xs_get := q($get $xs)
      -- logInfo m!"[DEBUG] {xs_get}"
      let xs_get <- Lean.PrettyPrinter.delab xs_get
      -- logInfo m!"[CHECK {xs_get}]"
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
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsGroebnerBasis
      _ $R $instCommSemiring $basis $ideal) =>

      let basislist <- parseSet basis
      dbg_trace "parsed basis: {basislist}"

      let sage_result ← runSage (.basis s!"{basislist}")
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

        let sage_gb ← runSage (.GBasis s!"{I_gens_list}")
        let gb := Json.parse s!"{sage_gb}"
        let gb ← parseJson gb
        let Except.ok gb_arr := gb.getArr? | failure

        let exprArray ← gb_arr.mapM fun jsonElem => mkPolyExpr jsonElem

        let argsTerms : Array Term ← exprArray.mapM fun e => Lean.PrettyPrinter.delab e
        let f_term ← Lean.PrettyPrinter.delab f
        let I_term ← Lean.PrettyPrinter.delab I

        -- logInfo m!"f_term : {f_term}"
        -- logInfo m!"I_term : {I_term}"

        let setSyntax ← mkSetSyntaxFromTerms argsTerms
        -- logInfo m!"setSyntax {setSyntax}"

        let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)



        evalTactic (← `(tactic|
          have h_gb : lex.IsGroebnerBasis ($setSyntax : Set $polyType) (Ideal.span $setSyntax) := by
            simp
            basis
        ))

        evalTactic (← `(tactic|
          have h_rm : lex.IsRemainder ($f_term) ($setSyntax : Set $polyType) 0 := by
            simp
            remainder
        ))

        evalTactic (← `(tactic|
          have h_ideal : $I_term = Ideal.span ($setSyntax : Set $polyType) := by
            simp
            first | done | ideal
        ))

        evalTactic (← `(tactic|
          have h_gb' : lex.IsGroebnerBasis ($setSyntax : Set $polyType) $I_term := by
            rw [h_ideal]
            exact h_gb
        ))

        evalTactic (← `(tactic|
          apply (isRemainder_zero_iff_mem_ideal_of_isGroebner' h_gb').mp h_rm
        ))
      | _ => throwError "Expect Ideal.span, but got {I}"

    | ~q(¬($f ∈ ($I : @Ideal (@MvPolynomial $σ $R $i) $ring))) =>

      match I with
      | ~q(Ideal.span $I_gens) =>
        let f_str ←  parsePoly f

        let I_gens_list ←  parseSet I_gens

        let sage_gb ← runSage (.GBasis s!"{I_gens_list}")
        let gb := Json.parse s!"{sage_gb}"
        let gb ← parseJson gb
        let Except.ok gb_arr := gb.getArr? | failure

        let exprArray ← gb_arr.mapM fun jsonElem => mkPolyExpr jsonElem

        let argsTerms : Array Term ← exprArray.mapM fun e => Lean.PrettyPrinter.delab e

        let sage_rm ← runSage (.GRemainder f_str s!"{I_gens_list}")

        let Except.ok parsed := Lean.Json.parse sage_rm | failure
        let Except.ok p := Lean.fromJson? (α := Poly.Polynomial) parsed | failure
        let instOfNat ← Qq.synthInstanceQ q((n : Nat) → OfNat Nat n)
        let instField ← Qq.synthInstanceQ q(Field ℚ)
        let rm := p.mkQ q(Nat) instOfNat q(ℚ) instField

        let f_term ← Lean.PrettyPrinter.delab f
        let I_term ← Lean.PrettyPrinter.delab I
        let rm_term ← Lean.PrettyPrinter.delab rm
        -- logInfo m!"f_term : {f_term}"
        -- logInfo m!"I_term : {I_term}"
        -- logInfo m!"rm_term : {rm_term}"

        let setSyntax ← mkSetSyntaxFromTerms argsTerms

        let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)

        evalTactic (← `(tactic|
          have h_gb : lex.IsGroebnerBasis ($setSyntax : Set $polyType) (Ideal.span $setSyntax) := by
            simp
            basis
        ))

        evalTactic (← `(tactic|
          have h_ideal : $I_term = Ideal.span ($setSyntax : Set $polyType) := by
            simp
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
            simp
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
    -- | ~q(¬ ($f ∈ @Ideal.radical
    --         (@MvPolynomial $σ $R $i)
    --         $ring
    --         $I_gens)) =>
    | ~q(¬ ($f ∈ @Ideal.radical
            (@MvPolynomial $σ $R $i)
            $ring
            (@Ideal.span
              (@MvPolynomial $σ $R $i)
              (@CommSemiring.toSemiring
                  (@MvPolynomial $σ $R $i)
                  $ring)
              $I_gens))) =>

      let f_term ← Lean.PrettyPrinter.delab f
      let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)

      -- let _inst_R : Q(CommRing $R) ← synthInstanceQ q(CommRing $R)
      let _inst_R ← synthInstanceQ q(CommRing (MvPolynomial $σ $R))

      let one_sub_f_expr := q(((1 : MvPolynomial $σ $R) - $f : MvPolynomial $σ $R))
      let one_sub_f_term : Term ← Lean.PrettyPrinter.delab one_sub_f_expr
      let new_set_expr ← insertPolyToSetExpr one_sub_f_expr I_gens
      let new_set_term : Term ← Lean.PrettyPrinter.delab new_set_expr
      let I_gens_term : Term ← Lean.PrettyPrinter.delab I_gens
      logInfo m!"[NEW SET TERM] : {new_set_term}"

      let f_str ←  parsePoly f
      let I_gens_list ←  parseSet I_gens

      logInfo m!"{f_str}"
      logInfo m!"{I_gens_list}"

      evalTactic (← `(tactic|
          by_contra h
        ))
      evalTactic (← `(tactic|
          rw [Ideal.mem_radical_iff] at h
        ))
      evalTactic (← `(tactic|
          rcases h with ⟨n, hn⟩
        ))
      evalTactic (← `(tactic|
          have h₁: (1: $polyType) = ($f_term) ^ n + (1 - ($f_term)^n) := by
            rw [add_sub_cancel]
        ))
      evalTactic (← `(tactic|
          have h₂: ((1 : $polyType) - $f_term) ∣ ((1 : $polyType) - ($f_term)^n) := by
            exact one_sub_dvd_one_sub_pow ($f_term) n
        ))

      -- evalTactic (← `(tactic|
      --     have h₃: 1 ∈ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
      --       rcases h₂ with ⟨p, hp⟩
      --       rw [hp] at h₁
      --       have l₁ : X 2 ^ n ∈ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
      --         have t₁: Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) ≤ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
      --           apply Ideal.span_mono
      --           simp
      --         exact t₁ hn
      --       have l₂ : (1 - X 2) * p ∈ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
      --         apply Ideal.mul_mem_right
      --         have t₁: Ideal.span ({1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) ≤ Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) := by
      --           apply Ideal.span_mono
      --           simp
      --         have t₂: (1 - X 2) ∈ Ideal.span ({1-X 2} : Set (MvPolynomial (Fin 3) ℚ)) := by
      --           exact Ideal.mem_span_singleton_self (1 - X 2)
      --         exact t₁ t₂
      --       rw [h₁]
      --       apply Ideal.add_mem _ l₁ l₂
      --       rw [← h₁]
      --       refine ⟨Ideal.span {1 - X 2, X 0, X 1}, ?_⟩
      --       ext x
      --       constructor
      --       · intro h
      --         simp at h
      --         have l: ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ)) ⊆ (Ideal.span ({1 - X 2, X 0, X 1} : Set (MvPolynomial (Fin 3) ℚ))) := by
      --           exact Ideal.subset_span
      --         exact h l
      --       · intro h
      --         simp
      --         intro a
      --         simp at h
      --         exact h
      --   ))

      evalTactic (← `(tactic|
          have h₃: 1 ∈ Ideal.span ($new_set_term : Set $polyType) := by
            rcases h₂ with ⟨p, hp⟩
            rw [hp] at h₁
            have l₁ : ($f_term : $polyType) ^ n ∈ Ideal.span ($new_set_term : Set $polyType) := by
              have t₁: Ideal.span ($I_gens_term : Set $polyType)
              ≤ Ideal.span ($new_set_term : Set $polyType) := by
                apply Ideal.span_mono
                simp
              exact t₁ hn
            have l₂ : ((1 : $polyType) - ($f_term : $polyType)) * p
            ∈ Ideal.span ($new_set_term : Set $polyType) := by
              apply Ideal.mul_mem_right
              have t₁: Ideal.span ({(1 : $polyType) - ($f_term : $polyType)} : Set $polyType)
               ≤ Ideal.span ($new_set_term : Set $polyType) := by
                apply Ideal.span_mono
                simp
              have t₂: ((1 : $polyType) - ($f_term : $polyType))
               ∈ Ideal.span ({(1 : $polyType) - ($f_term : $polyType)} : Set $polyType) := by
                exact Ideal.mem_span_singleton_self (1 - $f_term)
              exact t₁ t₂
            rw [h₁]
            apply Ideal.add_mem _ l₁ l₂
            rw [← h₁]
            refine ⟨Ideal.span ($new_set_term), ?_⟩
            ext x
            constructor
            · intro h
              simp at h
              have l: ($new_set_term : Set $polyType) ⊆
              (Ideal.span ($new_set_term : Set $polyType)) := by
                exact Ideal.subset_span
              exact h l
            · intro h
              simp
              intro a
              simp at h
              exact h
        ))

      evalTactic (← `(tactic|
          have h₄ : lex.IsRemainder (1: $polyType)
            ($new_set_term : Set $polyType) 1 := by
            remainder
        ))

      evalTactic (← `(tactic|
          have h₅ : letI basis := ($new_set_term : Set $polyType)
          lex.IsGroebnerBasis basis (Ideal.span basis) := by
            basis
        ))

      evalTactic (← `(tactic|
          have h₆ : (1: $polyType) = 0 := by
            exact (remainder_eq_zero_iff_mem_ideal_of_isGroebner' h₅ h₄).mpr h₃
        ))

      evalTactic (← `(tactic|
          simp at h₆
        ))


    | _ => throwError "Goal must be of form `f ∈ (Ideal.span S).
    radical` or form of `f ∉ (Ideal.span S).radical`"




end IsRemainder


open MvPolynomial


namespace Mathlib.Tactic.IsGroebner

end IsGroebner

end Tactic

end Mathlib
