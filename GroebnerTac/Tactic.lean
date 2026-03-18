import Mathlib

import MonomialOrderedPolynomial
import Groebner.Groebner
import Groebner.ToMathlib.List

import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
import Lean.Meta.Tactic.TryThis

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
  let Except.ok p := Lean.fromJson? (α := Poly.Polynomial) parsed | failure
  let instOfNat ← Qq.synthInstanceQ q((n : Nat) → OfNat Nat n)
  let instField ← Qq.synthInstanceQ q(Field ℚ)
  let p := p.mkQ q(Nat) instOfNat q(ℚ) instField
  Lean.logInfo p


/-
We define a function to run Sage scripts in this section.
-/
inductive SageTask where
  | remainder (poly remainder : String)
  | basis (set : String)
  | ideal (genI genJ : String)
  | GBasis (set : String)
  | GRemainder (poly set : String)
  | radical (poly set : String)
  | Idealmem (poly set : String)

/-
The `SageTask` inductive type represents the different types of tasks we want to perform with Sage.
-/
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

/-
We define a function to run Sympy code
-/
inductive SympyTask where
  | remainder (poly remainder : String)
  | basis (set : String)
  | ideal (genI genJ : String)
  | GBasis (set : String)
  | GRemainder (poly set : String)
  | radical (poly set : String)
  | Idealmem (poly set : String)

def runSympy (task : SympyTask) : IO String := do
  let (scriptName, scriptArgs) := match task with
    | .remainder poly rem  => ("Remainder.py", #["-p", poly, "-d", rem])
    | .basis set           => ("Basis.py",     #["-s", set])
    | .ideal genI genJ     => ("Ideal.py",     #["-I", genI, "-J", genJ])
    | .GBasis set          => ("GBasis.py",    #["-s", set])
    | .GRemainder poly set => ("GRemainder.py", #["-p", poly, "-s", set])
    | .radical poly set    => ("Radical.py",  #["-p", poly, "-s", set])
    | .Idealmem poly set   => ("Idealmem.py", #["-p", poly, "-s", set])

  let cwd ← IO.currentDir
  let path := cwd / "Sympy" / scriptName

  -- check if the file exists
  if not (← path.pathExists) then
    dbg_trace f!"There does not exist {path}"
    throw <| IO.userError s!"could not find sage script {scriptName}"

  -- runsage
  let child ← IO.Process.spawn {
    cmd := "python3"
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


/-
We define a function to run Sage code using the API
-/
def runSageCode (code : String) : IO String.Slice := do
  let out ← IO.Process.output {
    cmd := "./.venv/bin/python",
    args := #["Runner/sage_runner.py", code]
  }

  if out.exitCode == 0 then
    return out.stdout.trimAscii
  else
    throw <| IO.userError s!"SageCell 执行失败: {out.stderr}"

def runner : IO Unit := do
  IO.println "正在向 SageMath 提交请求..."
  try
    let result ← runSageCode "factorial(3)"
    IO.println s!"计算结果:\n{result}"
  catch e =>
    IO.println e.toString

def runSage' (task : SageTask) : IO String.Slice := do
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

  if not (← path.pathExists) then
    throw <| IO.userError s!"could not find sage script {scriptName}"

  let code ← IO.FS.readFile path
  -- IO.println s!"Running Sage script {scriptName} with code:\n{code}"
  IO.println s!"xxxxxx{scriptArgs}"
  let out ← IO.Process.output {
    cmd := "./.venv/bin/python",
    args := #["-c", code] ++ scriptArgs
  }

  if out.exitCode == 0 then
    if !out.stderr.isEmpty then
      IO.println s!"Sage Warning: {out.stderr}"
    return out.stdout.trimAscii
  else
    throw <| IO.userError s!"Sage Script {scriptName} Exact fail ({out.exitCode}): {out.stderr}"

def testRemainder : IO String :=
  runSage (.remainder "X_0*X_1" "[X_0^2-X_1, 3*X_1]")

def testRemainder' : IO String.Slice :=
  runSage' (.remainder "X_0*X_1" "[X_0^2-X_1, 3*X_1]")

#eval testRemainder

-- #eval testRemainder'


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
        pure p

/-`mkPolyTerm` convert `Json` returned by sage to `Term` -/
def mkPolyTerm (jsonElement : Json) : MetaM Term := do
  let poly_result := Lean.fromJson? (α := Poly.Polynomial) jsonElement
  let poly ← parseResult poly_result
  match poly with
  | none => IO.throwServerError "There is not any result be parsed"
  | some p =>
    let p ← p.mkTerm
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

  | ~q(@OfNat.ofNat _ $b $n) =>
    pure s!"{b}"

  | _ =>

    if e.isAppOf ``HAdd.hAdd || e.isAppOf ``Add.add then
      let b := e.appArg!
      let a := e.appFn!.appArg!

      let a_q : Q(MvPolynomial $σ $R) := a
      let b_q : Q(MvPolynomial $σ $R) := b


      let aStr ← parsePoly (r:=r) a_q
      let bStr ← parsePoly (r:=r) b_q
      pure s!"({aStr} + {bStr})"

    else if e.isAppOf ``HSub.hSub || e.isAppOf ``Sub.sub then
      let b := e.appArg!
      let a := e.appFn!.appArg!

      let a_q : Q(MvPolynomial $σ $R) := a
      let b_q : Q(MvPolynomial $σ $R) := b

      let aStr ← parsePoly (r:=r) a_q
      let bStr ← parsePoly (r:=r) b_q
      pure s!"({aStr} - {bStr})"

    else if e.isAppOf ``HMul.hMul || e.isAppOf ``Mul.mul then
      let b := e.appArg!
      let a := e.appFn!.appArg!

      let a_q : Q(MvPolynomial $σ $R) := a
      let b_q : Q(MvPolynomial $σ $R) := b

      let aStr ← parsePoly (r:=r) a_q
      let bStr ← parsePoly (r:=r) b_q
      pure s!"{aStr} * {bStr}"

    else if e.isAppOf ``MvPolynomial.X then
      let idx := e.appArg!

      let idxStr ← Meta.ppExpr idx
      pure s!"X_{idxStr.pretty}"

    else if e.isAppOf ``OfNat.ofNat then
       let s ← Meta.ppExpr e
       pure s.pretty

    else if e.isAppOf ``Neg.neg then
      let a := e.appArg!
      let a_q : Q(MvPolynomial $σ $R) := a
      let aStr ← parsePoly (r:=r) a_q
      pure s!"(-{aStr})"

    else if e.isAppOf ``HPow.hPow || e.isAppOf ``Pow.pow then
      let exp := e.appArg!
      let base := e.appFn!.appArg!
      let base_q : Q(MvPolynomial $σ $R) := base

      let baseStr ← parsePoly (r:=r) base_q

      let nStr ← (do
        let expQ : Q(ℕ) := exp
        let .isNat _ n _ ← NormNum.derive (α := q(ℕ)) expQ | failure
        pure s!"{n.natLit!}"
      ) <|> (do
        let s ← Meta.ppExpr exp
        pure s.pretty
      )
      pure s!"{baseStr}^{nStr}"

    else if e.isAppOf ``DFunLike.coe then
      let args := e.getAppArgs

      let isTarget := args.size >= 6 && (
        let fn := args[4]!
        fn.isAppOf ``MvPolynomial.C || fn.isAppOf ``algebraMap || fn.isAppOf ``RingHom.id
      )

      if isTarget then
         let arg := args[5]!
         let val_q : Q($R) := arg
         try
           let r ← Mathlib.Meta.NormNum.derive val_q
           pure s!"{r.toRat.get!}"
         catch _ =>
           let s ← Meta.ppExpr arg
           pure s.pretty
      else
         let s ← Meta.ppExpr e
         pure s.pretty

    else if e.isAppOf ``MvPolynomial.C then
      let val := e.appArg!
      let val_q : Q($R) := val
      try
        let r ← Mathlib.Meta.NormNum.derive val_q
        pure s!"{r.toRat.get!}"
      catch _ =>
        let s ← Meta.ppExpr val
        pure s.pretty


    else
      logWarning m!"[parsePoly] cannot parse the structure: {e}"
      let s ← Meta.ppExpr e
      pure s.pretty


#eval parsePoly q(1 : MvPolynomial Nat Int)
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

  | ~q(Singleton.singleton $x) =>
    let xStr ← parsePoly (σ := σ) (R := R) (r := r) x
    pure [xStr]

  | ~q(Set.singleton $v) =>
    let vStr ← parsePoly (σ := σ) (R := R) (r := r) v
    pure [vStr]
  | ~q(singleton $v) =>

    let vStr ← parsePoly (σ := σ) (R := R) (r := r) v
    pure [vStr]
  | _ => throwError m!"[parseSet] Failed to parse the structure\n: {e}
  \n"


partial def parseSet' {u v : Level} {σ : Q(Type u)} {R : Q(Type v)} {r : Q(CommSemiring $R)}
    (e : Q(Set (MvPolynomial $σ $R))) : MetaM (List String) := do

  match e with
  | ~q(Insert.insert (γ:=Set _) $a $b) =>
    let VarA ← parsePoly (σ := σ) (R := R) (r := r) a
    let VarB ← parseSet' (σ := σ) (R := R) (r := r) b
    pure (VarA :: VarB)

  | ~q((∅: Set (MvPolynomial _ _))) => pure []
  | ~q(EmptyCollection.emptyCollection) => pure []

  | _ =>
    if e.isAppOf ``Insert.insert then

      let b_raw := e.appArg!
      let a_raw := e.appFn!.appArg!

      let a_q : Q(MvPolynomial $σ $R) := a_raw
      let b_q : Q(Set (MvPolynomial $σ $R)) := b_raw

      let VarA ← parsePoly (σ := σ) (R := R) (r := r) a_q
      let VarB ← parseSet' (σ := σ) (R := R) (r := r) b_q
      pure (VarA :: VarB)

    else if e.isAppOf ``Singleton.singleton then
      let x_raw := e.appArg!
      let x_q : Q(MvPolynomial $σ $R) := x_raw
      let xStr ← parsePoly (σ := σ) (R := R) (r := r) x_q
      pure [xStr]

    else if e.isAppOf ``Set.singleton then
      let x_raw := e.appArg!
      let x_q : Q(MvPolynomial $σ $R) := x_raw
      let xStr ← parsePoly (σ := σ) (R := R) (r := r) x_q
      pure [xStr]

    else
      throwError m!"[parseSet Error] Unmatched Structure\nExpr: {e}\nAppFn: {e.getAppFn}"


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

/-
In this section, we define the tactics to call Sage to prove some algebraic facts
-/
def verifyRemainderLogic (witness : Term) (isZeroTarget : Bool) : TacticM Unit := do
  let runUse := fun x => do Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]

  evalTactic (← `(tactic|
     simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  ))
  evalTactic (← `(tactic|
     rw [IsRemainder.isRemainder_range_fintype, ← exists_and_right]
  ))

  runUse witness

  evalTactic (← `(tactic| split_ands ))

  evalTactic (← `(tactic|
    focus
      set_option backward.isDefEq.respectTransparency false in
      simp [Fin.univ_succ, -List.get_eq_getElem, List.get]
      all_goals decide +kernel
  ))

  evalTactic (← `(tactic|
    focus
      intro i
      fin_cases i
      all_goals {
       simp only [List.get, Fin.isValue]
       all_goals
         exact withBotDegree_le_of_repr_le <| by decide +kernel
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

      let sage_result ← runSage (.remainder parsedPoly s!"{varsList}")

      let result := Json.parse s!"{sage_result}"

      let sage_json_result ← parseJson result

      let Except.ok arr := sage_json_result.getArr? | failure

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
          set_option backward.isDefEq.respectTransparency false in
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

      let parsedPoly ← parsePoly (σ := σ) (R := R) (r := instCommSemiring) poly
      let varsList ← parseSet (σ := σ) (R := R) (r := instCommSemiring) vars

      let sage_result ← runSage (.remainder parsedPoly s!"{varsList}")

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
          set_option backward.isDefEq.respectTransparency false in
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
  -- logInfo m!"[DEBUG `basis` Goal] : {goal}"
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsGroebnerBasis
      _ $R $instCommSemiring $basis $ideal) =>

      let basislist <- parseSet basis

      let sage_result ← runSage (.basis s!"{basislist}")
      let result := Json.parse s!"{sage_result}"
      let sage_json_result ← parseJson result

      let Except.ok arr := sage_json_result.getArr? | failure

      let parsedTermsArray ← arr.mapM mkPolyListTerm

      evalTactic (← `(tactic|
        rw [MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_isRemainder_sPolynomial_zero]
      ))
      evalTactic (← `(tactic|
        simp only [Fin.isValue, Subtype.forall, Set.mem_insert_iff, Set.mem_singleton_iff,
          forall_eq_or_imp, forall_eq, sPolynomial_self]
      ))
      evalTactic (← `(tactic|
        simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
      ))
      evalTactic (← `(tactic|
        simp_rw [IsRemainder.isRemainder_range_fintype]
      ))
      evalTactic (← `(tactic|
        split_ands
      ))
      for i in parsedTermsArray do
        evalTactic (← `(tactic|
        focus
          use $i:term
        ))
        evalTactic (← `(tactic|
          split_ands
        ))
        evalTactic (← `(tactic|
          focus
            set_option backward.isDefEq.respectTransparency false in
            simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
            -- with_unfolding_all decide
            all_goals decide +kernel-- PIT by reflection
        ))
        evalTactic (← `(tactic|
          focus
            intro i
            fin_cases i
            all_goals {
              simp only [List.get, Fin.isValue]
              all_goals
                exact withBotDegree_le_of_repr_le <| by decide +kernel
            }
        ))
        evalTactic (← `(tactic|
        · simp))
      evalTactic (← `(tactic| simp))
      let gs ← getUnsolvedGoals
      unless gs.isEmpty do
        evalTactic (← `(tactic| decide +kernel))



open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]

lemma aux_add_smul (R : Type*) {M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M]
    (g : R) (r f : M)
    (s : Set M) (h : r ∈ Submodule.span R s) :
    g • f + r ∈ Submodule.span R (insert f s) := by
  simp only [Submodule.span_insert]
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
    simp only [sup_le_iff]
    constructor
    · exact (Ideal.span_singleton_le_iff_mem I).mpr ha
    · exact hB

partial def getObjectsOfSet {u : Level} {M : Q(Type u)} (s : Q(Set $M)) (old : Array Q($M) := #[]) :
    TacticM (Option (Array Q($M))) := do
  match s with
  | ~q(insert $a $s) => getObjectsOfSet s (old ++ #[a])
    | ~q({$a}) => pure <| .some <| old ++ #[a]
    | ~q({}) => pure <| .some old
    | _ => pure <| .none

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
  let t ← instantiateMVars (← goal.getType)
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

      evalTactic (← `(tactic|{
        have h_gb :
        lex.IsGroebnerBasis ($basis_term : Set $polyType) (Ideal.span ($basis_term)) := by
          basis
        have h_ideal : Ideal.span ($basis_term : Set $polyType) = $ideal_term := by
          simp
          -- ideal
        simp only [h_ideal] at h_gb
        exact h_gb
      }))



elab "base" : tactic  => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← goal.getType)
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

      evalTactic (← `(tactic|{
        have h_gb :
        lex.IsGroebnerBasis ($basis_term : Set $polyType) (Ideal.span ($basis_term)) := by
          simp
          basis
        have h_ideal : Ideal.span ($basis_term : Set $polyType) = $ideal_term := by
          -- simp
          ideal
        simp only [h_ideal] at h_gb
        exact h_gb
      }))

elab "add_gb_hyp" name:(ident)? G:term : tactic =>
  withMainContext do

    let G_expr ← Term.withSynthesize <| Term.elabTerm G none
    let G_expr ← instantiateMVars G_expr

    let type ← inferType G_expr
    let type ← instantiateMVars type

    let (polyType) ← match type.getAppFnArgs with
      | (``Set, #[p]) => pure p
      | _ => throwError m!"Expected Set, got: {type}"
    let (σ_expr, R_expr, inst_expr) ← match polyType.getAppFnArgs with
      | (``MvPolynomial, #[s, r, i]) => pure (s, r, i)
      | _ => throwError m!"Expected MvPolynomial with instance,
      got: {polyType}
      Args: {polyType.getAppFnArgs}"

    let u_sigma ← getLevel σ_expr
    let v_R ← getLevel R_expr

    let σ : Q(Type u_sigma) := σ_expr
    let R : Q(Type v_R)     := R_expr

    let inst : Q(CommSemiring $R) := inst_expr

    let polys ← parseSet' (σ := σ) (R := R) (r := inst) G_expr

    let sage_gb ← runSage (.GBasis s!"{polys}")

    let gb := Json.parse s!"{sage_gb}"
    let gb ← parseJson gb
    let Except.ok gb_arr := gb.getArr? | failure

    let exprArray ← gb_arr.mapM fun jsonElem => mkPolyExpr jsonElem

    let argsTerms : Array Term ← exprArray.mapM fun e => Lean.PrettyPrinter.delab e

    let setSyntax ← mkSetSyntaxFromTerms argsTerms

    let stx ← `(lex.IsGroebnerBasis $setSyntax (Ideal.span $G))
    let ty ← Term.withSynthesize <| Term.elabTerm stx none
    let ty ← instantiateMVars ty

    let tacStx ← `(tactic| base)

    let proofMVar ← mkFreshExprSyntheticOpaqueMVar ty

    let unsolvedGoals ← Lean.Elab.Tactic.run proofMVar.mvarId! do
      Lean.Elab.Tactic.evalTactic tacStx

    unless unsolvedGoals.isEmpty do
      throwError m!"The tactic 'base' failed to prove the hypothesis, leaving unsolved goals."

    let proof ← instantiateMVars proofMVar

    let hypName := name.map (·.getId) |>.getD `this

    liftMetaTactic fun mvarId => do
      mvarId.withContext do
        let mvarIdNew ← mvarId.assert hypName ty proof
        let (_fvarId, mvarIdNew) ← mvarIdNew.intro1P
        return [mvarIdNew]


syntax (name := groebnerMembership) "ideal_membership" : tactic
@[tactic groebnerMembership]
def evalGroebnerMembership : Tactic := fun _stx => do
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

        let setSyntax ← mkSetSyntaxFromTerms argsTerms

        let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)

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
            exact (IsGroebnerBasis.remainder_eq_zero_iff_mem_ideal h_gb' h_rm).mpr h_mem
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
variable {T : Type*}
variable {R : Type*} [CommRing R] {σ : Type*}


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
  · intro h
    rcases h with ⟨n, hn⟩
    have eq : (1 : R_t) =
      (1 - ((X t) * (rename g f)) ^ n) +
      ((X t) * (rename g f)) ^ n := by
      ring
    nth_rw 2 [eq]
    apply Ideal.add_mem
    · apply Ideal.mem_sup_right
      have l₁: 1 - (X t) * (rename g f) ∣ 1 - (X t * (rename g) f) ^ n := by
        exact one_sub_dvd_one_sub_pow (X t * (rename g) f) n
      rcases l₁ with ⟨p, hp⟩
      rw [hp]
      apply Ideal.mul_mem_right
      exact Ideal.mem_span_singleton_self (1 - X t * (rename g) f)
    · apply Ideal.mem_sup_left
      rw [_root_.mul_pow]
      apply Ideal.mem_map_of_mem (rename g) at hn
      rw [map_pow] at hn
      apply Ideal.mul_mem_left
      convert hn using 1

  · intro h
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
          · exfalso
            exact h_disj i h1
          · congr
            apply h_inj
            exact Classical.choose_spec h2
          · exfalso
            exact h2 (Set.mem_range_self i)
        rw [h_comp]
        change (MvPolynomial.aeval (fun i ↦ algebraMap R R_f (X i))).toRingHom f
          = (algebraMap R R_f) f
        congr 1
        simp only [AlgHom.toRingHom_eq_coe]
        apply MvPolynomial.ringHom_ext
        · intro r
          simp only [RingHom.coe_coe, algHom_C]
          exact rfl
        · intro i
          simp only [RingHom.coe_coe, aeval_X]
      rw [val_t, val_f]
      rw [IsLocalization.mk'_spec]
      simp only [map_one]
      exact sub_self 1
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
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply, map_add]
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
def evalradicalMembership : Tactic := fun _stx => do
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

      let n_val : Nat := n.trimAscii.toNat!
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


      evalTactic (← `(tactic|
      simp only [Nat.reduceAdd, Fin.reduceLast, Fin.isValue, map_one,
        Set.image_singleton, rename_X, Fin.castSucc_zero, map_add] at h₁
      ))

      evalTactic (← `(tactic|
      exact h₁ h
      ))


    | _ => throwError "Goal must be of form `f ∈ (Ideal.span S).
    radical` or form of `f ∉ (Ideal.span S).radical`"



syntax (name := GBSolve) "gb_solve" : tactic
@[tactic GBSolve]
def evalGBSolve : Tactic := fun stx => do
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
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsGroebnerBasis
      _ $R $instCommSemiring $basis $ideal) =>
      let basis_term ← Lean.PrettyPrinter.delab basis
      let ideal_term ← Lean.PrettyPrinter.delab ideal

      let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)

      evalTactic (← `(tactic|{
        have h_gb :
        lex.IsGroebnerBasis ($basis_term : Set $polyType) (Ideal.span ($basis_term)) := by
          basis
        have h_ideal : Ideal.span ($basis_term : Set $polyType) = $ideal_term := by
          ideal
        simp only [h_ideal] at h_gb
        exact h_gb
      }))

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

      let n_val : Nat := n.trimAscii.toNat!
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


      evalTactic (← `(tactic|
      simp only [Nat.reduceAdd, Fin.reduceLast, Fin.isValue, map_one,
        Set.image_singleton, rename_X, Fin.castSucc_zero, map_add] at h₁
      ))

      evalTactic (← `(tactic|
      exact h₁ h
      ))

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

        let setSyntax ← mkSetSyntaxFromTerms argsTerms

        let polyType : Term ← Lean.PrettyPrinter.delab q(MvPolynomial $σ $R)

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

        evalTactic (← `(tactic|
          have h_ideal : $I_term = Ideal.span ($setSyntax : Set $polyType) := by
            ideal
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
            exact (IsGroebnerBasis.remainder_eq_zero_iff_mem_ideal h_gb' h_rm).mpr h_mem
        ))

        evalTactic (← `(tactic|
          contradiction
        ))
      | _ => throwError "Expect Ideal.span, but got {I}"


    | _ => throwError "The Goal can not match any parttern."

end IsRemainder

end Tactic

end Mathlib
