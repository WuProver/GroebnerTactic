-- import Mathlib
import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly


-- import GroebnerTac.AstToLean
-- import GroebnerTac.AstToSage
-- import GroebnerTac.MathMLToAST
-- import GroebnerTac.ExprToAst

import Groebner.Basic
import Groebner.List

import Mathlib.Tactic
import Lean


namespace Mathlib.Tactic.IsRemainder
open Lean Elab Tactic Meta Term
open Meta Ring Qq PrettyPrinter AtomM
open MvPolynomial MonomialOrder

/-- A schema for the data reported by the Sage calculation -/
structure SageCoeffAndPower where
  coeffs : Array ℕ
  power  : Array ℕ
  deriving FromJson, Repr


-- inductive Poly
--   | const : ℚ → Poly
--   | var : ℕ → Poly
--   | hyp : Term → Poly
--   | add : Poly → Poly → Poly
--   | sub : Poly → Poly → Poly
--   | mul : Poly → Poly → Poly
--   | div : Poly → Poly → Poly
--   | pow : Poly → Poly → Poly
--   | neg : Poly → Poly
--   deriving BEq

-- /--
-- This converts a poly object into a string representing it. The string
-- maintains the semantic structure of the poly object.

-- The output of this function must be valid Python syntax, and it assumes the variables `vars`
-- (see `sageCreateQuery`).
-- -/
-- def Poly.format : Poly → Lean.Format
--   | .const z => toString z
--   | .var n => s!"vars[{n}]" -- this references variable `vars`, which need to be bounded (below)
--   | .hyp e => s!"hyp{e}" -- this one can't be used by python
--   | .add p q => s!"({p.format} + {q.format})"
--   | .sub p q => s!"({p.format} - {q.format})"
--   | .mul p q => s!"({p.format} * {q.format})"
--   | .div p q => s!"({p.format} / {q.format})" -- this one can't be used by python
--   | .pow p q => s!"({p.format} ^ {q.format})"
--   | .neg p => s!"-{p.format}"

-- instance : Lean.ToFormat Poly := ⟨Poly.format⟩
-- instance : ToString Poly := ⟨(toString ·.format)⟩
-- instance : Repr Poly := ⟨fun p _ => p.format⟩
-- instance : Inhabited Poly := ⟨Poly.const 0⟩

-- instance : Quote ℤ where quote
--   | .ofNat n => quote n
--   | .negSucc n => Unhygienic.run `(-$(quote (n + 1)))

-- instance : Quote ℚ where
--   quote q :=
--     if q.den = 1 then quote q.num
--     else Unhygienic.run `($(quote q.num) / $(quote q.den))

-- variable (vars : Array Syntax.Term) in
-- /-- Converts a `Poly` expression into a `Syntax` suitable as an input to `linear_combination`. -/
-- def Poly.toSyntax : Poly → Unhygienic Syntax.Term
--   | .const z => pure (quote z)
--   | .var n => pure vars[n]!
--   | .hyp stx => pure stx
--   | .add p q => do `($(← p.toSyntax) + $(← q.toSyntax))
--   | .sub p q => do `($(← p.toSyntax) - $(← q.toSyntax))
--   | .mul p q => do `($(← p.toSyntax) * $(← q.toSyntax))
--   | .div p q => do `($(← p.toSyntax) / $(← q.toSyntax))
--   | .pow p q => do `($(← p.toSyntax) ^ $(← q.toSyntax))
--   | .neg p => do `(-$(← p.toSyntax))

-- attribute [local instance] monadLiftOptionMetaM in
-- /-- Reifies a ring expression of type `α` as a `Poly`. -/
-- partial def parse {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
--     (c : Ring.Cache sα) (e : Q($α)) : AtomM Poly := do
--   let els := do
--     try pure <| Poly.const (← (← NormNum.derive e).toRat)
--     catch _ => pure <| Poly.var (← addAtom e).1
--   let .const n _ := (← withReducible <| whnf e).getAppFn | els
--   match n, c.rα with
--   | ``HAdd.hAdd, _ | ``Add.add, _ => match e with
--     | ~q($a + $b) => pure <| (← parse sα c a).add (← parse sα c b)
--     | _ => els
--   | ``HMul.hMul, _ | ``Mul.mul, _ => match e with
--     | ~q($a * $b) => pure <| (← parse sα c a).mul (← parse sα c b)
--     | _ => els
--   | ``HSMul.hSMul, _ => match e with
--     | ~q(($a : ℕ) • ($b : «$α»)) => pure <| (← parse sℕ .nat a).mul (← parse sα c b)
--     | _ => els
--   | ``HPow.hPow, _ | ``Pow.pow, _ => match e with
--     | ~q($a ^ $b) =>
--       try pure <| (← parse sα c a).pow (.const (← (← NormNum.derive (u := .zero) b).toRat))
--       catch _ => els
--     | _ => els
--   | ``Neg.neg, some _ => match e with
--     | ~q(-$a) => pure <| (← parse sα c a).neg
--   | ``HSub.hSub, some _ | ``Sub.sub, some _ => match e with
--     | ~q($a - $b) => pure <| (← parse sα c a).sub (← parse sα c b)
--     | _ => els
--   | _, _ => els


-- /-- The possible hypothesis sources for a polyrith proof. -/
-- inductive Source where
--   /-- `input n` refers to the `n`-th input `ai` in `polyrith [a1, ..., an]`. -/
--   | input : Nat → Source
--   /-- `fvar h` refers to hypothesis `h` from the local context. -/
--   | fvar : FVarId → Source

-- def parseContext (only : Bool) (hyps : Array Expr) (target : Expr) :
--     AtomM (Expr × Array (Source × Poly) × Poly) := do
--   let fail {α} : AtomM α := throwError "polyrith failed: target is not an equality in semirings"
--   let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars target).eq? | fail
--   let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
--   let some v := u.dec | throwError "not a type{indentExpr α}"
--   have α : Q(Type v) := α
--   have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
--   let sα ← synthInstanceQ q(CommSemiring $α)
--   let c ← mkCache sα
--   let target := (← parse sα c e₁).sub (← parse sα c e₂)
--   let rec
--     /-- Parses a hypothesis and adds it to the `out` list. -/
--     processHyp src ty out := do
--       if let some (β, e₁, e₂) := (← instantiateMVars ty).eq? then
--         if ← withTransparency (← read).red <| isDefEq α β then
--           return out.push (src, (← parse sα c e₁).sub (← parse sα c e₂))
--       pure out
--   let mut out := #[]
--   if !only then
--     for ldecl in ← getLCtx do
--       out ← processHyp (.fvar ldecl.fvarId) ldecl.type out
--   for hyp in hyps, i in [:hyps.size] do
--     out ← processHyp (.input i) (← inferType hyp) out
--   pure (α, out, target)

namespace Poly
open Lean
variable {m : Type → Type} [Monad m] [MonadQuotation m] [MonadRef m]

/- or
structure V where
  v : Nat
  e : Nat
deriving FromJson, ToJson, Repr
-/
def V := Nat × Nat
deriving FromJson, ToJson, Repr

def V.mkQ {u u' : Lean.Level} (v : V) (σ : Q(Type $u))
    (instOfNat : Q((n : Nat) → OfNat $σ n))
    (R : Q(Type $u'))
    (instField : Q(Field $R)) : Q(MvPolynomial $σ $R) :=
  let i : Q(Nat) := mkNatLit v.1
  let e : Q(Nat) := mkNatLit v.2
  q(MvPolynomial.X ($instOfNat $i).ofNat ^ $e)

def V.mkTerm (v : V) : m Term :=
  let v' := Syntax.mkNumLit (toString v.1)
  if v.2 ≠ 1 then
    let e := Syntax.mkNumLit (toString v.2)
    `(term| MvPolynomial.X $v':num ^ $e:num)
  else
    `(term| MvPolynomial.X $v':num)

/- or
structure Q where
  n : Int
  d : Nat
deriving FromJson, ToJson, Repr
-/
def Q := Int × Nat
deriving FromJson, ToJson, Repr

def Q.mkQ (q : Q) : Q(ℚ) :=
  let n : Q(Int) := mkIntLit q.1
  let d : Q(Nat) := mkNatLit q.2
  q($n / $d)

def Q.mkTerm (q : Q) : m Term :=
  let n := Syntax.mkNumLit (toString q.1)
  if q.2 = 1 then
    `(term| $n:num)
  else
    `(term| ($n:num / $(Syntax.mkNumLit (toString q.2))))

structure Mon where
  c : Q
  e : Array V
deriving FromJson, ToJson, Repr

def Mon.mkQ {u v : Lean.Level} (m : Mon) (σ : Q(Type u))
    (instOfNat : Q((n : Nat) → OfNat $σ n))
    (R : Q(Type v))
    (instField : Q(Field $R)) : Q(MvPolynomial $σ $R) :=
  let c := m.c.mkQ
  m.e.foldl (β := Q(MvPolynomial $σ $R)) (init := q(MvPolynomial.C $c))
    (fun p m ↦
      let m := m.mkQ σ instOfNat R instField
      q($p * $m))

def Mon.mkTerm (m' : Mon) : m Term := do
  let c : Term ← `(term| MvPolynomial.C $(← m'.c.mkTerm))
  m'.e.foldlM (fun p m ↦ do `(term| $p * $(← m.mkTerm))) c

def Polynomial := List Poly.Mon
deriving FromJson, ToJson, Repr


def Polynomial.mkQ {u v : Lean.Level} (p : Polynomial) (σ : Q(Type $u))
    (instOfNat : Q((n : Nat) → OfNat $σ n))
    (R : Q(Type $v))
    (instField : Q(Field $R)) : Q(MvPolynomial $σ $R) :=
  p.foldl (α := Q(MvPolynomial $σ $R)) (init := q(0))
    (fun p m ↦
      let m := m.mkQ σ instOfNat R instField
      q($p + $m))

def Polynomial.mkTerm (p : Polynomial) : m Term := do
  p.foldlM (fun p m ↦ do `(term| $p + $(← m.mkTerm))) (← `(0))

end Poly

#eval do
  Lean.fromJson? (α := List Poly.Mon)
    (← Lean.Json.parse
      "[{\"c\" : [1, 2], \"e\": [[0, 2], [2, 3]]}, {\"c\" : [3, 5], \"e\": [[4, 1]]}]")


#eval do
  Lean.fromJson? (α := Poly.Polynomial)
    (← Lean.Json.parse
      "[{\"c\" : [1, 2], \"e\": [[0, 2], [2, 3]]}, {\"c\" : [3, 5], \"e\": [[4, 1]]}]")



#print Poly.instFromJsonMon.fromJson
#eval do
  Lean.fromJson? (α := Poly.Polynomial)
    (← Lean.Json.parse
      "[{\"c\" : [1, 2], \"e\": [[0, 2], [2, 3]]}, {\"c\" : [3, 5], \"e\": [[4, 1]]}]")

#check Lean.MetaM Unit

open Qq in
#eval show TermElabM Unit from do
  let Except.ok parsed := Lean.Json.parse
      "[{\"c\" : [1, 2], \"e\": [[0, 2], [2, 3]]}, {\"c\" : [3, 5], \"e\": [[4, 1]]}]" | failure
  logInfo (toString parsed)
  logInfo m!"{parsed}"
  let Except.ok p := Lean.fromJson? (α := Poly.Polynomial) parsed | failure
  let p ← p.mkTerm
  Lean.logInfo p
  Lean.logInfo <| show Expr from (← Term.elabTerm p .none)

-- def qToRat : Poly.Q → ℚ
--   | (n, d) => if h : d ≠ 0 then q(n/d)

-- #eval q(1/2)

/- We define how to start a sage process-/
def runsageAux (path poly remainder : String) : IO (String) := do
  let child ← IO.Process.spawn {
    cmd := "sage"
    args := #[path, "-p", poly, "-d", remainder]
    stdout := .piped,
    stderr := .piped
  }

  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait

  IO.println s!"Sage stdout: {stdout}"
  IO.println s!"Sage stderr: {stderr}"
  IO.println s!"Sage exit code: {exitCode}"


  -- let a ← Json.parse stdout >>= fromJson?
  -- match Json.parse stdout >>= fromJson? with
  -- | .ok result => return result
  -- | .error e => IO.throwServerError <|
  --     s!"Could not parse SageMath output (error: {e})\nSageMath output:\n{stdout}"
  return stdout

def runsage (poly remainder: String) : IO (String) := do
  let cwd ← IO.currentDir
  let path := cwd / "Sage" / "Groebner.sage"
  match ← path.pathExists with
  | true => runsageAux path.toString poly remainder
  | false => do
    dbg_trace f!"There does not exist {path}"
    throw <| IO.userError "could not find sage script Greobner.sage"

-- def parseResult (poly remainder: String)


#eval runsage "(((X_0^2 + X_1^3) + X_2^4) + X_3^5)" "[X_0, X_1]"

def stringToJson (s : String) : Except String Json :=
  Json.parse s

#eval stringToJson "[{\"coeffs\": [\"1\"], \"power\": [[1, 0, 0, 0]]}, {\"coeffs\": [\"1\"], \"power\": [[0, 2, 0, 0]]}]"



def sageresult := runsage "(((X_0^2 + X_1^3) + X_2^4) + X_3^5)" "[X_0, X_1]"


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

def processElement (jsonElement : Json) : MetaM Term := do
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

elab "rm" : tactic => do
  evalTactic (← `(tactic|{
    simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
    rw [isRemainder_range_fin]
    split_ands
    · use [X 0, X 1 ^ 2, X 2 ^ 3, X 3 ^ 4].get
      split_ands
      · simp [Fin.univ_succ, -List.get_eq_getElem, List.get]
        all_goals decide +kernel
      · intro i
        fin_cases i
        all_goals {
          simp [-List.get_eq_getElem, List.get]
          all_goals {
            rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
              SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
              ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
            decide +kernel
          }
        }
    · simp
  }))


-- elab ref:  "check_remainder" : tactic => do
--   let goal ← getMainGoal
--   logInfo s!"Checking remainder for goal: {← goal.getType}"

--   goal.withContext do
--     let hyps ← getHypotheses
--     let some goalAST ← LeanSage.exprToAST (← goal.getType) | throwError "Failed to convert goal to AST"
--     let (assumptions, baseSageCode) := buildSageCode goalAST hyps
--     let sageCode := s!"bool({baseSageCode})"
--     logInfo s!"assumptions: {assumptions}"
--     logInfo s!"sageCode : {sageCode}"

--     return ()

--   return ()

-- elab "showGoal" : tactic => do
--   let goal ← Lean.Elab.Tactic.getMainGoal
--   let t ← goal.getType
--   let t ←  checkTypeQ t q(Prop)
--   match t with
--   | none => return
--   | some expr =>
--     match expr with
--   | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder _ $R $instCommSemirng $poly $vars $r) =>
--       dbg_trace "poly = {poly}"
--       dbg_trace "vars = {vars}"
--       dbg_trace "r = {r}"
--       try
--         match poly with
--         | ~q($a + $b) =>
--           dbg_trace "It's a sum: a = {a}, b = {b}"
--         | ~q($a * $b) =>
--             dbg_trace "It's a multiple: {a} * {b}"
--         | ~q(HPow.hPow $base $exp) =>
--           dbg_trace "It's a pow: {base}^{exp}"
--         | ~q(MvPolynomial.X $i) =>
--           dbg_trace ": X_{i}"
--         | _ =>
--           dbg_trace "Error"
--       catch _ =>
--         dbg_trace "Failed to parse polynomial"
--   | _ =>
--       dbg_trace "not a lex.IsRemainder"


elab "remainder" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder _ $R $instCommSemiring $poly $vars $r) =>
      -- dbg_trace "poly = {poly}"
      -- dbg_trace "vars = {vars}"
      -- dbg_trace "r = {r}"
      logInfo m!"[DEBUG] vars = {vars}"

      let rec parsePoly (e : Expr) : Lean.MetaM String := do
        let e ← checkTypeQ e q(MvPolynomial $σ $R)
        match e with
        | none => pure s!"unknown"
        | some expr =>
          match expr with
          | ~q($a + $b) =>
            -- let left ← parsePoly a
            let a  ← parsePoly a
            let b  ← parsePoly b
            -- logInfo m!"[DEBUG]check {a}"
            -- logInfo m!"[DEBUG]check {b}"
            -- dbg_trace "[DEBUG] check {a}"
            pure s!"({a} + {b})"
            -- logInfo m!"FIND ADD LEFT: {left}"
            -- let right ← parsePoly b
            -- logInfo m!"FIND ADD RIGHT: {right}"
            -- dbg_trace "FIND ADD: {left} and {right}"
            -- pure s!"({left} + {right})"

          | ~q($a * $b) =>
            let left ← parsePoly a
            let right ← parsePoly b
            -- dbg_trace "FIND MUL: {left} and {right}"
            pure s!"({left} + {right})"

          -- | ~q(HPow.hPow $base $exp) =>
          --   let baseStr ← parsePoly base
          --   -- match base with
          --   -- | ~q(MvPolynomial.X $idx) =>
          --   dbg_trace "baseStr: {baseStr}"
          --   match exp with
          --   | ~q(@OfNat.ofNat _ _ $n) =>
          --     dbg_trace "FOUND EXPONENT {n}"
          --     pure s!"{baseStr}^{n}"
          --   | _ => pure s!"{baseStr}^{exp}"

          | ~q($a ^ ($n : ℕ)) =>
            let baseStr ← parsePoly a
            -- match baseStr with

            let n ← try
              let .isNat _ n _ ← NormNum.derive (α := q(ℕ)) n | failure
              pure n.natLit!
            catch _ =>
              pure n.natLit!
            -- dbg_trace "FOUND POW: {baseStr}^{n}"
            pure s!"{baseStr}^{n}"
            -- dbg_trace "FOUND POW: {baseStr}^{n}"
          | ~q(MvPolynomial.X $idx) =>
            match idx with
            -- | ~q(@OfNat.ofNat _ _ $n) => pure s!"X_{n}"
            -- | ~q(@OfNat.ofNat _ _ $n) => dbg_trace "FOUND VAR INDEX {n}"; pure s!"X_{n}"
            -- | _ => pure s!"X_{idx}"
            | ~q(@OfNat.ofNat _ _ $var) =>
              match var with
              | .app (.app (.app (.const `Fin.instOfNat _) _) _) n => pure s!"X_{n}"
              | _ => pure s!"X_{idx}"
          | ~q(@OfNat.ofNat _ _ $n) =>
            pure s!"{n}"
          | ~q(@Zero.toOfNat0 _ $z) =>
            logInfo m!"[DEBUG] Found zero constant{z}"
            dbg_trace s!"[DEBUG] Found zero constant {z}"
            pure "0"
          | _ =>
            pure s!"{e}"
      let rec parseVars (e : Q(Set (MvPolynomial $σ $R))) : Lean.MetaM (List String) := do
        -- let e ← checkTypeQ e q(Set (MvPolynomial $σ $R))
        match e with
        -- | none => pure []
        -- | some expr =>
        --   match expr with
        | ~q(Insert.insert (γ:=Set _) $a $b) =>
          let VarA ← parsePoly a
          let VarB ← parseVars b
          -- logInfo m!"[DEBUG] View A: {a}"
          -- logInfo m!"[DEBUG] View B: {b}"
          -- logInfo m!"[DEBUG] VarA: {VarA}"
          -- logInfo m!"[DEBUG] VarB: {VarB}"
          -- dbg_trace s!"View A: {a}"
          -- dbg_trace s!"View B: {b}"
          pure (VarA :: VarB)
        | ~q((∅: Set (MvPolynomial _ _))) => pure []
        | ~q(Set.singleton $v) =>
          let vStr ← parsePoly v
          logInfo m!"[DEBUG] Singleton var: {vStr}"
          pure [vStr]
        | ~q(singleton $v) =>
          let vStr ← parsePoly v
          logInfo m!"[DEBUG] Single var: {vStr}"
          pure [vStr]
        | _ => unreachable!

      let parsedPoly ← parsePoly poly
      let varsList ← parseVars vars
      let parsedR ← parsePoly r

      -- logInfo m!"parsed vars: {varsList}"
      -- logInfo m!"parsed polynomial: {parsedPoly}"
      -- dbg_trace "parsed vars: {varsList}"
      -- dbg_trace "parsed polynomial: {parsedPoly}"
      -- dbg_trace "parsed remainder: {parsedR}"

      let sage_result ← runsage parsedPoly s!"{varsList}"

      -- logInfo m!"[DEBUG] sage_result: {sage_result}"


      let result := Json.parse s!"{sage_result}"
      -- logInfo m!"[DEBUG] sage_json_result: {result}"
      let sage_json_result ← parseJson result
      logInfo m!"[DEBUG] sage_json_result after parsing: {sage_json_result}"
      let Except.ok arr := sage_json_result.getArr? | failure
      logInfo m!"Arr: {arr[0]!}"

      -- let firstElement ← arr.get? 0
      -- let mon_result := Lean.fromJson? (α := Poly.Polynomial) arr[0]!
      -- let mon ← parseResult mon_result
      -- match mon with
      -- | none => IO.throwServerError "There is not any result be parsed"
      -- | some p =>
      --   let instOfNat ← Qq.synthInstanceQ q((n : Nat) → OfNat Nat n)
      --   let instField ← Qq.synthInstanceQ q(Field ℚ)
      --   let p := p.mkQ q(Nat) instOfNat q(ℚ) instField
      --   Lean.logInfo p

      --   let x <- Lean.PrettyPrinter.delab p
      --   let runUse := fun x => do Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]
      --   runUse x
      let processList := arr.mapM processElement
      let resultArray : Array Term ← processList
      let xs : Term ← `(term| [$resultArray:term,*].get)
      logInfo m!"[DEBUG] {xs}, elab {← Term.elabTerm xs q(MvPolynomial $σ $R)}"
      let runUse := fun x => do Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]
      evalTactic (← `(tactic| simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]))
      evalTactic (← `(tactic| rw [isRemainder_range_fin, ← exists_and_right]))
      runUse xs




      -- let (x: Q(Fin _ ->)) := q($resultList.get)
    --   let exprSyns ← exprListToSyntaxArray resultList

    --   logInfo m!"[DEBUG] SYN: {exprSyns}"

    --   evalTactic (← `(tactic|{
    --   simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
    --   rw [isRemainder_range_fin]
    --   split_ands
    --   · use [X 0, X 1 ^ 2, X 2 ^ 3, X 3 ^ 4].get
    --     split_ands
    --     · simp [Fin.univ_succ, -List.get_eq_getElem, List.get]
    --       all_goals decide +kernel
    --     · intro i
    --       fin_cases i
    --       all_goals {
    --         simp [-List.get_eq_getElem, List.get]
    --         all_goals {
    --           rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
    --             SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
    --             ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
    --           decide +kernel
    --         }
    --       }
    --   · simp
    -- }))

      -- let syn := [$resultList:term,*].get
      -- let x ← Lean.PrettyPrinter.delab q([$resultList:term,*].get)

      -- let runUse := fun x => do Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]
      -- runUse x




      -- match result with
      -- | .ok SageJsonResult => pure s!"{result}"
      -- | .error e => IO.throwServerError <|
      -- s!"Could not parse SageMath output (error: {e})\nSageMath output:\n{out.stdout}"


      -- if let some {coeffs := polys, power := pow} := sage_result then
      --   let vars ← liftM <| (← get).atoms.mapM delab

      -- catch _ => throwError
      --   "polyrith found the following certificate, but it failed to close the goal:\n{stx}"
    | _ =>
      dbg_trace "not a lex.IsRemainder"


elab "groebner" : tactic  => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsGroebnerBasis _ $R $instCommSemiring $basis $ideal) =>
      dbg_trace "basis = {basis}"
      logInfo m!"basis = {basis}"

      let rec parsePoly (e : Expr) : Lean.MetaM String := do
        let e ← checkTypeQ e q(MvPolynomial $σ $R)
        match e with
        | none => pure s!"unknown"
        | some expr =>
          match expr with
          | ~q($a + $b) =>
            -- let left ← parsePoly a
            let a  ← parsePoly a
            let b  ← parsePoly b
            -- logInfo m!"[DEBUG]check {a}"
            -- logInfo m!"[DEBUG]check {b}"
            -- dbg_trace "[DEBUG] check {a}"
            pure s!"({a} + {b})"
            -- logInfo m!"FIND ADD LEFT: {left}"
            -- let right ← parsePoly b
            -- logInfo m!"FIND ADD RIGHT: {right}"
            -- dbg_trace "FIND ADD: {left} and {right}"
            -- pure s!"({left} + {right})"

          | ~q($a * $b) =>
            let left ← parsePoly a
            let right ← parsePoly b
            -- dbg_trace "FIND MUL: {left} and {right}"
            pure s!"({left} + {right})"

          -- | ~q(HPow.hPow $base $exp) =>
          --   let baseStr ← parsePoly base
          --   -- match base with
          --   -- | ~q(MvPolynomial.X $idx) =>
          --   dbg_trace "baseStr: {baseStr}"
          --   match exp with
          --   | ~q(@OfNat.ofNat _ _ $n) =>
          --     dbg_trace "FOUND EXPONENT {n}"
          --     pure s!"{baseStr}^{n}"
          --   | _ => pure s!"{baseStr}^{exp}"

          | ~q($a ^ ($n : ℕ)) =>
            let baseStr ← parsePoly a
            -- match baseStr with

            let n ← try
              let .isNat _ n _ ← NormNum.derive (α := q(ℕ)) n | failure
              pure n.natLit!
            catch _ =>
              pure n.natLit!
            -- dbg_trace "FOUND POW: {baseStr}^{n}"
            pure s!"{baseStr}^{n}"
            -- dbg_trace "FOUND POW: {baseStr}^{n}"
          | ~q(MvPolynomial.X $idx) =>
            match idx with
            -- | ~q(@OfNat.ofNat _ _ $n) => pure s!"X_{n}"
            -- | ~q(@OfNat.ofNat _ _ $n) => dbg_trace "FOUND VAR INDEX {n}"; pure s!"X_{n}"
            -- | _ => pure s!"X_{idx}"
            | ~q(@OfNat.ofNat _ _ $var) =>
              match var with
              | .app (.app (.app (.const `Fin.instOfNat _) _) _) n => pure s!"X_{n}"
              | _ => pure s!"X_{idx}"
          | ~q(@OfNat.ofNat _ _ $n) =>
            pure s!"{n}"
          | ~q(@Zero.toOfNat0 _ $z) =>
            logInfo m!"[DEBUG] Found zero constant{z}"
            dbg_trace s!"[DEBUG] Found zero constant {z}"
            pure "0"
          | _ =>
            pure s!"{e}"

      let rec parseBasis(e : Q(Finset (MvPolynomial $σ $R))) : Lean.MetaM (List String) := do
        match e with
        | ~q(Insert.insert (self := $_inst) $a $b) =>
          let VarA ← parsePoly a
          let VarB ← parseBasis b
          dbg_trace "See If enter this Branch"
          logInfo m!"[DEBUG] Insert basis element: {a}"
          logInfo m!"[DEBUG] Remaining basis: {b}"
          pure (VarA :: VarB)
        | ~q((∅: Finset (MvPolynomial _ _))) => pure []
        | ~q(singleton $v) =>
          let vStr ← parsePoly v
          logInfo m!"[DEBUG] Singleton basis element: {vStr}"
          pure [vStr]
        | _ =>
          unreachable!

      let basislist <- parseBasis basis
      dbg_trace "parsed basis: {basislist}"
      logInfo m!"parsed basis: {basislist}"



elab "test_some" : tactic => do
  evalTactic (← `(tactic|{
         rw[add_comm]
      }))
  let x <- Lean.PrettyPrinter.delab q(1)
  let runUse := fun x => do Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger .none) [x]
  runUse x


elab "test_use" : tactic => do
    evalTactic (← `(tactic|{
      simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
      rw [isRemainder_range_fin]
      split_ands
      }))
    evalTactic (← `(tactic|{· use [X 0, X 1 ^ 2, X 2 ^ 3, X 3 ^ 4].get})
    )
    evalTactic (← `(tactic|{
    split_ands
    · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
      all_goals decide +kernel-- PIT, proof by reflection
    · intro i
      fin_cases i
      all_goals {
        simp [-List.get_eq_getElem, List.get]
        all_goals {
          rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
            SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
            ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
          decide +kernel
        }
      }
    simp
    }))


end IsRemainder



namespace Mathlib.Tactic.IsGroebner

end IsGroebner

end Tactic

end Mathlib
