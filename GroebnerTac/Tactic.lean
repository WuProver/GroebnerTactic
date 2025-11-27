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
  let i : Q(Nat) := mkRawNatLit v.1
  let e : Q(Nat) := mkRawNatLit v.2
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


def Q.mkTerm (q : Q) : m Term :=
  let n := Syntax.mkNumLit (toString q.1)
  if q.2 = 1 then
    `(term| $n:num)
  else
    `(term| ($n:num / $(Syntax.mkNumLit (toString q.2))))

-- def Q.mkQ (q : Q) : Q(ℚ) :=
--   Mathlib.Meta.NormNum.mkRawRatLit ((q.1 : ℚ) / q.2)

def Q.mkQ (q : Q) : Q(ℚ) :=
  let n : Q(Int) := mkIntLit q.1
  let d : Q(Nat) := mkNatLit q.2
  q($n / $d)

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

end Poly

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

  -- IO.println s!"Sage stdout: {stdout}"
  -- IO.println s!"Sage stderr: {stderr}"
  -- IO.println s!"Sage exit code: {exitCode}"

  return stdout

def runsageAux' (path set : String) : IO (String) := do
  let child ← IO.Process.spawn {
    cmd := "sage"
    args := #[path, "-s", set]
    stdout := .piped,
    stderr := .piped
  }

  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait

  -- IO.println s!"Sage stdout: {stdout}"
  -- IO.println s!"Sage stderr: {stderr}"
  -- IO.println s!"Sage exit code: {exitCode}"

  return stdout


def runsageAux_ideal (path I_generator J_generator : String) : IO (String) := do
  let child ← IO.Process.spawn {
    cmd := "sage"
    args := #[path, "-I", I_generator, "-J", J_generator]
    stdout := .piped,
    stderr := .piped
  }

  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  IO.println stderr

  return stdout


def runsage (poly remainder: String) : IO (String) := do
  let cwd ← IO.currentDir
  let path := cwd / "Sage" / "Remainder.sage"
  match ← path.pathExists with
  | true => runsageAux path.toString poly remainder
  | false => do
    dbg_trace f!"There does not exist {path}"
    throw <| IO.userError "could not find sage script Greobner.sage"

def runsage' (set: String) : IO (String) := do
  let cwd ← IO.currentDir
  let path := cwd / "Sage" / "Basis.sage"
  match ← path.pathExists with
  | true => runsageAux' path.toString set
  | false => do
    dbg_trace f!"There does not exist {path}"
    throw <| IO.userError "could not find sage script Greobner.sage"

def runsage_ideal (I J: String) : IO (String) := do
  let cwd ← IO.currentDir
  let path := cwd / "Sage" / "Ideal.sage"
  match ← path.pathExists with
  | true => runsageAux_ideal path.toString I J
  | false => do
    dbg_trace f!"There does not exist {path}"
    throw <| IO.userError "could not find sage script Greobner.sage"

#eval runsage "(((X_0^2 + X_1^3) + X_2^4) + X_3^5)" "[X_0, X_1]"

#eval runsage_ideal "[(X_0 + X_1^2), X_1^2]" "[X_0, X_1^2]"

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
  -- let b ←  match a.getArr? with
  --   | Except.ok arr => pure arr
  --   | Except error e => throwError "Json fail"
  let Except.ok b:= a.getArr? | failure
  let process_a:= b.mapM processElement
  let resultArray ←  process_a
  let xs := resultArray.toList
  let get : Q((xs : List (MvPolynomial ℕ ℚ)) -> Fin xs.length -> MvPolynomial ℕ ℚ) := q(List.get)
  let xs : Q(List (MvPolynomial ℕ ℚ)) := liftListQ xs
  let xs_get := q($get $xs)
-- logInfo m!"[DEBUG] {xs_get}"
  let xs_get <- Lean.PrettyPrinter.delab xs_get
  -- logInfo m!"[CHECK {xs_get}]"
  pure xs_get

def parseCoeff' (a : Json) : TacticM Term := do
  -- let b ←  match a.getArr? with
  --   | Except.ok arr => pure arr
  --   | Except error e => throwError "Json fail"
  let Except.ok b:= a.getArr? | failure
  let process_a:= b.mapM processElement
  let resultArray ←  process_a
  let xs := resultArray.toList
  let get : Q((xs : List (MvPolynomial ℕ ℚ)) -> Fin xs.length -> MvPolynomial ℕ ℚ) := q(List.get)
  let xs : Q(List (MvPolynomial ℕ ℚ)) := liftListQ xs
  let xs <- Lean.PrettyPrinter.delab xs
  -- logInfo m!"[CHECK {xs_get}]"
  pure xs


elab "remainder" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder _ $R $instCommSemiring $poly $vars $r) =>
      -- logInfo m!"[DEBUG] vars = {vars}"
      let rec parsePoly (e : Expr) : Lean.MetaM String := do
        let e ← checkTypeQ e q(MvPolynomial $σ $R)
        match e with
        | none => pure s!"unknown"
        | some expr =>
          match expr with
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
          | ~q(@OfNat.ofNat _ $b $n) =>
            pure s!"{b}"
          | ~q(@Zero.toOfNat0 _ $z) =>
            -- logInfo m!"[DEBUG] Found zero constant{z}"
            -- dbg_trace s!"[DEBUG] Found zero constant {z}"
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
          logInfo m!"[DEBUG] VarA: {VarA}"
          logInfo m!"[DEBUG] VarB: {VarB}"
          -- dbg_trace s!"View A: {a}"
          -- dbg_trace s!"View B: {b}"
          pure (VarA :: VarB)
        | ~q((∅: Set (MvPolynomial _ _))) => pure []
        | ~q(Set.singleton $v) =>
          let vStr ← parsePoly v
          -- logInfo m!"[DEBUG] Singleton var: {vStr}"
          pure [vStr]
        | ~q(singleton $v) =>
          let vStr ← parsePoly v
          -- logInfo m!"[DEBUG] Single var: {vStr}"
          pure [vStr]
        | _ => unreachable!

      let parsedPoly ← parsePoly poly
      let varsList ← parseVars vars
      let parsedR ← parsePoly r

      logInfo m!"parsed polynomial: {parsedPoly}"
      logInfo m!"parsed vars: {varsList}"
      -- logInfo m!"parsed polynomial: {parsedPoly}"
      -- dbg_trace "parsed vars: {varsList}"
      -- dbg_trace "parsed polynomial: {parsedPoly}"
      -- dbg_trace "parsed remainder: {parsedR}"

      let sage_result ← runsage parsedPoly s!"{varsList}"

      -- logInfo m!"[CHECK] sage_result: {sage_result} sfduhfqiofhqof"


      let result := Json.parse s!"{sage_result}"
      logInfo m!"[DEBUG] sage_json_result: {result}"
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

      let rec parsePoly (e : Expr) : Lean.MetaM String := do
        let e ← checkTypeQ e q(MvPolynomial $σ $R)
        match e with
        | none => pure s!"unknown"
        | some expr =>
          match expr with
          | ~q($a + $b) =>
            let a  ← parsePoly a
            let b  ← parsePoly b
            pure s!"({a} + {b})"

          | ~q(@Sub.sub (MvPolynomial «$σ» «$R») $commring $a $b) => do
            let a ← parsePoly a
            let b ← parsePoly b
            pure s!"({a} - {b})"

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
            pure s!"{b}"

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
          -- logInfo m!"[DEBUG] Singleton var: {vStr}"
          pure [vStr]
        | ~q(singleton $v) =>
          let vStr ← parsePoly v
          -- logInfo m!"[DEBUG] Single var: {vStr}"
          pure [vStr]
        | _ => unreachable!

      let parsedPoly ← parsePoly poly
      let varsList ← parseVars vars
      let parsedR ← parsePoly r

      logInfo m!"parsed vars: {varsList}"
      logInfo m!"parsed polynomial: {parsedPoly}"
      -- dbg_trace "parsed vars: {varsList}"
      -- dbg_trace "parsed polynomial: {parsedPoly}"
      -- dbg_trace "parsed remainder: {parsedR}"

      let sage_result ← runsage parsedPoly s!"{varsList}"

      logInfo m!"[DEBUG] check sage_result 11_26: {sage_result}"


      let result := Json.parse s!"{sage_result}"
      -- logInfo m!"[DEBUG] sage_json_result: {result}"
      let sage_json_result ← parseJson result
      -- logInfo m!"[DEBUG] sage_json_result after parsing: {sage_json_result}"
      let Except.ok arr := sage_json_result.getArr? | failure
      -- logInfo m!"Arr: {arr[0]!}"

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

elab "basis" : tactic  => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsGroebnerBasis _ $R $instCommSemiring $basis $ideal) =>
      -- dbg_trace "basis = {basis}"
      -- logInfo m!"basis = {basis}"

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

            pure s!"({a} + {b})"

          | ~q($a * $b) =>
            let left ← parsePoly a
            let right ← parsePoly b
            -- dbg_trace "FIND MUL: {left} and {right}"
            pure s!"({left} * {right})"

          | ~q(@HSub.hSub (MvPolynomial «$σ» «$R») (MvPolynomial «$σ» «$R») (MvPolynomial «$σ» «$R») $commring $a $b) => do
            let a ← parsePoly a
            let b ← parsePoly b
            pure s!"({a} - {b})"

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
          | ~q(@OfNat.ofNat _ $b $n) =>
            pure s!"{b}"
          | ~q(@Zero.toOfNat0 _ $z) =>
            -- logInfo m!"[DEBUG] Found zero constant{z}"
            -- dbg_trace s!"[DEBUG] Found zero constant {z}"
            pure "0"
          | _ =>
            pure s!"{e}"

      let rec parseBasis(e : Q(Set (MvPolynomial $σ $R))) : Lean.MetaM (List String) := do
        match e with
        | ~q(Insert.insert (self := $_inst) $a $b) =>
          let VarA ← parsePoly a
          let VarB ← parseBasis b
          -- dbg_trace "See If enter this Branch"
          -- logInfo m!"[DEBUG] Insert basis element: {a}"
          -- logInfo m!"[DEBUG] Remaining basis: {b}"
          pure (VarA :: VarB)
        | ~q((∅: Set (MvPolynomial _ _))) => pure []
        | ~q(singleton $v) =>
          let vStr ← parsePoly v
          -- logInfo m!"[DEBUG] Singleton basis element: {vStr}"
          pure [vStr]
        | _ =>
          unreachable!

      let basislist <- parseBasis basis
      -- dbg_trace "parsed basis: {basislist}"
      logInfo m!"parsed basis: {basislist}"
      let sage_result ← runsage' s!"{basislist}"
      let result := Json.parse s!"{sage_result}"
      let sage_json_result ← parseJson result
      -- logInfo m!"[DEBUG] sage_json_result after parsing: {sage_json_result}"
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

-- elab "groebner_basis": tactic => do
--   let goal ← Lean.Elab.Tactic.getMainGoal
--   let t ← goal.getType
--   logInfo m!"[DEBUG] t : {t}"

structure Hypothesis where
  displayName : String
  type : String
deriving Repr

def Hypothesis.list : TacticM (Array Hypothesis) := do
  try withMainContext listHypotheses
  catch | _ => listHypotheses
where
  listHypotheses : TacticM (Array Hypothesis) := do
    let mut xs := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      xs := xs.push $ Hypothesis.mk s!"{decl.userName}" s!"{<- Meta.ppExpr decl.type}"
    return xs


open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)
variable {s : σ →₀ ℕ} {k : Type*} [Field k] {R : Type*} [CommRing R]

lemma aux {f g r : MvPolynomial σ k} {G : Set (MvPolynomial σ k)} (h : r ∈ Ideal.span G) : r + f * g ∈ Ideal.span (insert g G) := by
  have h₁ : f * g ∈ Ideal.span (insert g G) := by
    rw [Ideal.span_insert]
    refine Submodule.mem_sup_left (show f * g ∈ Ideal.span {g} from ?_)
    apply Ideal.mul_mem_left
    exact Ideal.mem_span_singleton_self g
  have h₂ : r ∈ Ideal.span (insert g G) := by
    rw [Ideal.span_insert]
    exact Submodule.mem_sup_right h
  exact (Submodule.add_mem_iff_right (Ideal.span (insert g G)) h₂).mpr h₁

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

      let rec parsePoly (e : Expr) : Lean.MetaM String := do
        let e ← checkTypeQ e q(MvPolynomial $σ $R)
        match e with
        | none => pure s!"unknown"
        | some expr =>
          match expr with
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
          | ~q(@OfNat.ofNat _ $b $n) =>
            logInfo s!"[debug]: go to this branch"
            pure s!"{b}"
          | ~q(@Zero.toOfNat0 _ $z) =>
            -- logInfo m!"[DEBUG] Found zero constant{z}"
            -- dbg_trace s!"[DEBUG] Found zero constant {z}"
            pure "0"
          | _ =>
            pure s!"{e}"

      let rec parseGenerator(e : Q(Set (MvPolynomial $σ $R))) : Lean.MetaM (List String) := do
        match e with
        | ~q(Insert.insert (self := $_inst) $a $b) =>
          let VarA ← parsePoly a
          let VarB ← parseGenerator b
          pure (VarA :: VarB)
        | ~q((∅: Set (MvPolynomial _ _))) => pure []
        | ~q(singleton $v) =>
          let vStr ← parsePoly v
          pure [vStr]
        | _ =>
          unreachable!

      match LHS, RHS with
      | ~q(Ideal.span $I_gens), ~q(Ideal.span $J_gens) =>
        let I_gens_list ←  parseGenerator I_gens
        let J_gens_list ←  parseGenerator J_gens
        let sage_result ← runsage_ideal s!"{I_gens_list}" s!"{J_gens_list}"

        let result := Json.parse s!"{sage_result}"
        let sage_json_result ← parseJson result
        let Except.ok poly_arr := sage_json_result.getArr? | failure
        evalTactic (← `(tactic|
          apply le_antisymm
        ))
        for poly_json in poly_arr do
          evalTactic (← `(tactic|
          focus
            rw [Ideal.span_le]
            intro x hx
            simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with (hx|hx) <;> rw [hx]
            ))
          let Except.ok poly_arr' := poly_json.getArr? | failure
          for poly in poly_arr' do

            let poly ← processElement poly
            let poly ← Lean.PrettyPrinter.delab poly
            logInfo m! "[DEBUG] poly to use : {poly}"
            evalTactic (← `(tactic|
              focus
                apply (iff_of_eq <| congrArg (a₂ := $poly:term ) (· ∈ _) (by decide +kernel)).mpr
                change _ ∈ (_ : Ideal _)
                repeat
                  conv in _ ∈ Ideal.span (insert _ _) => {}
                  apply aux
                apply Ideal.mul_mem_left
                apply Ideal.mem_span_singleton_self
              ))


      | _ =>
        dbg_trace "The left side is not an Ideal.span"


    | _ =>
      logError "Error: Goal is not an equality (Eq.eq) structure."


/-
From Here is some code used to debug and need to be reshaped as soon as possible
-/
partial def parsePoly {u v: Lean.Level}{σ : Q(Type $u)}{R : Q(Type $v)}{r : Q(CommSemiring $R)} (e : Q(MvPolynomial $σ $R)) : MetaM String := do
  match e with
  | ~q($a + $b) =>
    let a  ← parsePoly a
    let b  ← parsePoly b
    pure s!"({a} + {b})"
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



elab "debug" : tactic => do
  evalTactic (← `(tactic|
  apply le_antisymm
  ))
  evalTactic (← `(tactic|
  focus
    rw [Ideal.span_le]
    intro x hx
    simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (hx|hx) <;> rw [hx]
    ))
  evalTactic (← `(tactic|
    focus
      apply (iff_of_eq <| congrArg (a₂ := 1 * X 1 ^ 2 + 1 * X 0 ) (· ∈ _) (by decide +kernel)).mpr
      change _ ∈ (_ : Ideal _)
      repeat
        conv in _ ∈ Ideal.span (insert _ _) => {}
        apply aux
      apply Ideal.mul_mem_left
      apply Ideal.mem_span_singleton_self
    ))
  evalTactic (← `(tactic|
    focus
      apply (iff_of_eq <| congrArg (a₂ := 1 * X 1 ^ 2 + 0 * X 0 ) (· ∈ _) (by decide +kernel)).mpr
      change _ ∈ (_ : Ideal _)
      repeat
        conv in _ ∈ Ideal.span (insert _ _) => {}
        apply aux
      apply Ideal.mul_mem_left
      apply Ideal.mem_span_singleton_self
    ))
  evalTactic (← `(tactic|
  focus
    rw [Ideal.span_le]
    intro x hx
    simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (hx|hx) <;> rw [hx]
    ))
  evalTactic (← `(tactic|
    focus
      apply (iff_of_eq <| congrArg (a₂ := (- 1) * X 1 ^ 2 + 1 * (X 0 + X 1 ^ 2)) (· ∈ (_ : Ideal _)) (by decide +kernel)).mpr
      -- change _ ∈ (_ : Ideal _)
      repeat
        conv in _ ∈ Ideal.span (insert _ _) => {}
        apply aux
      apply Ideal.mul_mem_left
      apply Ideal.mem_span_singleton_self
    ))
  evalTactic (← `(tactic|
    focus
      apply (iff_of_eq <| congrArg (a₂ := 1 * X 1 ^ 2 + 0 * (X 0 + X 1 ^ 2)) (· ∈ (_ : Ideal _)) (by decide +kernel)).mpr
      -- change _ ∈ (_ : Ideal _)
      repeat
        conv in _ ∈ Ideal.span (insert _ _) => {}
        apply aux
      apply Ideal.mul_mem_left
      apply Ideal.mem_span_singleton_self
    ))



#eval parsePoly q(1: MvPolynomial Nat Nat)


end IsRemainder



namespace Mathlib.Tactic.IsGroebner

end IsGroebner

end Tactic



end Mathlib
