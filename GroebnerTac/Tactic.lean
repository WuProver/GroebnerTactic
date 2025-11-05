import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MvPolynomial
import MonomialOrderedPolynomial.Polynomial


import GroebnerTac.AstToLean
import GroebnerTac.AstToSage
import GroebnerTac.MathMLToAST
import GroebnerTac.ExprToAst

import Groebner.Basic
import Groebner.List

import Mathlib.Tactic
import Lean


namespace Mathlib.Tactic.IsRemainder
open Lean Elab Tactic Meta Term
open Meta Ring Qq PrettyPrinter AtomM
open MvPolynomial MonomialOrder

/- We define how to start a sage process-/
inductive SageResponse
| success (mathml : String) (plain : String)
| error (msg : String)

abbrev SageChild := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }

initialize sageProcess : IO.Ref (Option SageChild) ← IO.mkRef none

private def getSageProcess : IO SageChild := do
  match ← sageProcess.get with
  | some proc => return proc
  | none =>
    let proc ← IO.Process.spawn {
      cmd := "sage"
      args := #["-q"]
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    sageProcess.set (some proc)
    return proc

private def sageCodeTemplate : String :=
"reset()
import json
from sympy.printing.mathml import mathml
def to_mathml(expr):
    if hasattr(expr, '_sympy_'):
        return mathml(expr._sympy_())
    elif hasattr(expr, '__iter__') and not isinstance(expr, str):
        return '<list>' + ''.join(f'<item>{to_mathml(item)}</item>' for item in expr) + '</list>'
    else:
        return repr(expr)
try:
    {assumptions}
    res = ({cmd})
    a = res[-1] if isinstance(res, tuple) and 'assume' in '{cmd}' else res
    result = {'mathml': to_mathml(a), 'result': repr(a)}
except Exception as e:
    result = {'error': f'{type(e).__name__}: {e}', 'mathml': None, 'result': None}
print(json.dumps(result))

"

private def runSageCommand (cmd : String) (assumptions : String := "") : IO SageResponse := do
  let proc ← getSageProcess
  let py := sageCodeTemplate.replace "{cmd}" cmd |>.replace "{assumptions}" assumptions
  proc.stdin.putStr py
  proc.stdin.flush

  let line ← proc.stdout.getLine
  let jsonResponse := line.trim.replace "sage: " "" |>.replace "....: " ""

  match Lean.Json.parse jsonResponse with
  | .ok json => match json.getObjVal? "error" with
    | .ok errorMsg =>
      match errorMsg.getStr? with
      | .ok msg => return .error msg
      | .error _ => return .error "Parse error"
    | .error _ => match json.getObjVal? "mathml", json.getObjVal? "result" with
      | .ok mathmlJson, .ok resultJson =>
        match mathmlJson.getStr?, resultJson.getStr? with
        | .ok mathml, .ok result => return .success mathml result
        | _, _ => return .error "Invalid mathml/result format"
      | _, _ => return .error "Missing mathml/result fields"
  | .error err => return .error s!"JSON parse error: {err}"


def checkSage : IO Unit := do
  let output ← IO.Process.output {cmd := "which", args := #["sage"]}
  if output.exitCode != 0 then
    println! "SageMath 未安装或不在 PATH 中"
  else
    println! "SageMath 路径: {output.stdout}"

private def getHypotheses : TacticM (List MathAST) := do
  let lctx ← getLCtx
  let mut hyps : List MathAST := []
  for localDecl in lctx.decls do
    if let some decl := localDecl then
      if !decl.isImplementationDetail then
        if ← Meta.isProp decl.type then
          if let some propAST ← LeanSage.exprToAST decl.type then
            hyps := (.hypothesis propAST) :: hyps
  return hyps.reverse

private def buildSageCode (goalAST : MathAST) (hyps : List MathAST) : String × String :=
  match goalAST with
  | .exists vars body =>
    let constraints := hyps.map (fun | .hypothesis prop => prop | ast => ast)
    let transformedAST := .exists vars (constraints.foldl (fun acc h => .and [acc, h]) body)
    ("", astToSage transformedAST)
  | _ =>
    let assumptions := String.intercalate "\n    " (hyps.map astToSage)
    (assumptions, astToSage goalAST)


elab "remainder" : tactic => do
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


elab ref:  "check_remainder" : tactic => do
  let goal ← getMainGoal
  logInfo s!"Checking remainder for goal: {← goal.getType}"

  goal.withContext do
    let hyps ← getHypotheses
    let some goalAST ← LeanSage.exprToAST (← goal.getType) | throwError "Failed to convert goal to AST"
    let (assumptions, baseSageCode) := buildSageCode goalAST hyps
    let sageCode := s!"bool({baseSageCode})"
    logInfo s!"assumptions: {assumptions}"
    logInfo s!"sageCode : {sageCode}"

    return ()

  return ()

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



elab "showGoal" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let t ← checkTypeQ t q(Prop)
  match t with
  | none => return
  | some expr =>
    match expr with
    | ~q(@(@lex $σ $instLinearOrder $instWellFounded).IsRemainder _ $R $instCommSemiring $poly $vars $r) =>
      -- dbg_trace "poly = {poly}"
      dbg_trace "vars = {vars}"
      dbg_trace "r = {r}"

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
          logInfo m!"[DEBUG] View A: {a}"
          logInfo m!"[DEBUG] View B: {b}"
          logInfo m!"[DEBUG] VarA: {VarA}"
          logInfo m!"[DEBUG] VarB: {VarB}"
          dbg_trace s!"View A: {a}"
          dbg_trace s!"View B: {b}"
          pure (VarA :: VarB)
        | ~q((∅: Set (MvPolynomial _ _))) => pure []
        | ~q(Set.singleton $v) =>
          let vStr ← parsePoly v
          logInfo m!"[DEBUG] Singleton var: {vStr}"
          pure [vStr]
        | _ => pure []

      let parsedPoly ← parsePoly poly
      let varsList ← parseVars vars
      let parsedR ← parsePoly r


      dbg_trace "parsed vars: {varsList}"
      dbg_trace "parsed polynomial: {parsedPoly}"
      dbg_trace "parsed remainder: {parsedR}"

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
      pure ()


end IsRemainder

namespace Mathlib.Tactic.IsGroebner

end IsGroebner

end Tactic

end Mathlib
