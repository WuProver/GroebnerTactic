import Lean

open Lean

def runSageCode (code : String) : IO String.Slice := do
  let out ← IO.Process.output {
    cmd := "./.venv/bin/python",
    args := #["Runner/sage_runner.py", code]
  }

  if out.exitCode == 0 then
    return out.stdout.trimAscii
  else
    throw <| IO.userError s!"SageCell fail: {out.stderr}"

def runner : IO Unit := do
  try
    let result ← runSageCode "factorial(3)"
    IO.println s!"{result}"
  catch e =>
    IO.println e.toString

#eval runner
