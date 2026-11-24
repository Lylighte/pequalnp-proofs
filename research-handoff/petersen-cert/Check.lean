import Std.Sat.CNF.Dimacs
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

def readCnf (s : String) : Except String (CNF Nat) := do
  let header :: lines := s.splitOn "\n" | throw "missing DIMACS header"
  let ["p", "cnf", nv, nc] := header.splitOn " " | throw "bad DIMACS header"
  let some nvars := nv.toNat? | throw "invalid variable count"
  let some nclauses := nc.toNat? | throw "invalid clause count"
  let mut out : Array (CNF.Clause Nat) := #[]
  for line in lines do
    if line.isEmpty then continue
    let "0" :: reversed := (line.splitOn " ").reverse | throw "unterminated clause"
    let mut literals : List (Literal Nat) := []
    for token in reversed do
      let some i := token.toInt? | throw "bad literal"
      unless 0 < i.natAbs && i.natAbs ≤ nvars do throw "literal out of range"
      literals := (i.natAbs - 1, decide (i > 0)) :: literals
    out := out.push (CNF.Clause.ofLiterals literals)
  unless out.size == nclauses do throw "unexpected clause count"
  let cnf : CNF Nat := ⟨out⟩
  unless cnf.dimacs == s do throw "DIMACS byte-for-byte round-trip failed"
  return cnf

def main (args : List String) : IO Unit := do
  let [cnfPath, proofPath] := args | throw (IO.userError "expected a DIMACS path and an LRAT path")
  let cnf ← IO.ofExcept (readCnf (← IO.FS.readFile cnfPath))
  let actions ← IO.ofExcept (LRAT.parseLRATProof (← IO.FS.readBinFile proofPath))
  unless LRAT.check actions cnf do throw (IO.userError "LRAT rejected")
  -- Negative control: an empty trace cannot refute this input.
  if LRAT.check #[] cnf then throw (IO.userError "empty trace unexpectedly accepted")
  IO.println ("{\"check\":true,\"dimacsRoundTrip\":true,\"emptyTraceRejected\":true,\"clauses\":" ++
    toString cnf.clauses.size ++ ",\"actions\":" ++ toString actions.size ++ "}")
