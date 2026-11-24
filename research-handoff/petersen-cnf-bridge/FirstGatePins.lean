import SubmissionBridge

namespace PetersenFirstPins

open Std.Sat PEqualNP.AndCount PetersenCnfBridge PetersenDimacs PetersenExport
open PetersenGlobal PetersenBoundary PetersenSubmissionBridge

abbrev Mask := Fin 1024

def pins (l r : Mask) : CNF Variable := pack ((List.finRange 2).flatMap fun s =>
  (List.finRange 10).map fun v => [(bare 0 s v, (if s = 0 then l else r).val.testBit v.val)])

def pinned (l r : Mask) : CNF Variable := symbolicFormula ++ pins l r

-- Each certificate can be checked against this numbered formula for its two masks.
def numbered (l r : Mask) : CNF Nat := (pinned l r).relabel closedId

def FirstSides (C : AndCountCircuit 10) (l r : Mask) : Prop :=
  ∃ h : 0 < C.size, C.leftVars ⟨0,h⟩ = decode l ∧ C.rightVars ⟨0,h⟩ = decode r

def Candidate (C : AndCountCircuit 10) : Prop :=
  C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Vertex, (Finset.univ.filter (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    PetersenEquivariance.Separates Petersen905.graph C

theorem pins_hold (C : AndCountCircuit 10) (l r : Mask) (hm : FirstSides C l r) :
    (pins l r).eval (assignment (fromCircuit C)) = true := by
  obtain ⟨h, hl, hr⟩ := hm
  rw [pins, pack_valid]
  simp only [List.forall_mem_flatMap, List.forall_mem_map, List.mem_finRange, true_implies,
    List.mem_singleton]
  intro s v
  fin_cases s <;> simp [bare, assignment, fromCircuit, vars, h, hl, hr, decode]

theorem pinned_candidate (C : AndCountCircuit 10) (l r : Mask)
    (hc : Candidate C) (hm : FirstSides C l r) :
    (pinned l r).eval (assignment (fromCircuit C)) = true := by
  obtain ⟨_, hs, cap, sep⟩ := hc
  rw [pinned, CNF.eval_append, candidate_assignment C hs cap (row_labels C sep) zero_cover,
    pins_hold C l r hm]
  rfl

-- The covering hypothesis is about candidate circuits: it may first relabel
-- a candidate or exchange gate sides to reach a listed representative.
theorem of_numbered_cases (kept : Mask → Mask → Prop)
    (cover : (∃ C, Candidate C) → ∃ C l r, Candidate C ∧ kept l r ∧ FirstSides C l r)
    (unsat : ∀ l r, kept l r → (numbered l r).Unsat) : PostedStatement := by
  rintro G rfl ⟨C, hC⟩
  obtain ⟨D,l,r,hD,hk,hm⟩ := cover ⟨C,hC⟩
  have noSat := (unsat_after_renaming (pinned l r)).mp (unsat l r hk)
  have sat := pinned_candidate D l r hD hm
  rw [noSat (assignment (fromCircuit D))] at sat
  contradiction

end PetersenFirstPins
