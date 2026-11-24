import GlobalAssignment

namespace PetersenGlobal

open Std.Sat PetersenCnfBridge PetersenDimacs PetersenExport
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

def vars (C : AndCountCircuit 10) (i : Fin C.size) (s : Side) :=
  if s = 0 then C.leftVars i else C.rightVars i
def wires (C : AndCountCircuit 10) (i : Fin C.size) (s : Side) :=
  if s = 0 then C.leftGates i else C.rightGates i

-- Gate positions beyond the source circuit are padded with zero-valued gates.
-- The source gate index is always its original natural number.
def fromCircuit (C : AndCountCircuit 10) : Values where
  atom g s v := if h : g.val < C.size then decide (v ∈ vars C ⟨g.val,h⟩ s) else false
  wire g s j := if h : g.val < C.size then
    decide ((⟨j.val,by omega⟩ : Fin C.size) ∈ wires C ⟨g.val,h⟩ s) else false
  out g := if h : g.val < C.size then decide ((⟨g.val,h⟩ : Fin C.size) ∈ C.outGates) else false
  gate r g := if h : g.val < C.size then C.gateVal (pointSet r) ⟨g.val,h⟩ else false

theorem side_from (C : AndCountCircuit 10) (r : Row) (g : Gate) (s : Side) (h : g.val < C.size) :
    bitSide (fromCircuit C) r g s =
      sideTrue (pointSet r) (vars C ⟨g.val,h⟩ s) (wires C ⟨g.val,h⟩ s)
        ⟨g.val,h⟩ (C.gateVal (pointSet r)) := by
  let i : Fin C.size := ⟨g.val,h⟩
  have small (j : Fin g.val) : (earlier j).val < C.size := by change j.val < C.size; omega
  apply decide_eq_decide.mpr
  change ((∃ v : Vertex, (point r).1.testBit v.val = true ∧ (fromCircuit C).atom g s v = true) ∨
      ∃ j : Fin g.val, (fromCircuit C).wire g s j = true ∧ (fromCircuit C).gate r (earlier j) = true) ↔ _
  simp only [fromCircuit,h,dite_eq_left,small,decide_eq_true_eq,pointSet,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro (⟨v,hm,hv⟩ | ⟨j,hj,he⟩)
    · exact Or.inl ⟨v,hv,hm⟩
    · exact Or.inr ⟨⟨j.val,by omega⟩,hj,j.isLt,he⟩
  · rintro (⟨v,hv,hm⟩ | ⟨j,hj,hji,he⟩)
    · exact Or.inl ⟨v,hm,hv⟩
    · exact Or.inr ⟨⟨j.val,hji⟩,hj,he⟩

theorem gate_from (C : AndCountCircuit 10) (r : Row) (g : Gate) :
    (fromCircuit C).gate r g =
      (bitSide (fromCircuit C) r g 0 && bitSide (fromCircuit C) r g 1) := by
  by_cases h : g.val < C.size
  · rw [side_from C r g 0 h, side_from C r g 1 h]
    simpa [fromCircuit,h,vars,wires] using gate_equation C (pointSet r) ⟨g.val,h⟩
  · simp [fromCircuit,h,bitSide]

theorem used_from (C : AndCountCircuit 10) (v : Vertex) (g : Gate) (h : g.val < C.size) :
    bitUsed (fromCircuit C) v g =
      decide (v ∈ C.leftVars ⟨g.val,h⟩ ∨ v ∈ C.rightVars ⟨g.val,h⟩) := by
  simp [bitUsed,fromCircuit,h,vars]

theorem cap_from (C : AndCountCircuit 10)
    (cap : ∀ v : Vertex, (Finset.univ.filter (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2)
    (v : Vertex) : tripleClauses (bitUsed (fromCircuit C) v) := by
  intro a b c hcb hba
  by_cases ha : a.val < C.size
  · have hb : b.val < C.size := by omega
    have hc : c.val < C.size := by omega
    have old := ((circuit_occurrences C v).mpr (cap v))
      ⟨a.val,ha⟩ ⟨b.val,hb⟩ ⟨c.val,hc⟩ hcb hba
    simp only [packClause, CNF.Clause.eval_add, CNF.Clause.eval_empty] at old ⊢
    simpa only [used_from C v a ha,used_from C v b hb,used_from C v c hc] using old
  · simp [packClause,bitUsed,fromCircuit,ha]

theorem out_from (C : AndCountCircuit 10) (hk : C.size ≤ 6) (r : Row) (ho : C.outVars = ∅) :
    bitResult (fromCircuit C) r = C.eval (pointSet r) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bitResult,AndCountCircuit.eval,decide_eq_true_eq,ho,Finset.notMem_empty,
    false_and,exists_false, false_or]
  constructor
  · rintro ⟨g,hs,hv⟩
    by_cases h : g.val < C.size
    · exact ⟨⟨g.val,h⟩,by simpa [fromCircuit,h] using hs,by simpa [fromCircuit,h] using hv⟩
    · simp [fromCircuit,h] at hs
  · rintro ⟨j,hj,hv⟩
    let g : Gate := ⟨j.val,by omega⟩
    have hg : g.val < C.size := j.isLt
    exact ⟨g,by simpa [fromCircuit,hg,g] using hj,by simpa [fromCircuit,hg,g] using hv⟩

theorem candidate_assignment (C : AndCountCircuit 10) (hk : C.size ≤ 6)
    (cap : ∀ v : Vertex, (Finset.univ.filter (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2)
    (labels : ∀ r : Row, C.eval (pointSet r) = (point r).2)
    (cover : ∀ v : Vertex, ∃ r : Row, v ∈ pointSet r ∧ (point r).2 = false) :
    symbolicFormula.eval (assignment (fromCircuit C)) = true := by
  have noBare := outVars_empty_of_covered_zeros C pointSet (fun r => (point r).2) cover labels
  apply all_holds _ (cap_from C cap) (gate_from C)
  exact fun r => (out_from C hk r noBare).trans (labels r)

end PetersenGlobal
