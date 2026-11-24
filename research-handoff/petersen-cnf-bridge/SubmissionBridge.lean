import FromCircuit
import PetersenBoundary

namespace PetersenSubmissionBridge

open PetersenCnfBridge PetersenDimacs PetersenExport PetersenGlobal PetersenBoundary

-- The export iterates positive masks in insertion order; PetersenBoundary's
-- checked positive list is sorted. Keep the point order here and prove membership.
private def table : Array (Nat × Bool) := #[(50,false),(69,false),(104,false),(116,false),(138,false),(201,false),(208,false),(276,false),(385,false),(402,false),(521,false),(548,false),(554,false),(770,false),(773,false),(51,true),(54,true),(58,true),(114,true),(178,true),(306,true),(562,true),(71,true),(77,true),(85,true),(101,true),(197,true),(325,true),(581,true),(105,true),(106,true),(108,true),(120,true),(232,true),(360,true),(616,true),(117,true),(118,true),(124,true),(244,true),(372,true),(628,true),(139,true),(142,true),(154,true),(170,true),(202,true),(394,true),(650,true),(203,true),(205,true),(217,true),(233,true),(457,true),(713,true),(209,true),(210,true),(212,true),(216,true),(240,true),(464,true),(720,true),(277,true),(278,true),(284,true),(308,true),(340,true),(404,true),(788,true),(387,true),(389,true),(393,true),(401,true),(417,true),(449,true),(897,true),(403,true),(406,true),(410,true),(434,true),(466,true),(914,true),(523,true),(525,true),(537,true),(553,true),(585,true),(649,true),(777,true),(549,true),(550,true),(556,true),(564,true),(612,true),(676,true),(804,true),(555,true),(558,true),(570,true),(618,true),(682,true),(810,true),(771,true),(774,true),(778,true),(786,true),(802,true),(834,true),(898,true),(775,true),(781,true),(789,true),(805,true),(837,true),(901,true)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 18000000 in
private theorem table_exact : PetersenExport.points = table := by decide +kernel

private def listed (p : Nat × Bool) : Prop :=
  if p.2 then p.1 ∈ positiveMasks.map Fin.val else p.1 ∈ negativeMasks.map Fin.val

private instance (p : Nat × Bool) : Decidable (listed p) := by unfold listed; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6500000 in
private theorem listed_table : ∀ r : Row, listed (table[r.val]?.getD (0,false)) := by decide +kernel

theorem row_listed (r : Row) : listed (point r) := by
  simpa only [point,table_exact] using listed_table r

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6500000 in
theorem zero_cover : ∀ v : Vertex, ∃ r : Row, v ∈ pointSet r ∧ (point r).2 = false := by
  simp only [pointSet,point,table_exact]
  decide +kernel

private theorem as_mask (r : Row) (m : Fin 1024) (he : m.val = (point r).1) :
    pointSet r = decode m := by simp [pointSet,decode,he]

attribute [local irreducible] point PetersenExport.points

theorem row_labels (C : PEqualNP.AndCount.AndCountCircuit 10)
    (h : PetersenEquivariance.Separates Petersen905.graph C) :
    ∀ r : Row, C.eval (pointSet r) = (point r).2 := by
  intro r
  have rows := (separationIff C).mp h
  have mem : listed (point r) := row_listed r
  cases hb : (point r).2 with
  | false =>
    have hm : (point r).1 ∈ negativeMasks.map Fin.val := by simpa [listed,hb] using mem
    obtain ⟨m,hm,he⟩ := List.mem_map.mp hm
    rw [as_mask r m he]
    exact rows.1 _ (Finset.mem_image_of_mem decode (by simpa using hm))
  | true =>
    have hm : (point r).1 ∈ positiveMasks.map Fin.val := by simpa [listed,hb] using mem
    obtain ⟨m,hm,he⟩ := List.mem_map.mp hm
    rw [as_mask r m he]
    exact rows.2 _ (Finset.mem_image_of_mem decode (by simpa using hm))

def PostedStatement : Prop :=
∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
  ¬ (∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true))

theorem of_unsat (unsat : symbolicFormula.Unsat) : PostedStatement := by
  rintro G rfl ⟨C,_,hk,hcap,hsep⟩
  have sep : PetersenEquivariance.Separates Petersen905.graph C := hsep
  have sat := candidate_assignment C hk hcap (row_labels C sep) zero_cover
  rw [unsat (assignment (fromCircuit C))] at sat
  contradiction

theorem of_numbered_unsat (unsat : (symbolicFormula.relabel closedId).Unsat) :
    PostedStatement := of_unsat ((unsat_after_renaming symbolicFormula).mp unsat)

end PetersenSubmissionBridge
