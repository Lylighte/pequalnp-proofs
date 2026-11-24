import RowBridge

namespace PetersenCnfBridge

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- One indicator per vertex and gate. The two selector bits use both sides of
-- the same gate, so a vertex on both sides is counted only once.
def CapEncoding {n : ℕ} (C : AndCountCircuit n) : Prop :=
  ∃ flag : Fin n → Fin C.size → Bool, ∀ v,
    tripleClauses (flag v) ∧ ∀ i,
      (orBlock [.left,.right] .target).eval
        (portValues (decide (v ∈ C.leftVars i)) (decide (v ∈ C.rightVars i)) (flag v i)) = true

theorem capEncoding_iff {n : ℕ} (C : AndCountCircuit n) :
    CapEncoding C ↔
      ∀ v : Fin n, (Finset.univ.filter (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2 := by
  have used (v : Fin n) (i : Fin C.size) (f : Bool) :
      (orBlock [.left,.right] .target).eval
        (portValues (decide (v ∈ C.leftVars i)) (decide (v ∈ C.rightVars i)) f) = true ↔
      f = decide (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) := by
    rw [orBlock_valid]
    cases f <;> simp [portValues]
  constructor
  · rintro ⟨flag,h⟩ v
    have heq : flag v = fun i => decide (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) :=
      funext fun i => (used ..).mp ((h v).2 i)
    apply (circuit_occurrences C v).mp
    rw [← heq]
    exact (h v).1
  · intro h
    exact ⟨fun v i => decide (v ∈ C.leftVars i ∨ v ∈ C.rightVars i),
      fun v => ⟨(circuit_occurrences C v).mpr (h v), fun i => (used ..).mpr rfl⟩⟩

theorem outVars_empty_of_covered_zeros {n : ℕ} {R : Type} (C : AndCountCircuit n)
    (points : R → Finset (Fin n)) (labels : R → Bool)
    (cover : ∀ v : Fin n, ∃ t, v ∈ points t ∧ labels t = false)
    (correct : ∀ t, C.eval (points t) = labels t) : C.outVars = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨t,ht,hzero⟩ := cover v
  have yes : C.eval (points t) = true :=
    decide_eq_true (Or.inl ⟨v,hv,ht⟩)
  rw [correct t,hzero] at yes
  contradiction

-- A model-level equivalence. Shared raw selectors are supplied by the same C
-- in every row. The formula contains only the raw encoding's logical blocks.
theorem typed_circuit_iff {n : ℕ} {R : Type} (k : ℕ)
    (points : R → Finset (Fin n)) (labels : R → Bool)
    (cover : ∀ v : Fin n, ∃ t, v ∈ points t ∧ labels t = false) :
    (∃ C : AndCountCircuit n, C.size = k ∧ C.WellFormed ∧ C.outVars = ∅ ∧ CapEncoding C ∧
      ∃ vals : R → Fin C.size → Bool, ∀ t, (∀ i, GateEncoding C (points t) (vals t) i) ∧
        OutputEncoding C.outGates (vals t) (labels t)) ↔
    (∃ C : AndCountCircuit n, C.size = k ∧ C.WellFormed ∧
      (∀ v : Fin n, (Finset.univ.filter (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
      ∀ t, C.eval (points t) = labels t) := by
  constructor
  · rintro ⟨C,hk,hw,ho,hc,hr⟩
    exact ⟨C,hk,hw,(capEncoding_iff C).mp hc,(boundary_rows_iff C ho points labels).mp hr⟩
  · rintro ⟨C,hk,hw,hc,hr⟩
    have ho := outVars_empty_of_covered_zeros C points labels cover hr
    exact ⟨C,hk,hw,ho,(capEncoding_iff C).mpr hc,(boundary_rows_iff C ho points labels).mpr hr⟩

end PetersenCnfBridge
