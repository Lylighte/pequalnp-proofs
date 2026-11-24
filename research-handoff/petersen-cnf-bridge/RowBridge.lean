import CnfBridge

namespace PetersenCnfBridge

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open SideAtom

-- Each local atom maps to the shared circuit selector or gate value described below.
def SideEncoding {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val : Fin k → Bool) (target : Bool) : Prop :=
  ∃ a : SideAtom n k → Bool,
    (∀ v, a (.raw v) = decide (v ∈ B)) ∧ (∀ j, a (.link j) = decide (j ∈ F)) ∧
    (∀ j, a (.previous j) = val j) ∧ a .result = target ∧
    (∀ j < i, (andBlock (.link j) (.previous j) (.product j)).eval a = true) ∧
    (orBlock (sideInputs U i) .result).eval a = true

theorem sideEncoding_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (val : Fin k → Bool) (target : Bool) :
    SideEncoding U B F i val target ↔ target = sideTrue U B F i val := by
  constructor
  · rintro ⟨a,hb,hf,hv,ht,hp,ho⟩
    simpa [hb,hf,hv,ht] using side_assignment_forces_result U i a hp ho
  · rintro rfl
    exact ⟨sideAssignment U B F i val, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl,
      side_assignment_satisfies U B F i val⟩

-- A gate sees only earlier wires, as in the project's evaluator.
private theorem side_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (v w : Fin k → Bool) (h : ∀ j < i, v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor <;> rintro (hv | ⟨j,hj,hji,hv⟩)
  · exact Or.inl hv
  · exact Or.inr ⟨j,hj,hji,(h j hji).symm.trans hv⟩
  · exact Or.inl hv
  · exact Or.inr ⟨j,hj,hji,(h j hji).trans hv⟩

private theorem stable {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin C.size), i.val < d →
      C.gateValFuel U (d+1) i = C.gateValFuel U d i := by
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    have h j (hj : j < i) : C.gateValFuel U (d+1) j = C.gateValFuel U d j :=
      ih j (by have : j.val < i.val := hj; omega)
    simp only [gateValFuel]
    change (sideTrue U _ _ i (C.gateValFuel U (d+1)) && sideTrue U _ _ i (C.gateValFuel U (d+1))) = _
    rw [side_congr U (C.leftVars i) (C.leftGates i) i _ _ h,
        side_congr U (C.rightVars i) (C.rightGates i) i _ _ h]

theorem gate_equation {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) :=
  (stable C U C.size i i.isLt).symm

inductive Port | left | right | target

def portValues (l r out : Bool) : Port → Bool
  | .left => l
  | .right => r
  | .target => out

def GateEncoding {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (vals : Fin C.size → Bool) (i : Fin C.size) : Prop :=
  ∃ l r, SideEncoding U (C.leftVars i) (C.leftGates i) i vals l ∧
    SideEncoding U (C.rightVars i) (C.rightGates i) i vals r ∧
    (andBlock .left .right .target).eval (portValues l r (vals i)) = true

theorem all_gates_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (vals : Fin C.size → Bool) :
    (∀ i, GateEncoding C U vals i) ↔ vals = C.gateVal U := by
  constructor
  · intro enc
    funext i
    induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction with
    | h i ih =>
      obtain ⟨l,r,hl,hr,ht⟩ := enc i
      have hout : vals i = (l && r) := (andBlock_valid ..).mp ht
      rw [hout, (sideEncoding_iff ..).mp hl, (sideEncoding_iff ..).mp hr,
        side_congr U (C.leftVars i) (C.leftGates i) i _ _ ih,
        side_congr U (C.rightVars i) (C.rightGates i) i _ _ ih]
      exact (gate_equation C U i).symm
  · rintro rfl i
    exact ⟨_, _, (sideEncoding_iff ..).2 rfl, (sideEncoding_iff ..).2 rfl,
      (andBlock_valid ..).2 (gate_equation C U i)⟩

def OutputEncoding {k : ℕ} (selected : Finset (Fin k)) (vals : Fin k → Bool) (target : Bool) : Prop :=
  ∃ a : SideAtom 0 k → Bool,
    (∀ j, a (.link j) = decide (j ∈ selected)) ∧ (∀ j, a (.previous j) = vals j) ∧
    a .result = target ∧
    (∀ j, (andBlock (.link j) (.previous j) (.product j)).eval a = true) ∧
    (orBlock ((Finset.univ.sort (· ≤ ·)).map product) .result).eval a = true

theorem outputEncoding_iff {k : ℕ} (selected : Finset (Fin k)) (vals : Fin k → Bool) (target : Bool) :
    OutputEncoding selected vals target ↔ (target = true ↔ ∃ j ∈ selected, vals j = true) := by
  constructor
  · rintro ⟨a,hs,hv,ht,hp,ho⟩
    have prod (j : Fin k) : a (.product j) = (decide (j ∈ selected) && vals j) := by
      simpa [hs,hv] using (andBlock_valid ..).mp (hp j)
    simpa [ht,prod] using (orBlock_valid ..).mp ho
  · intro h
    let a : SideAtom 0 k → Bool
      | .raw v => Fin.elim0 v
      | .link j => decide (j ∈ selected)
      | .previous j => vals j
      | .product j => decide (j ∈ selected) && vals j
      | .result => target
    refine ⟨a,fun _ => rfl,fun _ => rfl,rfl,fun _ => (andBlock_valid ..).2 rfl,?_⟩
    apply (orBlock_valid ..).2
    simpa [a] using h

-- The production encoder omits bare output selectors. This assumption is kept explicit.
theorem boundary_rows_iff {n : ℕ} {R : Type} (C : AndCountCircuit n) (h : C.outVars = ∅)
    (points : R → Finset (Fin n)) (labels : R → Bool) :
    (∃ vals : R → Fin C.size → Bool,
      ∀ t, (∀ i, GateEncoding C (points t) (vals t) i) ∧
        OutputEncoding C.outGates (vals t) (labels t)) ↔
      ∀ t, C.eval (points t) = labels t := by
  have ends (t : R) : C.eval (points t) = true ↔ ∃ j ∈ C.outGates, C.gateVal (points t) j = true := by
    simp [AndCountCircuit.eval,h]
  constructor
  · rintro ⟨vals,hr⟩ t
    obtain ⟨hg,ho⟩ := hr t
    rw [(all_gates_iff ..).mp hg] at ho
    exact Bool.eq_iff_iff.mpr ((ends t).trans ((outputEncoding_iff ..).mp ho).symm)
  · intro he
    refine ⟨fun t => C.gateVal (points t), fun t => ⟨(all_gates_iff ..).2 rfl,?_⟩⟩
    apply (outputEncoding_iff ..).2
    simpa only [← he t] using ends t

end PetersenCnfBridge
