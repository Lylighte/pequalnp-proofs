import PetersenEquivariance

namespace GateReindex

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenEquivariance (bareCount Separates)

variable {n k : ℕ}

abbrev reindex (C : AndCountCircuit n) (e : Equiv.Perm (Fin C.size)) : AndCountCircuit n :=
  { C with
    leftVars := fun i => C.leftVars (e.symm i)
    rightVars := fun i => C.rightVars (e.symm i)
    leftGates := fun i => (C.leftGates (e.symm i)).map e.toEmbedding
    rightGates := fun i => (C.rightGates (e.symm i)).map e.toEmbedding
    outGates := C.outGates.map e.toEmbedding }

def Wire (C : AndCountCircuit n) (i j : Fin C.size) :=
  j ∈ C.leftGates i ∨ j ∈ C.rightGates i

def OrderOnWires (C : AndCountCircuit n) (e : Equiv.Perm (Fin C.size)) :=
  ∀ i j, Wire C i j → e j < e i

theorem reindexSize (C : AndCountCircuit n) (e : Equiv.Perm (Fin C.size)) :
    (reindex C e).size = C.size := rfl

theorem reindexWF (C : AndCountCircuit n) (e : Equiv.Perm (Fin C.size)) (top : OrderOnWires C e) :
    (reindex C e).WellFormed := by
  intro i
  obtain ⟨i,rfl⟩ := e.surjective i
  constructor
  · intro j hj
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hj
    exact top i j (Or.inl (by simpa using hj))
  · intro j hj
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hj
    exact top i j (Or.inr (by simpa using hj))

theorem bareEq (C : AndCountCircuit n) (e : Equiv.Perm (Fin C.size)) (v : Fin n) :
    bareCount (reindex C e) v = bareCount C v := by
  let source := Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
  have mapped : Finset.univ.filter (fun i : Fin C.size =>
      v ∈ (reindex C e).leftVars i ∨ v ∈ (reindex C e).rightVars i) = source.map e.toEmbedding := by
    ext i
    simp [source, Finset.mem_map_equiv]
  change _ = source.card
  exact (congrArg Finset.card mapped).trans (Finset.card_map e.toEmbedding)

lemma existsMapped (e : Equiv.Perm (Fin k)) (F : Finset (Fin k)) (P Q : Fin k → Prop)
    (hp : ∀ j ∈ F, Q (e j) ↔ P j) :
    (∃ j ∈ F.map e.toEmbedding, Q j) ↔ ∃ j ∈ F, P j := by
  constructor
  · rintro ⟨x,hx,hq⟩
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hx
    exact ⟨j,hj,(hp j hj).mp hq⟩
  · rintro ⟨j,hj,hp'⟩
    exact ⟨e j,Finset.mem_map_of_mem _ hj,(hp j hj).mpr hp'⟩

theorem fuelEq (C : AndCountCircuit n) (e : Equiv.Perm (Fin C.size)) (wf : C.WellFormed)
    (top : OrderOnWires C e) (U : Finset (Fin n)) (d : ℕ) (i : Fin C.size) :
    (reindex C e).gateValFuel U d (e i) = C.gateValFuel U d i := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    let D := reindex C e
    have side (B : Finset (Fin n)) (F : Finset (Fin C.size))
        (old : ∀ j ∈ F, j < i) (new : ∀ j ∈ F, e j < e i) :
        sideTrue U B (F.map e.toEmbedding) (e i) (D.gateValFuel U d) =
          sideTrue U B F i (C.gateValFuel U d) := by
      apply decide_eq_decide.mpr
      apply or_congr Iff.rfl
      apply existsMapped
      intro j hj
      change (e j < e i ∧ (reindex C e).gateValFuel U d (e j) = true) ↔
        (j < i ∧ C.gateValFuel U d j = true)
      simp only [new j hj, old j hj, true_and, ih j]
    simp only [gateValFuel, reindex, Equiv.symm_apply_apply]
    exact congrArg₂ Bool.and (side _ _ (wf i).1 (fun j hj => top i j (Or.inl hj)))
      (side _ _ (wf i).2 (fun j hj => top i j (Or.inr hj)))

theorem evalEq (C : AndCountCircuit n) (e : Equiv.Perm (Fin C.size)) (wf : C.WellFormed)
    (top : OrderOnWires C e) (U : Finset (Fin n)) : (reindex C e).eval U = C.eval U := by
  apply decide_eq_decide.mpr
  apply or_congr Iff.rfl
  apply existsMapped
  intro j _
  change (reindex C e).gateValFuel U C.size (e j) = true ↔ C.gateValFuel U C.size j = true
  rw [fuelEq C e wf top]

-- Move t to zero. Earlier gates move up one slot, and later gates keep their index.
def frontIndex (t x : Fin k) : Fin k :=
  ⟨if x.val = t.val then 0 else if x.val < t.val then x.val+1 else x.val, by
    split_ifs <;> omega⟩

lemma frontInjective (t : Fin k) : Function.Injective (frontIndex t) := by
  intro x y h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [frontIndex] at hh
  split_ifs at hh <;> omega

noncomputable def frontPerm (t : Fin k) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective _ (frontInjective t).bijective_of_finite

theorem atZero (t : Fin k) : (frontPerm t t).val = 0 := by
  change (frontIndex t t).val = 0
  simp [frontIndex]

theorem frontOrder (C : AndCountCircuit n) (t : Fin C.size) (wf : C.WellFormed)
    (left : C.leftGates t = ∅) (right : C.rightGates t = ∅) : OrderOnWires C (frontPerm t) := by
  intro i j h
  have old : j < i := h.elim ((wf i).1 j) ((wf i).2 j)
  have diff : i.val ≠ t.val := by
    intro eq
    have he : i = t := Fin.ext eq
    simp [Wire, he, left, right] at h
  change (frontIndex t j).val < (frontIndex t i).val
  change j.val < i.val at old
  simp only [frontIndex]
  split_ifs <;> omega

theorem independentToFront (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) (t : Fin C.size)
    (wf : C.WellFormed) (left : C.leftGates t = ∅) (right : C.rightGates t = ∅)
    (sep : Separates G C) :
    ∃ D : AndCountCircuit n, D.size = C.size ∧ D.WellFormed ∧
      (∀ v, bareCount D v = bareCount C v) ∧ (∀ U, D.eval U = C.eval U) ∧
      Separates G D ∧ ∃ j : Fin D.size, j.val = 0 ∧
        D.leftVars j = C.leftVars t ∧ D.rightVars j = C.rightVars t ∧
        D.leftGates j = ∅ ∧ D.rightGates j = ∅ := by
  let e := frontPerm t
  let D := reindex C e
  have top : OrderOnWires C e := frontOrder C t wf left right
  have eq (U) : D.eval U = C.eval U := evalEq C e wf top U
  refine ⟨D,rfl,reindexWF C e top,bareEq C e,eq,?_,e t,atZero t,?_,?_,?_,?_⟩
  · intro I hi hm
    simpa only [eq] using sep I hi hm
  · simp [D]
  · simp [D]
  · simp [D, reindex, left]
  · simp [D, reindex, right]

end GateReindex

#print axioms GateReindex.bareEq
#print axioms GateReindex.fuelEq
#print axioms GateReindex.independentToFront
