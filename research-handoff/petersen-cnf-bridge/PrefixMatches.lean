import SuffixProjection

namespace PetersenSuffix

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
variable {n : Nat}

-- C has the same first P.size gate selectors as P; output fields are irrelevant.
structure Matches (C P : AndCountCircuit n) (hk : P.size ≤ C.size) : Prop where
  left (i : Fin P.size) : C.leftVars (head C P.size hk i) = P.leftVars i
  right (i : Fin P.size) : C.rightVars (head C P.size hk i) = P.rightVars i
  leftWire (i j : Fin P.size) : head C P.size hk j ∈ C.leftGates (head C P.size hk i) ↔ j ∈ P.leftGates i
  rightWire (i j : Fin P.size) : head C P.size hk j ∈ C.rightGates (head C P.size hk i) ↔ j ∈ P.rightGates i

private theorem match_side (C P : AndCountCircuit n) (hk : P.size ≤ C.size) (U B : Finset (Fin n))
    (i : Fin P.size) (F : Finset (Fin C.size)) (G : Finset (Fin P.size))
    (w : ∀ j, head C P.size hk j ∈ F ↔ j ∈ G)
    (prior : ∀ j < i, C.gateVal U (head C P.size hk j) = P.gateVal U j) :
    sideTrue U B F (head C P.size hk i) (C.gateVal U) = sideTrue U B G i (P.gateVal U) := by
  apply decide_eq_decide.mpr
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j,hj,lt,yes⟩
    change j.val < i.val at lt
    let t : Fin P.size := ⟨j.val,by omega⟩
    have same : head C P.size hk t = j := Fin.ext rfl
    exact ⟨t,(w t).mp (same ▸ hj),lt,(prior t lt) ▸ (same ▸ yes)⟩
  · rintro ⟨j,hj,lt,yes⟩
    exact ⟨head C P.size hk j,(w j).mpr hj,lt,(prior j lt).trans yes⟩

theorem matched_gate (C P : AndCountCircuit n) (hk : P.size ≤ C.size) (h : Matches C P hk)
    (U : Finset (Fin n)) (i : Fin P.size) :
    C.gateVal U (head C P.size hk i) = P.gateVal U i := by
  induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin P.size → Fin P.size → Prop)).induction) with
  | h i ih =>
    rw [PetersenCnfBridge.gate_equation C U _,PetersenCnfBridge.gate_equation P U i,h.left i,h.right i]
    exact congrArg₂ Bool.and (match_side C P hk U _ i _ _ (h.leftWire i) ih)
      (match_side C P hk U _ i _ _ (h.rightWire i) ih)

private def headEmb (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) : Fin k ↪ Fin C.size :=
  ⟨head C k hk, fun _ _ he => Fin.ext (congrArg (fun j : Fin C.size => j.val) he)⟩

theorem prefix_count (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) (v : Fin n) :
    ((uses C v).filter (fun i => i.val < k)).card =
      (Finset.univ.filter (fun i : Fin k =>
        v ∈ C.leftVars (head C k hk i) ∨ v ∈ C.rightVars (head C k hk i))).card := by
  let A := Finset.univ.filter (fun i : Fin k =>
    v ∈ C.leftVars (head C k hk i) ∨ v ∈ C.rightVars (head C k hk i))
  have eq : A.map (headEmb C k hk) = (uses C v).filter (fun i => i.val < k) := by
    ext j
    simp only [A, uses, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨hi,i.isLt⟩
    · rintro ⟨m,lo⟩
      exact ⟨⟨j.val,lo⟩,m,rfl⟩
  rw [← eq, Finset.card_map]

theorem matched_available (C P : AndCountCircuit n) (hk : P.size ≤ C.size) (h : Matches C P hk) :
    available C P.size = available P P.size := by
  ext v
  simp only [available,Finset.mem_filter,Finset.mem_univ,true_and,prefix_count C _ hk,
    prefix_count P _ (Nat.le_refl _),h.left,h.right]
  rfl

theorem matched_row (C P : AndCountCircuit n) (hk : P.size ≤ C.size) (h : Matches C P hk)
    (U : Finset (Fin n)) : row C P.size hk U = row P P.size (Nat.le_refl _) U := by
  simp only [row, matched_available C P hk h,matched_gate C P hk h]
  rfl

end PetersenSuffix
