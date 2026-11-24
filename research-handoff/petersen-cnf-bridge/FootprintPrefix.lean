import FootprintCenters

namespace PetersenFootprintCenters

open PEqualNP.AndCount PetersenSuffix PetersenTailCnf PetersenFirstPins PetersenBoundary

-- Pack one actual second-gate side into the production selector numbering:
-- vertices 0..9, followed by a reference to gate zero at bit 10.
def packedBit (S : Finset (Fin 10)) (readGate : Bool) (i : Fin 11) :=
  if low : i.val < 10 then decide (⟨i.val,low⟩ ∈ S) else readGate

def packSide (S : Finset (Fin 10)) (readGate : Bool) : Fin 2048 :=
  let bv := BitVec.ofBoolListLE ((List.finRange 11).map (packedBit S readGate))
  ⟨bv.toNat,by simpa [bv] using bv.toFin.isLt⟩

theorem packSide_bit (S : Finset (Fin 10)) (g : Bool) (i : Fin 11) :
    (packSide S g).val.testBit i.val = packedBit S g i := by
  change (BitVec.ofBoolListLE ((List.finRange 11).map (packedBit S g))).getLsbD _ = _
  rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp)]
  simp

theorem packSide_raw (S : Finset (Fin 10)) (g : Bool) : bits 10 (packSide S g).val = S := by
  ext v
  have bit := packSide_bit S g (v.castAdd 1)
  change (packSide S g).val.testBit v.val = _ at bit
  simp [bits,bit,packedBit,v.isLt]

theorem packSide_gate (S : Finset (Fin 10)) (g : Bool) : (packSide S g).val.testBit 10 = g := by
  exact packSide_bit S g 10

private theorem packed_wires (C : AndCountCircuit 10) (hk : 2 ≤ C.size)
    (W : Fin C.size → Finset (Fin C.size)) (wf : ∀ i j, j ∈ W i → j < i)
    (s : Fin 2048) (eq : s.val.testBit 10 = decide (head C 2 hk 0 ∈ W (head C 2 hk 1)))
    (i j : Fin 2) : head C 2 hk j ∈ W (head C 2 hk i) ↔
      j ∈ (![∅,if s.val.testBit 10 then {0} else ∅] : Fin 2 → Finset (Fin 2)) i := by
  fin_cases i
  · change _ ↔ j ∈ (∅ : Finset (Fin 2))
    simp only [Finset.notMem_empty,iff_false]
    intro h
    have bad := wf _ _ h
    exact Nat.not_lt_zero j.val bad
  · fin_cases j
    · change _ ↔ (0 : Fin 2) ∈ (if s.val.testBit 10 then {0} else ∅ : Finset (Fin 2))
      by_cases yes : head C 2 hk 0 ∈ W (head C 2 hk 1) <;> simp [eq,yes]
    · have no : head C 2 hk 1 ∉ W (head C 2 hk 1) := fun h => (lt_irrefl _) (wf _ _ h)
      change head C 2 hk 1 ∈ W (head C 2 hk 1) ↔
        (1 : Fin 2) ∈ (if s.val.testBit 10 then {0} else ∅ : Finset (Fin 2))
      cases s.val.testBit 10 <;> simp [no]

theorem actual_prefix (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (wf : C.WellFormed)
    (a b : Fin 1024) (first : FirstSides C a b) :
    ∃ l r : Fin 2048, Matches C (gates a.val b.val l.val r.val) hk := by
  let h := head C 2 hk
  let mk (S : Fin C.size → Finset (Fin 10)) (W : Fin C.size → Finset (Fin C.size)) :=
    packSide (S (h 1)) (decide (h 0 ∈ W (h 1)))
  let l := mk C.leftVars C.leftGates
  let r := mk C.rightVars C.rightGates
  obtain ⟨_,la,rb⟩ := first
  refine ⟨l,r,⟨?_,?_,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact la
    · exact (packSide_raw _ _).symm
  · intro i
    fin_cases i
    · exact rb
    · exact (packSide_raw _ _).symm
  · exact packed_wires C hk C.leftGates (fun i => (wf i).1) l (packSide_gate _ _)
  · exact packed_wires C hk C.rightGates (fun i => (wf i).2) r (packSide_gate _ _)

def packFoot (a b s : Nat) : Fin 32768 :=
  let bv := BitVec.ofBoolListLE (negativeMasks.map (side a b s))
  ⟨bv.toNat,lt_of_lt_of_le bv.isLt (by rw [List.length_map]; decide)⟩

theorem packFoot_class (a b s : Nat) : SideClass a b s (packFoot a b s).val := by
  intro m hm
  have hi := List.idxOf_lt_length_of_mem hm
  change side a b s m = (BitVec.ofBoolListLE (negativeMasks.map (side a b s))).getLsbD _
  rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hi)]
  simp only [List.getElem_map,List.getElem_idxOf,Option.getD_some]

theorem actual_group (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (wf : C.WellFormed)
    (a b : Fin 1024) (first : FirstSides C a b) :
    ∃ l r : Fin 2048, ∃ p q : Fin 32768, Matches C (gates a b l r) hk ∧
      SideClass a b l p ∧ SideClass a b r q := by
  obtain ⟨l,r,front⟩ := actual_prefix C hk wf a b first
  exact ⟨l,r,packFoot a b l,packFoot a b r,front,packFoot_class a b l,packFoot_class a b r⟩

end PetersenFootprintCenters

#print axioms PetersenFootprintCenters.actual_prefix
#print axioms PetersenFootprintCenters.actual_group
