import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1414_aux
open PEqualNP.CircuitLowerBounds

abbrev Input := Fin 7 → Bool
def atMask (m : Fin 128) : Input := fun i => m.val.testBit i.val
theorem listed (x : Input) : ∃ m : Fin 128, atMask m = x := by
  let z := BitVec.ofBoolListLE (List.ofFn x)
  have h : z.toNat < 128 := by simpa [z] using z.isLt
  refine ⟨⟨z.toNat,h⟩,funext (fun i => ?_)⟩
  change z.getLsbD i.val = x i
  rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  exact List.getElem_ofFn _

def eliminable (C : Circuit) (p : Fin 7) (b : Bool) (j : Fin 10) :=
  (∀ y z : Input, y p = b → z p = b →
    (C.wires (List.ofFn y)).getD (7+j.val) false = (C.wires (List.ofFn z)).getD (7+j.val) false) ∨
  ∃ w < 7+j.val, ∀ u : Input, u p = b →
    (C.wires (List.ofFn u)).getD (7+j.val) false = (C.wires (List.ofFn u)).getD w false

def Tight (C : Circuit) := ∃ (p : Fin 7) (b : Bool) (S : Finset (Fin 10)),
  (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, eliminable C p b j

def allow (words : Array Nat) (p : Fin 7) (b : Bool) : Finset (Fin 10) :=
  Finset.univ.filter (fun j => words[2*p.val+b.toNat]!.testBit j.val)

def val (columns : Array Nat) (w : Nat) (m : Fin 128) := columns[w]!.testBit m.val
def sample (ws : Array Nat) (p : Fin 7) (b : Bool) (j : Fin 10) (k : Nat) : Fin 128 :=
  ⟨(ws[(2*p.val+b.toNat)*10+j.val]! >>> (7*k)) % 128,Nat.mod_lt _ (by decide)⟩

abbrev Check (columns ws : Array Nat) (p : Fin 7) (b : Bool) (j : Fin 10) : Prop :=
  let row := sample ws p b j
  let gate := val columns (7+j.val)
  atMask (row 0) p = b ∧ atMask (row 1) p = b ∧ gate (row 0) ≠ gate (row 1) ∧
    ∀ w : Fin (7+j.val), atMask (row (2+w.val)) p = b ∧ gate (row (2+w.val)) ≠ val columns w.val (row (2+w.val))
def Rows (C : Circuit) (cols : Array Nat) :=
  ∀ m : Fin 128, C.wires (List.ofFn (atMask m)) = List.ofFn (fun w : Fin 17 => val cols w.val m)

theorem wire {C : Circuit} {cols : Array Nat} (rows : Rows C cols) (m : Fin 128) (w : Nat) (hw : w < 17) :
    (C.wires (List.ofFn (atMask m))).getD w false = val cols w m := by
  rw [rows]
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hw)]
  exact List.getElem_ofFn _

theorem reject {C : Circuit} {cols ws good : Array Nat} (rows : Rows C cols)
    (checks : ∀ p b j, j ∉ allow good p b → Check cols ws p b j)
    (small : ∀ p b, (allow good p b).card < (if b = true then 4 else 3)) : ¬ Tight C := by
  rintro ⟨p,b,S,card,all⟩
  have sub : S ⊆ allow good p b := by
    intro j hj
    by_contra excluded
    let row := sample ws p b j
    have q := checks p b j excluded
    obtain ⟨x,y,diff,older⟩ := q
    have le : 7+j.val < 17 := by omega
    rcases all j hj with constant | ⟨w,wh,copy⟩
    · have eq := constant (atMask (row 0)) (atMask (row 1)) x y
      exact diff (by simpa only [wire rows _ _ le] using eq)
    · let i : Fin (7+j.val) := ⟨w,wh⟩
      obtain ⟨on,mismatch⟩ := older i
      have eq := copy (atMask (row (2+w))) on
      exact mismatch (by simpa only [wire rows _ _ le,wire rows _ _ (lt_trans wh le)] using eq)
  exact (Nat.not_lt_of_ge (card.trans (Finset.card_le_card sub))) (small p b)

def candidate : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.and,[1,7]⟩,⟨.or,[2,4]⟩,⟨.and,[3,9]⟩,⟨.or,[4,6]⟩,⟨.and,[5,11]⟩,⟨.and,[6,0]⟩,⟨.or,[8,10]⟩,⟨.or,[12,13]⟩,⟨.or,[14,15]⟩],16⟩
def cols : Array Nat := #[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xfafafafafafafafafafafafafafafafa,0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xff00f000ff00f000ff00f000ff00f000,0xffffffffffffffffffff0000ffff0000,0xffffffff00000000ffff000000000000,0xaaaaaaaaaaaaaaaa0000000000000000,0xffc8f8c8ffc8f8c8ffc8f8c8ffc8f8c8,0xffffffffaaaaaaaaffff000000000000,0xffffffffffeafaeafffff8c8ffc8f8c8]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 40000000 in
theorem dataOK : Rows candidate cols := by unfold Rows; decide +kernel
theorem basisOK : ∀ g ∈ candidate.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
theorem sizeOK : candidate.size = 10 := rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 40000000 in
private theorem correctnessTable : ∀ m : Fin 128, candidate.eval (List.ofFn (atMask m)) = true ↔ ∃ i : Fin 7, atMask m i = true ∧ atMask m (i+1) = true := by decide +kernel
theorem cycleOK (x : Input) : candidate.eval (List.ofFn x) = true ↔ ∃ i : Fin 7, x i = true ∧ x (i+1) = true := by
  obtain ⟨m,rfl⟩ := listed x
  exact correctnessTable m
private theorem equal0 : ∀ m : Fin 128, atMask m 0 = false → val cols 7 m = val cols 2 m := by decide +kernel
private theorem equal6 : ∀ m : Fin 128, atMask m 0 = false → val cols 13 m = false := by decide +kernel
private theorem equal8 : ∀ m : Fin 128, atMask m 0 = false → val cols 15 m = val cols 12 m := by decide +kernel
theorem yesTight : Tight candidate := by
  refine ⟨0,false,{0,6,8},by decide,?_⟩
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl|rfl|rfl
  · refine Or.inr ⟨2,by decide,?_⟩
    intro x hx
    obtain ⟨m,rfl⟩ := listed x
    exact (wire dataOK m 7 (by decide)).trans ((equal0 m hx).trans (wire dataOK m 2 (by decide)).symm)
  · left
    intro y z hy hz
    obtain ⟨u,rfl⟩ := listed y
    obtain ⟨v,rfl⟩ := listed z
    exact (wire dataOK u 13 (by decide)).trans ((equal6 u hy).trans ((equal6 v hz).symm.trans (wire dataOK v 13 (by decide)).symm))
  · refine Or.inr ⟨12,by decide,?_⟩
    intro x hx
    obtain ⟨m,rfl⟩ := listed x
    exact (wire dataOK m 15 (by decide)).trans ((equal8 m hx).trans (wire dataOK m 12 (by decide)).symm)
end PEqualNP.Outside.L_meta_1414_aux
