import FirstBlindClique

namespace BlindBatch
open PEqualNP.AndCount
open FirstBlindClique (V Input value blind)
open PetersenBoundary (decode)
abbrev Bits := BitVec 15
abbrev Mask := Fin 1024

def rowBits : V → Bits := ![17698,12817,18570,5172,713,6157,110,880,25472,31744]
def vertices : List V := [0,1,2,3,4,5,6,7,8,9]

theorem rowBit : ∀ x : V, ∀ r : Fin 15,
    (rowBits x).getLsbD r.val = true ↔ x ∈ Petersen905.rows r := by decide +kernel
theorem allVertices : ∀ x : V, x ∈ vertices := by decide +kernel

def sigAux (m : Mask) : List V → Bits
  | [] => 0
  | x :: xs => (if m.val.testBit x.val then rowBits x else 0) ||| sigAux m xs

def sig (m : Mask) := sigAux m vertices

lemma zeroBit (i : ℕ) : (0 : Bits).getLsbD i = false := by
  change (0 : ℕ).testBit i = false
  exact Nat.zero_testBit i

lemma sigAuxBit (m : Mask) (xs : List V) (r : Fin 15) :
    (sigAux m xs).getLsbD r.val = true ↔
      ∃ x ∈ xs, m.val.testBit x.val = true ∧ x ∈ Petersen905.rows r := by
  induction xs with
  | nil => simp [sigAux]
  | cons x xs ih =>
    by_cases h : m.val.testBit x.val = true
    · simp only [sigAux,h,ite_true,BitVec.getLsbD_or,Bool.or_eq_true,rowBit,ih]
      simp [h]
    · rw [sigAux,if_neg h,BitVec.getLsbD_or,zeroBit,Bool.false_or,ih]
      simp [h]

lemma decodeMem (m : Mask) (x : V) : x ∈ decode m ↔ m.val.testBit x.val = true := by
  simp [decode]

lemma sigBit (m : Mask) (r : Fin 15) : (sig m).getLsbD r.val = true ↔
    ∃ x ∈ decode m, x ∈ Petersen905.rows r := by
  simp only [sig,sigAuxBit, allVertices, true_and, decodeMem]

def stable (L R : Mask) (A B : Bits) (x : V) : Bits :=
  let p := (if L.val.testBit x.val then ~~~(0 : Bits) else A) &&&
    (if R.val.testBit x.val then ~~~(0 : Bits) else B)
  (~~~(rowBits x)) &&& (~~~((A &&& B) ^^^ p))

lemma plusMem (m : Mask) (x : V) (r : Fin 15) :
    (∃ v ∈ decode m, v ∈ insert x (Petersen905.rows r)) ↔
      m.val.testBit x.val = true ∨ ∃ v ∈ decode m, v ∈ Petersen905.rows r := by
  simp [Finset.mem_insert, and_or_left, exists_or, decodeMem]

lemma injected (b : Bool) (a : Bits) (r : Fin 15) :
    (if b then ~~~(0 : Bits) else a).getLsbD r.val = (b || a.getLsbD r.val) := by
  cases b
  · rfl
  · change (~~~(0 : Bits)).getLsbD r.val = true
    rw [BitVec.getLsbD_not]
    simp only [r.isLt,decide_true,zeroBit,Bool.not_false,Bool.and_self]

lemma stableBit (L R : Mask) (x : V) (r : Fin 15) :
    (stable L R (sig L) (sig R) x).getLsbD r.val = true ↔ blind (decode L) (decode R) x r := by
  have l := sigBit L r
  have rr := sigBit R r
  have row := rowBit x r
  unfold stable blind value
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  rw [show decide (∃ v ∈ decode L, v ∈ insert x (Petersen905.rows r)) =
      decide (L.val.testBit x.val = true ∨ ∃ v ∈ decode L, v ∈ Petersen905.rows r) from decide_eq_decide.mpr (plusMem L x r),
    show decide (∃ v ∈ decode R, v ∈ insert x (Petersen905.rows r)) =
      decide (R.val.testBit x.val = true ∨ ∃ v ∈ decode R, v ∈ Petersen905.rows r) from decide_eq_decide.mpr (plusMem R x r)]
  have l' : decide (∃ v ∈ decode L, v ∈ Petersen905.rows r) = (sig L).getLsbD r.val := Bool.eq_iff_iff.mpr (by simpa using l.symm)
  have r' : decide (∃ v ∈ decode R, v ∈ Petersen905.rows r) = (sig R).getLsbD r.val := Bool.eq_iff_iff.mpr (by simpa using rr.symm)
  rw [← row]
  simp only [Bool.decide_or, Bool.decide_eq_true,l',r']
  rw [injected,injected]
  cases L.val.testBit x.val <;> cases R.val.testBit x.val <;> cases (sig L).getLsbD r.val <;>
    cases (sig R).getLsbD r.val <;> cases (rowBits x).getLsbD r.val <;> decide

lemma nonzeroBit {b : Bits} (h : b ≠ 0) : ∃ r : Fin 15, b.getLsbD r.val = true := by
  by_contra! no
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa using no ⟨i,hi⟩

structure Entry where
  left : Mask
  right : Mask
  sigLeft : Bits
  sigRight : Bits
  group : List (V × Bits)

def one (e : Entry) (p : V × Bits) : Bool := decide (
  (e.left.val.testBit p.1.val = true ∨ e.right.val.testBit p.1.val = true) ∧ p.2 ≠ 0 ∧
  p.2 = stable e.left e.right e.sigLeft e.sigRight p.1)

def pair (p q : V × Bits) : Bool := decide (p.1 = q.1 ∨
  ((p.2 &&& rowBits q.1) ≠ 0 ∧ (p.2 &&& q.2) ≠ 0))

def check (e : Entry) : Bool :=
  decide (e.sigLeft = sig e.left ∧ e.sigRight = sig e.right ∧ e.group.length = 6 ∧
    (e.group.map Prod.fst).Nodup) && e.group.all (fun p => one e p && e.group.all (pair p))

def Seven (l r : Mask) : Prop := ∀ (C : AndCountCircuit 10) (g : Fin C.size), g.val = 0 →
  C.leftVars g = decode l → C.rightVars g = decode r →
  PetersenEquivariance.Separates Petersen905.graph C →
  (∀ x, PetersenEquivariance.bareCount C x ≤ 2) → 7 ≤ C.size

theorem sound (e : Entry) (ok : check e = true) : Seven e.left e.right := by
  intro C g zero l r sep cap
  have ⟨basic,checks⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨la,ra,len,nodup⟩ := of_decide_eq_true basic
  have row (p : V × Bits) (hp : p ∈ e.group) := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp checks) p hp)
  have valid (p) (hp : p ∈ e.group) := of_decide_eq_true (row p hp).1
  have bits (p) (hp : p ∈ e.group) (i : Fin 15) :
      p.2.getLsbD i.val = true ↔ blind (decode e.left) (decode e.right) p.1 i := by
    rw [(valid p hp).2.2,la,ra,stableBit]
  let T := (e.group.map Prod.fst).toFinset
  have item (x : V) (hx : x ∈ T) : ∃ b, (x,b) ∈ e.group := by
    obtain ⟨p,hp,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    rcases p with ⟨v,b⟩
    exact ⟨b,he ▸ hp⟩
  have both (p q) (hp : p ∈ e.group) (hq : q ∈ e.group) (ne : p.1 ≠ q.1) :=
    (of_decide_eq_true ((List.all_eq_true.mp (row p hp).2) q hq)).resolve_left ne
  have block (p q) (hp : p ∈ e.group) (hq : q ∈ e.group) (ne : p.1 ≠ q.1) :
      ∃ i : Fin 15, q.1 ∈ Petersen905.rows i ∧ blind (decode e.left) (decode e.right) p.1 i := by
    obtain ⟨i,hi⟩ := nonzeroBit (both p q hp hq ne).1
    rw [BitVec.getLsbD_and,Bool.and_eq_true] at hi
    exact ⟨i,(rowBit _ _).mp hi.2,(bits _ hp i).mp hi.1⟩
  have lower := FirstBlindClique.bound C g zero (decode e.left) (decode e.right) T l r sep cap
  have bound : T.card ≤ C.size-1 := by
    apply lower
    · intro x hx
      obtain ⟨b,hb⟩ := item x hx
      simpa only [decodeMem] using (valid _ hb).1
    · intro x hx
      obtain ⟨b,hb⟩ := item x hx
      obtain ⟨i,hi⟩ := nonzeroBit (valid _ hb).2.1
      exact ⟨i,(bits _ hb i).mp hi⟩
    · intro x hx y hy ne
      obtain ⟨a,ha⟩ := item x hx
      obtain ⟨b,hb⟩ := item y hy
      refine ⟨block _ _ ha hb ne,block _ _ hb ha ne.symm,?_⟩
      obtain ⟨i,hi⟩ := nonzeroBit (both _ _ ha hb ne).2
      rw [BitVec.getLsbD_and,Bool.and_eq_true] at hi
      exact ⟨i,(bits _ ha i).mp hi.1,(bits _ hb i).mp hi.2⟩
  have six : T.card = 6 := (List.toFinset_card_of_nodup nodup).trans (by simpa using len)
  omega

end BlindBatch
#print axioms BlindBatch.sound
