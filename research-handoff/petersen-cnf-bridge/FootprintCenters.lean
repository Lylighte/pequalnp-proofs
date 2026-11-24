import MixedStar

namespace PetersenFootprintCenters

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenSuffix PetersenTailCnf PetersenFirstPins PetersenNormalized PetersenBoundary PetersenMixedStar
open Petersen905 (related)

abbrev M := Fin 1024

abbrev gates (a b l r : Nat) : AndCountCircuit 10 where
  size := 2
  leftVars := ![bits 10 a,bits 10 l]
  rightVars := ![bits 10 b,bits 10 r]
  leftGates := ![∅,if l.testBit 10 then {0} else ∅]
  rightGates := ![∅,if r.testBit 10 then {0} else ∅]
  outVars := ∅
  outGates := ∅

def raw (s : Nat) (m : M) := decide (s &&& m.val ≠ 0)
def h0 (a b : Nat) (m : M) := raw a m && raw b m
def side (a b s : Nat) (m : M) := raw s m || (s.testBit 10 && h0 a b m)
def h1 (a b l r : Nat) (m : M) := side a b l m && side a b r m
def seen (s t : Nat) (v : V) := s.testBit v.val || t.testBit v.val
def count (a b l r : Nat) (v : V) := (seen a b v).toNat + (seen l r v).toNat
def Sub (s t : Nat) := ∀ i : Fin 11, s.testBit i.val = true → t.testBit i.val = true

theorem sub_of_and (s t : Nat) (h : s &&& t = s) : Sub s t := by
  intro i on
  have eq := congrArg (fun n : Nat => n.testBit i.val) h
  simpa only [Nat.testBit_and,on,Bool.true_and] using eq

theorem raw_iff (s : Nat) (m : M) : raw s m = true ↔ ∃ v ∈ bits 10 s, v ∈ decode m := by
  simp only [raw,decide_eq_true_eq]
  constructor
  · intro nonzero
    obtain ⟨i,act⟩ := Nat.exists_testBit_of_ne_zero nonzero
    rw [Nat.testBit_and,Bool.and_eq_true] at act
    have small : i < 10 := by
      by_contra! hi
      have h : 1024 ≤ 2^i := Nat.pow_le_pow_right (n := 2) (i := 10) (by decide) hi
      exact Bool.false_ne_true ((Nat.testBit_lt_two_pow (m.isLt.trans_le h)).symm.trans act.2)
    exact ⟨⟨i,small⟩,by simpa [bits] using act.1,by simpa [decode] using act.2⟩
  · rintro ⟨v,hv,hm⟩ zero
    have eq := congrArg (fun n : Nat => n.testBit v.val) zero
    simp only [Nat.testBit_and,Nat.zero_testBit,(Finset.mem_filter.mp hv).2,
      (Finset.mem_filter.mp hm).2, Bool.true_and] at eq
    contradiction

theorem first_eval (a b l r : Nat) (m : M) :
    (gates a b l r).gateVal (decode m) 0 = h0 a b m := by
  rw [PetersenOneHelper.firstProduct _ _ rfl]
  apply Bool.eq_iff_iff.mpr
  change (decide (∃ v ∈ bits 10 a, v ∈ decode m) && decide (∃ v ∈ bits 10 b, v ∈ decode m)) = true ↔ _
  simp only [Bool.and_eq_true,decide_eq_true_eq,h0,raw_iff]

private theorem second_side (a b l r s : Nat) (m : M) :
    sideTrue (decode m) (bits 10 s) (if s.testBit 10 then {0} else ∅) (1 : Fin 2)
      ((gates a b l r).gateVal (decode m)) = side a b s m := by
  apply Bool.eq_iff_iff.mpr
  cases eq : s.testBit 10 <;>
    simp [sideTrue,side,eq,raw_iff,first_eval]

theorem second_eval (a b l r : Nat) (m : M) :
    (gates a b l r).gateVal (decode m) 1 = h1 a b l r m := by
  rw [PetersenCnfBridge.gate_equation]
  exact congrArg₂ Bool.and (second_side a b l r l m) (second_side a b l r r m)

private theorem used (s t : Nat) (v : V) :
    (v ∈ bits 10 s ∨ v ∈ bits 10 t) ↔ seen s t v = true := by simp [seen,bits]

theorem use_count (a b l r : Nat) (v : V) :
    (uses (gates a b l r) v).card = count a b l r v := by
  let keep (j : Fin 2) := ![seen a b v,seen l r v] j
  have eq : uses (gates a b l r) v = (Finset.univ.filter fun j => keep j = true) := by
    ext j
    fin_cases j <;> simp [uses,gates,keep,used]
  rw [eq]
  have all : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  rw [all]
  cases f : seen a b v <;> cases g : seen l r v <;> simp [count,keep,f,g] <;> decide

theorem side_mono (a b s t : Nat) (incl : Sub s t) (m : M) :
    side a b s m = true → side a b t m = true := by
  simp only [side,Bool.or_eq_true,Bool.and_eq_true,raw_iff]
  rintro (⟨v,vs,vm⟩ | ⟨sel,z⟩)
  · exact Or.inl ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,incl (v.castAdd 1)
      (Finset.mem_filter.mp vs).2⟩,vm⟩
  · exact Or.inr ⟨incl 10 sel,z⟩

theorem count_mono (a b ll rl l r : Nat) (L : Sub ll l) (R : Sub rl r) (v : V) :
    count a b ll rl v ≤ count a b l r v := by
  have yes : seen ll rl v = true → seen l r v = true := by
    simp only [seen,Bool.or_eq_true]
    exact Or.imp (L (v.castAdd 1)) (R (v.castAdd 1))
  unfold count
  cases p : seen ll rl v <;> cases q : seen l r v <;> simp_all

-- The ith bit of the packed negative footprint is in the boundary's row order.
def fpOn (fp : Nat) (m : M) := fp.testBit (negativeMasks.idxOf m)
def SideClass (a b s fp : Nat) := ∀ m ∈ negativeMasks, side a b s m = fpOn fp m

structure Box where
  a : Nat
  b : Nat
  ll : Nat
  lh : Nat
  rl : Nat
  rh : Nat
  lf : Nat
  rf : Nat
  deriving Repr

structure Member (B : Box) (l r : Nat) : Prop where
  ll : Sub B.ll l
  lh : Sub l B.lh
  rl : Sub B.rl r
  rh : Sub r B.rh
  lf : SideClass B.a B.b l B.lf
  rf : SideClass B.a B.b r B.rf

def negSecond (B : Box) (m : M) := fpOn (B.lf &&& B.rf) m

theorem neg_eq (B : Box) (l r : Nat) (member : Member B l r) (m : M) (hm : m ∈ negativeMasks) :
    h1 B.a B.b l r m = negSecond B m := by
  simp only [h1,member.lf m hm,member.rf m hm,negSecond,fpOn,Nat.testBit_and]

theorem pos_upper (B : Box) (l r : Nat) (member : Member B l r) (m : M) :
    h1 B.a B.b l r m = true → h1 B.a B.b B.lh B.rh m = true := by
  simp only [h1,Bool.and_eq_true]
  exact And.imp (side_mono _ _ _ _ member.lh m) (side_mono _ _ _ _ member.rh m)

-- Positive and negative rows share the enlarged set of available bare variables.
-- A chosen bare signal is available on every row because use counts are row-independent.
def view (a b ll rl : Nat) (m : M) (z : Bool) (x : Fin 12) : Bool :=
  Fin.addCases (m := 10) (n := 2) (motive := fun _ => Bool)
    (fun v : V => m.val.testBit v.val && decide (count a b ll rl v < 2))
    (fun j => ![h0 a b m,z] j) x

theorem actual_view (a b l r : Nat) (m : M) (x : Fin 12) :
    x ∈ projected (gates a b l r) (decode m) ↔ view a b l r m (h1 a b l r m) x = true := by
  refine Fin.addCases (m := 10) (n := 2) (fun v => ?_) (fun j => ?_) x
  · have rawJoin (S : Finset V) (T : Finset (Fin 2)) : v.castAdd 2 ∈ join S T ↔ v ∈ S := by
      rw [← finSumFinEquiv_apply_left (n := 2) v]
      simp [join]
    have cut : ((uses (gates a b l r) v).filter (fun i => i.val < 2)) = uses (gates a b l r) v :=
      Finset.filter_eq_self.mpr (fun i _ => i.isLt)
    change v.castAdd 2 ∈ join (decode m ∩ available (gates a b l r) 2) _ ↔ _
    rw [rawJoin]
    simp only [Finset.mem_inter,available,decode,Finset.mem_filter,Finset.mem_univ,true_and,
      cut,view,Fin.addCases_left,Bool.and_eq_true,decide_eq_true_eq]
    rw [use_count a b l r v]
  · have gateJoin (S : Finset V) (T : Finset (Fin 2)) : Fin.natAdd 10 j ∈ join S T ↔ j ∈ T := by
      rw [← finSumFinEquiv_apply_right (m := 10) j]
      simp [join]
    change Fin.natAdd 10 j ∈ join _ (Finset.univ.filter (fun q : Fin 2 =>
      (gates a b l r).gateVal (decode m) q = true)) ↔ _
    rw [gateJoin]
    simp only [view,Fin.addCases_right,Finset.mem_filter,Finset.mem_univ,true_and]
    fin_cases j <;> simp [first_eval,second_eval]

def upper (B : Box) (m : M) := view B.a B.b B.ll B.rl m (h1 B.a B.b B.lh B.rh m)
def lowerNeg (B : Box) (m : M) := view B.a B.b B.ll B.rl m (negSecond B m)

theorem active_upper (B : Box) (l r : Nat) (member : Member B l r) (m : M) (x : Fin 12) :
    x ∈ projected (gates B.a B.b l r) (decode m) → upper B m x = true := by
  rw [actual_view]
  refine Fin.addCases (m := 10) (n := 2) (fun v => ?_) (fun j => ?_) x
  · simp only [upper,view,Fin.addCases_left,Bool.and_eq_true,decide_eq_true_eq]
    exact And.imp id (fun h => lt_of_le_of_lt (count_mono _ _ _ _ _ _ member.ll member.rl v) h)
  · simp only [upper,view,Fin.addCases_right]
    fin_cases j
    · simp
    · exact pos_upper B l r member m

theorem negative_transfer (B : Box) (l r : Nat) (member : Member B l r) (p n : M)
    (negative : n ∈ negativeMasks) (x : Fin 12) :
    x ∈ projected (gates B.a B.b l r) (decode p) → lowerNeg B n x = true →
      x ∈ projected (gates B.a B.b l r) (decode n) := by
  rw [actual_view,actual_view]
  refine Fin.addCases (m := 10) (n := 2) (fun v => ?_) (fun j => ?_) x
  · simp only [lowerNeg,view,Fin.addCases_left,Bool.and_eq_true,decide_eq_true_eq]
    exact fun hp hn => ⟨hn.1,hp.2⟩
  · simp only [lowerNeg,view,Fin.addCases_right]
    fin_cases j <;> simp [neg_eq B l r member n negative]

def blockedBits (B : Box) (p : M) := (List.finRange 12).all fun x =>
  (List.finRange 12).all fun y =>
    !(upper B p x && upper B p y && decide (10 ≤ x.val ∨ 10 ≤ y.val)) ||
      negativeMasks.any (fun n => lowerNeg B n x && lowerNeg B n y)

theorem blocked_member (B : Box) (l r : Nat) (member : Member B l r) (p : M)
    (cert : blockedBits B p = true) : Blocked (gates B.a B.b l r) (decode p) := by
  intro x hx y hy mixed
  have check := List.all_eq_true.mp (List.all_eq_true.mp cert x (List.mem_finRange x)) y (List.mem_finRange y)
  have ux := active_upper B l r member p x hx
  have uy := active_upper B l r member p y hy
  simp only [ux,uy,mixed,decide_true,Bool.true_and,Bool.not_true,Bool.false_or] at check
  obtain ⟨n,neg,on⟩ := List.any_eq_true.mp check
  obtain ⟨nx,ny⟩ := Bool.and_eq_true_iff.mp on
  exact ⟨decode n,Finset.mem_image_of_mem _ (by simpa using neg),
    negative_transfer B l r member p n neg x hx nx,negative_transfer B l r member p n neg y hy ny⟩

def RowEdge (p : M) (v w : V) := p ∈ positiveMasks ∧ ∀ a b : V,
  p.val.testBit a.val = true → p.val.testBit b.val = true → related a b = true →
    (a=v ∧ b=w) ∨ (a=w ∧ b=v)

instance (p : M) (v w : V) : Decidable (RowEdge p v w) := by unfold RowEdge; infer_instance

theorem forces (B : Box) (l r : Nat) (member : Member B l r) (p : M) (v w : V)
    (cert : blockedBits B p = true) (unique : RowEdge p v w) :
    ForcedEdge (gates B.a B.b l r) v w := by
  refine ⟨decode p,Finset.mem_image_of_mem _ (by simpa using unique.1),blocked_member B l r member p cert,?_⟩
  intro a ha b hb edge
  exact unique.2 a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 edge

theorem box_degree (B : Box) (l r : Nat) (member : Member B l r) (C : AndCountCircuit 10)
    (hk : 2 ≤ C.size) (front : Matches C (gates B.a B.b l r) hk) (hc : Candidate C) (shape : Shape C 2)
    (T : Finset V) (neighbors : V → Finset V)
    (forced : ∀ v ∈ T, ∀ w ∈ neighbors v, ∃ p, RowEdge p v w ∧ blockedBits B p = true)
    (high : ∀ v ∈ T, 2 < (neighbors v).card + count B.a B.b B.ll B.rl v) : T.card ≤ C.size-2 := by
  apply degree_bound C (gates B.a B.b l r) hk front hc shape T neighbors
  · intro v hv w hw
    obtain ⟨p,edge,blocked⟩ := forced v hv w hw
    exact forces B l r member p v w blocked edge
  · intro v hv
    rw [use_count]
    exact lt_of_lt_of_le (high v hv) (Nat.add_le_add_left (count_mono _ _ _ _ _ _ member.ll member.rl v) _)

def classCheck (a b s fp : Nat) := negativeMasks.all fun m => side a b s m == fpOn fp m
def boundsCheck (a b lo hi fp : Nat) := (List.range 2048).all fun s =>
  !classCheck a b s fp || ((lo &&& s == lo) && (s &&& hi == s))

theorem class_iff (a b s fp : Nat) : classCheck a b s fp = true ↔ SideClass a b s fp := by
  simp [classCheck,SideClass,List.all_eq_true]

theorem class_bounds (a b lo hi fp : Nat) (cert : boundsCheck a b lo hi fp = true)
    (s : Fin 2048) (cl : SideClass a b s.val fp) : Sub lo s.val ∧ Sub s.val hi := by
  have h := List.all_eq_true.mp cert s.val (List.mem_range.mpr s.isLt)
  have on := (class_iff a b s.val fp).mpr cl
  simp only [on,Bool.not_true,Bool.false_or,Bool.and_eq_true,beq_iff_eq] at h
  exact ⟨sub_of_and _ _ h.1,sub_of_and _ _ h.2⟩

theorem member_of_classes (B : Box) (l r : Fin 2048)
    (leftBounds : boundsCheck B.a B.b B.ll B.lh B.lf = true)
    (rightBounds : boundsCheck B.a B.b B.rl B.rh B.rf = true)
    (leftClass : SideClass B.a B.b l B.lf) (rightClass : SideClass B.a B.b r B.rf) :
    Member B l r := by
  have left := class_bounds _ _ _ _ _ leftBounds l leftClass
  have right := class_bounds _ _ _ _ _ rightBounds r rightClass
  exact ⟨left.1,left.2,right.1,right.2,leftClass,rightClass⟩

end PetersenFootprintCenters
