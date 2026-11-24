import FootprintPrefix

namespace PetersenFootprintPolar

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenSuffix PetersenTailCnf PetersenFirstPins PetersenNormalized PetersenBoundary
open PetersenMixedStar PetersenFootprintCenters

structure Port where
  vars : Input
  z : Bool
  o : Bool

def sensed (f : Port) (U : Input) (g h : Bool) : Prop :=
  (∃ v ∈ f.vars, v ∈ U) ∨ (f.z = true ∧ g = true) ∨ (f.o = true ∧ h = true)

def getPort (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (S : Input) (W : Finset (Fin C.size)) : Port :=
  ⟨S,decide (head C 2 hk 0 ∈ W),decide (head C 2 hk 1 ∈ W)⟩

private theorem old_side (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (U : Input) (S : Input)
    (W : Finset (Fin C.size)) (below : ∀ j ∈ W, j.val < 2)
    (i : Fin (C.size-2)) :
    sideTrue U S W (tail C 2 i) (C.gateVal U) = true ↔
      sensed (getPort C hk S W) U (C.gateVal U (head C 2 hk 0)) (C.gateVal U (head C 2 hk 1)) := by
  simp only [sideTrue,sensed,getPort,decide_eq_true_eq]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j,w,_,on⟩
    have lo := below j w
    have eq : j = head C 2 hk 0 ∨ j = head C 2 hk 1 := by
      rcases (show j.val=0 ∨ j.val=1 by omega) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases eq with rfl | rfl
    · exact Or.inl ⟨w,on⟩
    · exact Or.inr ⟨w,on⟩
  · rintro (⟨w,on⟩ | ⟨w,on⟩)
    · exact ⟨_,w,by change 0 < 2+i.val; omega,on⟩
    · exact ⟨_,w,by change 1 < 2+i.val; omega,on⟩

def left (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (i : Fin (C.size-2)) :=
  getPort C hk (C.leftVars (tail C 2 i)) (C.leftGates (tail C 2 i))
def right (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (i : Fin (C.size-2)) :=
  getPort C hk (C.rightVars (tail C 2 i)) (C.rightGates (tail C 2 i))

def outputs (L R : Fin k → Port) (U : Input) (g h : Bool) :=
  ∃ i, sensed (L i) U g h ∧ sensed (R i) U g h

private theorem gate_at_tail (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (shape : Shape C 2)
    (U : Input) (i : Fin (C.size-2)) :
    C.gateVal U (tail C 2 i) = true ↔
      sensed (left C hk i) U (C.gateVal U (head C 2 hk 0)) (C.gateVal U (head C 2 hk 1)) ∧
      sensed (right C hk i) U (C.gateVal U (head C 2 hk 0)) (C.gateVal U (head C 2 hk 1)) := by
  rw [PetersenCnfBridge.gate_equation,Bool.and_eq_true]
  exact and_congr (old_side C hk U _ _ (fun j w => shape.2.2.1 _ j (Or.inl w)) i)
    (old_side C hk U _ _ (fun j w => shape.2.2.1 _ j (Or.inr w)) i)

theorem old_outputs (B : Box) (l r : Nat) (C : AndCountCircuit 10) (hk : 2 ≤ C.size)
    (front : Matches C (gates B.a B.b l r) hk) (shape : Shape C 2) (m : M) :
    C.eval (decode m) = true ↔ outputs (left C hk) (right C hk) (decode m) (h0 B.a B.b m) (h1 B.a B.b l r m) := by
  have gate (i) := gate_at_tail C hk shape (decode m) i
  have e0 := (matched_gate C (gates B.a B.b l r) hk front (decode m) 0).trans (first_eval ..)
  have e1 := (matched_gate C (gates B.a B.b l r) hk front (decode m) 1).trans (second_eval ..)
  simp only [AndCountCircuit.eval,shape.2.2.2,Finset.notMem_empty,false_and,exists_false,false_or,decide_eq_true_eq]
  constructor
  · rintro ⟨j,out,on⟩
    have ge := (shape.1 j).mp out
    let i : Fin (C.size-2) := ⟨j.val-2,by omega⟩
    have eq : tail C 2 i = j := Fin.ext (by change 2+(j.val-2) = j.val; omega)
    exact ⟨i,e0 ▸ e1 ▸ (gate i).mp (eq ▸ on)⟩
  · rintro ⟨i,yes⟩
    exact ⟨tail C 2 i,(shape.1 _).mpr (by change 2 ≤ 2+i.val; omega),
      (gate i).mpr (e0.symm ▸ e1.symm ▸ yes)⟩

theorem outputs_mono (L R : Fin k → Port) (U : Input) (g h h' : Bool)
    (step : h = true → h' = true) : outputs L R U g h → outputs L R U g h' := by
  have mono (f) : sensed f U g h → sensed f U g h' := Or.imp id (Or.imp id (And.imp id step))
  rintro ⟨i,l,r⟩
  exact ⟨i,mono _ l,mono _ r⟩

-- Inline the replacement OR in every reading port. The retained first gate
-- is the only internal source of each of the k terminal gates.
def inlineVars (s : Nat) (f : Port) := if f.o then f.vars ∪ bits 10 s else f.vars
def inlineGate (s : Nat) (f : Port) := f.z || (f.o && s.testBit 10)
def oneWire (k : Nat) (on : Bool) : Finset (Fin (k+1)) := if on then {0} else ∅
abbrev shorter (a b s : Nat) (L R : Fin k → Port) : AndCountCircuit 10 where
  size := k+1
  leftVars := Fin.cases (bits 10 a) (fun i => inlineVars s (L i))
  rightVars := Fin.cases (bits 10 b) (fun i => inlineVars s (R i))
  leftGates := Fin.cases ∅ (fun i => oneWire k (inlineGate s (L i)))
  rightGates := Fin.cases ∅ (fun i => oneWire k (inlineGate s (R i)))
  outVars := ∅
  outGates := Finset.univ.filter (fun j => 0 < j.val)

private theorem wire_before (i : Fin k) (on : Bool) (j : Fin (k+1))
    (m : j ∈ oneWire k on) : j < i.succ := by
  cases on <;> simp [oneWire] at m
  subst j
  exact Fin.succ_pos _

theorem shorter_wf (a b s : Nat) (L R : Fin k → Port) : (shorter a b s L R).WellFormed := by
  intro i
  cases i using Fin.cases with
  | zero => simp [shorter]
  | succ i => exact ⟨wire_before i _,wire_before i _⟩

private theorem short_first (a b s : Nat) (L R : Fin k → Port) (m : M) :
    (shorter a b s L R).gateVal (decode m) 0 = h0 a b m := by
  rw [PetersenOneHelper.firstProduct _ _ rfl]
  apply Bool.eq_iff_iff.mpr
  change (decide (∃ v ∈ bits 10 a, v ∈ decode m) && decide (∃ v ∈ bits 10 b, v ∈ decode m)) = true ↔ _
  simp only [Bool.and_eq_true,decide_eq_true_eq,h0,raw_iff]

private theorem inline_side (a b s : Nat) (L R : Fin k → Port) (m : M) (f : Port) (i : Fin k) :
    sideTrue (decode m) (inlineVars s f) (oneWire k (inlineGate s f)) i.succ
      ((shorter a b s L R).gateVal (decode m)) = true ↔ sensed f (decode m) (h0 a b m) (side a b s m) := by
  have union_hit (S T : Input) : (∃ v ∈ S ∪ T, v ∈ decode m) ↔
      (∃ v ∈ S, v ∈ decode m) ∨ (∃ v ∈ T, v ∈ decode m) := by
    simp only [Finset.mem_union]; grind
  rcases f with ⟨V,z,o⟩
  cases z <;> cases o <;> cases eq : s.testBit 10 <;>
    simp [-Finset.mem_union,sideTrue,inlineVars,oneWire,inlineGate,sensed,side,eq,raw_iff,union_hit,short_first] <;> grind only

theorem shorter_outputs (a b s : Nat) (L R : Fin k → Port) (m : M) :
    (shorter a b s L R).eval (decode m) = true ↔ outputs L R (decode m) (h0 a b m) (side a b s m) := by
  have gate (i : Fin k) : (shorter a b s L R).gateVal (decode m) i.succ = true ↔
      sensed (L i) (decode m) (h0 a b m) (side a b s m) ∧ sensed (R i) (decode m) (h0 a b m) (side a b s m) := by
    rw [PetersenCnfBridge.gate_equation,Bool.and_eq_true]
    exact and_congr (inline_side a b s L R m (L i) i) (inline_side a b s L R m (R i) i)
  simp only [AndCountCircuit.eval,shorter,Finset.notMem_empty,false_and,exists_false,false_or,
    Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
  constructor
  · rintro ⟨j,ne,on⟩
    cases j using Fin.cases with
    | zero => exact False.elim (Nat.lt_irrefl 0 ne)
    | succ i => exact ⟨i,(gate i).mp on⟩
  · rintro ⟨i,on⟩
    exact ⟨i.succ,Fin.succ_pos _,(gate i).mpr on⟩

def polarCheck (B : Box) (s : Nat) :=
  negativeMasks.all (fun m => !side B.a B.b s m || negSecond B m) &&
  positiveMasks.all (fun m => !h1 B.a B.b B.lh B.rh m || side B.a B.b s m)

def allowed (B : Box) (f : M → Bool) := negativeMasks.all (fun n => !f n || negSecond B n)
def validRaw (B : Box) : Input := Finset.univ.filter fun v => allowed B (fun n => n.val.testBit v.val)
def maximalReplacement (B : Box) := packSide (validRaw B) (allowed B (h0 B.a B.b))

theorem maximal_safe (B : Box) (m : M) (mem : m ∈ negativeMasks) :
    side B.a B.b (maximalReplacement B).val m = true → negSecond B m = true := by
  have safe (f : M → Bool) (h : allowed B f = true) (on : f m = true) : negSecond B m = true := by
    have cert := List.all_eq_true.mp h m mem
    simpa [on] using cert
  simp only [side,Bool.or_eq_true,Bool.and_eq_true,raw_iff,maximalReplacement,packSide_raw,packSide_gate]
  rintro (⟨v,ok,on⟩ | ⟨ok,on⟩)
  · exact safe (fun n => n.val.testBit v.val) (Finset.mem_filter.mp ok).2 (Finset.mem_filter.mp on).2
  · exact safe (h0 B.a B.b) ok on

def positiveTest (B : Box) := positiveMasks.all (fun m =>
  !h1 B.a B.b B.lh B.rh m || side B.a B.b (maximalReplacement B).val m)

theorem maximal_check (B : Box) (pos : positiveTest B = true) : polarCheck B (maximalReplacement B).val = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨List.all_eq_true.mpr ?_,pos⟩
  intro m mem
  cases eq : side B.a B.b (maximalReplacement B).val m with
  | false => simp
  | true => simpa using maximal_safe B m mem eq

theorem box_polar (B : Box) (l r s : Nat) (member : Member B l r) (cert : polarCheck B s = true)
    (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (front : Matches C (gates B.a B.b l r) hk)
    (hc : Candidate C) (shape : Shape C 2) : False := by
  let L := left C hk
  let R := right C hk
  let D := shorter B.a B.b s L R
  have eqc (m) := old_outputs B l r C hk front shape m
  have eqd (m) := shorter_outputs B.a B.b s L R m
  have checks := Bool.and_eq_true_iff.mp cert
  have real := (separationIff C).mp hc.2.2.2
  apply PetersenOrbitCover.fiveBound D (shorter_wf B.a B.b s L R) ((separationIff D).mpr ⟨?_,?_⟩) (by
    have cap := hc.2.1
    change C.size-2+1 ≤ 5
    omega)
  · intro U hu
    obtain ⟨m,mem,rfl⟩ : ∃ m ∈ negativeMasks, decode m = U := by simpa [negatives] using hu
    apply Bool.eq_false_iff.mpr
    intro on
    have step : side B.a B.b s m = true → h1 B.a B.b l r m = true := by
      intro yes
      have ok := List.all_eq_true.mp checks.1 m mem
      simpa [yes,neg_eq B l r member m mem] using ok
    have old := (eqc m).mpr (outputs_mono L R _ _ _ _ step ((eqd m).mp on))
    exact Bool.false_ne_true ((real.1 _ hu).symm.trans old)
  · intro U hu
    obtain ⟨m,mem,rfl⟩ : ∃ m ∈ positiveMasks, decode m = U := by simpa [positives] using hu
    have step : h1 B.a B.b l r m = true → side B.a B.b s m = true := by
      intro yes
      have hi := pos_upper B l r member m yes
      have ok := List.all_eq_true.mp checks.2 m mem
      simpa [hi] using ok
    exact (eqd m).mpr (outputs_mono L R _ _ _ _ step ((eqc m).mp (real.2 _ hu)))

end PetersenFootprintPolar
