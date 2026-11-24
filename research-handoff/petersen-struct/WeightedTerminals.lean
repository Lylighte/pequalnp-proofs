import FootprintCenters

namespace PetersenWeighted

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenFirstPins PetersenNormalized PetersenBoundary PetersenTailCnf PetersenSuffix
open PetersenMixedStar (projected terminal_gate)

abbrev Input := Finset (Fin 10)

local instance {k : ℕ} (a b : Finset (Fin k)) : Decidable (hit a b) := by
  unfold hit
  infer_instance

-- A row with integer weight d appears as d distinct indices of the input map.
theorem capacity (C : AndCountCircuit 10) (hc : Candidate C) (u n cap : ℕ)
    (hu : u < C.size) (shape : Shape C u) (input : Fin n → Input)
    (pos : ∀ j, input j ∈ positives)
    (bound : ∀ g ∈ C.outGates,
      (Finset.univ.filter fun j : Fin n => C.gateVal (input j) g = true).card ≤ cap) :
    n ≤ cap * (C.size - u) := by
  classical
  have live (j : Fin n) : ∃ g ∈ C.outGates, C.gateVal (input j) g = true := by
    have yes := ((separationIff C).mp hc.2.2.2).2 (input j) (pos j)
    rw [AndCountCircuit.eval,decide_eq_true_eq] at yes
    rcases yes with ⟨v,hv,_⟩ | h
    · simp [shape.2.2.2] at hv
    · exact h
  choose gate member fires using live
  have fibers (g : Fin C.size) (hg : g ∈ C.outGates) :
      (Finset.univ.filter fun j : Fin n => gate j = g).card ≤ cap := by
    apply le_trans (Finset.card_le_card ?_) (bound g hg)
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2 ▸ fires j⟩
  have count := Finset.card_le_mul_card_image_of_maps_to
    (s := (Finset.univ : Finset (Fin n))) (t := C.outGates) (f := gate)
    (fun j _ => member j) cap fibers
  let start : Fin C.size := ⟨u,hu⟩
  have out : C.outGates = Finset.Ici start :=
    Finset.ext fun g => (shape.1 g).trans
      (show start ≤ g ↔ g ∈ Finset.Ici start from Finset.mem_Ici.symm)
  simpa [out,start] using count

def rightSide {α : Type} {k : ℕ} (indices : Finset α)
    (neg : α → Finset (Fin k)) (left : Finset (Fin k)) :
    Finset (Fin k) :=
  Finset.univ.filter fun y => ∀ i ∈ indices, y ∈ neg i → ¬ hit left (neg i)

theorem rightSide_spec {α : Type} {k : ℕ} (indices : Finset α) (neg : α → Finset (Fin k))
    (left : Finset (Fin k)) (y : Fin k) (hy : y ∈ rightSide indices neg left) :
    ∀ i ∈ indices, y ∈ neg i → ¬ hit left (neg i) :=
  (Finset.mem_filter.mp hy).2

-- Upper positive rows and lower negative rows may relax an entire family of
-- prefixes. Only the signals selected by an actual gate need a negative lift.
theorem bounded_products {α : Type} (C P : AndCountCircuit 10) (hk : P.size < C.size)
    (front : Matches C P hk.le) (hc : Candidate C) (shape : Shape C P.size)
    (n cap : ℕ) (input : Fin n → Input) (pos : ∀ j, input j ∈ positives)
    (indices : Finset α) (negInput : α → Input) (neg : ∀ i ∈ indices, negInput i ∈ negatives)
    (upper : Fin n → Finset (Fin (10+P.size))) (lower : α → Finset (Fin (10+P.size)))
    (up : ∀ j, projected P (input j) ⊆ upper j)
    (liftN : ∀ j, ∀ x ∈ projected P (input j), ∀ i ∈ indices,
      x ∈ lower i → x ∈ projected P (negInput i))
    (limit : ∀ left : Finset (Fin (10+P.size)),
      (Finset.univ.filter fun j : Fin n => hit left (upper j) ∧
        hit (rightSide indices lower left) (upper j)).card ≤ cap) :
    n ≤ cap * (C.size - P.size) := by
  classical
  apply capacity C hc _ n cap hk shape input pos
  intro g hg
  let seen := Finset.univ.biUnion (fun j => projected P (input j))
  let L := selector C P.size hk.le (C.leftVars g) (C.leftGates g) ∩ seen
  let R := selector C P.size hk.le (C.rightVars g) (C.rightGates g)
  have right (y) (hy : y ∈ R) (j) (yp : y ∈ projected P (input j)) :
      y ∈ rightSide indices lower L := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rintro i hi yn ⟨x,hx,xn⟩
    obtain ⟨hL,hS⟩ := Finset.mem_inter.mp hx
    obtain ⟨z,_,xz⟩ := Finset.mem_biUnion.mp hS
    have on := (terminal_gate C P hk.le front hc shape g hg (negInput i)).mpr
      ⟨⟨x,hL,liftN z x xz i hi xn⟩,⟨y,hy,liftN j y yp i hi yn⟩⟩
    exact Bool.false_ne_true (((shape.2.1 g).mpr ((shape.1 g).mp hg) _ (neg i hi)).symm.trans on)
  apply le_trans (Finset.card_le_card ?_) (limit L)
  intro j hj
  obtain ⟨⟨x,hx,px⟩,⟨y,hy,py⟩⟩ := (terminal_gate C P hk.le front hc shape g hg (input j)).mp
    (Finset.mem_filter.mp hj).2
  have sx : x ∈ seen := Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,px⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x,Finset.mem_inter.mpr ⟨hx,sx⟩,up j px⟩,
    ⟨y,right y hy j py,up j py⟩⟩

open PetersenFootprintCenters

def upperSet (B : Box) (m : M) := Finset.univ.filter fun x => upper B m x = true
def lowerSet (B : Box) (m : M) := Finset.univ.filter fun x => lowerNeg B m x = true

theorem box_capacity (B : Box) (l r : ℕ) (member : Member B l r)
    (C : AndCountCircuit 10) (hk : 2 < C.size)
    (front : Matches C (gates B.a B.b l r) hk.le) (hc : Candidate C) (shape : Shape C 2)
    (n cap : ℕ) (tickets : Fin n → M) (good : ∀ j, tickets j ∈ positiveMasks)
    (limit : ∀ left : Finset (Fin 12), (Finset.univ.filter fun j : Fin n =>
      hit left (upperSet B (tickets j)) ∧
      hit (rightSide negativeMasks.toFinset (lowerSet B) left) (upperSet B (tickets j))).card ≤ cap) :
    n ≤ cap * (C.size-2) := by
  apply bounded_products C (gates B.a B.b l r) hk front hc shape n cap
    (fun j => decode (tickets j)) (fun j => Finset.mem_image_of_mem _ (by simpa using good j))
    negativeMasks.toFinset decode (fun m hm => Finset.mem_image_of_mem _ hm)
    (fun j => upperSet B (tickets j)) (lowerSet B) _ _ limit
  · intro j x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,active_upper B l r member (tickets j) x hx⟩
  · intro j x hx m hm hn
    exact negative_transfer B l r member (tickets j) m (by simpa using hm) x hx (Finset.mem_filter.mp hn).2

def mask12 (L : Finset (Fin 12)) : Fin 4096 :=
  let s := BitVec.ofBoolListLE ((List.finRange 12).map fun x => decide (x ∈ L))
  ⟨s.toNat,by simpa [s] using s.toFin.isLt⟩

theorem mask12_bit (L : Finset (Fin 12)) (x : Fin 12) :
    (mask12 L).val.testBit x.val = decide (x ∈ L) := by
  change (BitVec.ofBoolListLE ((List.finRange 12).map fun v => decide (v ∈ L))).getLsbD _ = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp)]
  simp

def possible (left pos : Nat) (bad : Fin 12 → Nat) : Prop :=
  left &&& pos ≠ 0 ∧ ∃ y : Fin 12, pos.testBit y.val = true ∧ left &&& bad y = 0

instance (left pos : Nat) (bad : Fin 12 → Nat) : Decidable (possible left pos bad) := by
  unfold possible
  infer_instance

set_option maxRecDepth 6000 in
theorem numeric_capacity (B : Box) (l r : Nat) (member : Member B l r)
    (C : AndCountCircuit 10) (hk : 2 < C.size)
    (front : Matches C (gates B.a B.b l r) hk.le) (hc : Candidate C) (shape : Shape C 2)
    (n cap : ℕ) (tickets : Fin n → M) (good : ∀ j, tickets j ∈ positiveMasks)
    (pos : Fin n → Nat) (bad : Fin 12 → Nat)
    (positiveBits : ∀ j x, upper B (tickets j) x = true → (pos j).testBit x.val = true)
    (negativeBits : ∀ y x : Fin 12, (bad y).testBit x.val = true →
      ∃ m ∈ negativeMasks, lowerNeg B m x = true ∧ lowerNeg B m y = true)
    (limit : ∀ s : Fin 4096,
      (Finset.univ.filter fun j : Fin n => possible s.val (pos j) bad).card ≤ cap) :
    n ≤ cap * (C.size-2) := by
  apply box_capacity B l r member C hk front hc shape n cap tickets good
  intro L
  let s := mask12 L
  apply le_trans (Finset.card_le_card ?_) (limit s)
  intro j hj
  obtain ⟨⟨x,hx,xp⟩,⟨y,hy,yp⟩⟩ := (Finset.mem_filter.mp hj).2
  have xb := positiveBits j x (Finset.mem_filter.mp xp).2
  have yb := positiveBits j y (Finset.mem_filter.mp yp).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,⟨y,yb,?_⟩⟩
  · intro h
    have eq := congrArg (fun a : Nat => a.testBit x.val) h
    simp [s,mask12_bit,hx,xb] at eq
  · by_contra h
    obtain ⟨i,act⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and,Bool.and_eq_true] at act
    have hi : i < 12 := by
      by_contra! ge
      have power : 4096 ≤ 2^i := Nat.pow_le_pow_right (n := 2) (i := 12) (by decide) ge
      exact Bool.false_ne_true ((Nat.testBit_lt_two_pow (s.isLt.trans_le power)).symm.trans act.1)
    let z : Fin 12 := ⟨i,hi⟩
    have hz : z ∈ L := of_decide_eq_true ((mask12_bit L z).symm.trans act.1)
    obtain ⟨m,hm,mz,my⟩ := negativeBits y z act.2
    have none := rightSide_spec negativeMasks.toFinset (lowerSet B) L y hy
    have ym : y ∈ lowerSet B m := Finset.mem_filter.mpr ⟨Finset.mem_univ _,my⟩
    have zm : z ∈ lowerSet B m := Finset.mem_filter.mpr ⟨Finset.mem_univ _,mz⟩
    exact none m (List.mem_toFinset.mpr hm) ym ⟨z,hz,zm⟩

end PetersenWeighted

#print axioms PetersenWeighted.capacity
#print axioms PetersenWeighted.bounded_products
#print axioms PetersenWeighted.box_capacity
#print axioms PetersenWeighted.numeric_capacity
