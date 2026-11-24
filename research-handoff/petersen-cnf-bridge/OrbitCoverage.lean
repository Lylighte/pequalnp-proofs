import FirstGatePins
import PetersenAutomorphisms
import PolarityReduction

namespace PetersenOrbitCover

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenFirstPins PetersenBoundary PetersenAutomorphisms

abbrev V := Fin 10

def fromBits (f : V → Bool) : Mask :=
  let x := BitVec.ofBoolListLE ((List.finRange 10).map f)
  ⟨x.toNat, by simpa [x] using x.toFin.isLt⟩

theorem fromBits_bit (f : V → Bool) (v : V) : (fromBits f).val.testBit v.val = f v := by
  change (BitVec.ofBoolListLE ((List.finRange 10).map f)).getLsbD _ = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp)]
  simp

def encode (s : Finset V) := fromBits (fun v => decide (v ∈ s))

theorem decode_encode (s : Finset V) : decode (encode s) = s := by
  ext v
  simp [decode, encode, fromBits_bit]

def move (e : Equiv.Perm V) (m : Mask) := fromBits (fun v => m.val.testBit (e.symm v).val)

theorem decode_move (e : Equiv.Perm V) (m : Mask) :
    decode (move e m) = PetersenEquivariance.vertexSet e (decode m) := by
  ext v
  simp [decode, move, fromBits_bit, PetersenEquivariance.vertexSet, Finset.mem_map_equiv]

def key (l r : Mask) := l.val * 1024 + r.val

def Canonical (l r : Mask) : Prop := l ≤ r ∧ ∀ i : Fin 120,
  key l r ≤ key (move (permutation i) l) (move (permutation i) r) ∧
  key l r ≤ key (move (permutation i) r) (move (permutation i) l)

instance (l r : Mask) : Decidable (Canonical l r) := by unfold Canonical; infer_instance

def hit (m u : Mask) := decide (m.val &&& u.val ≠ 0)
def fire (l r u : Mask) := hit l u && hit r u

def replacement (l r : Mask) : Mask :=
  let forbidden := negativeMasks.foldl (fun a m => if fire l r m then a else a ||| m.val) 0
  ⟨1023 - forbidden, by omega⟩

def polar (l r : Mask) : Bool :=
  let s := replacement l r
  negativeMasks.all (fun u => !hit s u || fire l r u) &&
    positiveMasks.all (fun u => !fire l r u || hit s u)

def Kept (l r : Mask) : Prop := Canonical l r ∧ polar l r = false

theorem hit_iff (m u : Mask) : hit m u = true ↔ ∃ v ∈ decode m, v ∈ decode u := by
  simp only [hit, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨k,hk⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and, Bool.and_eq_true] at hk
    have small : k < 10 := by
      by_contra! late
      have high : 1024 ≤ 2^k := Nat.pow_le_pow_right (n := 2) (i := 10) (by decide) late
      exact Bool.false_ne_true ((Nat.testBit_lt_two_pow (m.isLt.trans_le high)).symm.trans hk.1)
    exact ⟨⟨k,small⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk.2⟩⟩
  · rintro ⟨v,hm,hu⟩ off
    have h := congrArg (fun n : Nat => n.testBit v.val) off
    apply (fun g : true = false => Bool.false_ne_true g.symm)
    simpa only [Nat.testBit_and, Nat.zero_testBit, (Finset.mem_filter.mp hm).2,
      (Finset.mem_filter.mp hu).2, Bool.true_and] using h

def FiveBound := ∀ C : AndCountCircuit 10, C.WellFormed →
  PetersenEquivariance.Separates Petersen905.graph C → ¬ C.size ≤ 5

private theorem first_fires (C : AndCountCircuit 10) (l r u : Mask) (h : 0 < C.size)
    (hl : C.leftVars ⟨0,h⟩ = decode l) (hr : C.rightVars ⟨0,h⟩ = decode r) :
    C.gateVal (decode u) ⟨0,h⟩ = true ↔ fire l r u = true := by
  rw [PetersenCnfBridge.gate_equation]
  have noEarlier (j : Fin C.size) : ¬ j < (⟨0,h⟩ : Fin C.size) := by
    change ¬ j.val < 0
    omega
  simp [sideTrue, hl, hr, fire, hit_iff, noEarlier]

theorem candidate_nonpolar (bound : FiveBound) (C : AndCountCircuit 10) (hc : Candidate C)
    (l r : Mask) (sides : FirstSides C l r) : polar l r = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨h,hl,hr⟩ := sides
  obtain ⟨wf,hs,cap,sep⟩ := hc
  let k := C.size - 1
  have hk : C.size = k+1 := by dsimp [k]; omega
  have rows := (separationIff C).mp sep
  have good := Bool.and_eq_true_iff.mp yes
  obtain ⟨D,ds,dwf,dneg,dpos⟩ := PolarityReduction.removeFirstPreservingLabels C k hk wf
    (decode (replacement l r)) (· ∈ negatives) (· ∈ positives) rows.1 rows.2 (by
      intro U hu on
      obtain ⟨u,mem,rfl⟩ : ∃ u ∈ negativeMasks, decode u = U := by simpa [negatives] using hu
      have safe := List.all_eq_true.mp good.1 u mem
      have hs := (hit_iff _ _).mpr on
      apply (first_fires C l r u h hl hr).mpr
      simpa [hs] using safe) (by
      intro U hu on
      obtain ⟨u,mem,rfl⟩ : ∃ u ∈ positiveMasks, decode u = U := by simpa [positives] using hu
      have safe := List.all_eq_true.mp good.2 u mem
      have hg := (first_fires C l r u h hl hr).mp on
      apply (hit_iff _ _).mp
      simpa [hg] using safe)
  exact bound D dwf ((separationIff D).mpr ⟨dneg,dpos⟩) (by omega)

private theorem transported (C : AndCountCircuit 10) (hc : Candidate C) (l r : Mask)
    (hs : FirstSides C l r) (e : Equiv.Perm V)
    (aut : ∀ a b, Petersen905.graph.Adj (e a) (e b) ↔ Petersen905.graph.Adj a b) (flip : Bool) :
    ∃ D, Candidate D ∧ FirstSides D
      (move e (if flip then r else l)) (move e (if flip then l else r)) := by
  obtain ⟨h,hl,hr⟩ := hs
  obtain ⟨wf,hsize,cap,sep⟩ := hc
  obtain ⟨D,ds,dwf,dcap,dsep,j,hj,jl,jr⟩ :=
    PetersenEquivariance.transportCandidate _ C e aut ⟨0,h⟩ flip wf cap sep
  have pos : 0 < D.size := by omega
  have he : j = (⟨0,pos⟩ : Fin D.size) := Fin.ext hj
  refine ⟨D,⟨dwf, ds.trans_le hsize, dcap, dsep⟩,pos,?_,?_⟩
  · cases flip <;> simpa [← he, hl, hr, decode_move] using jl
  · cases flip <;> simpa [← he, hl, hr, decode_move] using jr

-- Minimize among all realizable candidates, so each automorphic image and
-- side exchange is a competitor. No equivalence-class table is required.
theorem coverage (bound : FiveBound) (hex : ∃ C, Candidate C) :
    ∃ C l r, Candidate C ∧ Kept l r ∧ FirstSides C l r := by
  classical
  let P (n : Nat) := ∃ C l r, Candidate C ∧ FirstSides C l r ∧ key l r = n
  have ex : ∃ n, P n := by
    obtain ⟨C,hc⟩ := hex
    have hi := bound C hc.1 hc.2.2.2
    let t : Fin C.size := ⟨0,by omega⟩
    exact ⟨_,C,encode (C.leftVars t), encode (C.rightVars t),hc,
      ⟨t.isLt,(decode_encode _).symm,(decode_encode _).symm⟩,rfl⟩
  obtain ⟨C,l,r,hc,hs,eq⟩ := Nat.find_spec ex
  have least (D) (u v : Mask) (hd : Candidate D) (hv : FirstSides D u v) :
      key l r ≤ key u v := by
    rw [eq]
    exact Nat.find_min' ex ⟨D,u,v,hd,hv,rfl⟩
  have symmkey (e : Equiv.Perm V) (aut : ∀ a b, Petersen905.graph.Adj (e a) (e b) ↔
      Petersen905.graph.Adj a b) (flip : Bool) : key l r ≤
      key (move e (if flip then r else l)) (move e (if flip then l else r)) := by
    obtain ⟨D,hd,hv⟩ := transported C hc l r hs e aut flip
    exact least D _ _ hd hv
  have ord : l ≤ r := by
    obtain ⟨h,hl,hr⟩ := hs
    let j : Fin C.size := ⟨0,h⟩
    let D := PetersenEquivariance.swapGate C j
    have hd : Candidate D := ⟨(PetersenEquivariance.swapWF C j).mpr hc.1,hc.2.1,
      fun v => (PetersenEquivariance.swapBare C j v).trans_le (hc.2.2.1 v),
      PetersenEquivariance.swapSeparates _ C j hc.2.2.2⟩
    have sw := least D r l hd ⟨h,by simpa [D,j] using hr,by simpa [D,j] using hl⟩
    simp only [key] at sw
    change l.val ≤ r.val
    omega
  exact ⟨C,l,r,hc,⟨⟨ord,fun i => ⟨symmkey _ (preservesGraph i) false,
    symmkey _ (preservesGraph i) true⟩⟩,candidate_nonpolar bound C hc l r hs⟩,hs⟩

end PetersenOrbitCover
