import SecondPolarCube
import LightFootprintPolar
import WeightedIntervals

namespace PetersenSecondCube

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenSuffix PetersenFirstPins PetersenNormalized PetersenBoundary PetersenFootprintCenters
open PetersenWeighted

private theorem has_terminal (C : AndCountCircuit 10) (hc : Candidate C) (s : Shape C 2) :
    2 < C.size := by
  have present : (51 : M) ∈ positiveMasks := by decide
  have yes := ((separationIff C).mp hc.2.2.2).2 (decode 51)
    (Finset.mem_image_of_mem _ (by simpa using present))
  simp only [AndCountCircuit.eval,s.2.2.2,Finset.notMem_empty,false_and,
    exists_false,false_or,decide_eq_true_eq] at yes
  obtain ⟨i,out,_⟩ := yes
  exact lt_of_le_of_lt ((s.1 i).mp out) i.isLt

theorem ticket_invalid (a b : Nat) (Q : Rect) (n cap : Nat) (tickets : Fin n → M)
    (pos : Fin n → Nat) (bad : Fin 12 → Nat)
    (good : ∀ j, tickets j ∈ positiveMasks)
    (pbits : ∀ j x, positive a b Q (tickets j) x=true → (pos j).testBit x.val=true)
    (nbits : ∀ y x : Fin 12, (bad y).testBit x.val=true → ∃ m ∈ negativeMasks,
      negative a b Q m x=true ∧ negative a b Q m y=true)
    (limit : ∀ s : Fin 4096, (Finset.univ.filter (fun j => possible s.val (pos j) bad)).card ≤ cap)
    (few : 4*cap < n) : Invalid a b Q := by
  intro l r within C hk front hc shape
  have capBound := numeric_capacity (box a b Q l r) l r (member a b Q l r within) C
    (has_terminal C hc shape) front hc shape n cap tickets good pos bad pbits (by
      intro y x yes
      obtain ⟨m,hm,hx,hy⟩ := nbits y x yes
      exact ⟨m,hm,negative_refines a b Q l r within m hm x hx,negative_refines a b Q l r within m hm y hy⟩) limit
  have four : C.size-2 ≤ 4 := by have six := hc.2.1; omega
  exact Nat.not_lt_of_ge (capBound.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left cap four)) few

theorem safe_invalid (a b : Nat) (Q : Rect)
    (always : (∀ m ∈ negativeMasks, h0 a b m=false) ∨
      (∀ m ∈ negativeMasks, h1 a b Q.lh Q.rh m=false)) : Invalid a b Q := by
  intro l r within C hk front hc shape
  have mustFire (i : Fin 2) : ¬ (∀ u ∈ negatives, C.gateVal u (head C 2 hk i)=false) := by
    intro yes
    exact Nat.not_le_of_gt i.isLt ((shape.2.1 _).mp yes)
  rcases always with off | off
  · apply mustFire 0; intro u hu
    obtain ⟨m,hm,rfl⟩ : ∃m∈negativeMasks, decode m=u := by simpa [negatives] using hu
    exact (matched_gate C _ hk front _ 0).trans ((first_eval ..).trans (off m hm))
  · apply mustFire 1; intro u hu
    obtain ⟨m,hm,rfl⟩ : ∃m∈negativeMasks, decode m=u := by simpa [negatives] using hu
    rw [matched_gate C _ hk front _ 1,second_eval]
    apply Bool.eq_false_iff.mpr; intro yes
    have bits := Bool.and_eq_true_iff.mp yes
    have top : h1 a b Q.lh Q.rh m=true := Bool.and_eq_true_iff.mpr
      ⟨side_mono _ _ _ _ within.lh m bits.1,side_mono _ _ _ _ within.rh m bits.2⟩
    exact Bool.false_ne_true ((off m hm).symm.trans top)

theorem light_polar_rectangle (a b : Nat) (Q : Rect) (s : Nat) (valid : polarAt a b Q s = true) :
    Invalid a b Q := by
  intro l r within C hk front hc shape
  apply PetersenLightPolar.replacement a b l r s C hk front hc shape
  · intro m hm yes
    have z := List.all_eq_true.mp (Bool.and_eq_true_iff.mp valid).1 m hm
    have low : h1 a b Q.ll Q.rl m=true := by simpa [yes] using z
    have bits := Bool.and_eq_true_iff.mp low
    exact Bool.and_eq_true_iff.mpr ⟨side_mono _ _ _ _ within.ll m bits.1,side_mono _ _ _ _ within.rl m bits.2⟩
  · intro m hm yes
    have bits := Bool.and_eq_true_iff.mp yes
    have top : h1 a b Q.lh Q.rh m=true := Bool.and_eq_true_iff.mpr
      ⟨side_mono _ _ _ _ within.lh m bits.1,side_mono _ _ _ _ within.rh m bits.2⟩
    have z := List.all_eq_true.mp (Bool.and_eq_true_iff.mp valid).2 m hm
    simpa [top] using z

end PetersenSecondCube
