import BatchData

namespace PetersenSecondCube.Batch

open PEqualNP.AndCount PetersenSuffix PetersenFirstPins PetersenNormalized PetersenBoundary
open PetersenFootprintCenters PetersenMixedStar

def pfoot (a b : Nat) (Q : Rect) := projectedCol pc a b Q.ll Q.rl Q.lh Q.rh
def nfoot (a b : Nat) (Q : Rect) (x : Fin 12) :=
  projectedCol nc a b Q.ll Q.rl Q.ll Q.rl x &&& 32767
def bitmap (a b : Nat) (Q : Rect) := mixedRows (pfoot a b Q) (nfoot a b Q)

private theorem neg_common (a b : Nat) (Q : Rect) (x y : Fin 12) (yes : nfoot a b Q x &&& nfoot a b Q y ≠ 0) :
    ∃ w∈negativeMasks, negative a b Q w x=true ∧ negative a b Q w y=true := by
  obtain ⟨i,hit⟩ := Nat.exists_testBit_of_ne_zero yes
  simp only [nfoot,Nat.testBit_and,Bool.and_eq_true] at hit
  have small : i<15 := by
    have bound := hit.1.2
    change (2^15-1 : Nat).testBit i=true at bound
    rw [Nat.testBit_two_pow_sub_one] at bound
    exact of_decide_eq_true bound
  let j : Fin 15 := ⟨i,small⟩
  have valid (t : Fin 12) : (projectedCol nc a b Q.ll Q.rl Q.ll Q.rl t).testBit i =
      negative a b Q (negRow j) t := projected_spec _ _ _ _ _ _ _ _ _ (fun v => n_bits v j) t
  exact ⟨negRow j,n_ok j,(valid x).symm.trans hit.1.1,(valid y).symm.trans hit.2.1⟩

def edgeOn (m : Nat) (e : Fin 15) := ((m >>> (4*e.val)) &&& 15) != 15

private theorem edge_row (m : Nat) (e : Fin 15) (on : edgeOn m e=true) :
    ∃ j : Fin 4, m.testBit (index e j).val=false := by
  by_contra no
  have all (j : Fin 4) : m.testBit (4*e.val+j.val)=true := by
    cases h : m.testBit (4*e.val+j.val) with
    | false => exact False.elim (no ⟨j,h⟩)
    | true => rfl
  have eq : (m >>> (4*e.val)) &&& 15 = 15 := by
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and,Nat.testBit_shiftRight]
    have mask : (15:Nat).testBit k=decide (k<4) := Nat.testBit_two_pow_sub_one 4 k
    rw [mask]
    by_cases small : k<4
    · have bit := all ⟨k,small⟩
      simpa [small,Nat.add_comm] using bit
    · simp [small]
  simp [edgeOn,eq] at on

theorem edge_force (a b : Nat) (Q : Rect) (l r : Fin 2048) (within : Within Q l r) (e : Fin 15)
    (on : edgeOn (bitmap a b Q) e=true) : ForcedEdge (gates a b l r) (fromV e) (toV e) := by
  obtain ⟨s,off⟩ := edge_row _ _ on
  let j := index e s
  let witness : Mark := ⟨posRow j,fromV e,toV e⟩
  apply checked_mark a b Q l r within witness
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (rows_ok e s),?_⟩
  apply unmixed a b Q _ j.val (pfoot a b Q) (nfoot a b Q) _ (neg_common a b Q) off
  intro x hx
  exact (projected_spec pc a b Q.ll Q.rl Q.lh Q.rh j.val (posRow j) (fun v => p_bits v j) x).trans hx

def spentBit (a b : Nat) (Q : Rect) :=
  let m := bitmap a b Q
  (List.finRange 15).any fun e => edgeOn m e &&
    decide (2 ≤ count a b Q.ll Q.rl (fromV e) ∨ 2 ≤ count a b Q.ll Q.rl (toV e))

theorem spent_sound (a b : Nat) (Q : Rect) (pass : spentBit a b Q=true) : Invalid a b Q := by
  intro l r within C hk front hc shape
  obtain ⟨e,_,on⟩ := List.any_eq_true.mp pass
  have split := Bool.and_eq_true_iff.mp on
  have cap := forced_available C _ hk front hc shape _ _ (edge_force a b Q l r within e split.1)
  rw [use_count a b l r _,use_count a b l r _] at cap
  have low := of_decide_eq_true split.2
  have s := count_mono a b Q.ll Q.rl l r within.ll within.rl (fromV e)
  have t := count_mono a b Q.ll Q.rl l r within.ll within.rl (toV e)
  omega

def edgesAt (m : Nat) (v : V) := Finset.univ.filter fun j => edgeOn m (incident v j)=true
def highAt (a b : Nat) (Q : Rect) (m : Nat) :=
  Finset.univ.filter fun v => 2 < (edgesAt m v).card + count a b Q.ll Q.rl v
def centerBit (a b : Nat) (Q : Rect) := decide (4 < (highAt a b Q (bitmap a b Q)).card)

theorem centers_sound (a b : Nat) (Q : Rect) (pass : centerBit a b Q=true) : Invalid a b Q := by
  intro l r within C hk front hc shape
  let m := bitmap a b Q
  let T := highAt a b Q m
  let neighbors (v : V) := (edgesAt m v).image (adjacent v)
  have need := degree_bound C _ hk front hc shape T neighbors (by
    intro v _ w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    have forced := edge_force a b Q l r within (incident v j) (Finset.mem_filter.mp hj).2
    rcases incident_pairs v j with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · simpa only [h1,h2] using forced
    · simpa only [h1,h2] using reverse_mark _ _ _ forced) (by
    intro v hv
    have low := (Finset.mem_filter.mp hv).2
    rw [use_count a b l r v]
    change 2 < ((edgesAt m v).image (adjacent v)).card + _
    rw [Finset.card_image_of_injective _ (fun _ _ eq => adjacent_inj v _ _ eq)]
    exact lt_of_lt_of_le low (Nat.add_le_add_left (count_mono a b Q.ll Q.rl l r within.ll within.rl v) _))
  have large : 4 < T.card := of_decide_eq_true pass
  change T.card ≤ C.size-2 at need
  have six := hc.2.1
  omega

end PetersenSecondCube.Batch
