import BatchProbe

namespace PetersenSecondCube.Envelope

open PEqualNP.AndCount PetersenSuffix PetersenFirstPins PetersenNormalized PetersenBoundary
open PetersenFootprintCenters PetersenMixedStar PetersenSecondCube.Batch

structure Group where
  use : Nat
  positive : Nat
  negative : Nat

def fits (s : Group) (a b : Nat) := (a ||| b = s.use) ∧
  (source pc a b &&& s.positive = source pc a b) ∧
  (s.negative &&& source nc a b = s.negative)
instance (s : Group) (a b : Nat) : Decidable (fits s a b) := by unfold fits; infer_instance

def Le (a b : Nat) := ∀ j : Nat, a.testBit j=true → b.testBit j=true

private theorem le_and {a b : Nat} (h : a &&& b = a) : Le a b := by
  intro j yes
  have bit := congrArg (fun n : Nat => n.testBit j) h
  simpa [Nat.testBit_and,yes] using bit

theorem count_eq (s : Group) (a b : Nat) (fit : fits s a b) (l r : Nat) (v : V) :
    count a b l r v = count s.use 0 l r v := by
  simp [count,seen,←fit.1,Nat.testBit_or]

def column (col : V → Nat) (use root ll rl lhs rhs : Nat) (x : Fin 12) : Nat :=
  Fin.addCases (m:=10) (n:=2) (motive:=fun _ => Nat)
    (fun v : V => if count use 0 ll rl v < 2 then col v else 0)
    (fun j => ![root,sideCol col root lhs &&& sideCol col root rhs] j) x

private theorem project_eq (s : Group) (a b : Nat) (fit : fits s a b) (col : V → Nat)
    (ll rl lhs rhs : Nat) (x : Fin 12) :
    projectedCol col a b ll rl lhs rhs x = column col s.use (source col a b) ll rl lhs rhs x := by
  refine Fin.addCases (m:=10) (n:=2) (fun v => ?_) (fun j => ?_) x
  · simp [projectedCol,column,Fin.addCases_left,count_eq s a b fit]
  · simp [projectedCol,column,Fin.addCases_right]

private theorem col_mono (col : V → Nat) (use l h ll rl lhs rhs : Nat) (le : Le l h)
    (x : Fin 12) : Le (column col use l ll rl lhs rhs x) (column col use h ll rl lhs rhs x) := by
  have side (u : Nat) : Le (sideCol col l u) (sideCol col h u) := by
    intro j yes
    cases has : u.testBit 10 <;> simp [sideCol,has,Nat.testBit_or] at yes ⊢
    · exact yes
    · exact yes.imp id (le j)
  refine Fin.addCases (m:=10) (n:=2) (fun v => ?_) (fun j => ?_) x
  · simp only [column,Fin.addCases_left]; exact fun _ h => h
  · simp only [column,Fin.addCases_right]; fin_cases j
    · exact le
    · intro i yes
      change (sideCol col l lhs &&& sideCol col l rhs).testBit i=true at yes
      change (sideCol col h lhs &&& sideCol col h rhs).testBit i=true
      simp only [Nat.testBit_and,Bool.and_eq_true] at yes ⊢
      exact ⟨side lhs i yes.1,side rhs i yes.2⟩

def pfun (s : Group) (Q : Rect) := column pc s.use s.positive Q.ll Q.rl Q.lh Q.rh
def nfun (s : Group) (Q : Rect) (x : Fin 12) := column nc s.use s.negative Q.ll Q.rl Q.ll Q.rl x &&& 32767
def summary (s : Group) (Q : Rect) := mixedRows (pfun s Q) (nfun s Q)

private theorem upper (s : Group) (a b : Nat) (fit : fits s a b) (Q : Rect) (i : Fin 60) (x : Fin 12)
    (yes : PetersenSecondCube.positive a b Q (posRow i) x=true) : (pfun s Q x).testBit i.val=true := by
  have h := (projected_spec pc a b Q.ll Q.rl Q.lh Q.rh i.val (posRow i) (fun v => p_bits v i) x).trans yes
  rw [project_eq s a b fit] at h
  exact col_mono _ _ _ _ _ _ _ _ (le_and fit.2.1) _ _ h

private theorem lower (s : Group) (a b : Nat) (fit : fits s a b) (Q : Rect) (x y : Fin 12)
    (yes : nfun s Q x &&& nfun s Q y ≠ 0) :
    ∃ w∈negativeMasks, PetersenSecondCube.negative a b Q w x=true ∧ PetersenSecondCube.negative a b Q w y=true := by
  obtain ⟨i,hit⟩ := Nat.exists_testBit_of_ne_zero yes
  simp only [nfun,Nat.testBit_and,Bool.and_eq_true] at hit
  have small : i<15 := by
    have bound := hit.1.2
    change (2^15-1 : Nat).testBit i=true at bound
    rw [Nat.testBit_two_pow_sub_one] at bound
    exact of_decide_eq_true bound
  let j : Fin 15 := ⟨i,small⟩
  have lift (t : Fin 12) (h : (column nc s.use s.negative Q.ll Q.rl Q.ll Q.rl t).testBit i=true) :
      PetersenSecondCube.negative a b Q (negRow j) t=true := by
    have real := col_mono nc s.use _ _ Q.ll Q.rl Q.ll Q.rl (le_and fit.2.2) t i h
    rw [←project_eq s a b fit] at real
    exact (projected_spec nc a b Q.ll Q.rl Q.ll Q.rl j.val (negRow j) (fun v => n_bits v j) t).symm.trans real
  exact ⟨negRow j,n_ok j,lift x hit.1.1,lift y hit.2.1⟩

-- A missing bit in one four-row edge group gives a concrete private positive.
private theorem pick_row (m : Nat) (e : Fin 15) (on : edgeOn m e=true) :
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
    · simpa [small,Nat.add_comm] using all ⟨k,small⟩
    · simp [small]
  simp [edgeOn,eq] at on

theorem edge_force (s : Group) (a b : Nat) (fit : fits s a b) (Q : Rect) (l r : Fin 2048)
    (within : Within Q l r) (e : Fin 15) (on : edgeOn (summary s Q) e=true) :
    ForcedEdge (gates a b l r) (fromV e) (toV e) := by
  obtain ⟨j,clear⟩ := pick_row _ _ on
  let row := index e j
  let mark : Mark := ⟨posRow row,fromV e,toV e⟩
  apply checked_mark a b Q l r within mark
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (rows_ok e j),
    unmixed a b Q _ row.val _ _ (upper s a b fit Q row) (lower s a b fit Q) clear⟩

def refutes (s : Group) (Q : Rect) := ∀ a b, fits s a b → Invalid a b Q

def spent (s : Group) (Q : Rect) :=
  let m := summary s Q
  (List.finRange 15).any fun e => edgeOn m e &&
    decide (2 ≤ count s.use 0 Q.ll Q.rl (fromV e) ∨ 2 ≤ count s.use 0 Q.ll Q.rl (toV e))

def centers (s : Group) (Q : Rect) := decide (4 < (highAt s.use 0 Q (summary s Q)).card)

theorem spent_sound (s : Group) (Q : Rect) (pass : spent s Q=true) : refutes s Q := by
  intro a b fit l r within C hk front hc shape
  obtain ⟨e,_,on⟩ := List.any_eq_true.mp pass
  have split := Bool.and_eq_true_iff.mp on
  have cap := forced_available C _ hk front hc shape _ _ (edge_force s a b fit Q l r within e split.1)
  rw [use_count a b l r _,use_count a b l r _] at cap
  have low := of_decide_eq_true split.2
  have v := count_mono a b Q.ll Q.rl l r within.ll within.rl (fromV e)
  have w := count_mono a b Q.ll Q.rl l r within.ll within.rl (toV e)
  rw [count_eq s a b fit] at v w
  omega

theorem centers_sound (s : Group) (Q : Rect) (pass : centers s Q=true) : refutes s Q := by
  intro a b fit l r within C hk front hc shape
  let m := summary s Q
  let T := highAt s.use 0 Q m
  let neighbors (v : V) := (edgesAt m v).image (adjacent v)
  have need := degree_bound C _ hk front hc shape T neighbors (by
    intro v _ w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    have h := edge_force s a b fit Q l r within (incident v j) (Finset.mem_filter.mp hj).2
    rcases incident_pairs v j with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · simpa only [h1,h2] using h
    · simpa only [h1,h2] using reverse_mark _ _ _ h) (by
    intro v hv
    have low := (Finset.mem_filter.mp hv).2
    rw [use_count a b l r v]
    change 2 < ((edgesAt m v).image (adjacent v)).card + _
    rw [Finset.card_image_of_injective _ (fun _ _ eq => adjacent_inj v _ _ eq)]
    have lift := count_mono a b Q.ll Q.rl l r within.ll within.rl v
    rw [count_eq s a b fit] at lift
    exact lt_of_lt_of_le low (Nat.add_le_add_left lift _))
  have large : 4 < T.card := of_decide_eq_true pass
  change T.card ≤ C.size-2 at need
  have six := hc.2.1
  omega

end PetersenSecondCube.Envelope
