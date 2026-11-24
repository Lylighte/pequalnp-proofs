import EnvelopeTree

namespace PetersenSecondCube.Envelope

open PetersenSecondCube.Batch PetersenFootprintCenters PetersenMixedStar

def masked (live : Fin 12 → Bool) (col : Fin 12 → Nat) (x : Fin 12) :=
  if live x then col x else 0

-- Removing the same wires from positive and negative rows can only remove
-- mixed positive rows. A surviving bad pair has both of its wires live.
theorem mixed_mask (p n : Fin 12 → Nat) (live : Fin 12 → Bool) :
    Le (mixedRows (masked live p) (masked live n)) (mixedRows p n) := by
  have one (h : Fin 12) : Le (masked live p h &&& unpaired (masked live p) (masked live n) h)
      (p h &&& unpaired p n h) := by
    intro j yes
    rw [Nat.testBit_and,Bool.and_eq_true] at yes ⊢
    by_cases eh : live h=true
    · refine ⟨by simpa [masked,eh] using yes.1,?_⟩
      obtain ⟨x,hx,hit⟩ := (gatherBits_bit ..).mp yes.2
      apply (gatherBits_bit ..).mpr
      refine ⟨x,hx,?_⟩
      by_cases ex : live x=true
      · simpa [masked,eh,ex] using hit
      · simp [masked,Bool.eq_false_iff.mpr ex] at hit
    · simpa [masked,Bool.eq_false_iff.mpr eh] using yes.1
  intro j yes
  simp only [mixedRows,Nat.testBit_or,Bool.or_eq_true] at yes ⊢
  exact yes.imp (one 10 j) (one 11 j)

def active (use : Nat) (Q : Rect) : Fin 12 → Bool :=
  Fin.addCases (m:=10) (n:=2) (motive:=fun _ => Bool)
    (fun v : V => decide (count use 0 Q.ll Q.rl v < 2)) (fun _ => true)

theorem count_use_mono (small big : Nat) (sub : small &&& big=small) (l r : Nat) (v : V) :
    count small 0 l r v ≤ count big 0 l r v := by
  have hit := congrArg (fun n : Nat => n.testBit v.val) sub
  simp [count,seen]
  cases e : small.testBit v.val <;> cases f : big.testBit v.val <;>
    simp [e,f,Nat.testBit_and] at hit ⊢

def withUse (s : Group) (u : Nat) : Group := {s with use:=u}

theorem column_mask (s : Group) (u : Nat) (sub : s.use &&& u=s.use) (col : V → Nat)
    (root lhs rhs : Nat) (Q : Rect) (x : Fin 12) :
    column col u root Q.ll Q.rl lhs rhs x =
    masked (active u Q) (column col s.use root Q.ll Q.rl lhs rhs) x := by
  refine Fin.addCases (m:=10) (n:=2) (fun v => ?_) (fun j => ?_) x
  · have mono := count_use_mono _ _ sub Q.ll Q.rl v
    by_cases small : count u 0 Q.ll Q.rl v < 2
    · have old : count s.use 0 Q.ll Q.rl v ≤ 1 := by omega
      have young : count u 0 Q.ll Q.rl v ≤ 1 := by omega
      simp [column,masked,active,Fin.addCases_left,young,old]
    · have large : ¬count u 0 Q.ll Q.rl v ≤ 1 := by omega
      simp [column,masked,active,Fin.addCases_left,large]
  · simp [column,masked,active,Fin.addCases_right]

theorem summary_use_mono (s : Group) (u : Nat) (sub : s.use &&& u=s.use) (Q : Rect) :
    Le (summary (withUse s u) Q) (summary s Q) := by
  have hp : pfun (withUse s u) Q=masked (active u Q) (pfun s Q) :=
    funext fun x => column_mask s u sub pc s.positive Q.lh Q.rh Q x
  have hn : nfun (withUse s u) Q=masked (active u Q) (nfun s Q) := by
    funext x
    change column nc u s.negative Q.ll Q.rl Q.ll Q.rl x &&& 32767 = _
    rw [column_mask s u sub nc s.negative Q.ll Q.rl Q x]
    cases e : active u Q x <;> simp [masked,nfun,e]
  simpa only [summary,hp,hn] using mixed_mask (pfun s Q) (nfun s Q) (active u Q)

theorem edge_on_mono (lo hi : Nat) (le : Le lo hi) (e : Fin 15) (on : edgeOn hi e=true) :
    edgeOn lo e=true := by
  by_contra missing
  have all : (lo >>> (4*e.val)) &&& 15=15 := by simpa [edgeOn] using missing
  have eq : (hi >>> (4*e.val)) &&& 15=15 := by
    apply Nat.eq_of_testBit_eq; intro k
    have bits := congrArg (fun n : Nat => n.testBit k) all
    simp only [Nat.testBit_and,Nat.testBit_shiftRight] at bits ⊢
    cases h : (15:Nat).testBit k <;> simp [h] at bits ⊢
    exact le _ bits
  simp [edgeOn,eq] at on

theorem spent_use_mono (s : Group) (u : Nat) (sub : s.use &&& u=s.use) (Q : Rect)
    (ok : spent s Q=true) : spent (withUse s u) Q=true := by
  obtain ⟨e,em,h⟩ := List.any_eq_true.mp ok
  obtain ⟨on,c⟩ := Bool.and_eq_true_iff.mp h
  apply List.any_eq_true.mpr; refine ⟨e,em,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
  · exact edge_on_mono _ _ (summary_use_mono s u sub Q) e on
  · apply decide_eq_true
    exact (of_decide_eq_true c).imp
      (fun lo => le_trans lo (count_use_mono _ _ sub _ _ _))
      (fun lo => le_trans lo (count_use_mono _ _ sub _ _ _))

theorem centers_use_mono (s : Group) (u : Nat) (sub : s.use &&& u=s.use) (Q : Rect)
    (ok : centers s Q=true) : centers (withUse s u) Q=true := by
  apply decide_eq_true
  refine lt_of_lt_of_le (of_decide_eq_true ok) (Finset.card_le_card ?_)
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,lt_of_lt_of_le (Finset.mem_filter.mp hv).2 (Nat.add_le_add ?_ ?_)⟩
  · apply Finset.card_le_card; intro j hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,edge_on_mono _ _ (summary_use_mono s u sub Q) (incident v j)
      (Finset.mem_filter.mp hj).2⟩
  · exact count_use_mono _ _ sub _ _ _

def fitsLoose (s : Group) (a b : Nat) := s.use &&& (a|||b)=s.use ∧
  (source pc a b &&& s.positive = source pc a b) ∧
  (s.negative &&& source nc a b=s.negative)
instance (s : Group) (a b : Nat) : Decidable (fitsLoose s a b) := by unfold fitsLoose; infer_instance

def refutesLoose (s : Group) (Q : Rect) := ∀ a b, fitsLoose s a b → Invalid a b Q

theorem verify_use_mono (s : Group) (u : Nat) (sub : s.use &&& u=s.use)
    (t : Branch) (Q : Rect) (ok : verify s t Q=true) : verify (withUse s u) t Q=true := by
  induction t generalizing Q with
  | spent => exact spent_use_mono _ _ sub _ ok
  | centers => exact centers_use_mono _ _ sub _ ok
  | fork side i l r hl hr =>
    exact Bool.and_eq_true_iff.mpr ⟨hl _ (Bool.and_eq_true_iff.mp ok).1,hr _ (Bool.and_eq_true_iff.mp ok).2⟩

theorem program_loose (s : Group) (Q : Rect) (tokens : List Nat) (ok : program s Q tokens=true) :
    refutesLoose s Q := by
  intro a b fit
  unfold program at ok
  split at ok
  next t _ =>
    exact sound (withUse s (a|||b)) t Q (verify_use_mono s _ fit.1 t Q ok) a b ⟨rfl,fit.2⟩
  next => contradiction

theorem split_loose (s : Group) (Q : Rect) (side : Bool) (i : Fin 11)
    (z : refutesLoose s (off Q side i)) (o : refutesLoose s (on Q side i)) : refutesLoose s Q :=
  fun a b fit => split_invalid a b Q side i (z a b fit) (o a b fit)

end PetersenSecondCube.Envelope
