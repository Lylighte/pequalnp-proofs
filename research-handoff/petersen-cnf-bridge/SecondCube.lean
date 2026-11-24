import FootprintPrefix
import FootprintSpent

namespace PetersenSecondCube

open PEqualNP.AndCount PetersenSuffix PetersenTailCnf PetersenFirstPins PetersenNormalized
open PetersenBoundary PetersenMixedStar PetersenFootprintCenters

structure Rect where
  ll : Nat
  lh : Nat
  rl : Nat
  rh : Nat
  deriving DecidableEq

structure Within (Q : Rect) (l r : Nat) : Prop where
  ll : Sub Q.ll l
  lh : Sub l Q.lh
  rl : Sub Q.rl r
  rh : Sub r Q.rh

def allRect : Rect := ⟨0,2047,0,2047⟩

theorem start (l r : Nat) : Within allRect l r := by
  have top : ∀ i : Fin 11, (2047:Nat).testBit i.val = true := by decide
  exact ⟨fun i => by simp [allRect],fun i _ => top i,fun i => by simp [allRect],fun i _ => top i⟩

-- The actual 15-bit footprints of both selected sides refine this rectangle.
def box (a b : Nat) (Q : Rect) (l r : Nat) : Box :=
  ⟨a,b,Q.ll,Q.lh,Q.rl,Q.rh,packFoot a b l,packFoot a b r⟩

theorem member (a b : Nat) (Q : Rect) (l r : Nat) (mem : Within Q l r) : Member (box a b Q l r) l r :=
  ⟨mem.ll,mem.lh,mem.rl,mem.rh,packFoot_class a b l,packFoot_class a b r⟩

-- A common lower approximation on negative rows serves every exact pair of
-- footprints in the rectangle. Positive rows use its upper masks instead.
def positive (a b : Nat) (Q : Rect) (p : M) := view a b Q.ll Q.rl p (h1 a b Q.lh Q.rh p)
def negative (a b : Nat) (Q : Rect) (n : M) := view a b Q.ll Q.rl n (h1 a b Q.ll Q.rl n)

private theorem view_mono (a b ll rl : Nat) (m : M) (z z' : Bool)
    (inc : z = true → z' = true) (x : Fin 12) : view a b ll rl m z x = true → view a b ll rl m z' x = true := by
  refine Fin.addCases (m := 10) (n := 2) (fun v => ?_) (fun j => ?_) x
  · simp [view]
  · simp only [view,Fin.addCases_right]
    fin_cases j
    · simp
    · exact inc

theorem negative_refines (a b : Nat) (Q : Rect) (l r : Nat) (mem : Within Q l r) (n : M) (hn : n ∈ negativeMasks)
    (x : Fin 12) : negative a b Q n x = true → lowerNeg (box a b Q l r) n x = true := by
  apply view_mono
  rw [← neg_eq (box a b Q l r) l r (member a b Q l r mem) n hn]
  simp only [h1,Bool.and_eq_true]
  exact And.imp (side_mono _ _ _ _ mem.ll n) (side_mono _ _ _ _ mem.rl n)

def unmix (a b : Nat) (Q : Rect) (p : M) := (List.finRange 2).all fun j =>
  let x := Fin.natAdd 10 j
  !(positive a b Q p x) || (List.finRange 12).all fun y =>
    !(positive a b Q p y) || negativeMasks.any (fun n => negative a b Q n x && negative a b Q n y)

theorem blocked (a b : Nat) (Q : Rect) (l r : Nat) (mem : Within Q l r) (p : M)
    (cert : unmix a b Q p = true) : Blocked (gates a b l r) (decode p) := by
  let B := box a b Q l r
  have inside : Member B l r := member a b Q l r mem
  have ordered (x y : Fin 12) (large : 10 ≤ x.val)
      (hx : x ∈ projected (gates a b l r) (decode p)) (hy : y ∈ projected (gates a b l r) (decode p)) :
      ∃ n ∈ negatives, x ∈ projected (gates a b l r) n ∧ y ∈ projected (gates a b l r) n := by
    let j : Fin 2 := ⟨x.val-10,by omega⟩
    have eq : Fin.natAdd 10 j = x := Fin.ext (by change 10+(x.val-10)=x.val; omega)
    have cx := List.all_eq_true.mp cert j (List.mem_finRange j)
    have ux : positive a b Q p x = true := active_upper B l r inside p x hx
    have uy : positive a b Q p y = true := active_upper B l r inside p y hy
    simp only [eq,ux,Bool.not_true,Bool.false_or] at cx
    have cy := List.all_eq_true.mp cx y (List.mem_finRange y)
    simp only [uy,Bool.not_true,Bool.false_or] at cy
    obtain ⟨n,hn,both⟩ := List.any_eq_true.mp cy
    have nmem := negative_refines a b Q l r mem n hn
    have pass := negative_transfer B l r inside p n hn
    exact ⟨decode n,Finset.mem_image_of_mem _ (by simpa using hn),
      pass x hx (nmem x (Bool.and_eq_true_iff.mp both).1),pass y hy (nmem y (Bool.and_eq_true_iff.mp both).2)⟩
  intro x hx y hy mixed
  rcases mixed with big | big
  · exact ordered x y big hx hy
  · obtain ⟨n,hn,vy,vx⟩ := ordered y x big hy hx
    exact ⟨n,hn,vx,vy⟩

structure Mark where
  p : M
  v : V
  w : V

def markOK (a b : Nat) (Q : Rect) (e : Mark) := decide (RowEdge e.p e.v e.w) && unmix a b Q e.p

theorem checked_mark (a b : Nat) (Q : Rect) (l r : Nat) (mem : Within Q l r) (e : Mark)
    (yes : markOK a b Q e = true) : ForcedEdge (gates a b l r) e.v e.w := by
  have chk := Bool.and_eq_true_iff.mp yes
  have row : RowEdge e.p e.v e.w := of_decide_eq_true chk.1
  refine ⟨decode e.p,Finset.mem_image_of_mem _ (by simpa using row.1),blocked a b Q l r mem e.p chk.2,?_⟩
  intro x hx y hy edge
  exact row.2 x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 edge

theorem reverse_mark (P : AndCountCircuit 10) (v w : V) (h : ForcedEdge P v w) : ForcedEdge P w v := by
  obtain ⟨u,hp,blk,uniq⟩ := h
  exact ⟨u,hp,blk,fun a ha b hb edge => (uniq a ha b hb edge).symm⟩

def nextTo (marks : List Mark) (v : V) : Finset V :=
  Finset.univ.filter (fun w => marks.any fun e => (e.v == v && e.w == w) || (e.v == w && e.w == v))

def large (a b : Nat) (Q : Rect) (marks : List Mark) : Finset V :=
  Finset.univ.filter (fun v => 2 < (nextTo marks v).card + count a b Q.ll Q.rl v)

inductive Witness where
  | spent (e : Mark)
  | centers (edges : List Mark)

def witnessOK (a b : Nat) (Q : Rect) : Witness → Bool
  | .spent e => markOK a b Q e && decide (2 ≤ count a b Q.ll Q.rl e.v ∨ 2 ≤ count a b Q.ll Q.rl e.w)
  | .centers es => es.all (markOK a b Q) && decide (4 < (large a b Q es).card)

theorem leaf_sound (a b : Nat) (Q : Rect) (l r : Nat) (mem : Within Q l r) (C : AndCountCircuit 10)
    (hk : 2 ≤ C.size) (front : Matches C (gates a b l r) hk) (hc : Candidate C) (shape : Shape C 2)
    (w : Witness) (good : witnessOK a b Q w = true) : False := by
  cases w with
  | spent e =>
    have yes := Bool.and_eq_true_iff.mp good
    have edge := checked_mark a b Q l r mem e yes.1
    have cap := forced_available C _ hk front hc shape e.v e.w edge
    rw [use_count a b l r e.v,use_count a b l r e.w] at cap
    have low := of_decide_eq_true yes.2
    have lhs := count_mono a b Q.ll Q.rl l r mem.ll mem.rl e.v
    have rhs := count_mono a b Q.ll Q.rl l r mem.ll mem.rl e.w
    omega
  | centers es =>
    have yes := Bool.and_eq_true_iff.mp good
    have need := degree_bound C _ hk front hc shape (large a b Q es) (nextTo es) (by
      intro v _ w hn
      obtain ⟨e,he,on⟩ := List.any_eq_true.mp (Finset.mem_filter.mp hn).2
      have edge := checked_mark a b Q l r mem e (List.all_eq_true.mp yes.1 e he)
      simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at on
      rcases on with ⟨hv,hw⟩ | ⟨hw,hv⟩
      · exact hv ▸ hw ▸ edge
      · exact hv ▸ hw ▸ reverse_mark _ _ _ edge) (by
      intro v hv
      rw [use_count a b l r v]
      have low := (Finset.mem_filter.mp hv).2
      exact lt_of_lt_of_le low (Nat.add_le_add_left (count_mono a b Q.ll Q.rl l r mem.ll mem.rl v) _))
    have cap := hc.2.1
    have high := of_decide_eq_true yes.2
    change (large a b Q es).card ≤ C.size-2 at need
    omega

end PetersenSecondCube
