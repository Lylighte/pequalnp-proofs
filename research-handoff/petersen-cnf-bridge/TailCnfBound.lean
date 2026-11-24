import Mathlib

namespace PetersenTailCnf

variable {W I : Type} [DecidableEq W]

-- A visible wire is true on a row precisely when it belongs to its wire set.
def hit (clause row : Finset W) : Prop := ∃ w ∈ clause, w ∈ row
def sat (cnf : List (Finset W)) (row : Finset W) : Prop := ∀ c ∈ cnf, hit c row

@[simp] theorem hit_union (a b row : Finset W) : hit (a ∪ b) row ↔ hit a row ∨ hit b row := by
  simp [hit, or_and_right, exists_or]

omit [DecidableEq W] in
@[simp] theorem hit_empty (row : Finset W) : ¬hit ∅ row := by simp [hit]

def incompatible (q : Finset I) (visible : I → Finset W) (pos : I → Prop) : Prop :=
  ∀ x ∈ q, ∀ y ∈ q, x ≠ y → ∃ p, pos p ∧ visible p ⊆ visible x ∪ visible y

-- Associate to each negative row one clause it misses. A shared missed
-- clause would also be missed by the positive witness below the union.
theorem clause_lower_bound (cnf : List (Finset W)) (q : Finset I)
    (visible : I → Finset W) (pos : I → Prop)
    (neg : ∀ x ∈ q, ¬ sat cnf (visible x)) (yes : ∀ p, pos p → sat cnf (visible p))
    (inc : incompatible q visible pos) : q.card ≤ cnf.length := by
  classical
  have miss (x : q) : ∃ c : cnf.toFinset, ¬ hit c.val (visible x.val) := by
    by_contra! all
    exact neg x.val x.property (fun c hc => all ⟨c,by simpa using hc⟩)
  choose chooseClause missed using miss
  have inj : Function.Injective chooseClause := by
    intro x y eq
    by_contra diff
    obtain ⟨p,hp,sub⟩ := inc x.val x.property y.val y.property
      (fun e => diff (Subtype.ext e))
    obtain ⟨w,hw,ht⟩ := yes p hp (chooseClause x).val (List.mem_toFinset.mp (chooseClause x).property)
    rcases Finset.mem_union.mp (sub ht) with hx | hy
    · exact missed x ⟨w,hw,hx⟩
    · exact missed y ⟨w,eq ▸ hw,hy⟩
  have count := Fintype.card_le_of_injective chooseClause inj
  simp only [Fintype.card_coe] at count
  exact count.trans (List.toFinset_card_le cnf)

-- The numerical witness in the enumeration tests p AND (x OR y) = p.
def bits (n m : Nat) : Finset (Fin n) := Finset.univ.filter (fun v => m.testBit v.val)

theorem dominated_union (n p x y : Nat) (h : p &&& (x ||| y) = p) :
    bits n p ⊆ bits n x ∪ bits n y := by
  intro w hw
  have on := (Finset.mem_filter.mp hw).2
  have eq := congrArg (fun k : Nat => k.testBit w.val) h
  simp only [Nat.testBit_and, Nat.testBit_or, on, Bool.true_and] at eq
  simpa [bits] using eq

theorem incompatible_of_masks (n : Nat) (q : Finset I) (mask : I → Nat) (pos : I → Prop)
    (pair : ∀ x ∈ q, ∀ y ∈ q, x ≠ y → ∃ p, pos p ∧ mask p &&& (mask x ||| mask y) = mask p) :
    incompatible q (fun i => bits n (mask i)) pos := by
  intro x hx y hy hxy
  obtain ⟨p,hp,hb⟩ := pair x hx y hy hxy
  exact ⟨p,hp,dominated_union n _ _ _ hb⟩

-- Add the direct OR of selected visible wires to each clause.
def withOutput (o : Finset W) (f : List (Finset W)) := f.map (o ∪ ·)

@[simp] theorem withOutput_sat (o row : Finset W) (f : List (Finset W)) :
    sat (withOutput o f) row ↔ hit o row ∨ sat f row := by
  simp only [sat,withOutput,List.forall_mem_map,hit_union]
  by_cases h : hit o row <;> simp [h]

def four (o a b c d : Finset W) : List (Finset W) :=
  withOutput o [a ∪ c,a ∪ d,b ∪ c,b ∪ d]

theorem four_eval (o a b c d row : Finset W) : sat (four o a b c d) row ↔
    hit o row ∨ (hit a row ∧ hit b row) ∨ (hit c row ∧ hit d row) := by
  simp [four,sat,withOutput]
  tauto

-- Each terminal is a binary AND. It can be omitted from the output and can
-- select helper H on either side. Every other side input is visible.
structure Terminal (W : Type) where
  left : Finset W
  right : Finset W
  useLeft : Bool
  useRight : Bool
  enabled : Bool

def fires (t : Terminal W) (row : Finset W) (h : Prop) : Prop :=
  t.enabled = true ∧ (hit t.left row ∨ (t.useLeft = true ∧ h)) ∧
    (hit t.right row ∨ (t.useRight = true ∧ h))

-- Normalize the side which can read H to the first position. A disabled
-- terminal is zero, represented by an empty opposite side.
def host (t : Terminal W) := if t.useRight then t.right else t.left
def opp (t : Terminal W) : Finset W :=
  if t.enabled then (if t.useRight then t.left else t.right) else ∅
def reads (t : Terminal W) := t.useLeft || t.useRight
def singleSide (t : Terminal W) : Prop := ¬(t.enabled = true ∧ t.useLeft = true ∧ t.useRight = true)

omit [DecidableEq W] in
theorem normalize (t : Terminal W) (row : Finset W) (h : Prop) (one : singleSide t) :
    fires t row h ↔ (hit (host t) row ∨ (reads t = true ∧ h)) ∧ hit (opp t) row := by
  rcases t with ⟨a,b,x,y,en⟩
  cases x <;> cases y <;> cases en <;> simp_all [singleSide,fires,host,opp,reads,and_comm]

-- If H fires on a negative input, an enabled terminal which is false
-- there cannot read H on both sides.
omit [DecidableEq W] in
theorem singleSide_of_unsafe (t : Terminal W) (row : Finset W) {h : Prop}
    (on : h) (off : ¬fires t row h) : singleSide t := by
  rintro ⟨en,hl,hr⟩
  exact off ⟨en,Or.inr ⟨hl,on⟩,Or.inr ⟨hr,on⟩⟩

def addWhen (on : Bool) (base extra : Finset W) := if on then base ∪ extra else base

def pairClauses (on : Bool) (base hl hr : Finset W) :=
  [addWhen on base hl, addWhen on base hr]

omit [DecidableEq W] in
private theorem sat_append (f g : List (Finset W)) (row : Finset W) :
    sat (f ++ g) row ↔ sat f row ∧ sat g row := by simp only [sat,List.forall_mem_append]

omit [DecidableEq W] in
private theorem sat_one (c row : Finset W) : sat [c] row ↔ hit c row := by simp [sat]

private theorem sat_pair (on : Bool) (a hl hr row : Finset W) :
    sat (pairClauses on a hl hr) row ↔ hit a row ∨ (on = true ∧ hit hl row ∧ hit hr row) := by
  cases on <;> simp [pairClauses, addWhen, sat, or_and_left]

private theorem distribute (a b c d : Prop) :
    (a ∧ b) ∨ (c ∧ d) ↔ (b ∨ d) ∧ (a ∨ c) ∧ (a ∨ d) ∧ (b ∨ c) := by tauto

def seven (o hl hr : Finset W) (t u : Terminal W) : List (Finset W) :=
  let a := host t
  let b := opp t
  let c := host u
  let d := opp u
  let both := reads t || reads u
  withOutput o ([b ∪ d] ++ (pairClauses both (a ∪ c) hl hr ++
    (pairClauses (reads t) (a ∪ d) hl hr ++ pairClauses (reads u) (b ∪ c) hl hr)))

theorem seven_eval (o hl hr row : Finset W) (t u : Terminal W)
    (ht : singleSide t) (hu : singleSide u) :
    let h := hit hl row ∧ hit hr row
    sat (seven o hl hr t u) row ↔ hit o row ∨ fires t row h ∨ fires u row h := by
  dsimp only
  rw [normalize t row _ ht, normalize u row _ hu]
  rw [distribute]
  simp only [seven, withOutput_sat, sat_append, sat_one, sat_pair, hit_union,
    Bool.or_eq_true, or_and_right, or_assoc, or_comm, or_left_comm]

theorem independent_bound (q : Finset I) (visible : I → Finset W) (pos : I → Prop)
    (o a b c d : Finset W) (inc : incompatible q visible pos)
    (neg : ∀ x ∈ q, ¬ (hit o (visible x) ∨
      (hit a (visible x) ∧ hit b (visible x)) ∨ (hit c (visible x) ∧ hit d (visible x))))
    (yes : ∀ p, pos p → hit o (visible p) ∨
      (hit a (visible p) ∧ hit b (visible p)) ∨ (hit c (visible p) ∧ hit d (visible p))) :
    q.card ≤ 4 :=
  clause_lower_bound (four o a b c d) q visible pos
    (fun x hx h => neg x hx ((four_eval ..).mp h)) (fun p hp => (four_eval ..).mpr (yes p hp)) inc

def helperOutput (o hl hr : Finset W) (t u : Terminal W) (row : Finset W) : Prop :=
  let h := hit hl row ∧ hit hr row
  hit o row ∨ fires t row h ∨ fires u row h

theorem one_helper_bound (q : Finset I) (visible : I → Finset W) (pos : I → Prop)
    (o hl hr : Finset W) (t u : Terminal W) (ht : singleSide t) (hu : singleSide u)
    (inc : incompatible q visible pos)
    (neg : ∀ x ∈ q, ¬ helperOutput o hl hr t u (visible x))
    (yes : ∀ p, pos p → helperOutput o hl hr t u (visible p)) : q.card ≤ 7 :=
  clause_lower_bound (seven o hl hr t u) q visible pos
    (fun x hx h => neg x hx ((seven_eval _ _ _ _ _ _ ht hu).mp h))
    (fun p hp => (seven_eval _ _ _ _ _ _ ht hu).mpr (yes p hp)) inc

theorem one_helper_bound_of_unsafe (q : Finset I) (visible : I → Finset W) (pos : I → Prop)
    (o hl hr : Finset W) (t u : Terminal W)
    (unsafeWitness : ∃ x, hit hl (visible x) ∧ hit hr (visible x) ∧
      ¬helperOutput o hl hr t u (visible x))
    (inc : incompatible q visible pos)
    (neg : ∀ x ∈ q, ¬helperOutput o hl hr t u (visible x))
    (yes : ∀ p, pos p → helperOutput o hl hr t u (visible p)) : q.card ≤ 7 := by
  obtain ⟨x,l,r,off⟩ := unsafeWitness
  have on := And.intro l r
  apply one_helper_bound q visible pos o hl hr t u _ _ inc neg yes
  · exact singleSide_of_unsafe t (visible x) on (fun h => off (Or.inr (Or.inl h)))
  · exact singleSide_of_unsafe u (visible x) on (fun h => off (Or.inr (Or.inr h)))

end PetersenTailCnf

-- Concrete eight-row certificate from the retained prefix census.
namespace PetersenTailCnf.Example

def nRows : List Nat := [50,69,104,116,138,201,208,385]
def pRows : List Nat := [51,58,77,54,85,108,71,106,105,139,114,120,212,154,209,197,393]
def edgeMasks : List Nat := [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288]
def independent (m : Nat) := edgeMasks.all (fun e => m &&& e != e)
def maximalIndependent (m : Nat) := independent m && (List.range 10).all
  (fun v => m.testBit v || !independent (m ||| (1 <<< v)))
def extension (m : Nat) := (List.range 10).any
  (fun v => m.testBit v && maximalIndependent (m ^^^ (1 <<< v)))

def gate (m l r bit : Nat) := if m &&& l ≠ 0 ∧ m &&& r ≠ 0 then m ||| bit else m
def projected (m : Nat) :=
  -- The third gate consumes vertex 4's second bare occurrence.
  (gate (gate (gate m 1 4 1024) 410 1760 2048) 16 2048 4096) &&& 8175

theorem checked_pairs :
    nRows.all maximalIndependent = true ∧ pRows.all extension = true ∧
    nRows.all (fun a => nRows.all (fun b => if a=b then true else
      pRows.any (fun p => projected p &&& (projected a ||| projected b) == projected p))) = true ∧
    nRows.toFinset.card = 8 := by decide +kernel

theorem clique : incompatible nRows.toFinset (fun i => bits 13 (projected i)) (· ∈ pRows) := by
  apply incompatible_of_masks
  intro x hx y hy neq
  have row := List.all_eq_true.mp checked_pairs.2.2.1 x (List.mem_toFinset.mp hx)
  have pair := List.all_eq_true.mp row y (List.mem_toFinset.mp hy)
  simpa [neq,List.any_eq_true] using pair

theorem needs_eight (f : List (Finset (Fin 13)))
    (hn : ∀ n ∈ nRows, ¬sat f (bits 13 (projected n)))
    (hp : ∀ p ∈ pRows, sat f (bits 13 (projected p))) : 8 ≤ f.length := by
  rw [← checked_pairs.2.2.2]
  exact clause_lower_bound f _ _ _ (fun n h => hn n (List.mem_toFinset.mp h)) hp clique

theorem no_one_helper (o hl hr : Finset (Fin 13)) (t u : Terminal (Fin 13))
    (ht : singleSide t) (hu : singleSide u)
    (hn : ∀ n ∈ nRows, ¬helperOutput o hl hr t u (bits 13 (projected n)))
    (hp : ∀ p ∈ pRows, helperOutput o hl hr t u (bits 13 (projected p))) : False := by
  have low := needs_eight (seven o hl hr t u)
    (fun n h sat => hn n h ((seven_eval _ _ _ _ _ _ ht hu).mp sat))
    (fun p h => (seven_eval _ _ _ _ _ _ ht hu).mpr (hp p h))
  exact (by decide : ¬ 8 ≤ 7) low

end PetersenTailCnf.Example

#print axioms PetersenTailCnf.clause_lower_bound
#print axioms PetersenTailCnf.dominated_union
#print axioms PetersenTailCnf.four_eval
#print axioms PetersenTailCnf.seven_eval
#print axioms PetersenTailCnf.singleSide_of_unsafe
#print axioms PetersenTailCnf.independent_bound
#print axioms PetersenTailCnf.one_helper_bound
#print axioms PetersenTailCnf.one_helper_bound_of_unsafe
#print axioms PetersenTailCnf.Example.checked_pairs
#print axioms PetersenTailCnf.Example.needs_eight
#print axioms PetersenTailCnf.Example.no_one_helper
