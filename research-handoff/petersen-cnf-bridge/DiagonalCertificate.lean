import DiagonalFactData

namespace PetersenDiagonalNumeric

open PetersenFootprintCenters PetersenTailCnf

def population (t : M) := (bits 10 t.val).card
def plainOk (t j o : M) := (j.val &&& t.val == j.val) &&
  ((List.finRange 10).all fun v => !o.val.testBit v.val || (List.finRange 10).any fun c =>
    t.val.testBit c.val && !j.val.testBit c.val && (c==v || (nb c).testBit v.val)) &&
  (List.finRange 70).all (fun i => raw o (pval i) || raw j (star i))

-- Residual positives need the single ternary term, and the term is false
-- on negatives. Four distinct centers make every binary rectangle nonempty.
structure Model where
  t : M
  j : M
  o : M
  a : M
  b : M
  size : population t ≤ 4
  positive (i : Fin 70) : raw t (star i) = false →
    raw a (pval i) = true ∧ raw b (pval i) = true ∧ raw o (pval i) = true
  negative (i : Fin 15) : ¬(raw a (nrow i) = true ∧ raw b (nrow i) = true ∧ raw o (nrow i) = true)
  ports : population t = 4 → plainOk t j o = true

def pick (q i : Nat) : Fin 15 := ⟨((q >>> (4*i))%16)%15, Nat.mod_lt _ (by decide)⟩
def witness (t : M) (x y : Fin 15) := (List.finRange 70).any fun i =>
  !raw t (star i) && ((pval i).val &&& ((nrow x).val ||| (nrow y).val) == (pval i).val)

def clique (t : M) (n q : Nat) := (List.finRange n).all fun i => (List.finRange n).all fun j =>
  decide (i.val ≥ j.val) || witness t (pick q i.val) (pick q j.val)

private theorem hit_union_mono (a : Nat) (p x y : M) (sub : p.val &&& (x.val ||| y.val) = p.val)
    (on : raw a p = true) : raw a x = true ∨ raw a y = true := by
  obtain ⟨v,m,h⟩ := (raw_iff a p).mp on
  rcases Finset.mem_union.mp (dominated_union 10 p.val x.val y.val sub h) with hx | hy
  · exact Or.inl ((raw_iff a x).mpr ⟨v,m,hx⟩)
  · exact Or.inr ((raw_iff a y).mpr ⟨v,m,hy⟩)

private theorem color_impossible (t : M) (q k : Nat) (h : clique t (k+1) q = true)
    (colors : Fin k → Nat) (cover : ∀ j : Fin (k+1), ∃ c, raw (colors c) (nrow (pick q j.val)) = false)
    (pos : ∀ c i, raw t (star i) = false → raw (colors c) (pval i) = true) : False := by
  classical
  choose color off using cover
  have diff (x y : Fin (k+1)) (xy : x < y) : color x ≠ color y := by
    intro same
    have chk := List.all_eq_true.mp (List.all_eq_true.mp h x (List.mem_finRange x)) y (List.mem_finRange y)
    have lt : ¬ x.val ≥ y.val := Nat.not_le_of_lt xy
    simp only [lt,decide_false,Bool.false_or] at chk
    obtain ⟨i,_,good⟩ := List.any_eq_true.mp chk
    have v := Bool.and_eq_true_iff.mp good
    have on := pos (color x) i (by simpa using v.1)
    rcases hit_union_mono (colors (color x)) _ _ _ (eq_of_beq v.2) on with left | right
    · simp [off x] at left
    · simp [same,off y] at right
  have inj : Function.Injective color := by
    intro x y eq
    rcases lt_trichotomy x y with lo | same | hi
    · exact False.elim (diff x y lo eq)
    · exact same
    · exact False.elim (diff y x hi eq.symm)
  have le := Fintype.card_le_of_injective color inj
  simp only [Fintype.card_fin] at le
  omega

theorem four_impossible (M : Model) (q : Nat) (checked : clique M.t 4 q = true) : False := by
  apply color_impossible M.t q 3 checked (![M.a.val,M.b.val,M.o.val]) ?_ ?_
  · intro j
    let n := nrow (pick q j.val)
    have no := M.negative (pick q j.val)
    by_cases a : raw M.a.val n = true
    · by_cases b : raw M.b.val n = true
      · exact ⟨2,Bool.eq_false_iff.mpr (fun o => no ⟨a,b,o⟩)⟩
      · exact ⟨1,Bool.eq_false_iff.mpr b⟩
    · exact ⟨0,Bool.eq_false_iff.mpr a⟩
  · intro c i off
    have good := M.positive i off
    fin_cases c
    · exact good.1
    · exact good.2.1
    · exact good.2.2

def touches (o : Nat) (q : Nat) := (List.finRange 3).all fun j => raw o (nrow (pick q j.val))

theorem three_impossible (M : Model) (q : Nat) (checked : clique M.t 3 q = true) (ok : touches M.o.val q = true) : False := by
  apply color_impossible M.t q 2 checked (![M.a.val,M.b.val]) ?_ ?_
  · intro j
    let n := nrow (pick q j.val)
    have o := List.all_eq_true.mp ok j (List.mem_finRange j)
    by_cases a : raw M.a.val n = true
    · exact ⟨1,Bool.eq_false_iff.mpr (fun b => M.negative (pick q j.val) ⟨a,b,o⟩)⟩
    · exact ⟨0,Bool.eq_false_iff.mpr a⟩
  · intro c i off
    have good := M.positive i off
    fin_cases c
    · exact good.1
    · exact good.2.1

def SubMask (a b : Nat) := ∀ i, a.testBit i = true → b.testBit i = true

theorem raw_mono (a b : Nat) (sub : SubMask a b) (m : M) : raw a m = true → raw b m = true := by
  rw [raw_iff,raw_iff]
  rintro ⟨v,va,vm⟩
  exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub v.val (Finset.mem_filter.mp va).2⟩,vm⟩

def possibleMode (t o : M) := (List.finRange 1024).any (fun j => plainOk t j o)

inductive PortTree where
  | split (v : Fin 10) (zero one : PortTree)
  | miss (i : Fin 70)
  | tri (q : Nat)
  | mode (o : M)

def portCheck (t : M) : PortTree → Nat → Nat → Bool
  | .split v l r,lo,hi => portCheck t l lo (hi ^^^ 2^v.val) && portCheck t r (lo ||| 2^v.val) hi
  | .miss i,_,hi => !raw t (star i) && !raw hi (pval i)
  | .tri q,lo,_ => clique t 3 q && touches lo q
  | .mode o,lo,hi => decide (lo=o.val ∧ hi=o.val ∧ population t=4) && !possibleMode t o

theorem port_impossible (M : Model) (w : PortTree) (lo hi : Nat)
    (lower : SubMask lo M.o.val) (upper : SubMask M.o.val hi) (valid : portCheck M.t w lo hi = true) : False := by
  induction w generalizing lo hi with
  | split v left right il ir =>
    have h := Bool.and_eq_true_iff.mp valid
    cases flag : M.o.val.testBit v.val with
    | false =>
      apply il lo _ lower ?_ h.1
      intro i on
      have ne : v.val ≠ i := fun eq => Bool.false_ne_true ((eq ▸ flag).symm.trans on)
      simp [Nat.testBit_xor,Nat.testBit_two_pow_of_ne ne,upper i on]
    | true =>
      apply ir _ hi ?_ upper h.2
      intro i on
      by_cases eq : v.val = i
      · exact eq ▸ flag
      · simp only [Nat.testBit_or,Nat.testBit_two_pow_of_ne eq,Bool.or_false] at on
        exact lower i on
  | miss i =>
    have h := Bool.and_eq_true_iff.mp valid
    have yes := raw_mono _ _ upper (pval i) (M.positive i (by simpa using h.1)).2.2
    simp [yes] at h
  | tri q =>
    have h := Bool.and_eq_true_iff.mp valid
    apply three_impossible M q h.1 (List.all_eq_true.mpr ?_)
    intro i _
    exact raw_mono lo _ lower _ (List.all_eq_true.mp h.2 i (List.mem_finRange i))
  | mode o =>
    have h := Bool.and_eq_true_iff.mp valid
    obtain ⟨e,f,s⟩ := of_decide_eq_true h.1
    have eq : M.o = o := Fin.ext (Nat.eq_of_testBit_eq (fun i => by
      cases a : M.o.val.testBit i <;> cases b : o.val.testBit i <;> simp_all [SubMask]))
    have yes : possibleMode M.t o = true := List.any_eq_true.mpr ⟨M.j,List.mem_finRange _,eq ▸ M.ports s⟩
    exact Bool.false_ne_true ((by simpa using h.2 : possibleMode M.t o = false).symm.trans yes)

theorem exception_impossible (M : Model) (w : PortTree) (valid : portCheck M.t w 0 1023 = true) : False :=
  port_impossible M w 0 1023 (fun i => by simp) (fun i h => by
    have small : i < 10 := by
      by_contra! big
      have le : 1024 ≤ 2^i := Nat.pow_le_pow_right (n:=2) (i:=10) (by decide) big
      exact Bool.false_ne_true ((Nat.testBit_lt_two_pow (M.o.isLt.trans_le le)).symm.trans h)
    change (2^10-1 : Nat).testBit i = true
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true small) valid

end PetersenDiagonalNumeric
