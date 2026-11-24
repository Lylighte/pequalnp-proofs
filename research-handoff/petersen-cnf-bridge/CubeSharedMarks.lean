import CubeBitCode

namespace PetersenSecondCube

open PEqualNP.AndCount PetersenFirstPins PetersenNormalized PetersenBoundary
open PetersenFootprintCenters PetersenWeighted
open PetersenMixedStar (V)

def containedIf (p i c : Nat) := !p.testBit i || (p &&& c == p)

private theorem cover_included (p i c j : Nat) (ok : containedIf p i c=true)
    (hi : p.testBit i=true) (hj : p.testBit j=true) : c.testBit j=true := by
  obtain eq : p &&& c = p := by simpa [containedIf,hi] using ok
  have atBit := congrArg (fun z : Nat => z.testBit j) eq
  simpa [Nat.testBit_and,hj] using atBit

def compactMark (a b : Nat) (Q : Rect) (c0 c1 : Nat) (e : Mark) :=
  let p := pcode a b Q e.p
  containedIf p 10 c0 && containedIf p 11 c1

private theorem compact_ok (a b : Nat) (Q : Rect) (e : Mark)
    (valid : compactMark a b Q (neighbors a b Q 10) (neighbors a b Q 11) e=true) :
    unmix a b Q e.p = true := by
  have checks := Bool.and_eq_true_iff.mp valid
  apply List.all_eq_true.mpr; intro j hj
  let x := Fin.natAdd 10 j
  by_cases yes : positive a b Q e.p x=true
  · apply Bool.or_eq_true_iff.mpr; right
    apply List.all_eq_true.mpr; intro y hy
    by_cases on : positive a b Q e.p y=true
    · apply Bool.or_eq_true_iff.mpr; right
      have px : (pcode a b Q e.p).testBit x.val=true :=
        (code_spec _ _ _ _ _ _ _).trans yes
      have py : (pcode a b Q e.p).testBit y.val=true :=
        (code_spec _ _ _ _ _ _ _).trans on
      have active : (neighbors a b Q x).testBit y.val=true := by
        fin_cases j
        · exact cover_included _ 10 _ _ checks.1 px py
        · exact cover_included _ 11 _ _ checks.2 px py
      obtain ⟨m,hm,ay,ax⟩ := (numeric_neighbors _ _ _ _ _).mp active
      exact List.any_eq_true.mpr ⟨m,hm,Bool.and_eq_true_iff.mpr ⟨ax,ay⟩⟩
    · simp [Bool.eq_false_iff.mpr on]
  · change (!positive a b Q e.p x || _) = true
    simp [Bool.eq_false_iff.mpr yes]

def wrows : Witness → List Mark
  | .spent e => [e]
  | .centers es => es

def compact (a b : Nat) (Q : Rect) (w : Witness) :=
  let c0 := neighbors a b Q 10
  let c1 := neighbors a b Q 11
  (wrows w).all (compactMark a b Q c0 c1) && match w with
    | .spent e => decide (2 ≤ count a b Q.ll Q.rl e.v ∨ 2 ≤ count a b Q.ll Q.rl e.w)
    | .centers es => decide (4 < (large a b Q es).card)

theorem fast_invalid (a b : Nat) (Q : Rect) (w : Witness)
    (edges : ∀ e∈wrows w, RowEdge e.p e.v e.w) (checked : compact a b Q w=true) : Invalid a b Q := by
  have proofs := Bool.and_eq_true_iff.mp checked
  have mark (e) (he : e ∈ wrows w) : markOK a b Q e=true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true (edges e he),compact_ok _ _ _ _ (List.all_eq_true.mp proofs.1 e he)⟩
  intro l r inside C hk front hc shape
  apply leaf_sound a b Q l r inside C hk front hc shape w
  cases w with
  | spent e => exact Bool.and_eq_true_iff.mpr ⟨mark e (by simp [wrows]),proofs.2⟩
  | centers es => exact Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr mark,proofs.2⟩

theorem indexed_spent (a b : Nat) (Q : Rect) (rows : Fin t → Mark)
    (known : ∀ i, RowEdge (rows i).p (rows i).v (rows i).w) (i : Fin t)
    (ok : compact a b Q (.spent (rows i))=true) : Invalid a b Q :=
  fast_invalid a b Q _ (by simpa [wrows] using known i) ok

theorem indexed_centers (a b : Nat) (Q : Rect) (rows : Fin t → Mark)
    (known : ∀ i, RowEdge (rows i).p (rows i).v (rows i).w) (is : List (Fin t))
    (ok : compact a b Q (.centers (is.map rows))=true) : Invalid a b Q :=
  fast_invalid a b Q _ (by
    intro e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    exact known i) ok

def room (n cap : Nat) (pos : Fin n → Nat) (hi blocked : Nat) := decide
  ((Finset.univ.filter (fun j => hi &&& pos j ≠ 0 ∧ pos j &&& blocked ≠ pos j)).card ≤ cap)

def verifyFast (n cap : Nat) (pos : Fin n → Nat) (conflict : Fin 12 → Nat) :
    List (Fin 12) → Nat → Nat → Bool
  | [],hi,blocked => room n cap pos hi blocked
  | i :: is,hi,blocked => room n cap pos hi blocked ||
    (verifyFast n cap pos conflict is (hi ^^^ 2^i.val) blocked &&
     verifyFast n cap pos conflict is hi (blocked ||| conflict i))

private theorem room_sound (n cap : Nat) (p : Fin n → Nat) (conflict : Fin 12 → Nat)
    (s hi ban : Nat) (upper : MaskLe s hi)
    (locked : ∀ y : Fin 12, ban.testBit y.val=true → s &&& conflict y ≠ 0)
    (ok : room n cap p hi ban=true) :
    (Finset.univ.filter (fun j => possible s (p j) conflict)).card ≤ cap := by
  apply le_trans (Finset.card_le_card ?_) (of_decide_eq_true ok)
  intro j m
  obtain ⟨nonempty,y,on,openBit⟩ := (Finset.mem_filter.mp m).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit_mono upper nonempty,?_⟩
  intro eq
  have bit := congrArg (fun z : Nat => z.testBit y.val) eq
  exact locked y (by simpa [Nat.testBit_and,on] using bit) openBit

theorem fast_limit (n cap : Nat) (p : Fin n → Nat) (bad : Fin 12 → Nat)
    (symm : ∀ y x : Fin 12, (bad y).testBit x.val=true → (bad x).testBit y.val=true)
    (bits : List (Fin 12)) (hi ban : Nat) (ok : verifyFast n cap p bad bits hi ban=true)
    (s : Nat) (upper : MaskLe s hi)
    (locked : ∀ y : Fin 12, ban.testBit y.val=true → s &&& bad y ≠ 0) :
    (Finset.univ.filter (fun j => possible s (p j) bad)).card ≤ cap := by
  induction bits generalizing hi ban with
  | nil => exact room_sound _ _ _ _ _ _ _ upper locked ok
  | cons i is ih =>
    rcases Bool.or_eq_true_iff.mp ok with leaf | kids
    · exact room_sound _ _ _ _ _ _ _ upper locked leaf
    have two := Bool.and_eq_true_iff.mp kids
    by_cases on : s.testBit i.val=true
    · apply ih _ _ two.2 upper; intro y h
      rw [Nat.testBit_or,Bool.or_eq_true] at h
      rcases h with h | h
      · exact locked y h
      · intro zero
        have eq := congrArg (fun z : Nat => z.testBit i.val) zero
        simp [Nat.testBit_and,on,symm i y h] at eq
    · apply ih _ _ two.1 _ locked
      intro j set
      have ne : i.val ≠ j := fun eq => on (eq ▸ set)
      simp [Nat.testBit_xor,ne,upper j set]

theorem fast_ticket_invalid (a b : Nat) (Q : Rect) (n cap : Nat) (tickets : Fin n → M)
    (order : List (Fin 12)) (good : ∀ j, tickets j∈positiveMasks)
    (checked : verifyFast n cap (fun j => pcode a b Q (tickets j)) (neighbors a b Q) order 4095 0=true)
    (few : 4*cap<n) : Invalid a b Q := by
  apply ticket_invalid a b Q n cap tickets (fun j => pcode a b Q (tickets j)) (neighbors a b Q) good
  · intro j x; rw [pcode,code_spec]; exact id
  · intro y x; exact (numeric_neighbors ..).mp
  · intro s
    apply fast_limit _ _ _ _ _ order 4095 0 checked s.val
    · intro i yes
      have small : i < 12 := by
        by_contra! ge
        have pow : 4096 ≤ 2^i := Nat.pow_le_pow_right (n:=2) (i:=12) (by decide) ge
        exact Bool.false_ne_true ((Nat.testBit_lt_two_pow (s.isLt.trans_le pow)).symm.trans yes)
      change (2^12-1 : Nat).testBit i = true
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true small
    · simp
    · intro y x bit
      obtain ⟨m,mem,on,off⟩ := (numeric_neighbors ..).mp bit
      exact (numeric_neighbors ..).mpr ⟨m,mem,off,on⟩
  · exact few

end PetersenSecondCube
