import WeightedTerminals

namespace PetersenWeighted

def MaskLe (a b : Nat) := ∀ i, a.testBit i = true → b.testBit i = true

theorem hit_mono {a b p : Nat} (le : MaskLe a b) (ha : a &&& p ≠ 0) : b &&& p ≠ 0 := by
  obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero ha
  rw [Nat.testBit_and,Bool.and_eq_true] at hi
  intro zero
  have eq := congrArg (fun m : Nat => m.testBit i) zero
  simp only [Nat.testBit_and,le i hi.1,hi.2,Bool.and_self,Nat.zero_testBit] at eq
  exact Bool.false_ne_true eq.symm

def relaxed (lo hi pos : Nat) (bad : Fin 12 → Nat) : Prop :=
  hi &&& pos ≠ 0 ∧ ∃ y : Fin 12, pos.testBit y.val = true ∧ lo &&& bad y = 0

instance (lo hi pos : Nat) (bad : Fin 12 → Nat) : Decidable (relaxed lo hi pos bad) := by
  unfold relaxed
  infer_instance

def leaf {n : Nat} (lo hi : Nat) (pos : Fin n → Nat) (bad : Fin 12 → Nat) (cap : Nat) :=
  decide ((Finset.univ.filter fun j => relaxed lo hi (pos j) bad).card ≤ cap)

def verify {n : Nat} (pos : Fin n → Nat) (bad : Fin 12 → Nat) (cap : Nat) :
    List Nat → Nat → Nat → Bool
  | [],lo,hi => leaf lo hi pos bad cap
  | i :: bits,lo,hi => leaf lo hi pos bad cap ||
    (verify pos bad cap bits lo (hi ^^^ 2^i) && verify pos bad cap bits (lo ||| 2^i) hi)

theorem fits_split (lo hi s i : Nat) (low : MaskLe lo s) (high : MaskLe s hi) :
    MaskLe s (hi ^^^ 2^i) ∨ MaskLe (lo ||| 2^i) s := by
  by_cases on : s.testBit i = true
  · right
    intro j h
    rw [Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq] at h
    exact h.elim (low j) (fun eq => eq ▸ on)
  · left
    intro j h
    have ne : i ≠ j := fun eq => on (eq ▸ h)
    simp [Nat.testBit_xor,ne,high j h]

theorem leaf_sound {n : Nat} (pos : Fin n → Nat) (bad : Fin 12 → Nat) (cap lo hi s : Nat)
    (low : MaskLe lo s) (high : MaskLe s hi) (atLeaf : leaf lo hi pos bad cap = true) :
    (Finset.univ.filter fun j => possible s (pos j) bad).card ≤ cap := by
  apply le_trans (Finset.card_le_card ?_) (of_decide_eq_true atLeaf)
  intro j mem
  obtain ⟨hit,y,positive,safe⟩ := (Finset.mem_filter.mp mem).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,hit_mono high hit,y,positive,?_⟩
  by_contra overlap
  exact hit_mono low overlap safe

theorem verify_sound {n : Nat} (pos : Fin n → Nat) (bad : Fin 12 → Nat) (cap : Nat)
    (bits : List Nat) (lo hi : Nat) (ok : verify pos bad cap bits lo hi = true)
    (s : Nat) (low : MaskLe lo s) (high : MaskLe s hi) :
    (Finset.univ.filter fun j => possible s (pos j) bad).card ≤ cap := by
  induction bits generalizing lo hi with
  | nil => exact leaf_sound pos bad cap lo hi s low high ok
  | cons i bits ih =>
    rcases Bool.or_eq_true_iff.mp ok with leafOK | next
    · exact leaf_sound pos bad cap lo hi s low high leafOK
    · obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp next
      rcases fits_split lo hi s i low high with a | b
      · exact ih _ _ left low a
      · exact ih _ _ right b high

theorem interval_limit {n : Nat} (pos : Fin n → Nat) (bad : Fin 12 → Nat) (cap : Nat)
    (bits : List Nat) (ok : verify pos bad cap bits 0 4095 = true) (s : Fin 4096) :
    (Finset.univ.filter fun j => possible s.val (pos j) bad).card ≤ cap := by
  apply verify_sound pos bad cap bits 0 4095 ok s.val
  · simp [MaskLe]
  · intro i yes
    have small : i < 12 := by
      by_contra! ge
      have power : 4096 ≤ 2^i := Nat.pow_le_pow_right (n := 2) (i := 12) (by decide) ge
      exact Bool.false_ne_true ((Nat.testBit_lt_two_pow (s.isLt.trans_le power)).symm.trans yes)
    change (2^12-1 : Nat).testBit i = true
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true small

end PetersenWeighted
#print axioms PetersenWeighted.interval_limit
