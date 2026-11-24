import DiagonalStars

namespace PetersenDiagonalStars

open PetersenDiagonalNumeric PetersenFootprintCenters
open PetersenMixedStar (V Input)
open PetersenTailCnf (hit bits)
open PetersenBoundary (decode positiveMasks negativeMasks)
open PetersenOrbitCover (encode decode_encode fromBits_bit)
open Petersen905 (related)

private theorem given_rows : (∀ i, pval i ∈ positiveMasks) ∧ (∀ i, nrow i ∈ negativeMasks) := by decide +kernel
private theorem stars : ∀ (i : Fin 70) (v : V), (star i).val.testBit v.val = true ↔
    v ∈ decode (pval i) ∧ ∃ w ∈ decode (pval i), related v w = true := by decide +kernel
private theorem adjacency : ∀ v w : V, (nb v).testBit w.val = related v w := by decide +kernel

private theorem encoded (S : Input) (v : V) : (encode S).val.testBit v.val = decide (v ∈ S) := fromBits_bit _ _
private theorem hit_rows (S : Input) (p : M) : raw (encode S) p = true ↔ hit S (decode p) := by
  rw [raw_iff]
  change (∃ v ∈ decode (encode S), v ∈ decode p) ↔ _
  rw [decode_encode]; rfl

private theorem hit_star (S : Input) (i : Fin 70) : raw (encode S) (star i) = true ↔ starHit S (decode (pval i)) := by
  rw [hit_rows]
  constructor
  · rintro ⟨v,vs,hit⟩
    exact ⟨v,vs,(stars i v).mp (Finset.mem_filter.mp hit).2⟩
  · rintro ⟨v,vs,h⟩
    exact ⟨v,vs,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(stars i v).mpr h⟩⟩

private theorem encoded_subset (S T : Input) (h : S ⊆ T) : (encode S).val &&& (encode T).val = (encode S).val := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  by_cases top : i < 10
  · let v : V := ⟨i,top⟩
    have s := encoded S v; have t := encoded T v
    change (encode S).val.testBit i = _ at s
    change (encode T).val.testBit i = _ at t
    rw [s,t]
    by_cases mem : v ∈ S
    · simp [mem,h mem]
    · simp [mem]
  · have high : 1024 ≤ 2^i := Nat.pow_le_pow_right (n:=2) (i:=10) (by decide) (by omega)
    simp [Nat.testBit_lt_two_pow ((encode S).isLt.trans_le high)]

theorem sketch_impossible (s : Sketch) : False := by
  have pop : population (encode s.T) = s.T.card := congrArg Finset.card (decode_encode s.T)
  apply Checked.impossible ⟨encode s.T,encode s.J,encode s.O,encode s.A,encode s.B,
    pop ▸ s.small,?_,?_,?_⟩
  · intro i no
    have m : decode (pval i) ∈ PetersenBoundary.positives :=
      Finset.mem_image_of_mem _ (by simpa using given_rows.1 i)
    have h := s.pos _ m (fun yes => Bool.false_ne_true (no.symm.trans ((hit_star s.T i).mpr yes)))
    exact ⟨(hit_rows _ _).mpr h.1,(hit_rows _ _).mpr h.2.1,(hit_rows _ _).mpr h.2.2⟩
  · intro i h
    have m : decode (nrow i) ∈ PetersenBoundary.negatives :=
      Finset.mem_image_of_mem _ (by simpa using given_rows.2 i)
    exact s.neg _ m ⟨(hit_rows _ _).mp h.1,(hit_rows _ _).mp h.2.1,(hit_rows _ _).mp h.2.2⟩
  · intro four
    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr (encoded_subset _ _ s.subset),?_⟩,?_⟩
    · apply List.all_eq_true.mpr
      intro v _
      by_cases vo : v ∈ s.O
      · obtain ⟨c,ct,cj,adj⟩ := s.supports (pop ▸ four) v vo
        apply Bool.or_eq_true_iff.mpr
        right; apply List.any_eq_true.mpr
        refine ⟨c,List.mem_finRange _,?_⟩
        simp only [encoded,ct,cj,decide_true,decide_false,Bool.not_false,Bool.true_and,adjacency]
        rcases adj with eq | eq
        · simp [eq]
        · simp [eq]
      · simp [encoded,vo]
    · apply List.all_eq_true.mpr
      intro i _
      have m : decode (pval i) ∈ PetersenBoundary.positives :=
        Finset.mem_image_of_mem _ (by simpa using given_rows.1 i)
      exact Bool.or_eq_true_iff.mpr ((s.plain _ m).imp (hit_rows _ _).mpr (hit_star _ _).mpr)

end PetersenDiagonalStars
