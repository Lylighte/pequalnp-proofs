import RemoveFirst

namespace PolarityReduction
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit FirstGateReduction

-- Gate unfolding lemmas from the upstream L_meta_635 proof.
private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

variable {n k : ℕ}

def Direction (positive : Bool) (old new : Prop) : Prop :=
  if positive then old → new else new → old

lemma andDirection (p : Bool) {a b c d : Prop}
    (h₁ : Direction p a c) (h₂ : Direction p b d) :
    Direction p (a ∧ b) (c ∧ d) := by
  cases p <;> simp only [Direction, Bool.false_eq_true, ite_false, ite_true] at * <;> tauto

lemma inlineSideDirection (p : Bool) (U S V : Finset (Fin n)) (G : Finset (Fin (k+1)))
    (P : Fin (k+1) → Prop) (Q : Fin k → Prop)
    (zero : Direction p (P 0) (∃ v ∈ S, v ∈ U)) (next : ∀ i, Direction p (P i.succ) (Q i)) :
    Direction p ((∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, P j)
      ((∃ v ∈ vars S V G, v ∈ U) ∨ ∃ j ∈ wires G, Q j) := by
  let alt : Fin (k+1) → Prop := Fin.cases (∃ v ∈ S, v ∈ U) Q
  have h := inlineSide U S V G alt Q Iff.rfl (fun _ => Iff.rfl)
  rw [← h]
  have pair (j : Fin (k+1)) : Direction p (P j) (alt j) := by
    cases j using Fin.cases with
    | zero => exact zero
    | succ i => exact next i
  cases p <;> simp only [Direction, Bool.false_eq_true, ite_false, ite_true] at pair ⊢ <;>
    rintro (hv | ⟨j, hj, hv⟩)
  · exact Or.inl hv
  · exact Or.inr ⟨j, hj, pair j hv⟩
  · exact Or.inl hv
  · exact Or.inr ⟨j, hj, pair j hv⟩

variable (L R : Fin (k+1) → Finset (Fin n)) (A B : Fin (k+1) → Finset (Fin (k+1)))
    (O : Finset (Fin n)) (F : Finset (Fin (k+1))) (S : Finset (Fin n))

theorem inlinedDirection (U : Finset (Fin n)) (p : Bool)
    (first : Direction p ((before L R A B O F).gateVal U 0 = true) (∃ v ∈ S, v ∈ U)) :
    Direction p ((before L R A B O F).eval U = true) ((after L R A B O F S).eval U = true) := by
  let C := before L R A B O F
  let D := after L R A B O F S
  have gates (i : Fin k) : Direction p (C.gateVal U i.succ = true) (D.gateVal U i = true) := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin k → Fin k → Prop)).induction) with
    | h i ih =>
      have side (V : Finset (Fin n)) (G : Finset (Fin (k+1))) :
          Direction p (sideTrue U V G i.succ (C.gateVal U) = true)
            (sideTrue U (vars S V G) (wires G) i (D.gateVal U) = true) := by
        simp only [sideTrue, decide_eq_true_eq]
        apply inlineSideDirection
        · simpa using first
        · intro j
          rw [Fin.succ_lt_succ_iff]
          by_cases hj : j < i
          · simpa [hj] using ih j hj
          · cases p <;> simp [hj, Direction]
      rw [gateVal_unfold C U i.succ, gateVal_unfold D U i, Bool.and_eq_true, Bool.and_eq_true]
      exact andDirection p (side (L i.succ) (A i.succ)) (side (R i.succ) (B i.succ))
  simp only [AndCountCircuit.eval, decide_eq_true_eq]
  exact inlineSideDirection p U S O F (fun i => C.gateVal U i = true)
    (fun i => D.gateVal U i = true) first gates

theorem removeFirstPreservingLabels {n : ℕ} (C : AndCountCircuit n) (k : ℕ)
    (hk : C.size = k+1) (wf : C.WellFormed) (S : Finset (Fin n))
    (negative positive : Finset (Fin n) → Prop)
    (negEval : ∀ U, negative U → C.eval U = false)
    (posEval : ∀ U, positive U → C.eval U = true)
    (noNew : ∀ U, negative U → (∃ v ∈ S, v ∈ U) → C.gateVal U ⟨0, by omega⟩ = true)
    (noLoss : ∀ U, positive U → C.gateVal U ⟨0, by omega⟩ = true → ∃ v ∈ S, v ∈ U) :
    ∃ D : AndCountCircuit n, D.size = k ∧ D.WellFormed ∧
      (∀ U, negative U → D.eval U = false) ∧ (∀ U, positive U → D.eval U = true) := by
  cases C with
  | mk size L A R B O F =>
    change size = k+1 at hk
    subst size
    refine ⟨after L R A B O F S, rfl, inlinedWF L R A B O F S wf, ?_, ?_⟩
    · intro U hu
      apply Bool.eq_false_iff.mpr
      intro ht
      exact Bool.false_ne_true ((negEval U hu).symm.trans
        (inlinedDirection L R A B O F S U false (noNew U hu) ht))
    · intro U hu
      exact inlinedDirection L R A B O F S U true (noLoss U hu) (posEval U hu)

end PolarityReduction

#print axioms PolarityReduction.removeFirstPreservingLabels
