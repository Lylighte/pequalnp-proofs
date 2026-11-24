import Mathlib
import PEqualNP.Defs.AndCountCircuit

namespace FirstGateReduction
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- Gate unfolding lemmas reproduced from the pinned upstream L_meta_635 proof.
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

def vars (S B : Finset (Fin n)) (F : Finset (Fin (k+1))) :=
  if 0 ∈ F then B ∪ S else B

def wires (F : Finset (Fin (k+1))) := Finset.univ.filter (fun i : Fin k => i.succ ∈ F)

lemma inlineSide (U S B : Finset (Fin n)) (F : Finset (Fin (k+1)))
    (P : Fin (k+1) → Prop) (Q : Fin k → Prop)
    (zero : P 0 ↔ ∃ v ∈ S, v ∈ U) (next : ∀ i, P i.succ ↔ Q i) :
    ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, P j) ↔
    ((∃ v ∈ vars S B F, v ∈ U) ∨ ∃ j ∈ wires F, Q j) := by
  simp only [Fin.exists_fin_succ, zero, next, wires, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases h : 0 ∈ F
  · simp [vars, h]
    grind
  · simp [vars, h]

variable (L R : Fin (k+1) → Finset (Fin n)) (A B : Fin (k+1) → Finset (Fin (k+1)))
    (O : Finset (Fin n)) (F : Finset (Fin (k+1))) (S : Finset (Fin n))

abbrev before : AndCountCircuit n := ⟨k+1, L, A, R, B, O, F⟩

abbrev after : AndCountCircuit n :=
  ⟨k, fun i => vars S (L i.succ) (A i.succ), fun i => wires (A i.succ),
      fun i => vars S (R i.succ) (B i.succ), fun i => wires (B i.succ),
      vars S O F, wires F⟩

theorem inlinedWF (wf : (before L R A B O F).WellFormed) :
    (after L R A B O F S).WellFormed := by
  intro i
  constructor
  · intro j hj
    have h : j.succ ∈ A i.succ := by simpa [wires, after] using hj
    exact Fin.succ_lt_succ_iff.mp ((wf i.succ).1 j.succ h)
  · intro j hj
    have h : j.succ ∈ B i.succ := by simpa [wires, after] using hj
    exact Fin.succ_lt_succ_iff.mp ((wf i.succ).2 j.succ h)

theorem inlinedEval (U : Finset (Fin n))
    (first : (before L R A B O F).gateVal U 0 = true ↔ ∃ v ∈ S, v ∈ U) :
    (before L R A B O F).eval U = (after L R A B O F S).eval U := by
  let C := before L R A B O F
  let D := after L R A B O F S
  have gates (i : Fin k) : C.gateVal U i.succ = D.gateVal U i := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin k → Fin k → Prop)).induction) with
    | h i ih =>
      refine (gateVal_unfold C U i.succ).trans (Eq.trans ?_ (gateVal_unfold D U i).symm)
      have side (V : Finset (Fin n)) (G : Finset (Fin (k+1))) :
          sideTrue U V G i.succ (C.gateVal U) =
            sideTrue U (vars S V G) (wires G) i (D.gateVal U) := by
        apply decide_eq_decide.mpr
        apply inlineSide
        · simpa using first
        · intro j
          rw [Fin.succ_lt_succ_iff]
          by_cases hj : j < i
          · rw [ih j hj]
          · simp [hj]
      exact congrArg₂ Bool.and (side (L i.succ) (A i.succ)) (side (R i.succ) (B i.succ))
  apply decide_eq_decide.mpr
  exact inlineSide U S O F (fun i => C.gateVal U i = true) (fun i => D.gateVal U i = true)
    first (fun i => by rw [gates])

theorem removeFirst {n : ℕ} (C : AndCountCircuit n) (k : ℕ) (hk : C.size = k+1)
    (wf : C.WellFormed) (S : Finset (Fin n)) (domain : Finset (Fin n) → Prop)
    (first : ∀ U, domain U → (C.gateVal U ⟨0, by omega⟩ = true ↔ ∃ v ∈ S, v ∈ U)) :
    ∃ D : AndCountCircuit n, D.size = k ∧ D.WellFormed ∧ ∀ U, domain U → C.eval U = D.eval U := by
  cases C with
  | mk size L A R B O F =>
    change size = k+1 at hk
    subst size
    exact ⟨after L R A B O F S, rfl, inlinedWF L R A B O F S wf,
      fun U hU => inlinedEval L R A B O F S U (first U hU)⟩

end FirstGateReduction

#print axioms FirstGateReduction.removeFirst
