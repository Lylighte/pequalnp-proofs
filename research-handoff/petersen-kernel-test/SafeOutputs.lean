import PetersenBoundary

namespace SafeOutputs

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit


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

variable {n : ℕ}

abbrev promote (C : AndCountCircuit n) (S : Finset (Fin C.size)) : AndCountCircuit n :=
  { C with
    leftGates := fun i => C.leftGates i \ S
    rightGates := fun i => C.rightGates i \ S
    outGates := C.outGates ∪ S }

theorem properties (C : AndCountCircuit n) (S : Finset (Fin C.size)) (wf : C.WellFormed) :
    let D := promote C S
    D.size = C.size ∧ D.WellFormed ∧ (∀ v, PetersenEquivariance.bareCount D v = PetersenEquivariance.bareCount C v) ∧
    S ⊆ D.outGates ∧ ∀ i, Disjoint (D.leftGates i) S ∧ Disjoint (D.rightGates i) S := by
  refine ⟨rfl,?_,fun _ => rfl,Finset.subset_union_right,?_⟩
  · intro i
    exact ⟨fun j hj => (wf i).1 j (Finset.mem_sdiff.mp hj).1,
      fun j hj => (wf i).2 j (Finset.mem_sdiff.mp hj).1⟩
  · intro i
    exact ⟨Finset.disjoint_sdiff.symm, Finset.disjoint_sdiff.symm⟩

theorem decrease (C : AndCountCircuit n) (S : Finset (Fin C.size)) (U : Finset (Fin n)) (i : Fin C.size) :
    (promote C S).gateVal U i = true → C.gateVal U i = true := by
  have g (d : ℕ) (i : Fin C.size) : (promote C S).gateValFuel U d i = true →
      C.gateValFuel U d i = true := by
    induction d generalizing i with
    | zero => exact id
    | succ d ih =>
      have side (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
          sideTrue U B (F \ S) i ((promote C S).gateValFuel U d) = true →
          sideTrue U B F i (C.gateValFuel U d) = true := by
        simp only [sideTrue, decide_eq_true_eq, Finset.mem_sdiff]
        rintro (hv | ⟨j,⟨hf,_⟩,lt,ht⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨j,hf,lt,ih j ht⟩
      simp only [gateValFuel, Bool.and_eq_true]
      exact fun ht => ⟨side _ _ ht.1,side _ _ ht.2⟩
  exact g C.size i

theorem quietEq (C : AndCountCircuit n) (S : Finset (Fin C.size)) (U : Finset (Fin n))
    (quiet : ∀ j ∈ S, (promote C S).gateVal U j = false) (i : Fin C.size) :
    C.gateVal U i = (promote C S).gateVal U i := by
  induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
  | h i ih =>
    have side (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
        sideTrue U B F i (C.gateVal U) = sideTrue U B (F \ S) i ((promote C S).gateVal U) := by
      apply decide_eq_decide.mpr
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨j,hj,lt,ht⟩
        rw [ih j lt] at ht
        have keep : j ∉ S := fun hs => Bool.false_ne_true ((quiet j hs).symm.trans ht)
        exact ⟨j,Finset.mem_sdiff.mpr ⟨hj,keep⟩,lt,ht⟩
      · rintro ⟨j,hj,lt,ht⟩
        exact ⟨j,(Finset.mem_sdiff.mp hj).1,lt,(ih j lt).trans ht⟩
    rw [gateVal_unfold C U i,gateVal_unfold (promote C S) U i]
    exact congrArg₂ Bool.and (side _ _) (side _ _)

theorem evalIff (C : AndCountCircuit n) (S : Finset (Fin C.size)) (U : Finset (Fin n)) :
    (promote C S).eval U = true ↔ C.eval U = true ∨ ∃ j ∈ S, C.gateVal U j = true := by
  let D := promote C S
  constructor
  · intro ht
    rw [AndCountCircuit.eval,decide_eq_true_eq] at ht
    rcases ht with hv | ⟨j,hj,ht⟩
    · exact Or.inl (decide_eq_true (Or.inl hv))
    · have old := decrease C S U j ht
      rcases Finset.mem_union.mp hj with ho | hs
      · exact Or.inl (decide_eq_true (Or.inr ⟨j,ho,old⟩))
      · exact Or.inr ⟨j,hs,old⟩
  · intro old
    by_cases anyTrue : ∃ j ∈ S, D.gateVal U j = true
    · obtain ⟨j,hj,ht⟩ := anyTrue
      exact decide_eq_true (Or.inr ⟨j,Finset.mem_union_right _ hj,ht⟩)
    · have quiet (j) (hj : j ∈ S) : D.gateVal U j = false :=
        Bool.eq_false_iff.mpr (fun ht => anyTrue ⟨j,hj,ht⟩)
      have eq := quietEq C S U quiet
      rcases old with out | ⟨j,hj,ht⟩
      · rw [AndCountCircuit.eval,decide_eq_true_eq] at out
        rcases out with hv | ⟨j,hj,ht⟩
        · exact decide_eq_true (Or.inl hv)
        · exact decide_eq_true (Or.inr ⟨j,Finset.mem_union_left _ hj,(eq j).symm.trans ht⟩)
      · exact (anyTrue ⟨j,hj,(eq j).symm.trans ht⟩).elim

theorem preserveLabels (C : AndCountCircuit n) (S : Finset (Fin C.size))
    (neg pos : Finset (Fin n) → Prop)
    (safe : ∀ U, neg U → ∀ j ∈ S, C.gateVal U j = false)
    (hn : ∀ U, neg U → C.eval U = false) (hp : ∀ U, pos U → C.eval U = true) :
    let D := promote C S
    (∀ U, neg U → D.eval U = false) ∧ (∀ U, pos U → D.eval U = true) := by
  constructor
  · intro U hu
    apply Bool.eq_false_iff.mpr
    intro yes
    rcases (evalIff C S U).mp yes with out | ⟨j,hj,ht⟩
    · exact Bool.false_ne_true ((hn U hu).symm.trans out)
    · exact Bool.false_ne_true ((safe U hu j hj).symm.trans ht)
  · intro U hu
    exact (evalIff C S U).mpr (Or.inl (hp U hu))

def firstGates (C : AndCountCircuit n) (k : ℕ) := Finset.univ.filter (fun i : Fin C.size => i.val < k)

theorem normalizedFirst (C : AndCountCircuit 10) (k : ℕ) (wf : C.WellFormed)
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (safe : ∀ U ∈ PetersenBoundary.negatives, ∀ j : Fin C.size, j.val < k → C.gateVal U j = false) :
    let S := firstGates C k
    let D := promote C S
    D.size = C.size ∧ D.WellFormed ∧
    (∀ v, PetersenEquivariance.bareCount D v = PetersenEquivariance.bareCount C v) ∧
    PetersenEquivariance.Separates Petersen905.graph D ∧ S ⊆ D.outGates ∧
    (∀ i, Disjoint (D.leftGates i) S ∧ Disjoint (D.rightGates i) S) ∧
    ∀ i : Fin C.size, i.val < k → D.leftGates i = ∅ ∧ D.rightGates i = ∅ := by
  let S := firstGates C k
  obtain ⟨size,formed,counts,output,clean⟩ := properties C S wf
  obtain ⟨hn,hp⟩ := (PetersenBoundary.separationIff C).mp sep
  have labels := preserveLabels C S (· ∈ PetersenBoundary.negatives) (· ∈ PetersenBoundary.positives)
    (fun U hu j hj => safe U hu j (Finset.mem_filter.mp hj).2) hn hp
  refine ⟨size,formed,counts,(PetersenBoundary.separationIff _).mpr labels, output,clean,?_⟩
  intro i hi
  have empty (F : Finset (Fin C.size)) (earlier : ∀ j ∈ F, j < i) : F \ S = ∅ := by
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_trans (earlier j hj) hi⟩
  exact ⟨empty _ (wf i).1,empty _ (wf i).2⟩

-- An isolated safe gate is one of the star shapes, or has no true input.
theorem starShape (C : AndCountCircuit 10) (i : Fin C.size)
    (safe : ∀ U ∈ PetersenBoundary.negatives, C.gateVal U i = false) :
    C.leftVars i = ∅ ∨ C.rightVars i = ∅ ∨
    ∃ c : Fin 10, ∃ T : Finset (Fin 10), T.Nonempty ∧
      (∀ x ∈ T, Petersen905.graph.Adj c x) ∧
      ((C.leftVars i = {c} ∧ C.rightVars i = T) ∨ (C.rightVars i = {c} ∧ C.leftVars i = T)) := by
  classical
  have rect (a) (ha : a ∈ C.leftVars i) (b) (hb : b ∈ C.rightVars i) :
      Petersen905.related a b = true := by
    by_contra! no
    obtain ⟨r,har,hbr⟩ := Petersen905.jointlyPresent a b (Bool.eq_false_iff.mpr no)
    have ht : C.gateVal (Petersen905.rows r) i = true := by
      rw [gateVal_unfold,Bool.and_eq_true]
      exact ⟨decide_eq_true (Or.inl ⟨a,ha,har⟩),decide_eq_true (Or.inl ⟨b,hb,hbr⟩)⟩
    exact Bool.false_ne_true ((safe _ ((PetersenBoundary.negativeIff _).mpr
      (Petersen905.rowsGood r))).symm.trans ht)
  rcases (C.leftVars i).eq_empty_or_nonempty with emp | hL
  · exact Or.inl emp
  rcases (C.rightVars i).eq_empty_or_nonempty with emp | hR
  · exact Or.inr (Or.inl emp)
  obtain ⟨c,cover⟩ := Petersen905.starCenter _ _ rect
  have singleton {A : Finset (Fin 10)} (ne : A.Nonempty) (only : ∀ x ∈ A, x = c) : A = {c} := by
    obtain ⟨y,hy⟩ := ne
    have hc : c ∈ A := only y hy ▸ hy
    ext x
    rw [Finset.mem_singleton]
    exact ⟨only x,fun hx => hx ▸ hc⟩
  apply Or.inr
  apply Or.inr
  by_cases allLeft : ∀ x ∈ C.leftVars i, x = c
  · have eq := singleton hL allLeft
    have hc : c ∈ C.leftVars i := eq ▸ Finset.mem_singleton_self _
    exact ⟨c,_,hR,fun x hx => (Petersen905.adjacency _ _).mpr (rect c hc x hx),Or.inl ⟨eq,rfl⟩⟩
  · push Not at allLeft
    obtain ⟨x,hx,diff⟩ := allLeft
    have eq := singleton hR (fun y hy => (cover x hx y hy).resolve_left diff)
    have hc : c ∈ C.rightVars i := eq ▸ Finset.mem_singleton_self _
    exact ⟨c,_,hL,fun a ha => ((Petersen905.adjacency _ _).mpr (rect a ha c hc)).symm,Or.inr ⟨eq,rfl⟩⟩


-- In the normalized prefix the complete truth table is the product of its original bare sides.
theorem prefixFires (C : AndCountCircuit n) (k : ℕ) (wf : C.WellFormed)
    (i : Fin C.size) (earlier : i.val < k) (U : Finset (Fin n)) :
    (promote C (firstGates C k)).gateVal U i = true ↔
      (∃ a ∈ C.leftVars i, a ∈ U) ∧ (∃ b ∈ C.rightVars i, b ∈ U) := by
  let S := firstGates C k
  have empty (F : Finset (Fin C.size)) (before : ∀ j ∈ F, j < i) : F \ S = ∅ := by
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_trans (before j hj) earlier⟩
  have hl : (promote C S).leftGates i = ∅ := empty _ (wf i).1
  have hr : (promote C S).rightGates i = ∅ := empty _ (wf i).2
  change (promote C S).gateVal U i = true ↔ _
  rw [gateVal_unfold, Bool.and_eq_true]
  rw [hl,hr]
  simp [sideTrue]


end SafeOutputs

#print axioms SafeOutputs.evalIff
#print axioms SafeOutputs.normalizedFirst

#print axioms SafeOutputs.starShape

#print axioms SafeOutputs.prefixFires
