import SafeOutputs
import GateReindex

namespace PetersenNormalized

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem splitOrder {k : ℕ} (A : Finset (Fin k)) :
    ∃ e : Equiv.Perm (Fin k),
      (∀ i, (e i).val < A.card ↔ i ∈ A) ∧
      (∀ i ∈ A, ∀ j ∈ A, i < j → e i < e j) := by
  classical
  let a := (A.orderIsoOfFin rfl).symm
  let b := (Aᶜ.orderIsoOfFin rfl).symm
  have dims : Aᶜ.card + A.card = k := by simp
  let f (i : Fin k) : Fin k :=
    if h : i ∈ A then
      ⟨(a ⟨i,h⟩).val, by have := (a ⟨i,h⟩).isLt; omega⟩
    else
      ⟨A.card + (b ⟨i,Finset.mem_compl.mpr h⟩).val, by
        have := (b ⟨i,Finset.mem_compl.mpr h⟩).isLt
        omega⟩
  have low (i : Fin k) (hi : i ∈ A) : (f i).val = (a ⟨i,hi⟩).val := by simp [f,hi]
  have high (i : Fin k) (hi : i ∉ A) :
      (f i).val = A.card + (b ⟨i,Finset.mem_compl.mpr hi⟩).val := by simp [f,hi]
  have below (i : Fin k) : (f i).val < A.card ↔ i ∈ A := by
    by_cases hi : i ∈ A
    · exact iff_of_true ((low i hi) ▸ (a ⟨i,hi⟩).isLt) hi
    · rw [high i hi]
      simp [hi]
  have inj : Function.Injective f := by
    intro i j eq
    have he := congrArg Fin.val eq
    by_cases hi : i ∈ A
    · have hj := (below j).mp (eq ▸ (below i).mpr hi)
      rw [low i hi,low j hj] at he
      exact congrArg Subtype.val (a.injective (Fin.ext he))
    · have hj : j ∉ A := fun h => hi ((below i).mp (eq.symm ▸ (below j).mpr h))
      rw [high i hi,high j hj] at he
      exact congrArg Subtype.val (b.injective (Fin.ext (Nat.add_left_cancel he)))
  refine ⟨Equiv.ofBijective f ⟨inj,Finite.injective_iff_surjective.mp inj⟩,below,?_⟩
  intro i hi j hj lt
  change (f i).val < (f j).val
  rw [low i hi,low j hj]
  exact a.strictMono (show (⟨i,hi⟩ : A) < ⟨j,hj⟩ from lt)

open PetersenBoundary (negatives positives)
open PetersenEquivariance (bareCount Separates)
open GateReindex (Wire)

theorem normalForm (C : AndCountCircuit 10) (wf : C.WellFormed) (sep : Separates Petersen905.graph C) :
    ∃ (E : AndCountCircuit 10) (u : ℕ),
      E.size = C.size ∧ E.WellFormed ∧ Separates Petersen905.graph E ∧
      (∀ v, bareCount E v = bareCount C v) ∧
      (∀ i : Fin E.size, i ∈ E.outGates ↔ u ≤ i.val) ∧
      (∀ i : Fin E.size, (∀ U ∈ negatives, E.gateVal U i = false) ↔ u ≤ i.val) ∧
      (∀ i j : Fin E.size, Wire E i j → j.val < u) ∧ E.outVars = ∅ ∧ u < E.size := by
  classical
  let S : Finset (Fin C.size) := Finset.univ.filter (fun i => ∀ U ∈ negatives, C.gateVal U i = false)
  let A := Sᶜ
  let D := SafeOutputs.promote C S
  obtain ⟨_,wfD,cntD,_,_⟩ := SafeOutputs.properties C S wf
  obtain ⟨hn,hp⟩ := (PetersenBoundary.separationIff C).mp sep
  have hs (U) (hu : U ∈ negatives) (j) (hj : j ∈ S) : C.gateVal U j = false :=
    (Finset.mem_filter.mp hj).2 U hu
  have eqN (U) (hu : U ∈ negatives) (i : Fin C.size) : C.gateVal U i = D.gateVal U i :=
    SafeOutputs.quietEq C S U (fun j hj => Bool.eq_false_iff.mpr (fun t =>
      Bool.false_ne_true ((hs U hu j hj).symm.trans (SafeOutputs.decrease C S U j t)))) i
  have inSafe : C.outGates ⊆ S := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun U hu => Bool.eq_false_iff.mpr (fun ht => ?_)⟩
    have yes : C.eval U = true := decide_eq_true (Or.inr ⟨i,hi,ht⟩)
    exact Bool.false_ne_true ((hn U hu).symm.trans yes)
  have oD : D.outGates = S := Finset.union_eq_right.mpr inSafe
  obtain ⟨e,below,inc⟩ := splitOrder A
  have live (i j : Fin C.size) (w : Wire D i j) : j ∈ A := by
    rcases w with h | h
    · exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp h).2
    · exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp h).2
  have top : GateReindex.OrderOnWires D e := by
    intro i j w
    by_cases hi : i ∈ A
    · exact inc j (live i j w) i hi (w.elim ((wfD i).1 j) ((wfD i).2 j))
    · have hj := (below j).mpr (live i j w)
      have hge := mt (below i).mp hi
      change (e j).val < (e i).val
      omega
  let E := GateReindex.reindex D e
  have value (U) (i : Fin C.size) : E.gateVal U (e i) = D.gateVal U i :=
    GateReindex.fuelEq D e wfD top U D.size i
  have endI (i : Fin C.size) : i ∈ S ↔ A.card ≤ (e i).val := by
    rw [← Nat.not_lt,below]
    simp [A]
  have labels := SafeOutputs.preserveLabels C S (· ∈ negatives) (· ∈ positives) hs hn hp
  have sepE : Separates Petersen905.graph E := by
    apply (PetersenBoundary.separationIff E).mpr
    exact ⟨fun U hu => (GateReindex.evalEq D e wfD top U).trans (labels.1 U hu),
      fun U hu => (GateReindex.evalEq D e wfD top U).trans (labels.2 U hu)⟩
  have outputs (i : Fin E.size) : i ∈ E.outGates ↔ A.card ≤ i.val := by
    obtain ⟨j,rfl⟩ := e.surjective i
    change e j ∈ D.outGates.map e.toEmbedding ↔ _
    simpa [oD] using (endI j)
  have noRaw : C.outVars = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    let U := Petersen905.rows (Petersen905.through v 0)
    have hu : U ∈ negatives := (PetersenBoundary.negativeIff _).mpr (Petersen905.rowsGood _)
    have yes : C.eval U = true := decide_eq_true (Or.inl ⟨v,hv,Petersen905.rowContains v 0⟩)
    exact Bool.false_ne_true ((hn U hu).symm.trans yes)
  refine ⟨E,A.card,rfl,GateReindex.reindexWF D e top,sepE,
    fun v => (GateReindex.bareEq D e v).trans (cntD v),outputs,?_,?_,noRaw,?_⟩
  · intro i
    obtain ⟨j,rfl⟩ := e.surjective i
    rw [← endI]
    change (∀ U ∈ negatives, E.gateVal U (e j) = false) ↔ j ∈ S
    constructor
    · exact fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun U hu =>
        (eqN U hu j).trans ((value U j).symm.trans (h U hu))⟩
    · exact fun h U hu => (value U j).trans ((eqN U hu j).symm.trans (hs U hu j h))
  · intro i j w
    obtain ⟨a,rfl⟩ := e.surjective i
    obtain ⟨b,rfl⟩ := e.surjective j
    apply (below b).mpr
    apply live a b
    simpa [E,Wire,GateReindex.reindex,Finset.mem_map_equiv] using w
  · have nonempty : positives.Nonempty := Finset.card_pos.mp (by rw [PetersenBoundary.sizes.2.1]; decide)
    obtain ⟨U,hu⟩ := nonempty
    have he := ((PetersenBoundary.separationIff E).mp sepE).2 U hu
    rw [AndCountCircuit.eval,decide_eq_true_eq] at he
    rcases he with ⟨v,hv,_⟩ | ⟨i,hi,_⟩
    · change v ∈ C.outVars at hv
      simp [noRaw] at hv
    · exact lt_of_le_of_lt ((outputs i).mp hi) i.isLt

end PetersenNormalized

#print axioms PetersenNormalized.splitOrder
#print axioms PetersenNormalized.normalForm
