import SuffixProjection

namespace PetersenSuffix

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit PetersenTailCnf
variable {n : Nat}

def ReadsBefore (C : AndCountCircuit n) (u : Nat) : Prop :=
  ∀ i j, j ∈ C.leftGates i ∨ j ∈ C.rightGates i → j.val < u

theorem suffix_reads (C : AndCountCircuit n) (k a : Nat) (hk : k ≤ C.size)
    (h : ReadsBefore C (k+a)) : ReadsBefore (suffix C k hk) a := by
  intro i j hj
  have mem : tail C k j ∈ C.leftGates (tail C k i) ∨
      tail C k j ∈ C.rightGates (tail C k i) := by simpa [suffix,later] using hj
  have high := h _ _ mem
  change k+j.val < k+a at high
  omega

private theorem plain_side (C : AndCountCircuit n) (i : Fin C.size) (U B : Finset (Fin n))
    (F : Finset (Fin C.size)) (none : ∀ j ∈ F, ¬ j < i) :
    sideTrue U B F i (C.gateVal U) = true ↔ hit B U := by
  simp only [sideTrue,decide_eq_true_eq]
  constructor
  · rintro (a | ⟨j,hj,hlt,_⟩)
    · exact a
    · exact (none j hj hlt).elim
  · exact Or.inl

private theorem raw_gate (C : AndCountCircuit n) (i : Fin C.size) (U : Finset (Fin n))
    (none : ∀ j, j ∈ C.leftGates i ∨ j ∈ C.rightGates i → ¬j < i) :
    C.gateVal U i = true ↔ hit (C.leftVars i) U ∧ hit (C.rightVars i) U := by
  rw [PetersenCnfBridge.gate_equation, Bool.and_eq_true]
  exact and_congr (plain_side C i U _ _ (fun j hj => none j (Or.inl hj)))
    (plain_side C i U _ _ (fun j hj => none j (Or.inr hj)))

private def activeRight (C : AndCountCircuit n) (i : Fin C.size) :=
  if i ∈ C.outGates then C.rightVars i else ∅

theorem two_cnf (C : AndCountCircuit n) (sz : C.size = 2) (w : ReadsBefore C 0) :
    ∃ f : List (Finset (Fin n)), f.length = 4 ∧ ∀ U, C.eval U = true ↔ sat f U := by
  let a : Fin C.size := ⟨0,by omega⟩
  let b : Fin C.size := ⟨1,by omega⟩
  have gate (i : Fin C.size) (U : Finset (Fin n)) :
      i ∈ C.outGates ∧ C.gateVal U i = true ↔ hit (C.leftVars i) U ∧ hit (activeRight C i) U := by
    rw [raw_gate C i U (fun j m => (Nat.not_lt_zero _ (w _ _ m)).elim)]
    by_cases o : i ∈ C.outGates <;> simp [activeRight,o]
  refine ⟨four C.outVars (C.leftVars a) (activeRight C a) (C.leftVars b) (activeRight C b),rfl,?_⟩
  intro U
  rw [four_eval,AndCountCircuit.eval,decide_eq_true_eq,← gate a U,← gate b U]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i,hs,hv⟩
    have select : i=a ∨ i=b := by
      by_cases eq : i.val=0
      · exact Or.inl (Fin.ext eq)
      · exact Or.inr (Fin.ext (by change i.val=1; omega))
    rcases select with rfl | rfl
    · exact Or.inl ⟨hs,hv⟩
    · exact Or.inr ⟨hs,hv⟩
  · rintro (⟨m,v⟩ | ⟨m,v⟩)
    · exact ⟨a,m,v⟩
    · exact ⟨b,m,v⟩

private def terminalAt (C : AndCountCircuit n) (h i : Fin C.size) : Terminal (Fin n) where
  left := C.leftVars i
  right := C.rightVars i
  useLeft := decide (h ∈ C.leftGates i)
  useRight := decide (h ∈ C.rightGates i)
  enabled := decide (i ∈ C.outGates)

private theorem helper_side (C : AndCountCircuit n) (h i : Fin C.size) (U B : Finset (Fin n))
    (F : Finset (Fin C.size)) (lt : h < i) (only : ∀ j ∈ F, j < i → j=h) :
    sideTrue U B F i (C.gateVal U) = true ↔
      hit B U ∨ h ∈ F ∧ C.gateVal U h = true := by
  simp only [sideTrue,decide_eq_true_eq]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j,hj,old,on⟩
    obtain rfl := only j hj old
    exact ⟨hj,on⟩
  · rintro ⟨m,on⟩
    exact ⟨h,m,lt,on⟩

private theorem helper_terminal (C : AndCountCircuit n) (h i : Fin C.size)
    (zero : h.val=0) (lt : h < i) (w : ReadsBefore C 1) (U : Finset (Fin n)) :
    i ∈ C.outGates ∧ C.gateVal U i = true ↔
      fires (terminalAt C h i) U (C.gateVal U h = true) := by
  rw [PetersenCnfBridge.gate_equation C U i,Bool.and_eq_true]
  have only (j) (m : j ∈ C.leftGates i ∨ j ∈ C.rightGates i) : j=h := by
    have old := w _ _ m
    apply Fin.ext
    omega
  rw [helper_side C h i U _ _ lt (fun j m _ => only j (Or.inl m)),
    helper_side C h i U _ _ lt (fun j m _ => only j (Or.inr m))]
  simp [fires,terminalAt]

theorem three_cnf (C : AndCountCircuit n) (sz : C.size = 3) (w : ReadsBefore C 1)
    (witness : ∃ U, C.gateVal U ⟨0,by omega⟩ = true ∧ C.eval U = false) :
    ∃ f : List (Finset (Fin n)), f.length = 7 ∧ ∀ U, C.eval U = true ↔ sat f U := by
  let h : Fin C.size := ⟨0,by omega⟩
  let a : Fin C.size := ⟨1,by omega⟩
  let b : Fin C.size := ⟨2,by omega⟩
  let t := terminalAt C h a
  let u := terminalAt C h b
  obtain ⟨X,on,off⟩ := witness
  have hidden : h ∉ C.outGates := by
    intro m
    have yes : C.eval X = true := decide_eq_true (Or.inr ⟨h,m,on⟩)
    exact Bool.false_ne_true (off.symm.trans yes)
  have hg (U) : C.gateVal U h = true ↔ hit (C.leftVars h) U ∧ hit (C.rightVars h) U :=
    raw_gate C h U (fun j _ => by change ¬j.val < 0; omega)
  have out (U) : C.eval U = true ↔
      helperOutput C.outVars (C.leftVars h) (C.rightVars h) t u U := by
    rw [AndCountCircuit.eval,decide_eq_true_eq]
    dsimp only [helperOutput,t,u]
    rw [← hg U, ← helper_terminal C h a rfl (by change (0:Nat)<1; decide) w U,
      ← helper_terminal C h b rfl (by change (0:Nat)<2; decide) w U]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨i,m,yes⟩
      have nozero : i.val ≠ 0 := fun e => hidden ((Fin.ext (b := h) e) ▸ m)
      by_cases ea : i=a
      · exact Or.inl (ea ▸ And.intro m yes)
      · have eb : i=b := Fin.ext (by change i.val=2; have ne : i.val≠1 := fun e => ea (Fin.ext e); omega)
        exact Or.inr (eb ▸ And.intro m yes)
    · rintro (⟨m,v⟩ | ⟨m,v⟩)
      · exact ⟨a,m,v⟩
      · exact ⟨b,m,v⟩
  have offX : ¬helperOutput C.outVars (C.leftVars h) (C.rightVars h) t u X :=
    fun yes => Bool.false_ne_true (off.symm.trans ((out X).mpr yes))
  have oneT := singleSide_of_unsafe t X ((hg X).mp on) (fun y => offX (Or.inr (Or.inl y)))
  have oneU := singleSide_of_unsafe u X ((hg X).mp on) (fun y => offX (Or.inr (Or.inr y)))
  exact ⟨seven C.outVars (C.leftVars h) (C.rightVars h) t u,rfl,
    fun U => (out U).trans (seven_eval _ _ _ _ _ _ oneT oneU).symm⟩

theorem two_projected (C : AndCountCircuit n) (k : Nat) (sz : C.size=k+2)
    (cap : Cap C) (o : C.outVars ⊆ available C k) (w : ReadsBefore C k) :
    ∃ f : List (Finset (Fin (n+k))), f.length=4 ∧
      ∀ U, C.eval U = true ↔ sat f (row C k (by omega) U) := by
  have wk : ReadsBefore (suffix C k (by omega)) 0 := suffix_reads C k 0 (by omega) w
  obtain ⟨f,hf,ev⟩ := two_cnf (suffix C k (by omega)) (by change C.size-k=2; omega) wk
  exact ⟨f,hf,fun U => by rw [← eval_agrees C k (by omega) cap o U]; exact ev _⟩

theorem three_projected (C : AndCountCircuit n) (k : Nat) (sz : C.size=k+3)
    (cap : Cap C) (o : C.outVars ⊆ available C k) (w : ReadsBefore C (k+1))
    (witness : ∃ U, C.gateVal U ⟨k,by omega⟩ = true ∧ C.eval U = false) :
    ∃ f : List (Finset (Fin (n+k))), f.length=7 ∧
      ∀ U, C.eval U = true ↔ sat f (row C k (by omega) U) := by
  let D := suffix C k (by omega)
  have szD : D.size=3 := by change C.size-k=3; omega
  have wk : ReadsBefore D 1 := suffix_reads C k 1 (by omega) w
  obtain ⟨X,on,off⟩ := witness
  have hd : ∃ Z, D.gateVal Z ⟨0,by omega⟩ = true ∧ D.eval Z = false := by
    refine ⟨row C k (by omega) X,?_,(eval_agrees C k (by omega) cap o X).trans off⟩
    have e := gate_agrees C k (by omega) cap X (⟨0,by omega⟩ : Fin (C.size-k))
    exact e.trans on
  obtain ⟨f,hf,ev⟩ := three_cnf D szD wk hd
  exact ⟨f,hf,fun U => by rw [← eval_agrees C k (by omega) cap o U]; exact ev _⟩

end PetersenSuffix
