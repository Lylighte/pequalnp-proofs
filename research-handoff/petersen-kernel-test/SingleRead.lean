import PetersenBoundary

namespace SingleRead

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

lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
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

def OnlyAt (C : AndCountCircuit n) (x : Fin n) (g : Fin C.size) : Prop :=
  ∀ i, i ≠ g → x ∉ C.leftVars i ∧ x ∉ C.rightVars i

def hit (C : AndCountCircuit n) (g : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size))
    (U : Finset (Fin n)) := sideTrue U B F g (C.gateVal U) = true

lemma sideInsert (C : AndCountCircuit n) (U : Finset (Fin n)) (x : Fin n)
    (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size))
    (earlier : ∀ j < i, C.gateVal (insert x U) j = C.gateVal U j) :
    hit C i B F (insert x U) ↔ hit C i B F U ∨ x ∈ B := by
  simp only [hit,sideTrue,decide_eq_true_eq]
  constructor
  · rintro (⟨v,hv,h⟩ | ⟨j,hj,lt,ht⟩)
    · rcases Finset.mem_insert.mp h with rfl | hu
      · exact Or.inr hv
      · exact Or.inl (Or.inl ⟨v,hv,hu⟩)
    · exact Or.inl (Or.inr ⟨j,hj,lt,(earlier j lt).symm.trans ht⟩)
  · rintro ((⟨v,hv,hu⟩ | ⟨j,hj,lt,ht⟩) | hx)
    · exact Or.inl ⟨v,hv,Finset.mem_insert_of_mem hu⟩
    · exact Or.inr ⟨j,hj,lt,(earlier j lt).trans ht⟩
    · exact Or.inl ⟨x,hx,Finset.mem_insert_self ..⟩

lemma controlGate (C : AndCountCircuit n) (U : Finset (Fin n)) (x : Fin n) (g : Fin C.size)
    (only : OnlyAt C x g) (i : Fin C.size)
    (same : g ≤ i → C.gateVal (insert x U) g = C.gateVal U g) :
    C.gateVal (insert x U) i = C.gateVal U i := by
  induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
  | h i ih =>
    by_cases eq : i = g
    · subst i
      exact same (le_refl g)
    have prior (j) (lt : j < i) := ih j lt (fun le => same (le.trans lt.le))
    have neither := only i eq
    apply Bool.eq_iff_iff.mpr
    rw [gateVal_unfold C (insert x U),gateVal_unfold C U,Bool.and_eq_true,Bool.and_eq_true]
    change (hit C i _ _ (insert x U) ∧ hit C i _ _ (insert x U)) ↔ (hit C i _ _ U ∧ hit C i _ _ U)
    rw [sideInsert C U x i _ _ prior,sideInsert C U x i _ _ prior]
    simp [neither.1,neither.2]

lemma mustSwitch (C : AndCountCircuit n) (g : Fin C.size) (x : Fin n) (U : Finset (Fin n))
    (only : OnlyAt C x g) (out : x ∉ C.outVars)
    (off : C.eval U = false) (on : C.eval (insert x U) = true) :
    let a := hit C g (C.leftVars g) (C.leftGates g) U
    let b := hit C g (C.rightVars g) (C.rightGates g) U
    ¬ (a ∧ b) ∧ (a ∨ x ∈ C.leftVars g) ∧ (b ∨ x ∈ C.rightVars g) := by
  have different : C.gateVal (insert x U) g ≠ C.gateVal U g := by
    intro eq
    have all (j) := controlGate C U x g only j (fun _ => eq)
    rw [AndCountCircuit.eval, decide_eq_true_eq] at on
    have yes : C.eval U = true := by
      apply decide_eq_true
      rcases on with ⟨v,hv,hu⟩ | ⟨j,hj,ht⟩
      · rcases Finset.mem_insert.mp hu with rfl | hu
        · exact (out hv).elim
        · exact Or.inl ⟨v,hv,hu⟩
      · exact Or.inr ⟨j,hj,(all j).symm.trans ht⟩
    exact Bool.false_ne_true (off.symm.trans yes)
  have prior (j) (lt : j < g) :=
    controlGate C U x g only j (fun le => ((not_le_of_gt lt) le).elim)
  have old : C.gateVal U g = true ↔
      hit C g (C.leftVars g) (C.leftGates g) U ∧ hit C g (C.rightVars g) (C.rightGates g) U := by
    rw [gateVal_unfold,Bool.and_eq_true]
    exact Iff.rfl
  have new : C.gateVal (insert x U) g = true ↔
      (hit C g (C.leftVars g) (C.leftGates g) U ∨ x ∈ C.leftVars g) ∧
      (hit C g (C.rightVars g) (C.rightGates g) U ∨ x ∈ C.rightVars g) := by
    rw [gateVal_unfold,Bool.and_eq_true]
    exact and_congr (sideInsert C U x g _ _ prior) (sideInsert C U x g _ _ prior)
  have no : C.gateVal U g ≠ true := by
    intro yes
    have both := old.mp yes
    exact different ((new.mpr ⟨Or.inl both.1,Or.inl both.2⟩).trans yes.symm)
  refine ⟨fun h => no (old.mpr h),new.mp ?_⟩
  cases he : C.gateVal (insert x U) g with
  | true => rfl
  | false => exact (different (he.trans (Bool.eq_false_iff.mpr no).symm)).elim

def Dominates (C : AndCountCircuit n) (g : Fin C.size) (x y : Fin n) : Prop :=
  (x ∈ C.leftVars g → y ∈ C.leftVars g) ∧ (x ∈ C.rightVars g → y ∈ C.rightVars g)

lemma comparable (C : AndCountCircuit n) (g : Fin C.size) (x y : Fin n) (U : Finset (Fin n))
    (sx : OnlyAt C x g) (sy : OnlyAt C y g) (ox : x ∉ C.outVars) (oy : y ∉ C.outVars)
    (off : C.eval U = false) (onx : C.eval (insert x U) = true) (ony : C.eval (insert y U) = true) :
    Dominates C g x y ∨ Dominates C g y x := by
  obtain ⟨off,ax,bx⟩ := mustSwitch C g x U sx ox off onx
  obtain ⟨_,ay,by'⟩ := mustSwitch C g y U sy oy ‹C.eval U = false› ony
  unfold Dominates
  tauto

lemma comparableConflict (C : AndCountCircuit n) (g : Fin C.size) (x y : Fin n) (U : Finset (Fin n))
    (sx : OnlyAt C x g) (ox : x ∉ C.outVars) (off : C.eval U = false)
    (on : C.eval (insert x U) = true) (hy : y ∈ U) (dom : Dominates C g x y) : False := by
  obtain ⟨no,hl,hr⟩ := mustSwitch C g x U sx ox off on
  apply no
  exact ⟨hl.elim id (fun hx => decide_eq_true (Or.inl ⟨y,dom.1 hx,hy⟩)),
    hr.elim id (fun hx => decide_eq_true (Or.inl ⟨y,dom.2 hx,hy⟩))⟩

-- The deletion index is arbitrary; all single-row deletions are included.
set_option maxHeartbeats 3000000 in
theorem rowWitnesses : ∀ (drop : Fin 15) (x y : Fin 10), x ≠ y →
    (∃ r : Fin 15, r ≠ drop ∧ x ∈ Petersen905.rows r ∧ y ∉ Petersen905.rows r) ∧
    (∃ r : Fin 15, r ≠ drop ∧ x ∉ Petersen905.rows r ∧ y ∉ Petersen905.rows r) := by
  decide +kernel

def Fourteen (C : AndCountCircuit 10) (drop : Fin 15) : Prop :=
  ∀ r : Fin 15, r ≠ drop → C.eval (Petersen905.rows r) = false ∧
    ∀ x ∉ Petersen905.rows r, C.eval (insert x (Petersen905.rows r)) = true

theorem noBareOutput (C : AndCountCircuit 10) (drop : Fin 15) (sep : Fourteen C drop) (x : Fin 10) :
    x ∉ C.outVars := by
  obtain ⟨y,hy⟩ := exists_ne x
  obtain ⟨r,hr,hx,_⟩ := (rowWitnesses drop x y hy.symm).1
  intro hout
  have ht : C.eval (Petersen905.rows r) = true := decide_eq_true (Or.inl ⟨x,hout,hx⟩)
  exact Bool.false_ne_true ((sep r hr).1.symm.trans ht)

theorem cannotShare (C : AndCountCircuit 10) (drop : Fin 15) (sep : Fourteen C drop)
    (x y : Fin 10) (g : Fin C.size) (sx : OnlyAt C x g) (sy : OnlyAt C y g) : x = y := by
  by_contra hne
  have ox := noBareOutput C drop sep x
  have oy := noBareOutput C drop sep y
  obtain ⟨r,hr,hx,hy⟩ := (rowWitnesses drop x y hne).2
  have zero := (sep r hr).1
  have dom := comparable C g x y _ sx sy ox oy zero ((sep r hr).2 x hx) ((sep r hr).2 y hy)
  rcases dom with d | d
  · obtain ⟨r,hr,hy,hx⟩ := (rowWitnesses drop y x (Ne.symm hne)).1
    exact comparableConflict C g x y _ sx ox (sep r hr).1 ((sep r hr).2 x hx) hy d
  · obtain ⟨r,hr,hx,hy⟩ := (rowWitnesses drop x y hne).1
    exact comparableConflict C g y x _ sy oy (sep r hr).1 ((sep r hr).2 y hy) hx d

def reads (C : AndCountCircuit n) (x : Fin n) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => x ∈ C.leftVars i ∨ x ∈ C.rightVars i)

theorem singleCount (C : AndCountCircuit 10) (drop : Fin 15) (sep : Fourteen C drop) (T : Finset (Fin 10))
    (atMostOne : ∀ x ∈ T, (reads C x).card ≤ 1) : T.card ≤ C.size := by
  classical
  have nonzero : 0 < C.size := by
    obtain ⟨r,hr,hx,_⟩ := (rowWitnesses drop 0 1 (by decide)).2
    have ht := (sep r hr).2 0 hx
    rw [AndCountCircuit.eval,decide_eq_true_eq] at ht
    rcases ht with ⟨x,hout,_⟩ | ⟨j,_,_⟩
    · exact (noBareOutput C drop sep x hout).elim
    · exact Nat.zero_lt_of_lt j.isLt
  have existsPlace (x : ↥T) : ∃ g : Fin C.size, ∀ i ∈ reads C x.val, i = g := by
    by_cases ne : (reads C x.val).Nonempty
    · obtain ⟨g,hg⟩ := ne
      exact ⟨g,fun i hi => Finset.card_le_one.mp (atMostOne x.val x.property) i hi g hg⟩
    · exact ⟨⟨0,nonzero⟩,fun i hi => (ne ⟨i,hi⟩).elim⟩
  choose place unique using existsPlace
  have only (x : ↥T) : OnlyAt C x.val (place x) := by
    intro i notEqual
    have neither : ¬ (x.val ∈ C.leftVars i ∨ x.val ∈ C.rightVars i) := fun h =>
      notEqual (unique x i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩))
    exact not_or.mp neither
  have inj : Function.Injective place := by
    intro x y eq
    exact Subtype.ext (cannotShare C drop sep x.val y.val (place x) (only x) (eq ▸ only y))
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective _ inj


end SingleRead

#print axioms SingleRead.cannotShare

#print axioms SingleRead.singleCount
