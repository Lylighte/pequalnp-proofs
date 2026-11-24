import SingleRead

namespace PrefixSingleRead

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open SingleRead (hit reads sideInsert Dominates)
variable {n : ℕ}

def Blind (C : AndCountCircuit n) (k : ℕ) (x : Fin n) (U : Finset (Fin n)) : Prop :=
  ∀ i : Fin C.size, i.val < k → C.gateVal (insert x U) i = C.gateVal U i

def Edge (C : AndCountCircuit n) (k : ℕ) (x : Fin n) (U : Finset (Fin n)) : Prop :=
  Blind C k x U ∧ C.eval U = false ∧ C.eval (insert x U) = true

def SwitchAt (C : AndCountCircuit n) (g : Fin C.size) (x : Fin n) (U : Finset (Fin n)) : Prop :=
  let a := hit C g (C.leftVars g) (C.leftGates g) U
  let b := hit C g (C.rightVars g) (C.rightGates g) U
  ¬ (a ∧ b) ∧ (a ∨ x ∈ C.leftVars g) ∧ (b ∨ x ∈ C.rightVars g)

theorem firstSwitch (C : AndCountCircuit n) (k : ℕ) (x : Fin n) (U : Finset (Fin n))
    (bareOut : x ∉ C.outVars) (edge : Edge C k x U) :
    ∃ g : Fin C.size, k ≤ g.val ∧ g ∈ reads C x ∧ SwitchAt C g x U := by
  classical
  obtain ⟨blind,off,on⟩ := edge
  let S := Finset.univ.filter (fun g : Fin C.size => C.gateVal (insert x U) g ≠ C.gateVal U g)
  have ne : S.Nonempty := by
    rw [AndCountCircuit.eval,decide_eq_true_eq] at on
    rcases on with ⟨v,hv,h⟩ | ⟨g,hg,h⟩
    · rcases Finset.mem_insert.mp h with rfl | old
      · exact (bareOut hv).elim
      · have yes : C.eval U = true := decide_eq_true (Or.inl ⟨v,hv,old⟩)
        exact (Bool.false_ne_true (off.symm.trans yes)).elim
    · refine ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      intro eq
      have yes : C.eval U = true := decide_eq_true (Or.inr ⟨g,hg,eq.symm.trans h⟩)
      exact Bool.false_ne_true (off.symm.trans yes)
  let g := S.min' ne
  have mem : g ∈ S := S.min'_mem ne
  have different := (Finset.mem_filter.mp mem).2
  have tail : k ≤ g.val := by exact le_of_not_gt (fun lt => different (blind g lt))
  have prior (j : Fin C.size) (lt : j < g) : C.gateVal (insert x U) j = C.gateVal U j := by
    by_contra hn
    exact (not_le_of_gt lt) (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
  have old : C.gateVal U g = true ↔
      hit C g (C.leftVars g) (C.leftGates g) U ∧ hit C g (C.rightVars g) (C.rightGates g) U := by
    rw [SingleRead.gateVal_unfold,Bool.and_eq_true]
    exact Iff.rfl
  have new : C.gateVal (insert x U) g = true ↔
      (hit C g (C.leftVars g) (C.leftGates g) U ∨ x ∈ C.leftVars g) ∧
      (hit C g (C.rightVars g) (C.rightGates g) U ∨ x ∈ C.rightVars g) := by
    rw [SingleRead.gateVal_unfold,Bool.and_eq_true]
    exact and_congr (sideInsert C U x g _ _ prior) (sideInsert C U x g _ _ prior)
  have no : C.gateVal U g ≠ true := by
    intro yes
    have both := old.mp yes
    exact different ((new.mpr ⟨Or.inl both.1,Or.inl both.2⟩).trans yes.symm)
  have yes : C.gateVal (insert x U) g = true := by
    cases he : C.gateVal (insert x U) g with
    | true => rfl
    | false => exact (different (he.trans (Bool.eq_false_iff.mpr no).symm)).elim
  have s : SwitchAt C g x U := ⟨fun h => no (old.mpr h),new.mp yes⟩
  refine ⟨g,tail,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,s⟩
  unfold SwitchAt at s
  tauto

def ConflictsOn {V U : Type*} (member : V → U → Prop) (edge : V → U → Prop) (x y : V) : Prop :=
  (∃ u, member y u ∧ edge x u) ∧ (∃ u, member x u ∧ edge y u) ∧ (∃ u, edge x u ∧ edge y u)

abbrev Conflict (C : AndCountCircuit n) (k : ℕ) := ConflictsOn (· ∈ ·) (Edge C k)

lemma comparableImpossible (C : AndCountCircuit n) (g : Fin C.size) (x y : Fin n)
    (U : Finset (Fin n)) (s : SwitchAt C g x U) (hy : y ∈ U) (dom : Dominates C g x y) : False := by
  obtain ⟨no,hl,hr⟩ := s
  exact no ⟨hl.elim id (fun hx => decide_eq_true (Or.inl ⟨y,dom.1 hx,hy⟩)),
    hr.elim id (fun hx => decide_eq_true (Or.inl ⟨y,dom.2 hx,hy⟩))⟩

lemma conflictCannotShare (C : AndCountCircuit n) (k : ℕ) (x y : Fin n) (g : Fin C.size)
    (sx : ∀ U, Edge C k x U → SwitchAt C g x U)
    (sy : ∀ U, Edge C k y U → SwitchAt C g y U) (conflict : Conflict C k x y) : False := by
  obtain ⟨⟨u,hy,ex⟩,⟨v,hx,ey⟩,⟨w,exw,eyw⟩⟩ := conflict
  have a := sx w exw
  have b := sy w eyw
  have comp : Dominates C g x y ∨ Dominates C g y x := by
    unfold Dominates
    unfold SwitchAt at a b
    tauto
  rcases comp with d | d
  · exact comparableImpossible C g x y u (sx u ex) hy d
  · exact comparableImpossible C g y x v (sy v ey) hx d

def Used (C : AndCountCircuit n) (k : ℕ) (x : Fin n) : Prop :=
  ∃ p ∈ reads C x, p.val < k

lemma uniqueTail (C : AndCountCircuit n) (k : ℕ) (x : Fin n) (cap : (reads C x).card ≤ 2)
    (used : Used C k x) (a b : Fin C.size) (ha : k ≤ a.val) (hb : k ≤ b.val)
    (ma : a ∈ reads C x) (mb : b ∈ reads C x) : a = b := by
  obtain ⟨p,hp,lt⟩ := used
  have le : ((reads C x).erase p).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hp]
    omega
  apply Finset.card_le_one.mp le a _ b _
  · exact Finset.mem_erase.mpr ⟨fun eq => (Nat.not_le_of_gt lt) (eq ▸ ha),ma⟩
  · exact Finset.mem_erase.mpr ⟨fun eq => (Nat.not_le_of_gt lt) (eq ▸ hb),mb⟩

theorem coloring (C : AndCountCircuit n) (k : ℕ) (T : Finset (Fin n))
    (noOut : ∀ x ∈ T, x ∉ C.outVars)
    (cap : ∀ x ∈ T, (reads C x).card ≤ 2)
    (used : ∀ x ∈ T, Used C k x) (active : ∀ x ∈ T, ∃ U, Edge C k x U) :
    ∃ color : ↥T → Fin (C.size - k), ∀ x y : ↥T, Conflict C k x.val y.val → color x ≠ color y := by
  classical
  have someGate (x : ↥T) : ∃ g : Fin C.size, k ≤ g.val ∧ g ∈ reads C x.val := by
    obtain ⟨U,e⟩ := active _ x.property
    obtain ⟨g,tail,r,_⟩ := firstSwitch C k _ U (noOut _ x.property) e
    exact ⟨g,tail,r⟩
  choose g tail r using someGate
  have controls (x : ↥T) (U) (e : Edge C k x.val U) : SwitchAt C (g x) x.val U := by
    obtain ⟨j,hj,mj,s⟩ := firstSwitch C k _ U (noOut _ x.property) e
    have eq := uniqueTail C k x.val (cap _ x.property) (used _ x.property) j (g x) hj (tail x) mj (r x)
    exact eq ▸ s
  let color (x : ↥T) : Fin (C.size-k) := ⟨(g x).val-k,by have := (g x).isLt; have := tail x; omega⟩
  refine ⟨color,?_⟩
  intro x y conflict eq
  have diff : (g x).val-k = (g y).val-k := congrArg Fin.val eq
  have same : g x = g y := by apply Fin.ext; have := tail x; have := tail y; omega
  exact conflictCannotShare C k x.val y.val (g x) (controls x) (same ▸ controls y) conflict

abbrev RowBlind (C : AndCountCircuit 10) (k : ℕ) (x : Fin 10) (r : Fin 15) :=
  x ∉ Petersen905.rows r ∧ Blind C k x (Petersen905.rows r)

abbrev RowConflict (C : AndCountCircuit 10) (k : ℕ) :=
  ConflictsOn (fun (v : Fin 10) (r : Fin 15) => v ∈ Petersen905.rows r) (RowBlind C k)

theorem petersenColoring (C : AndCountCircuit 10) (k : ℕ) (T : Finset (Fin 10))
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x ∈ T, PetersenEquivariance.bareCount C x ≤ 2)
    (used : ∀ x ∈ T, Used C k x)
    (active : ∀ x ∈ T, ∃ r, RowBlind C k x r) :
    ∃ color : ↥T → Fin (C.size - k), ∀ x y : ↥T, RowConflict C k x.val y.val → color x ≠ color y := by
  have boundary (r : Fin 15) := (PetersenBoundary.goodGraph _).mp (Petersen905.rowsGood r)
  have values (r : Fin 15) := sep _ (boundary r).1 (boundary r).2
  have out (x : Fin 10) : x ∉ C.outVars := SingleRead.noBareOutput C 0 (fun r _ => values r) x
  have edge (x r) (h : RowBlind C k x r) : Edge C k x (Petersen905.rows r) :=
    ⟨h.2,(values r).1,(values r).2 x h.1⟩
  obtain ⟨color,proper⟩ := coloring C k T (fun x _ => out x) cap used (by
    intro x hx
    obtain ⟨r,h⟩ := active x hx
    exact ⟨_,edge x r h⟩)
  refine ⟨color,?_⟩
  intro x y conflict
  obtain ⟨⟨u,hy,hx'⟩,⟨v,hx,hy'⟩,⟨w,ax,ay⟩⟩ := conflict
  exact proper x y ⟨⟨_,hy,edge x u hx'⟩,⟨_,hx,edge y v hy'⟩,⟨_,edge x w ax,edge y w ay⟩⟩

theorem petersenCliqueBound (C : AndCountCircuit 10) (k : ℕ) (T : Finset (Fin 10))
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x ∈ T, PetersenEquivariance.bareCount C x ≤ 2)
    (used : ∀ x ∈ T, Used C k x)
    (active : ∀ x ∈ T, ∃ r, RowBlind C k x r)
    (clique : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → RowConflict C k x y) :
    T.card ≤ C.size-k := by
  obtain ⟨color,proper⟩ := petersenColoring C k T sep cap used active
  have injective : Function.Injective color := by
    intro x y eq
    by_contra neq
    exact proper x y (clique _ x.property _ y.property (fun same => neq (Subtype.ext same))) eq
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective _ injective

end PrefixSingleRead

#print axioms PrefixSingleRead.firstSwitch
#print axioms PrefixSingleRead.coloring

#print axioms PrefixSingleRead.petersenCliqueBound
