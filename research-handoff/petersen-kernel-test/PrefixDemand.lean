import PrefixSingleRead

namespace PrefixDemand
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PrefixSingleRead (SwitchAt ConflictsOn Used)
open SingleRead (reads hit Dominates)
variable {n : ℕ}

def SignatureLE (C : AndCountCircuit n) (k : ℕ) (P I : Finset (Fin n)) : Prop :=
  ∀ j : Fin C.size, j.val < k → C.gateVal P j = true → C.gateVal I j = true

-- P may drop several vertices of I. Its sole possible new vertex is x.
def Demand (C : AndCountCircuit n) (k : ℕ) (x : Fin n) (I : Finset (Fin n)) : Prop :=
  ∃ P, P ⊆ insert x I ∧ SignatureLE C k P I ∧ C.eval I = false ∧ C.eval P = true

abbrev Conflict (C : AndCountCircuit n) (k : ℕ) := ConflictsOn (· ∈ ·) (Demand C k)

theorem ofBlind (C : AndCountCircuit n) (k : ℕ) (x : Fin n) (I : Finset (Fin n))
    (edge : PrefixSingleRead.Edge C k x I) : Demand C k x I :=
  ⟨_,Finset.Subset.refl _,fun j hj h => (edge.1 j hj).symm.trans h,edge.2⟩

lemma sideUpper (C : AndCountCircuit n) (P I : Finset (Fin n)) (x : Fin n) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (cover : P ⊆ insert x I)
    (prior : SignatureLE C i.val P I) (yes : hit C i B F P) :
    hit C i B F I ∨ x ∈ B := by
  rcases of_decide_eq_true yes with ⟨v,hv,hP⟩ | ⟨j,mem,lt,h⟩
  · rcases Finset.mem_insert.mp (cover hP) with rfl | old
    · exact Or.inr hv
    · exact Or.inl (decide_eq_true (Or.inl ⟨v,hv,old⟩))
  · exact Or.inl (decide_eq_true (Or.inr ⟨j,mem,lt,prior j lt h⟩))

theorem firstRise (C : AndCountCircuit n) (k : ℕ) (x : Fin n) (I : Finset (Fin n))
    (bareOut : x ∉ C.outVars) (demand : Demand C k x I) :
    ∃ g : Fin C.size, k ≤ g.val ∧ g ∈ reads C x ∧ SwitchAt C g x I := by
  classical
  obtain ⟨P,cover,sig,off,on⟩ := demand
  let S := Finset.univ.filter (fun g : Fin C.size => C.gateVal P g = true ∧ C.gateVal I g = false)
  have ne : S.Nonempty := by
    rw [AndCountCircuit.eval,decide_eq_true_eq] at on
    rcases on with ⟨v,hv,h⟩ | ⟨g,hg,h⟩
    · rcases Finset.mem_insert.mp (cover h) with rfl | old
      · exact (bareOut hv).elim
      · have yes : C.eval I = true := decide_eq_true (Or.inl ⟨v,hv,old⟩)
        exact (Bool.false_ne_true (off.symm.trans yes)).elim
    · refine ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,Bool.eq_false_iff.mpr ?_⟩⟩
      intro old
      have yes : C.eval I = true := decide_eq_true (Or.inr ⟨g,hg,old⟩)
      exact Bool.false_ne_true (off.symm.trans yes)
  let g := S.min' ne
  have mem : g ∈ S := S.min'_mem ne
  obtain ⟨pos,neg⟩ := (Finset.mem_filter.mp mem).2
  have tail : k ≤ g.val := le_of_not_gt (fun lt => Bool.false_ne_true (neg.symm.trans (sig g lt pos)))
  have prior : SignatureLE C g.val P I := by
    intro j lt h
    by_contra hn
    have m : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,Bool.eq_false_iff.mpr hn⟩
    exact (not_le_of_gt lt) (S.min'_le j m)
  have gate (U) : C.gateVal U g = true ↔
      hit C g (C.leftVars g) (C.leftGates g) U ∧ hit C g (C.rightVars g) (C.rightGates g) U := by
    rw [SingleRead.gateVal_unfold,Bool.and_eq_true]
    exact Iff.rfl
  have no : ¬ (hit C g (C.leftVars g) (C.leftGates g) I ∧ hit C g (C.rightVars g) (C.rightGates g) I) :=
    fun s => Bool.false_ne_true (neg.symm.trans ((gate I).mpr s))
  obtain ⟨l,r⟩ := (gate P).mp pos
  have s : SwitchAt C g x I := ⟨no,sideUpper C P I x g _ _ cover prior l,sideUpper C P I x g _ _ cover prior r⟩
  refine ⟨g,tail,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,s⟩
  unfold SwitchAt at s
  tauto

theorem placement (C : AndCountCircuit n) (k : ℕ) (T : Finset (Fin n))
    (noOut : ∀ x ∈ T, x ∉ C.outVars)
    (cap : ∀ x ∈ T, (reads C x).card ≤ 2)
    (used : ∀ x ∈ T, Used C k x) (active : ∀ x ∈ T, ∃ I, Demand C k x I) :
    ∃ g : ↥T → Fin C.size, ∀ x : ↥T, k ≤ (g x).val ∧ g x ∈ reads C x.val ∧
      ∀ I, Demand C k x.val I → SwitchAt C (g x) x.val I := by
  classical
  have someGate (x : ↥T) : ∃ g : Fin C.size, k ≤ g.val ∧ g ∈ reads C x.val := by
    obtain ⟨I,e⟩ := active _ x.property
    obtain ⟨g,tail,r,_⟩ := firstRise C k _ I (noOut _ x.property) e
    exact ⟨g,tail,r⟩
  choose g tail r using someGate
  refine ⟨g,fun x => ⟨tail x,r x,?_⟩⟩
  intro I e
  obtain ⟨j,hj,mj,s⟩ := firstRise C k _ I (noOut _ x.property) e
  have eq := PrefixSingleRead.uniqueTail C k x.val (cap _ x.property) (used _ x.property) j (g x) hj (tail x) mj (r x)
  exact eq ▸ s

theorem coloring (C : AndCountCircuit n) (k : ℕ) (T : Finset (Fin n))
    (noOut : ∀ x ∈ T, x ∉ C.outVars) (cap : ∀ x ∈ T, (reads C x).card ≤ 2)
    (used : ∀ x ∈ T, Used C k x) (active : ∀ x ∈ T, ∃ I, Demand C k x I) :
    ∃ color : ↥T → Fin (C.size - k), ∀ x y : ↥T, Conflict C k x.val y.val → color x ≠ color y := by
  classical
  obtain ⟨g,h⟩ := placement C k T noOut cap used active
  let color (x : ↥T) : Fin (C.size-k) := ⟨(g x).val-k,by have := (g x).isLt; have := (h x).1; omega⟩
  refine ⟨color,?_⟩
  intro x y conflict eq
  have diff : (g x).val-k = (g y).val-k := congrArg Fin.val eq
  have same : g x = g y := by apply Fin.ext; have := (h x).1; have := (h y).1; omega
  obtain ⟨⟨u,hy,ex⟩,⟨v,hx,ey⟩,⟨w,exw,eyw⟩⟩ := conflict
  have xc := (h x).2.2
  have yc : ∀ I, Demand C k y.val I → SwitchAt C (g x) y.val I := same ▸ (h y).2.2
  have sx := xc w exw
  have sy := yc w eyw
  have comp : Dominates C (g x) x.val y.val ∨ Dominates C (g x) y.val x.val := by
    unfold Dominates
    unfold SwitchAt at sx sy
    tauto
  rcases comp with d | d
  · exact PrefixSingleRead.comparableImpossible C _ _ _ u (xc u ex) hy d
  · exact PrefixSingleRead.comparableImpossible C _ _ _ v (yc v ey) hx d

def RowDemand (C : AndCountCircuit 10) (k : ℕ) (x : Fin 10) (r : Fin 15) : Prop :=
  ∃ P ∈ PetersenBoundary.positives, P ⊆ insert x (Petersen905.rows r) ∧ SignatureLE C k P (Petersen905.rows r)

abbrev RowConflict (C : AndCountCircuit 10) (k : ℕ) :=
  ConflictsOn (fun (v : Fin 10) (r : Fin 15) => v ∈ Petersen905.rows r) (RowDemand C k)

theorem petersenColoring (C : AndCountCircuit 10) (k : ℕ) (T : Finset (Fin 10))
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x ∈ T, PetersenEquivariance.bareCount C x ≤ 2)
    (used : ∀ x ∈ T, Used C k x) (active : ∀ x ∈ T, ∃ r, RowDemand C k x r) :
    ∃ color : ↥T → Fin (C.size - k), ∀ x y : ↥T, RowConflict C k x.val y.val → color x ≠ color y := by
  have boundary (r : Fin 15) := (PetersenBoundary.goodGraph _).mp (Petersen905.rowsGood r)
  have values (r : Fin 15) := sep _ (boundary r).1 (boundary r).2
  have out (x : Fin 10) : x ∉ C.outVars := SingleRead.noBareOutput C 0 (fun r _ => values r) x
  have dem (x r) (h : RowDemand C k x r) : Demand C k x (Petersen905.rows r) := by
    obtain ⟨P,hp,sub,sig⟩ := h
    exact ⟨P,sub,sig,(values r).1,((PetersenBoundary.separationIff C).mp sep).2 P hp⟩
  obtain ⟨color,proper⟩ := coloring C k T (fun x _ => out x) cap used (by
    intro x hx
    obtain ⟨r,h⟩ := active x hx
    exact ⟨_,dem x r h⟩)
  refine ⟨color,?_⟩
  intro x y conflict
  obtain ⟨⟨u,hy,hx'⟩,⟨v,hx,hy'⟩,⟨w,ax,ay⟩⟩ := conflict
  exact proper x y ⟨⟨_,hy,dem x u hx'⟩,⟨_,hx,dem y v hy'⟩,⟨_,dem x w ax,dem y w ay⟩⟩

theorem cliqueBound (C : AndCountCircuit 10) (k : ℕ) (T : Finset (Fin 10))
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x ∈ T, PetersenEquivariance.bareCount C x ≤ 2)
    (used : ∀ x ∈ T, Used C k x) (active : ∀ x ∈ T, ∃ r, RowDemand C k x r)
    (clique : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → RowConflict C k x y) : T.card ≤ C.size-k := by
  obtain ⟨color,proper⟩ := petersenColoring C k T sep cap used active
  have injective : Function.Injective color := by
    intro x y eq
    by_contra neq
    exact proper x y (clique _ x.property _ y.property (fun same => neq (Subtype.ext same))) eq
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective _ injective

end PrefixDemand

#print axioms PrefixDemand.placement
#print axioms PrefixDemand.cliqueBound
