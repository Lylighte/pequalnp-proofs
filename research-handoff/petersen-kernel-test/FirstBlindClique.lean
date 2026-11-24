import PrefixSingleRead

namespace FirstBlindClique

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PrefixSingleRead
abbrev V := Fin 10
abbrev Input := Finset V

def value (L R U : Input) : Bool :=
  decide (∃ x ∈ L, x ∈ U) && decide (∃ x ∈ R, x ∈ U)

def blind (L R : Input) (x : V) (r : Fin 15) : Prop :=
  x ∉ Petersen905.rows r ∧ value L R (insert x (Petersen905.rows r)) = value L R (Petersen905.rows r)

abbrev conflict (L R : Input) := ConflictsOn (fun (x : V) r => x ∈ Petersen905.rows r) (blind L R)

lemma zeroValue (C : AndCountCircuit 10) (g : Fin C.size) (zero : g.val = 0)
    (L R : Input) (l : C.leftVars g = L) (r : C.rightVars g = R) (U : Input) :
    C.gateVal U g = value L R U := by
  have no (j : Fin C.size) : ¬ j < g := by change ¬ j.val < g.val; omega
  rw [SingleRead.gateVal_unfold]
  simp [sideTrue,l,r,no,value]

theorem bound (C : AndCountCircuit 10) (g : Fin C.size) (zero : g.val = 0)
    (L R T : Input) (l : C.leftVars g = L) (r : C.rightVars g = R)
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x, PetersenEquivariance.bareCount C x ≤ 2)
    (support : ∀ x ∈ T, x ∈ L ∨ x ∈ R) (active : ∀ x ∈ T, ∃ row, blind L R x row)
    (complete : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → conflict L R x y) :
    T.card ≤ C.size-1 := by
  have liftBlind (x row) (b : blind L R x row) : RowBlind C 1 x row := by
    refine ⟨b.1,?_⟩
    intro j hj
    have id : j = g := by apply Fin.ext; omega
    subst j
    simpa only [zeroValue C g zero L R l r] using b.2
  apply petersenCliqueBound C 1 T sep (fun x _ => cap x)
  · intro x hx
    refine ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by omega⟩
    simpa only [l,r] using support x hx
  · intro x hx
    obtain ⟨j,hj⟩ := active x hx
    exact ⟨j,liftBlind x j hj⟩
  · intro x hx y hy hne
    obtain ⟨⟨u,uy,ex⟩,⟨v,vx,ey⟩,⟨w,wx,wy⟩⟩ := complete x hx y hy hne
    exact ⟨⟨u,uy,liftBlind x u ex⟩,⟨v,vx,liftBlind y v ey⟩,
      ⟨w,liftBlind x w wx,liftBlind y w wy⟩⟩

def left1 : Input := {0}
def right126 : Input := {1,2,3,4,5,6}

set_option maxHeartbeats 3000000 in
theorem table126 : (∀ x ∈ right126, ∃ row, blind left1 right126 x row) ∧
    (∀ x ∈ right126, ∀ y ∈ right126, x ≠ y → conflict left1 right126 x y) := by
  unfold conflict ConflictsOn blind
  decide +kernel

theorem seven126 (C : AndCountCircuit 10) (g : Fin C.size) (zero : g.val = 0)
    (l : C.leftVars g = left1) (r : C.rightVars g = right126)
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x, PetersenEquivariance.bareCount C x ≤ 2) : 7 ≤ C.size := by
  have h := bound C g zero left1 right126 right126 l r sep cap (fun _ hx => Or.inr hx)
    table126.1 table126.2
  have sz : right126.card = 6 := by decide +kernel
  omega

end FirstBlindClique

#print axioms FirstBlindClique.seven126
