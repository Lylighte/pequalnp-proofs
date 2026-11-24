import PrefixDemand
import FirstBlindClique

namespace FirstDemandClique
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open FirstBlindClique (V Input value)
open PrefixSingleRead (ConflictsOn)
abbrev Witness := V → Fin 15 → Fin 15 × V

-- A witness gives the base negative row and vertex of one positive extension.
def cert (L R : Input) (w : Witness) (x : V) (r : Fin 15) : Prop :=
  let s := (w x r).1
  let v := (w x r).2
  let P := insert v (Petersen905.rows s)
  v ∉ Petersen905.rows s ∧ P ⊆ insert x (Petersen905.rows r) ∧
    (value L R P = true → value L R (Petersen905.rows r) = true)

abbrev conflict (L R : Input) (w : Witness) :=
  ConflictsOn (fun (x : V) r => x ∈ Petersen905.rows r) (cert L R w)

theorem bound (C : AndCountCircuit 10) (g : Fin C.size) (zero : g.val = 0)
    (L R T : Input) (l : C.leftVars g = L) (r : C.rightVars g = R)
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x, PetersenEquivariance.bareCount C x ≤ 2)
    (w : Witness) (support : ∀ x ∈ T, x ∈ L ∨ x ∈ R) (active : ∀ x ∈ T, ∃ row, cert L R w x row)
    (complete : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → conflict L R w x y) :
    T.card ≤ C.size-1 := by
  have liftDemand (x row) (b : cert L R w x row) : PrefixDemand.RowDemand C 1 x row := by
    let s := (w x row).1
    let v := (w x row).2
    let P := insert v (Petersen905.rows s)
    have hp : P ∈ PetersenBoundary.positives :=
      (PetersenBoundary.positiveIff _).mpr ⟨_,Petersen905.rowsGood s,v,b.1,rfl⟩
    refine ⟨P,hp,b.2.1,?_⟩
    intro j hj
    have id : j = g := by apply Fin.ext; omega
    subst j
    simpa only [FirstBlindClique.zeroValue C g zero L R l r] using b.2.2
  apply PrefixDemand.cliqueBound C 1 T sep (fun x _ => cap x)
  · intro x hx
    refine ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by omega⟩
    simpa only [l,r] using support x hx
  · intro x hx
    obtain ⟨j,hj⟩ := active x hx
    exact ⟨j,liftDemand x j hj⟩
  · intro x hx y hy hne
    obtain ⟨⟨u,uy,ex⟩,⟨v,vx,ey⟩,⟨w,wx,wy⟩⟩ := complete x hx y hy hne
    exact ⟨⟨u,uy,liftDemand x u ex⟩,⟨v,vx,liftDemand y v ey⟩,
      ⟨w,liftDemand x w wx,liftDemand y w wy⟩⟩

def left50 : Input := {1,4,5}
def right201 : Input := {0,3,6,7}
def clique123 : Input := {0,1,3,4,5,6}
def witness : Witness :=
  ![![(0,0),(0,0),(2,0),(1,4),(4,0),(0,0),(6,0),(0,0),(0,0),(8,1),(0,0),(0,0),(10,1),(0,0),(0,0)],
  ![(0,0),(0,0),(2,1),(0,2),(0,0),(0,0),(6,1),(7,1),(0,0),(0,0),(0,0),(11,1),(0,0),(0,0),(13,2)],
  ![(0,2),(0,0),(2,2),(0,0),(4,2),(1,3),(6,2),(0,0),(8,2),(7,1),(10,2),(0,0),(11,1),(13,2),(0,0)],
  ![(0,0),(1,3),(0,0),(2,2),(0,0),(0,0),(6,3),(0,0),(8,3),(4,4),(0,0),(0,0),(0,0),(0,0),(10,2)],
  ![(0,0),(0,0),(2,4),(0,0),(4,4),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(11,4),(0,3),(13,4),(7,9)],
  ![(0,0),(0,0),(0,0),(0,0),(4,5),(0,0),(6,5),(7,5),(0,0),(0,7),(0,0),(0,0),(0,0),(13,5),(11,8)],
  ![(0,0),(0,0),(0,0),(0,0),(4,6),(0,0),(0,0),(0,0),(8,6),(6,1),(10,6),(0,0),(2,1),(0,0),(1,8)],
  ![(0,0),(1,7),(2,7),(3,7),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(10,7),(0,0),(4,5),(0,0),(8,2)],
  ![(0,8),(1,8),(2,8),(3,8),(4,8),(5,8),(6,8),(0,0),(0,0),(0,0),(10,8),(11,8),(12,8),(0,0),(0,0)],
  ![(0,9),(1,9),(2,9),(3,9),(4,9),(5,9),(6,9),(7,9),(8,9),(9,9),(0,0),(0,0),(0,0),(0,0),(0,0)]]

set_option maxHeartbeats 3000000 in
theorem table123 : (∀ x ∈ clique123, ∃ row, cert left50 right201 witness x row) ∧
    (∀ x ∈ clique123, ∀ y ∈ clique123, x ≠ y → conflict left50 right201 witness x y) := by
  unfold conflict ConflictsOn cert
  decide +kernel

theorem seven50_201 (C : AndCountCircuit 10) (g : Fin C.size) (zero : g.val = 0)
    (l : C.leftVars g = left50) (r : C.rightVars g = right201)
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x, PetersenEquivariance.bareCount C x ≤ 2) : 7 ≤ C.size := by
  have h := bound C g zero left50 right201 clique123 l r sep cap witness (by decide +kernel)
    table123.1 table123.2
  have sz : clique123.card = 6 := by decide +kernel
  omega

def right203 : Input := {0,1,3,6,7}
def clique249 : Input := {0,3,4,5,6,7}
def witness203 : Witness :=
  ![![(0,0),(0,0),(2,0),(1,4),(4,0),(0,0),(6,0),(0,0),(0,0),(8,1),(0,0),(0,0),(10,1),(13,0),(0,0)],
  ![(0,0),(0,0),(2,1),(0,2),(0,0),(0,0),(6,1),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,2),(0,0),(2,2),(0,0),(4,2),(1,3),(6,2),(0,0),(8,2),(7,1),(10,2),(0,0),(11,1),(13,2),(0,0)],
  ![(0,3),(1,3),(0,0),(2,2),(0,0),(0,0),(6,3),(0,0),(8,3),(4,4),(0,0),(0,0),(0,0),(13,3),(10,2)],
  ![(0,0),(0,0),(2,4),(0,0),(4,4),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(11,4),(0,3),(13,4),(7,9)],
  ![(0,0),(0,0),(0,0),(0,0),(4,5),(0,0),(6,5),(7,5),(0,0),(0,7),(0,0),(0,0),(0,0),(13,5),(11,8)],
  ![(0,6),(0,0),(0,0),(0,0),(4,6),(0,0),(0,0),(0,0),(8,6),(6,1),(10,6),(0,0),(2,1),(13,6),(1,8)],
  ![(0,7),(1,7),(2,7),(3,7),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(10,7),(0,0),(4,5),(13,7),(8,2)],
  ![(0,8),(1,8),(2,8),(3,8),(4,8),(5,8),(6,8),(0,0),(0,0),(0,0),(10,8),(11,8),(12,8),(0,0),(0,0)],
  ![(0,9),(1,9),(2,9),(3,9),(4,9),(5,9),(6,9),(7,9),(8,9),(9,9),(0,0),(0,0),(0,0),(0,0),(0,0)]]

set_option maxHeartbeats 3000000 in
theorem table249 : (∀ x ∈ clique249, ∃ row, cert left50 right203 witness203 x row) ∧
    (∀ x ∈ clique249, ∀ y ∈ clique249, x ≠ y → conflict left50 right203 witness203 x y) := by
  unfold conflict ConflictsOn cert
  decide +kernel

theorem seven50_203 (C : AndCountCircuit 10) (g : Fin C.size) (zero : g.val = 0)
    (l : C.leftVars g = left50) (r : C.rightVars g = right203)
    (sep : PetersenEquivariance.Separates Petersen905.graph C)
    (cap : ∀ x, PetersenEquivariance.bareCount C x ≤ 2) : 7 ≤ C.size := by
  have h := bound C g zero left50 right203 clique249 l r sep cap witness203 (by decide +kernel)
    table249.1 table249.2
  have sz : clique249.card = 6 := by decide +kernel
  omega

end FirstDemandClique

#print axioms FirstDemandClique.seven50_201

#print axioms FirstDemandClique.seven50_203
