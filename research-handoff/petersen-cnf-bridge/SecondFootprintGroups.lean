import FootprintPrefix

namespace PetersenSecondGroups

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenSuffix PetersenFootprintCenters PetersenFirstPins PetersenNormalized PetersenEquivariance

structure Bin where
  footprint : Nat
  lo : Nat
  hi : Nat
  deriving Inhabited

def conforms (a b : Nat) (s : Fin 2048) (g : Bin) := classCheck a b s g.footprint &&
  ((g.lo &&& s.val == g.lo) && (s.val &&& g.hi == s.val))

def sideTable (a b : Nat) (bins : Fin k → Bin) (route : Fin 2048 → Fin k) :=
  (List.finRange 2048).all (fun s => conforms a b s (bins (route s)))

def pair (a b : Nat) (x y : Bin) : Box := ⟨a,b,x.lo,x.hi,y.lo,y.hi,x.footprint,y.footprint⟩

theorem actual_member (a b : Nat) (bins : Fin k → Bin) (route : Fin 2048 → Fin k)
    (cert : sideTable a b bins route = true) (l r : Fin 2048) :
    Member (pair a b (bins (route l)) (bins (route r))) l r := by
  have known (s : Fin 2048) := List.all_eq_true.mp cert s (List.mem_finRange s)
  have inside (s : Fin 2048) : Sub (bins (route s)).lo s.val ∧ Sub s.val (bins (route s)).hi ∧
      SideClass a b s.val (bins (route s)).footprint := by
    have h := known s
    simp only [conforms,Bool.and_eq_true,beq_iff_eq] at h
    exact ⟨sub_of_and _ _ h.2.1,sub_of_and _ _ h.2.2,(class_iff ..).mp h.1⟩
  obtain ⟨ll,lh,lf⟩ := inside l
  obtain ⟨rl,rh,rf⟩ := inside r
  exact ⟨ll,lh,rl,rh,lf,rf⟩

def Refuted (B : Box) : Prop :=
  ∀ l r : Fin 2048, Member B l r → ∀ (C : AndCountCircuit 10) (hk : 2 ≤ C.size),
    Matches C (gates B.a B.b l r) hk → Candidate C → Shape C 2 → False

theorem swap_candidate (C : AndCountCircuit 10) (g : Fin C.size) (hc : Candidate C) :
    Candidate (swapGate C g) := by
  refine ⟨(swapWF C g).mpr hc.1,hc.2.1,?_,swapSeparates _ _ g hc.2.2.2⟩
  intro v
  change bareCount (swapGate C g) v ≤ 2
  rw [swapBare]
  exact hc.2.2.1 v

theorem swap_shape (C : AndCountCircuit 10) (g : Fin C.size) (shape : Shape C 2) :
    Shape (swapGate C g) 2 := by
  refine ⟨shape.1,?_,?_,shape.2.2.2⟩
  · intro i
    simpa only [gateVal,swapFuel] using shape.2.1 i
  · intro i j wire
    apply shape.2.2.1 i j
    by_cases he : i=g
    · simpa [GateReindex.Wire,swapGate,he,or_comm] using wire
    · simpa [GateReindex.Wire,swapGate,he] using wire

theorem swap_matches (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (a b l r : Nat)
    (front : Matches C (gates a b l r) hk) :
    Matches (swapGate C (head C 2 hk 1)) (gates a b r l) hk := by
  have ne : head C 2 hk 0 ≠ head C 2 hk 1 := fun h => (by decide : (0:Nat) ≠ 1) (congrArg Fin.val h)
  have f0 := front.left 0; have f1 := front.left 1
  have g0 := front.right 0; have g1 := front.right 1
  constructor
  · intro i; fin_cases i
    · change (if head C 2 hk 0 = head C 2 hk 1 then C.rightVars (head C 2 hk 0) else C.leftVars (head C 2 hk 0)) = _
      rw [ite_eq_right ne]
      exact f0
    · exact g1
  · intro i; fin_cases i
    · change (if head C 2 hk 0 = head C 2 hk 1 then C.leftVars (head C 2 hk 0) else C.rightVars (head C 2 hk 0)) = _
      rw [ite_eq_right ne]
      exact g0
    · exact f1
  · intro i j; fin_cases i
    · change head C 2 hk j ∈ (if head C 2 hk 0 = head C 2 hk 1 then C.rightGates (head C 2 hk 0) else C.leftGates (head C 2 hk 0)) ↔ _
      rw [ite_eq_right ne]
      exact front.leftWire 0 j
    · exact front.rightWire 1 j
  · intro i j; fin_cases i
    · change head C 2 hk j ∈ (if head C 2 hk 0 = head C 2 hk 1 then C.leftGates (head C 2 hk 0) else C.rightGates (head C 2 hk 0)) ↔ _
      rw [ite_eq_right ne]
      exact front.rightWire 0 j
    · exact front.leftWire 1 j

theorem swapped (a b : Nat) (x y : Bin) (ref : Refuted (pair a b x y)) : Refuted (pair a b y x) := by
  intro l r mem C hk front hc shape
  apply ref r l ⟨mem.rl,mem.rh,mem.ll,mem.lh,mem.rf,mem.lf⟩ (swapGate C (head C 2 hk 1)) hk
    (swap_matches C hk a b l r front) (swap_candidate C _ hc) (swap_shape C _ shape)

-- The branch checker can contain any of the individually proved rejection tests.
-- Only one orientation per class pair needs to pass.
def halfPairs (k : Nat) (check : Fin k → Fin k → Bool) :=
  (List.finRange k).all (fun i => (List.finRange (i.val+1)).all
    (fun j => check i ⟨j.val,by have := j.isLt; omega⟩))

theorem dispatch (a b : Fin 1024) (bins : Fin k → Bin) (route : Fin 2048 → Fin k)
    (sideOK : sideTable a b bins route = true)
    (check : Fin k → Fin k → Bool) (coverage : halfPairs k check = true)
    (sound : ∀ i j, check i j = true → Refuted (pair a b (bins i) (bins j)))
    (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (first : FirstSides C a b) (hc : Candidate C) (shape : Shape C 2) :
    False := by
  obtain ⟨l,r,front⟩ := actual_prefix C hk hc.1 a b first
  have half (i j : Fin k) (le : j ≤ i) : Refuted (pair a b (bins i) (bins j)) := by
    let t : Fin (i.val+1) := ⟨j.val,by change j.val ≤ i.val at le; omega⟩
    have outer := List.all_eq_true.mp coverage i (List.mem_finRange i)
    exact sound i j (List.all_eq_true.mp outer t (List.mem_finRange t))
  have full (i j : Fin k) : Refuted (pair a b (bins i) (bins j)) := by
    rcases le_total j i with h | h
    · exact half i j h
    · exact swapped a b (bins j) (bins i) (half j i h)
  exact full (route l) (route r) l r (actual_member a b bins route sideOK l r) C hk front hc shape

end PetersenSecondGroups
