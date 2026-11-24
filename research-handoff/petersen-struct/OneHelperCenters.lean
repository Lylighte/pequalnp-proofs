import NormalizedCandidate

namespace PetersenOneHelper

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenBoundary (negatives positives)
open PetersenFirstPins (Candidate)
open PetersenNormalized (Shape)
open Petersen905 (related)

abbrev V := Fin 10
abbrev Input := Finset V

def Forced (H : Input → Bool) (v w : V) : Prop :=
  ∃ P ∈ positives, (∀ a ∈ P, ∀ b ∈ P, related a b = true →
    (a = v ∧ b = w) ∨ (a = w ∧ b = v)) ∧
    (H P = false ∨ ∀ x ∈ P, ∃ N ∈ negatives, x ∈ N ∧ H N = true)

theorem rectangular (C : AndCountCircuit 10) (hc : Candidate C) (g : Fin C.size)
    (isOut : g ∈ C.outGates) (a b : V) (ha : a ∈ C.leftVars g) (hb : b ∈ C.rightVars g) :
    related a b = true := by
  by_contra! h
  obtain ⟨j,haj,hbj⟩ := Petersen905.jointlyPresent a b (Bool.eq_false_iff.mpr h)
  let N := Petersen905.rows j
  have hn : N ∈ negatives := (PetersenBoundary.negativeIff _).mpr (Petersen905.rowsGood j)
  have yes : C.gateVal N g = true := by
    rw [PetersenCnfBridge.gate_equation,Bool.and_eq_true]
    exact ⟨decide_eq_true (Or.inl ⟨a,ha,haj⟩),decide_eq_true (Or.inl ⟨b,hb,hbj⟩)⟩
  have out : C.eval N = true := decide_eq_true (Or.inr ⟨g,isOut,yes⟩)
  exact Bool.false_ne_true ((((PetersenBoundary.separationIff C).mp hc.2.2.2).1 N hn).symm.trans out)

theorem covered (C : AndCountCircuit 10) (hc : Candidate C) (shape : Shape C 1)
    (h : Fin C.size) (zero : h.val = 0) (v w : V)
    (forced : Forced (fun U => C.gateVal U h) v w) :
    ∃ g ∈ C.outGates,
      (v ∈ C.leftVars g ∧ w ∈ C.rightVars g) ∨ (w ∈ C.leftVars g ∧ v ∈ C.rightVars g) := by
  classical
  obtain ⟨P,hp,unique,block⟩ := forced
  obtain ⟨out,neg,wire,raw⟩ := shape
  obtain ⟨labelsN,labelsP⟩ := (PetersenBoundary.separationIff C).mp hc.2.2.2
  have evalP := labelsP P hp
  rw [AndCountCircuit.eval,decide_eq_true_eq] at evalP
  rcases evalP with ⟨x,hx,_⟩ | ⟨g,isOut,gt⟩
  · simp [raw] at hx
  have safe := (neg g).mpr ((out g).mp isOut)
  have prev (j : Fin C.size) (hj : GateReindex.Wire C g j) : j = h := by
    have bound := wire g j hj
    apply Fin.ext
    omega
  let rawHit (S : Finset V) := ∃ x ∈ S, x ∈ P
  let H (U : Input) := C.gateVal U h
  have decomp (B : Finset V) (F : Finset (Fin C.size)) (ref : ∀ j ∈ F, GateReindex.Wire C g j)
      (on : sideTrue P B F g (C.gateVal P) = true) :
      rawHit B ∨ (h ∈ F ∧ h < g ∧ H P = true) := by
    rw [sideTrue,decide_eq_true_eq] at on
    rcases on with bare | ⟨j,hj,lt,ht⟩
    · exact Or.inl bare
    · obtain rfl := prev j (ref j hj)
      exact Or.inr ⟨hj,lt,ht⟩
  rw [PetersenCnfBridge.gate_equation,Bool.and_eq_true] at gt
  have L := decomp _ _ (fun j hj => Or.inl hj) gt.1
  have R := decomp _ _ (fun j hj => Or.inr hj) gt.2
  have reject (N) (hn : N ∈ negatives) (left : sideTrue N (C.leftVars g) (C.leftGates g) g (C.gateVal N) = true)
      (right : sideTrue N (C.rightVars g) (C.rightGates g) g (C.gateVal N) = true) : False := by
    have off := safe N hn
    rw [PetersenCnfBridge.gate_equation,left,right] at off
    exact Bool.false_ne_true off.symm
  rcases L with ⟨a,ha,ap⟩ | ⟨hl,lt,hpOn⟩
  · rcases R with ⟨b,hb,bp⟩ | ⟨hr,lt,hpOn⟩
    · refine ⟨g,isOut,?_⟩
      rcases unique a ap b bp (rectangular C hc g isOut a b ha hb) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨ha,hb⟩
      · exact Or.inr ⟨ha,hb⟩
    · rcases block with off | row
      · exact (Bool.false_ne_true (off.symm.trans hpOn)).elim
      · obtain ⟨N,hn,hN,on⟩ := row a ap
        exact (reject N hn (decide_eq_true (Or.inl ⟨a,ha,hN⟩)) (decide_eq_true (Or.inr ⟨h,hr,lt,on⟩))).elim
  · rcases block with off | row
    · exact (Bool.false_ne_true (off.symm.trans hpOn)).elim
    · rcases R with ⟨b,hb,bp⟩ | ⟨hr,lt',_⟩
      · obtain ⟨N,hn,hN,on⟩ := row b bp
        exact (reject N hn (decide_eq_true (Or.inr ⟨h,hl,lt,on⟩)) (decide_eq_true (Or.inl ⟨b,hb,hN⟩))).elim
      · have notAll : ¬ ∀ N ∈ negatives, C.gateVal N h = false := by
          intro all
          have bad := (neg h).mp all
          omega
        push Not at notAll
        obtain ⟨N,hn,on⟩ := notAll
        have yes : C.gateVal N h = true := by simpa using on
        exact (reject N hn (decide_eq_true (Or.inr ⟨h,hl,lt,yes⟩)) (decide_eq_true (Or.inr ⟨h,hr,lt',yes⟩))).elim

theorem centersBound (C : AndCountCircuit 10) (hc : Candidate C) (shape : Shape C 1)
    (h : Fin C.size) (zero : h.val = 0) (T : Finset V) (neighbors : V → Finset V)
    (forced : ∀ v ∈ T, ∀ w ∈ neighbors v, Forced (fun U => C.gateVal U h) v w)
    (degree : ∀ v ∈ T, 2 < (neighbors v).card +
      (if v ∈ C.leftVars h ∨ v ∈ C.rightVars h then 1 else 0)) :
    T.card ≤ 5 := by
  classical
  have star (i : Fin C.size) (hi : i ∈ C.outGates) : ∃ t : V,
      ∀ a ∈ C.leftVars i, ∀ b ∈ C.rightVars i, a = t ∨ b = t :=
    Petersen905.starCenter _ _ (fun a ha b hb => rectangular C hc i hi a b ha hb)
  let center (i : Fin C.size) : V := if hi : i ∈ C.outGates then (star i hi).choose else 0
  have centerSpec (i : Fin C.size) (hi : i ∈ C.outGates) (a) (ha : a ∈ C.leftVars i)
      (b) (hb : b ∈ C.rightVars i) : a = center i ∨ b = center i := by
    simpa [center,hi] using (star i hi).choose_spec a ha b hb
  have hidden : h ∉ C.outGates := by
    intro hh
    have bad := (shape.1 h).mp hh
    omega
  have inc : T ⊆ C.outGates.image center := by
    intro v hv
    by_contra absent
    let occ := Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
    have sub : neighbors v ⊆ (occ.erase h).image center := by
      intro w hw
      obtain ⟨g,hg,cover⟩ := covered C hc shape h zero v w (forced v hv w hw)
      have neq : g ≠ h := fun eq => hidden (eq ▸ hg)
      have diff : v ≠ center g := fun eq => absent (eq ▸ Finset.mem_image_of_mem center hg)
      rcases cover with ⟨left,right⟩ | ⟨left,right⟩
      · exact Finset.mem_image.mpr ⟨g,Finset.mem_erase.mpr ⟨neq,Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,Or.inl left⟩⟩,((centerSpec g hg v left w right).resolve_left diff).symm⟩
      · exact Finset.mem_image.mpr ⟨g,Finset.mem_erase.mpr ⟨neq,Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,Or.inr right⟩⟩,((centerSpec g hg w left v right).resolve_right diff).symm⟩
    have bound : (neighbors v).card ≤ (occ.erase h).card := (Finset.card_le_card sub).trans Finset.card_image_le
    have cap : occ.card ≤ 2 := hc.2.2.1 v
    have high := degree v hv
    by_cases yes : v ∈ C.leftVars h ∨ v ∈ C.rightVars h
    · have eq := Finset.card_erase_add_one (s := occ) (Finset.mem_filter.mpr ⟨Finset.mem_univ h,yes⟩)
      simp only [yes,ite_true] at high
      omega
    · have le := Finset.card_le_card (Finset.erase_subset h occ)
      simp only [yes,ite_false] at high
      omega
  have outs : C.outGates ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _,fun eq => hidden (eq ▸ Finset.mem_univ h)⟩
  have bound := (Finset.card_le_card inc).trans Finset.card_image_le
  have small := Finset.card_lt_card outs
  rw [Finset.card_univ,Fintype.card_fin] at small
  have hs := hc.2.1
  omega

theorem positiveHidden (C : AndCountCircuit 10) (hc : Candidate C) (u : ℕ) (shape : Shape C u) :
    0 < u := by
  by_contra! zero
  apply Petersen905.allSafeImpossible C hc.2.1 hc.2.2.1 hc.2.2.2
  intro i j
  have safe := (shape.2.1 i).mpr (by omega)
  exact safe _ ((PetersenBoundary.negativeIff _).mpr (Petersen905.rowsGood j))

def rawProduct (L R U : Input) : Bool :=
  decide (∃ x ∈ L, x ∈ U) && decide (∃ x ∈ R, x ∈ U)

theorem firstProduct (C : AndCountCircuit 10) (h : Fin C.size) (zero : h.val = 0) (U : Input) :
    C.gateVal U h = rawProduct (C.leftVars h) (C.rightVars h) U := by
  have no (j : Fin C.size) : ¬j < h := by change ¬j.val < h.val; omega
  rw [PetersenCnfBridge.gate_equation]
  simp [rawProduct,sideTrue,no]

theorem masksImpossible (C : AndCountCircuit 10) (hc : Candidate C) (shape : Shape C 1)
    (l r : Fin 1024) (first : PetersenFirstPins.FirstSides C l r)
    (T : Finset V) (neighbors : V → Finset V) (many : 5 < T.card)
    (forced : ∀ v ∈ T, ∀ w ∈ neighbors v,
      Forced (rawProduct (PetersenBoundary.decode l) (PetersenBoundary.decode r)) v w)
    (degree : ∀ v ∈ T, 2 < (neighbors v).card +
      (if v ∈ PetersenBoundary.decode l ∨ v ∈ PetersenBoundary.decode r then 1 else 0)) : False := by
  obtain ⟨pos,hl,hr⟩ := first
  let h : Fin C.size := ⟨0,pos⟩
  have eq : (fun U => C.gateVal U h) = rawProduct (PetersenBoundary.decode l) (PetersenBoundary.decode r) := by
    funext U
    rw [firstProduct C h rfl,show C.leftVars h = _ from hl,show C.rightVars h = _ from hr]
  have le := centersBound C hc shape h rfl T neighbors (eq ▸ forced)
    (by simpa only [h,hl,hr] using degree)
  omega

end PetersenOneHelper

#print axioms PetersenOneHelper.covered
#print axioms PetersenOneHelper.centersBound
#print axioms PetersenOneHelper.positiveHidden

#print axioms PetersenOneHelper.masksImpossible
