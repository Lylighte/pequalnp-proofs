import NormalizedOrder
import CertifiedCoverage
import BlindBatchAll

namespace PetersenNormalized

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit PetersenEquivariance
open PetersenFirstPins PetersenOrbitCover PetersenBoundary PetersenAutomorphisms

def Shape (C : AndCountCircuit 10) (u : ℕ) : Prop :=
  (∀ i : Fin C.size, i ∈ C.outGates ↔ u ≤ i.val) ∧
  (∀ i : Fin C.size, (∀ U ∈ negatives, C.gateVal U i = false) ↔ u ≤ i.val) ∧
  (∀ i j : Fin C.size, GateReindex.Wire C i j → j.val < u) ∧ C.outVars = ∅

abbrev Auto (e : Equiv.Perm (Fin 10)) :=
  ∀ a b, Petersen905.graph.Adj (e a) (e b) ↔ Petersen905.graph.Adj a b

theorem negativeImage (e : Equiv.Perm (Fin 10)) (he : Auto e) (I) :
    vertexSet e I ∈ negatives ↔ I ∈ negatives := by
  rw [negativeIff,negativeIff,goodGraph,goodGraph]
  have mem (v) : e v ∈ vertexSet e I ↔ v ∈ I := by simp [vertexSet]
  constructor
  · rintro ⟨ind,max⟩
    refine ⟨fun a ha b hb hadj => ind _ ((mem a).mpr ha) _ ((mem b).mpr hb) ((he a b).mpr hadj),?_⟩
    intro w hw
    obtain ⟨z,hz,adj⟩ := max (e w) (mt (mem w).mp hw)
    obtain ⟨a,rfl⟩ := e.surjective z
    exact ⟨a,(mem a).mp hz,(he a w).mp adj⟩
  · rintro ⟨ind,max⟩
    constructor
    · intro a ha b hb hadj
      obtain ⟨x,rfl⟩ := e.surjective a
      obtain ⟨y,rfl⟩ := e.surjective b
      exact ind x ((mem x).mp ha) y ((mem y).mp hb) ((he x y).mp hadj)
    · intro w hw
      obtain ⟨z,rfl⟩ := e.surjective w
      obtain ⟨a,ha,adj⟩ := max z (mt (mem z).mpr hw)
      exact ⟨e a,(mem a).mpr ha,(he a z).mpr adj⟩

theorem shapeRelabel (C : AndCountCircuit 10) (u) (e : Equiv.Perm (Fin 10))
    (aut : Auto e) (h : Shape C u) : Shape (relabel C e) u := by
  obtain ⟨out,neg,wire,raw⟩ := h
  refine ⟨out,?_,wire,by simp [raw,vertexSet]⟩
  intro i
  rw [← neg i]
  have gate (I) : (relabel C e).gateVal (vertexSet e I) i = C.gateVal I i :=
    congrFun (relabelFuel C e I C.size) i
  constructor
  · intro zeros I hi
    exact (gate I).symm.trans (zeros _ ((negativeImage e aut I).mpr hi))
  · intro zeros J hj
    let I := vertexSet e.symm J
    have eq : vertexSet e I = J := by ext x; simp [I,vertexSet,Finset.mem_map_equiv]
    rw [← eq,gate]
    exact zeros I ((negativeImage e aut I).mp (eq ▸ hj))

theorem shapeSwap (C : AndCountCircuit 10) (u) (t : Fin C.size) (h : Shape C u) :
    Shape (swapGate C t) u := by
  obtain ⟨out,neg,wire,raw⟩ := h
  refine ⟨out,?_,?_,raw⟩
  · intro i
    simpa only [gateVal,swapFuel,swapSize] using neg i
  · intro i j hj
    apply wire i j
    by_cases hi : i = t
    · simpa [GateReindex.Wire,swapGate,hi,or_comm] using hj
    · simpa [GateReindex.Wire,swapGate,hi] using hj

theorem canonicalNormal (hex : ∃ C : AndCountCircuit 10, Candidate C) :
    ∃ C u l r, Candidate C ∧ C.size = 6 ∧ u < 6 ∧ Shape C u ∧ Kept l r ∧ FirstSides C l r := by
  classical
  let P (n : ℕ) := ∃ C u l r, Candidate C ∧ C.size = 6 ∧ u < 6 ∧
    Shape C u ∧ FirstSides C l r ∧ key l r = n
  have ex : ∃ n, P n := by
    obtain ⟨C,hc⟩ := hex
    obtain ⟨wf,capSize,cap,sep⟩ := hc
    have lo := fiveBound C wf sep
    obtain ⟨E,u,ds,wfe,spe,ct,out,neg,wire,raw,bound⟩ := normalForm C wf sep
    let t : Fin E.size := ⟨0,by omega⟩
    exact ⟨_,E,u,encode (E.leftVars t),encode (E.rightVars t),
      ⟨wfe,by omega,fun v => (ct v).trans_le (cap v),spe⟩,by omega,by omega,
      ⟨out,neg,wire,raw⟩,⟨t.isLt,(decode_encode _).symm,(decode_encode _).symm⟩,rfl⟩
  obtain ⟨C,u,l,r,hc,size,hu,shape,sc,keyEq⟩ := Nat.find_spec ex
  obtain ⟨pos,hl,hr⟩ := sc
  let t : Fin C.size := ⟨0,pos⟩
  have least (D) (a b : Mask) (hd : Candidate D) (ds : D.size = C.size)
      (hs : Shape D u) (sides : FirstSides D a b) : key l r ≤ key a b := by
    rw [keyEq]
    exact Nat.find_min' ex ⟨D,u,a,b,hd,ds.trans size,hu,hs,sides,rfl⟩
  have pair (e : Equiv.Perm (Fin 10)) (aut : Auto e) :
      key l r ≤ key (move e l) (move e r) ∧ key l r ≤ key (move e r) (move e l) := by
    let R := relabel C e
    have cap (v) : bareCount R v ≤ 2 := by
      obtain ⟨w,rfl⟩ := e.surjective v
      exact (relabelBare C e w).trans_le (hc.2.2.1 w)
    have hR : Candidate R := ⟨(relabelWF C e).mpr hc.1,hc.2.1,cap,relabelSeparates _ C e aut hc.2.2.2⟩
    have sr := shapeRelabel C u e aut shape
    have left : R.leftVars t = decode (move e l) := by simp [R,t,hl,decode_move]
    have right : R.rightVars t = decode (move e r) := by simp [R,t,hr,decode_move]
    refine ⟨least R _ _ hR rfl sr ⟨pos,left,right⟩,?_⟩
    apply least (swapGate R t) _ _ ⟨(swapWF R t).mpr hR.1,hR.2.1,
      fun v => (swapBare R t v).trans_le (cap v),swapSeparates _ R t hR.2.2.2⟩ rfl (shapeSwap R u t sr)
    exact ⟨pos,by simpa [t,swapGate] using right,by simpa [t,swapGate] using left⟩
  have ord : l ≤ r := by
    have sw := least (swapGate C t) r l ⟨(swapWF C t).mpr hc.1,hc.2.1,
      fun v => (swapBare C t v).trans_le (hc.2.2.1 v),swapSeparates _ C t hc.2.2.2⟩ rfl
      (shapeSwap C u t shape) ⟨pos,by simpa [t,swapGate] using hr,by simpa [t,swapGate] using hl⟩
    simp only [key] at sw
    change l.val ≤ r.val
    omega
  exact ⟨C,u,l,r,hc,size,hu,shape,⟨⟨ord,fun i => pair _ (preservesGraph i)⟩,
    candidate_nonpolar fiveBound C hc l r ⟨pos,hl,hr⟩⟩,⟨pos,hl,hr⟩⟩

def Remaining (l r : Mask) : Prop := Kept l r ∧ (l,r) ∉ BlindBatchAll.ids

theorem remainingNormal (hex : ∃ C : AndCountCircuit 10, Candidate C) :
    ∃ (C : AndCountCircuit 10) (u : Fin 6) (l r : Mask), Candidate C ∧ C.size = 6 ∧ Shape C u.val ∧
      Remaining l r ∧ FirstSides C l r := by
  obtain ⟨C,u,l,r,hc,size,hu,shape,kept,pos,hl,hr⟩ := canonicalNormal hex
  have fresh : (l,r) ∉ BlindBatchAll.ids := by
    intro mem
    have seven := BlindBatchAll.seven l r mem C ⟨0,pos⟩ rfl hl hr hc.2.2.2 hc.2.2.1
    omega
  exact ⟨C,⟨u,hu⟩,l,r,hc,size,shape,⟨kept,fresh⟩,pos,hl,hr⟩

theorem of_remaining
    (cases : ∀ (C : AndCountCircuit 10) (u : Fin 6) l r,
      Candidate C → C.size = 6 → Shape C u.val → Remaining l r → FirstSides C l r → False) :
    PetersenSubmissionBridge.PostedStatement := by
  rintro G rfl ⟨C,hC⟩
  obtain ⟨D,u,l,r,hd,size,shape,remain,sides⟩ := remainingNormal ⟨C,hC⟩
  exact cases D u l r hd size shape remain sides

end PetersenNormalized

#print axioms PetersenNormalized.canonicalNormal
#print axioms PetersenNormalized.remainingNormal
#print axioms PetersenNormalized.of_remaining
