import Mathlib
import PEqualNP.Defs.AndCountCircuit

namespace PetersenEquivariance

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

variable {n : ℕ}

abbrev vertexSet (e : Equiv.Perm (Fin n)) (U : Finset (Fin n)) := U.map e.toEmbedding

abbrev relabel (C : AndCountCircuit n) (e : Equiv.Perm (Fin n)) : AndCountCircuit n :=
  { C with
    leftVars := fun i => vertexSet e (C.leftVars i)
    rightVars := fun i => vertexSet e (C.rightVars i)
    outVars := vertexSet e C.outVars }

abbrev swapGate (C : AndCountCircuit n) (t : Fin C.size) : AndCountCircuit n :=
  { C with
    leftVars := fun i => if i = t then C.rightVars i else C.leftVars i
    rightVars := fun i => if i = t then C.leftVars i else C.rightVars i
    leftGates := fun i => if i = t then C.rightGates i else C.leftGates i
    rightGates := fun i => if i = t then C.leftGates i else C.rightGates i }

def bareCount (C : AndCountCircuit n) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card

theorem relabelSize (C : AndCountCircuit n) (e : Equiv.Perm (Fin n)) :
    (relabel C e).size = C.size := rfl

theorem swapSize (C : AndCountCircuit n) (t : Fin C.size) :
    (swapGate C t).size = C.size := rfl

theorem relabelWF (C : AndCountCircuit n) (e : Equiv.Perm (Fin n)) :
    (relabel C e).WellFormed ↔ C.WellFormed := Iff.rfl

theorem swapWF (C : AndCountCircuit n) (t : Fin C.size) :
    (swapGate C t).WellFormed ↔ C.WellFormed := by
  change (∀ i : Fin C.size, _) ↔ ∀ i : Fin C.size, _
  apply forall_congr'
  intro i
  by_cases h : i = t <;> simp [swapGate, h, and_comm]

theorem relabelBare (C : AndCountCircuit n) (e : Equiv.Perm (Fin n)) (v : Fin n) :
    bareCount (relabel C e) (e v) = bareCount C v := by
  simp [bareCount, relabel, vertexSet]

theorem swapBare (C : AndCountCircuit n) (t : Fin C.size) (v : Fin n) :
    bareCount (swapGate C t) v = bareCount C v := by
  unfold bareCount
  congr 1
  ext i
  by_cases h : i = t <;> simp [swapGate, h, or_comm]

lemma meetsRelabel (e : Equiv.Perm (Fin n)) (B U : Finset (Fin n)) :
    (∃ w ∈ vertexSet e B, w ∈ vertexSet e U) ↔ ∃ v ∈ B, v ∈ U := by
  simp only [vertexSet, Finset.mem_map_equiv]
  constructor
  · rintro ⟨w, hB, hU⟩
    exact ⟨e.symm w,hB,hU⟩
  · rintro ⟨v,hB,hU⟩
    exact ⟨e v, by simpa using hB, by simpa using hU⟩

lemma sideRelabel {k : ℕ} (e : Equiv.Perm (Fin n)) (U B : Finset (Fin n))
    (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool) :
    sideTrue (vertexSet e U) (vertexSet e B) F i val = sideTrue U B F i val := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  rw [meetsRelabel]

theorem relabelFuel (C : AndCountCircuit n) (e : Equiv.Perm (Fin n)) (U : Finset (Fin n)) (d : ℕ) :
    (relabel C e).gateValFuel (vertexSet e U) d = C.gateValFuel U d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext i
    simp only [gateValFuel, ih]
    exact congrArg₂ Bool.and (sideRelabel e U _ _ _ _) (sideRelabel e U _ _ _ _)

theorem swapFuel (C : AndCountCircuit n) (t : Fin C.size) (U : Finset (Fin n)) (d : ℕ) :
    (swapGate C t).gateValFuel U d = C.gateValFuel U d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext i
    simp only [gateValFuel, ih]
    by_cases h : i = t <;> simp [h, Bool.and_comm]

theorem relabelEval (C : AndCountCircuit n) (e : Equiv.Perm (Fin n)) (U : Finset (Fin n)) :
    (relabel C e).eval (vertexSet e U) = C.eval U := by
  unfold AndCountCircuit.eval gateVal
  rw [relabelFuel]
  apply decide_eq_decide.mpr
  exact or_congr (meetsRelabel e C.outVars U) Iff.rfl

theorem swapEval (C : AndCountCircuit n) (t : Fin C.size) (U : Finset (Fin n)) :
    (swapGate C t).eval U = C.eval U := by
  unfold AndCountCircuit.eval gateVal
  rw [swapFuel]

def Separates (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) : Prop :=
  ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
    (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
    C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true

theorem relabelSeparates (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) (e : Equiv.Perm (Fin n))
    (aut : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b) (h : Separates G C) :
    Separates G (relabel C e) := by
  intro I ind maximal
  let J := vertexSet e.symm I
  have mem (v : Fin n) : v ∈ J ↔ e v ∈ I := Finset.mem_map_equiv
  have back : vertexSet e J = I := by
    ext w
    simp [vertexSet, J, Finset.mem_map_equiv]
  obtain ⟨hz, ho⟩ := h J
    (fun a ha c hc adj => ind (e a) ((mem a).mp ha) (e c) ((mem c).mp hc) ((aut a c).mpr adj))
    (by
      intro w hw
      obtain ⟨a, ha, adj⟩ := maximal (e w) (fun hin => hw ((mem w).mpr hin))
      refine ⟨e.symm a, (mem _).mpr (by simpa using ha), (aut _ _).mp ?_⟩
      simpa using adj)
  constructor
  · rw [← back, relabelEval, hz]
  · intro w hw
    have hpos := ho (e.symm w) (fun hin => hw (by simpa using (mem _).mp hin))
    have mapped : vertexSet e (insert (e.symm w) J) = insert w I := by
      simp only [vertexSet, Finset.map_insert]
      rw [show e.toEmbedding (e.symm w) = w from e.apply_symm_apply w]
      exact congrArg (insert w) back
    rw [← mapped, relabelEval, hpos]

theorem swapSeparates (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (t : Fin C.size) (h : Separates G C) : Separates G (swapGate C t) := by
  intro I hi hm
  simpa only [swapEval] using h I hi hm

-- A candidate can be moved to either side order of any automorphic image.
-- The distinguished index retains its numeric value, so this specializes to gate zero.
theorem transportCandidate (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (e : Equiv.Perm (Fin n)) (aut : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b)
    (t : Fin C.size) (flip : Bool) (wf : C.WellFormed)
    (cap : ∀ v, bareCount C v ≤ 2) (separates : Separates G C) :
    ∃ D : AndCountCircuit n, D.size = C.size ∧ D.WellFormed ∧
      (∀ v, bareCount D v ≤ 2) ∧ Separates G D ∧
      ∃ j : Fin D.size, j.val = t.val ∧
        D.leftVars j = vertexSet e (if flip then C.rightVars t else C.leftVars t) ∧
        D.rightVars j = vertexSet e (if flip then C.leftVars t else C.rightVars t) := by
  let R := relabel C e
  have wfR : R.WellFormed := (relabelWF C e).mpr wf
  have spR : Separates G R := relabelSeparates G C e aut separates
  have capR (w : Fin n) : bareCount R w ≤ 2 := by
    obtain ⟨v, rfl⟩ := e.surjective w
    exact (relabelBare C e v).trans_le (cap v)
  cases flip with
  | false => exact ⟨R, rfl, wfR, capR, spR, t, rfl, rfl, rfl⟩
  | true =>
    refine ⟨swapGate R t, rfl, (swapWF R t).mpr wfR, ?_, swapSeparates G R t spR, t, rfl, ?_, ?_⟩
    · exact fun v => (swapBare R t v).trans_le (capR v)
    · simp [R, relabel]
    · simp [R, relabel]

end PetersenEquivariance

#print axioms PetersenEquivariance.relabelWF
#print axioms PetersenEquivariance.swapWF
#print axioms PetersenEquivariance.relabelBare
#print axioms PetersenEquivariance.swapBare
#print axioms PetersenEquivariance.relabelFuel
#print axioms PetersenEquivariance.swapFuel
#print axioms PetersenEquivariance.relabelSeparates
#print axioms PetersenEquivariance.swapSeparates

#print axioms PetersenEquivariance.transportCandidate
