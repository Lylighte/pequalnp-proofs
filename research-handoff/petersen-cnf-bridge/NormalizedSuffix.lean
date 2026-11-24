import SuffixCnf
import PrefixMatches
import NormalizedCandidate

namespace PetersenSuffix

open PEqualNP.AndCount PetersenTailCnf PetersenBoundary
open PetersenEquivariance (Separates bareCount)
open GateReindex (Wire)

theorem unsafe_witness (C : AndCountCircuit 10) (u : Nat)
    (sep : Separates Petersen905.graph C)
    (safe : ∀ i : Fin C.size, (∀ U ∈ negatives, C.gateVal U i = false) ↔ u ≤ i.val)
    (i : Fin C.size) (hi : i.val < u) :
    ∃ U, C.gateVal U i = true ∧ C.eval U = false := by
  classical
  have bad := mt (safe i).mp (not_le_of_gt hi)
  push Not at bad
  obtain ⟨U,mem,on⟩ := bad
  refine ⟨U,?_,((separationIff C).mp sep).1 U mem⟩
  cases e : C.gateVal U i <;> simp_all

-- These hypotheses are supplied verbatim by PetersenNormalized.normalForm.
theorem normalized_two (C : AndCountCircuit 10) (k : Nat) (size : C.size=k+2)
    (cap : ∀ v, bareCount C v ≤ 2) (o : C.outVars=∅)
    (w : ∀ i j : Fin C.size, Wire C i j → j.val < k) :
    ∃ f : List (Finset (Fin (10+k))), f.length=4 ∧
      ∀ U, C.eval U = true ↔ sat f (row C k (by omega) U) :=
  two_projected C k size cap (by rw [o]; exact Finset.empty_subset _) w

theorem normalized_three (C : AndCountCircuit 10) (k : Nat) (size : C.size=k+3)
    (cap : ∀ v, bareCount C v ≤ 2) (o : C.outVars=∅)
    (w : ∀ i j : Fin C.size, Wire C i j → j.val < k+1)
    (sep : Separates Petersen905.graph C)
    (safe : ∀ i : Fin C.size, (∀ U ∈ negatives, C.gateVal U i = false) ↔ k+1 ≤ i.val) :
    ∃ f : List (Finset (Fin (10+k))), f.length=7 ∧
      ∀ U, C.eval U = true ↔ sat f (row C k (by omega) U) :=
  three_projected C k size cap (by rw [o]; exact Finset.empty_subset _) w
    (unsafe_witness C (k+1) sep safe ⟨k,by omega⟩ (by change k < k+1; omega))

private theorem match_clique_bound (C P : AndCountCircuit 10) (hk : P.size ≤ C.size)
    (front : Matches C P hk) (sep : Separates Petersen905.graph C) (d : Nat)
    (formula : ∃ f : List (Finset (Fin (10+P.size))), f.length=d ∧
      ∀ U, C.eval U = true ↔ sat f (row C P.size hk U))
    (q : Finset (Finset (Fin 10))) (neg : q ⊆ negatives)
    (inc : incompatible q (row P P.size (Nat.le_refl _)) (· ∈ positives)) : q.card ≤ d := by
  obtain ⟨f,len,eval⟩ := formula
  have lab := (separationIff C).mp sep
  rw [← len]
  apply clause_lower_bound f q _ _ _ _ inc
  · intro x hx h
    rw [← matched_row C P hk front x] at h
    exact Bool.false_ne_true ((lab.1 x (neg hx)).symm.trans ((eval x).mpr h))
  · intro x hx
    rw [← matched_row C P hk front x]
    exact (eval x).mp (lab.2 x hx)

-- Reusable on stored prefix certificates. The row map in the clique
-- hypothesis is computed solely from P, independently of all completions.
theorem two_clique (C P : AndCountCircuit 10) (size : C.size=P.size+2)
    (front : Matches C P (by omega)) (hc : PetersenFirstPins.Candidate C)
    (shape : PetersenNormalized.Shape C P.size)
    (q : Finset (Finset (Fin 10))) (neg : q ⊆ negatives)
    (inc : incompatible q (row P P.size (Nat.le_refl _)) (· ∈ positives)) : q.card ≤ 4 :=
  match_clique_bound C P _ front hc.2.2.2 4
    (normalized_two C P.size size hc.2.2.1 shape.2.2.2 shape.2.2.1) q neg inc

theorem three_clique (C P : AndCountCircuit 10) (size : C.size=P.size+3)
    (front : Matches C P (by omega)) (hc : PetersenFirstPins.Candidate C)
    (shape : PetersenNormalized.Shape C (P.size+1))
    (q : Finset (Finset (Fin 10))) (neg : q ⊆ negatives)
    (inc : incompatible q (row P P.size (Nat.le_refl _)) (· ∈ positives)) : q.card ≤ 7 :=
  match_clique_bound C P _ front hc.2.2.2 7
    (normalized_three C P.size size hc.2.2.1 shape.2.2.2 shape.2.2.1 hc.2.2.2 shape.2.1)
    q neg inc

namespace Fixture

open PetersenTailCnf.Example

-- Raw selector masks [(1,4), (410,1760), (16,2048)]. Bit 10 refers to
-- gate zero and bit 11 to gate one.
def prefix3 : AndCountCircuit 10 where
  size := 3
  leftVars := ![bits 10 1,bits 10 410,bits 10 16]
  rightVars := ![bits 10 4,bits 10 736,∅]
  leftGates := fun _ => ∅
  rightGates := ![∅,{0},{1}]
  outVars := ∅
  outGates := ∅

set_option maxRecDepth 9000 in
set_option maxHeartbeats 5000000 in
theorem rows_checked :
    (nRows ++ pRows).all (fun m => decide
      (row prefix3 3 (by decide) (bits 10 m) = bits 13 (projected m))) = true ∧
    nRows.all (fun m => negativeMasks.any (fun v => v.val == m)) = true ∧
    pRows.all (fun m => positiveMasks.any (fun v => v.val == m)) = true := by decide +kernel

-- This statement quantifies over all six-gate circuits extending the named
-- prefix. Neither selectors of the three remaining gates nor their inputs
-- are fixed. It covers the normalized cut with four unsafe gates.
theorem excludes_completion (C : AndCountCircuit 10) (size : C.size=6)
    (front : Matches C prefix3 (by change 3 ≤ C.size; omega))
    (cap : ∀ v, bareCount C v ≤ 2) (o : C.outVars=∅)
    (w : ∀ i j : Fin C.size, Wire C i j → j.val < 4)
    (sep : Separates Petersen905.graph C)
    (safe : ∀ i : Fin C.size, (∀ U ∈ negatives, C.gateVal U i = false) ↔ 4 ≤ i.val) : False := by
  obtain ⟨f,len,eval⟩ := normalized_three C 3 size cap o w sep safe
  have rowEq (m : Nat) (mem : m ∈ nRows ++ pRows) :
      row C 3 (by omega) (bits 10 m) = bits 13 (projected m) := by
    have fixed := of_decide_eq_true (List.all_eq_true.mp rows_checked.1 m mem)
    exact (matched_row C prefix3 _ front (bits 10 m)).trans fixed
  have labels := (separationIff C).mp sep
  have low := needs_eight f (by
    intro m hm yes
    have found := List.all_eq_true.mp rows_checked.2.1 m hm
    obtain ⟨v,hv,e⟩ := List.any_eq_true.mp found
    have me : v.val=m := beq_iff_eq.mp e
    have neg := labels.1 (decode v) (Finset.mem_image_of_mem decode (by simpa using hv))
    have on := (eval (bits 10 m)).mpr (rowEq m (List.mem_append_left _ hm) ▸ yes)
    subst m
    exact Bool.false_ne_true (neg.symm.trans on)) (by
    intro m hm
    have found := List.all_eq_true.mp rows_checked.2.2 m hm
    obtain ⟨v,hv,e⟩ := List.any_eq_true.mp found
    have me : v.val=m := beq_iff_eq.mp e
    have yes := labels.2 (decode v) (Finset.mem_image_of_mem decode (by simpa using hv))
    rw [← rowEq m (List.mem_append_right _ hm)]
    apply (eval _).mp
    subst m; exact yes)
  omega

theorem excludes_shape (C : AndCountCircuit 10) (size : C.size=6)
    (front : Matches C prefix3 (by change 3 ≤ C.size; omega))
    (hc : PetersenFirstPins.Candidate C) (shape : PetersenNormalized.Shape C 4) : False :=
  excludes_completion C size front hc.2.2.1 shape.2.2.2 shape.2.2.1 hc.2.2.2 shape.2.1

end Fixture
end PetersenSuffix

#print axioms PetersenSuffix.suffix_available
#print axioms PetersenSuffix.gate_agrees
#print axioms PetersenSuffix.eval_agrees
#print axioms PetersenSuffix.wellFormed
#print axioms PetersenSuffix.matched_row
#print axioms PetersenSuffix.normalized_two
#print axioms PetersenSuffix.normalized_three
#print axioms PetersenSuffix.two_clique
#print axioms PetersenSuffix.three_clique
#print axioms PetersenSuffix.Fixture.rows_checked
#print axioms PetersenSuffix.Fixture.excludes_completion
#print axioms PetersenSuffix.Fixture.excludes_shape
