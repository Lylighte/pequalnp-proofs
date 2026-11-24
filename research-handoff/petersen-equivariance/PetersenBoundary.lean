import PetersenSafe
import PetersenEquivariance

namespace PetersenBoundary

open Petersen905 (V Good rows rowsGood related graph adjacency)
open PEqualNP.AndCount

-- Each bit v of a mask denotes the graph input v.
def decode (m : Fin 1024) : Finset V := Finset.univ.filter (fun v => m.val.testBit v.val)

-- Decimal values copied from the reduction's boundaryMasks, partitioned by independence.
def negativeMasks : List (Fin 1024) := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def positiveMasks : List (Fin 1024) := [51, 54, 58, 71, 77, 85, 101, 105, 106, 108, 114, 117, 118, 120, 124, 139, 142, 154, 170, 178, 197, 202, 203, 205, 209, 210, 212, 216, 217, 232, 233, 240, 244, 277, 278, 284, 306, 308, 325, 340, 360, 372, 387, 389, 393, 394, 401, 403, 404, 406, 410, 417, 434, 449, 457, 464, 466, 523, 525, 537, 549, 550, 553, 555, 556, 558, 562, 564, 570, 581, 585, 612, 616, 618, 628, 649, 650, 676, 682, 713, 720, 771, 774, 775, 777, 778, 781, 786, 788, 789, 802, 804, 805, 810, 834, 837, 897, 898, 901, 914]

def negatives := negativeMasks.toFinset.image decode
def positives := positiveMasks.toFinset.image decode

-- This is the published L_meta_635 allRows argument on the published definitions.
theorem allRows : ∀ I : Finset V, Good I → ∃ r, I = rows r := by
  unfold Good
  decide +kernel

def extensions : Finset (Finset V) := Finset.univ.biUnion fun r : Fin 15 =>
  (Finset.univ.filter (fun v : V => v ∉ rows r)).image (fun v => insert v (rows r))

set_option maxHeartbeats 10000000 in
theorem negativeRows : negatives = Finset.univ.image rows := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem positiveExtensions : positives = extensions := by decide +kernel

set_option maxHeartbeats 12000000 in
theorem sizes : negatives.card = 15 ∧ positives.card = 100 ∧
    negativeMasks.length = 15 ∧ positiveMasks.length = 100 ∧ Disjoint negatives positives := by
  decide +kernel

theorem negativeIff (I : Finset V) : I ∈ negatives ↔ Good I := by
  rw [negativeRows]
  constructor
  · intro h
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp h
    exact rowsGood r
  · intro h
    obtain ⟨r, rfl⟩ := allRows I h
    exact Finset.mem_image_of_mem _ (Finset.mem_univ r)

theorem positiveIff (U : Finset V) :
    U ∈ positives ↔ ∃ I : Finset V, Good I ∧ ∃ w : V, w ∉ I ∧ insert w I = U := by
  rw [positiveExtensions]
  simp only [extensions, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨r, w, hw, he⟩
    exact ⟨rows r, rowsGood r, w, hw, he⟩
  · rintro ⟨I, hi, w, hw, he⟩
    obtain ⟨r, rfl⟩ := allRows I hi
    exact ⟨r, w, hw, he⟩

theorem goodGraph (I : Finset V) : Good I ↔
    (∀ a ∈ I, ∀ b ∈ I, ¬ graph.Adj a b) ∧
    (∀ w : V, w ∉ I → ∃ a ∈ I, graph.Adj a w) := by
  unfold Good
  have hn (a b : V) : related a b = false ↔ ¬ graph.Adj a b := by
    rw [adjacency, Bool.eq_false_iff]
  simp only [hn]
  apply and_congr_right
  intro _
  constructor
  · intro h w hw
    obtain ⟨a, ha, hadj⟩ := h w hw
    exact ⟨a, ha, ((adjacency w a).mpr hadj).symm⟩
  · intro h w hw
    obtain ⟨a, ha, hadj⟩ := h w hw
    exact ⟨a, ha, (adjacency w a).mp hadj.symm⟩

theorem separationIff (C : AndCountCircuit 10) :
    PetersenEquivariance.Separates graph C ↔
      (∀ U ∈ negatives, C.eval U = false) ∧ (∀ U ∈ positives, C.eval U = true) := by
  constructor
  · intro h
    constructor
    · intro U hu
      obtain ⟨ind,maximal⟩ := (goodGraph U).mp ((negativeIff U).mp hu)
      exact (h U ind maximal).1
    · intro U hu
      obtain ⟨I, hi, w, hw, rfl⟩ := (positiveIff U).mp hu
      obtain ⟨ind,maximal⟩ := (goodGraph I).mp hi
      exact (h I ind maximal).2 w hw
  · intro ⟨hn,hp⟩ I ind maximal
    have hi := (goodGraph I).mpr ⟨ind,maximal⟩
    exact ⟨hn I ((negativeIff I).mpr hi),
      fun w hw => hp (insert w I) ((positiveIff _).mpr ⟨I, hi, w, hw, rfl⟩)⟩

end PetersenBoundary

#print axioms PetersenBoundary.sizes
#print axioms PetersenBoundary.separationIff
