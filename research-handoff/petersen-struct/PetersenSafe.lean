import Mathlib
import PEqualNP.Defs.AndCountCircuit

-- Selected definitions and supporting lemmas from the upstream L_meta_635 proof.
namespace Petersen905

open PEqualNP.AndCount

abbrev V := Fin 10

def edges : Finset (Sym2 V) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}

def related (v w : V) : Bool := decide (s(v, w) ∈ edges)

def Good (I : Finset V) : Prop :=
  (∀ v ∈ I, ∀ w ∈ I, related v w = false) ∧
  (∀ u : V, u ∉ I → ∃ v ∈ I, related u v = true)

def rows : Fin 15 → Finset V := ![{1, 4, 5}, {0, 2, 6}, {3, 5, 6}, {2, 4, 5, 6}, {1, 3, 7}, {0, 3, 6, 7}, {4, 6, 7}, {2, 4, 8}, {0, 7, 8}, {1, 4, 7, 8}, {0, 3, 9}, {2, 5, 9}, {1, 3, 5, 9}, {1, 8, 9}, {0, 2, 8, 9}]

def through : V → Fin 5 → Fin 15 := ![![1, 5, 8, 10, 14],
    ![0, 4, 9, 12, 13],
    ![1, 3, 7, 11, 14],
    ![2, 4, 5, 10, 12],
    ![0, 3, 6, 7, 9],
    ![0, 2, 3, 11, 12],
    ![1, 2, 3, 5, 6],
    ![4, 5, 6, 8, 9],
    ![7, 8, 9, 13, 14],
    ![10, 11, 12, 13, 14]]

theorem rowsGood : ∀ i, Good (rows i) := by
  unfold Good
  decide +kernel

theorem rowContains : ∀ v i, v ∈ rows (through v i) := by decide +kernel

open PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

def Separates (C : AndCountCircuit 10) : Prop :=
  ∀ I, Good I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

theorem bare_out_empty (C : AndCountCircuit 10) (h : Separates C) (v : V) : v ∉ C.outVars := by
  intro hv
  have he := (h _ (rowsGood (through v 0))).1
  have ht : C.eval (rows (through v 0)) = true :=
    decide_eq_true (Or.inl ⟨v, hv, rowContains v 0⟩)
  simp [he] at ht

theorem jointlyPresent : ∀ a b : V, related a b = false → ∃ i, a ∈ rows i ∧ b ∈ rows i := by
  decide +kernel

theorem noSquare : ∀ a b c d : V, related a c = true → related a d = true →
    related b c = true → related b d = true → a = b ∨ c = d := by decide +kernel

theorem isolatedEdge : ∀ a b : V, related a b = true → ∃ i, a ∉ rows i ∧
    ∀ x ∈ insert a (rows i), ∀ y ∈ insert a (rows i), related x y = true →
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by decide +kernel

theorem starCenter (L R : Finset V) (h : ∀ a ∈ L, ∀ b ∈ R, related a b = true) :
    ∃ t : V, ∀ a ∈ L, ∀ b ∈ R, a = t ∨ b = t := by
  rcases L.eq_empty_or_nonempty with he | ⟨a, ha⟩
  · exact ⟨0, by simp [he]⟩
  rcases R.eq_empty_or_nonempty with he | ⟨b, hb⟩
  · exact ⟨0, by simp [he]⟩
  by_cases hl : ∀ x ∈ L, x = a
  · exact ⟨a, fun x hx _ _ => Or.inl (hl x hx)⟩
  push Not at hl
  obtain ⟨x, hx, hn⟩ := hl
  exact ⟨b, fun _ _ y hy => Or.inr ((noSquare x a y b
    (h x hx y hy) (h x hx b hb) (h a ha y hy) (h a ha b hb)).resolve_left hn)⟩

theorem firstTrue (C : AndCountCircuit 10) (h : Separates C) (U : Finset V) (hu : C.eval U = true) :
    ∃ i, (∃ a ∈ C.leftVars i, a ∈ U) ∧ (∃ b ∈ C.rightVars i, b ∈ U) := by
  by_contra hn
  have hz (d : ℕ) (i : Fin C.size) : C.gateValFuel U d i = false := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      apply Bool.eq_false_iff.mpr
      simp only [gateValFuel, sideTrue, ih, Bool.false_eq_true,
        and_false, exists_false, or_false]
      exact fun ht => hn ⟨i, by simpa only [Bool.and_eq_true, decide_eq_true_eq] using ht⟩
  rw [eval, decide_eq_true_eq] at hu
  rcases hu with ⟨v, hv, _⟩ | ⟨i, _, ht⟩
  · exact bare_out_empty C h v hv
  · simp [gateVal, hz] at ht


-- All-safe case of the published L-meta-905 boundary problem.
def graph : SimpleGraph V := SimpleGraph.fromRel (fun a b : V =>
  ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
    (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)))

theorem adjacency : ∀ a b : V, graph.Adj a b ↔ related a b = true := by
  unfold graph SimpleGraph.fromRel
  decide +kernel

theorem threeNeighbors : ∀ v : V, (Finset.univ.filter (fun w => related v w = true)).card = 3 := by
  decide +kernel

theorem allSafeImpossible (C : AndCountCircuit 10) (size : C.size ≤ 6)
    (cap : ∀ v : V, (Finset.univ.filter
      (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2)
    (sep : ∀ I : Finset V, (∀ a ∈ I, ∀ c ∈ I, ¬ graph.Adj a c) →
      (∀ w : V, w ∉ I → ∃ a ∈ I, graph.Adj a w) →
      C.eval I = false ∧ ∀ w : V, w ∉ I → C.eval (insert w I) = true)
    (safe : ∀ i j, C.gateVal (rows j) i = false) : False := by
  classical
  have h : Separates C := by
    intro I hI
    apply sep
    · intro a ha c hc hac
      have he := (adjacency a c).mp hac
      rw [hI.1 a ha c hc] at he
      contradiction
    · intro w hw
      obtain ⟨a, ha, hadj⟩ := hI.2 w hw
      exact ⟨a, ha, ((adjacency w a).mpr hadj).symm⟩
  have rect (i : Fin C.size) (a : V) (ha : a ∈ C.leftVars i) (b : V) (hb : b ∈ C.rightVars i) :
      related a b = true := by
    by_contra! hn
    obtain ⟨j, hja, hjb⟩ := jointlyPresent a b (Bool.eq_false_iff.mpr hn)
    have ht : C.gateVal (rows j) i = true := by
      rw [gateVal_unfold, Bool.and_eq_true]
      exact ⟨decide_eq_true (Or.inl ⟨a, ha, hja⟩), decide_eq_true (Or.inl ⟨b, hb, hjb⟩)⟩
    simp [safe] at ht
  choose center hc using fun i => starCenter _ _ (rect i)
  let centers := Finset.univ.image center
  have small : centers.card ≤ C.size := Finset.card_image_le.trans_eq (by simp)
  obtain ⟨v, hv⟩ : ∃ v : V, v ∉ centers := by
    by_contra! hall
    have he : centers = Finset.univ := Finset.eq_univ_of_forall hall
    rw [he, Finset.card_univ, Fintype.card_fin] at small
    omega
  let occ := Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
  have inc : Finset.univ.filter (fun w => related v w = true) ⊆ occ.image center := by
    intro w hw
    obtain ⟨j, hvj, oneEdge⟩ := isolatedEdge v w (Finset.mem_filter.mp hw).2
    obtain ⟨i, ⟨a, ha, hau⟩, ⟨b, hb, hbu⟩⟩ :=
      firstTrue C h _ ((h _ (rowsGood j)).2 v hvj)
    have hcenter : v ≠ center i := by
      intro eq
      apply hv
      exact eq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have hstar := hc i a ha b hb
    rcases oneEdge a hau b hbu (rect i a ha b hb) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl ha⟩,
        (hstar.resolve_left hcenter).symm⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr hb⟩,
        (hstar.resolve_right hcenter).symm⟩
  have bound := (Finset.card_le_card inc).trans (Finset.card_image_le.trans (cap v))
  rw [threeNeighbors] at bound
  omega

end Petersen905

#print axioms Petersen905.allSafeImpossible
