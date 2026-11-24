import TailCnfBound
import RowBridge

namespace PetersenSuffix

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit PetersenTailCnf

variable {n : Nat}

def uses (C : AndCountCircuit n) (v : Fin n) :=
  Finset.univ.filter fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i

def available (C : AndCountCircuit n) (k : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun v => ((uses C v).filter (fun i => i.val < k)).card < 2

def Cap (C : AndCountCircuit n) := ∀ v, (uses C v).card ≤ 2

theorem suffix_available (C : AndCountCircuit n) (cap : Cap C) (k : Nat) (i : Fin C.size)
    (hi : k ≤ i.val) : C.leftVars i ∪ C.rightVars i ⊆ available C k := by
  intro v hv
  let pre := (uses C v).filter (fun g => g.val < k)
  have mem : i ∈ uses C v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_union.mp hv⟩
  have sub : insert i pre ⊆ uses C v := Finset.insert_subset mem (Finset.filter_subset _ _)
  have fresh : i ∉ pre := fun h => (not_lt_of_ge hi) (Finset.mem_filter.mp h).2
  have cnt := (Finset.card_le_card sub).trans (cap v)
  rw [Finset.card_insert_of_notMem fresh] at cnt
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by change pre.card < 2; omega⟩

def head (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) (j : Fin k) : Fin C.size :=
  ⟨j.val,by omega⟩
def tail (C : AndCountCircuit n) (k : Nat) (j : Fin (C.size-k)) : Fin C.size :=
  ⟨k+j.val,by omega⟩

def join (a : Finset (Fin n)) (b : Finset (Fin k)) : Finset (Fin (n+k)) :=
  (a.disjSum b).map finSumFinEquiv.toEmbedding

private theorem hit_join (a x : Finset (Fin n)) (b y : Finset (Fin k)) :
    hit (join a b) (join x y) ↔ hit a x ∨ hit b y := by
  constructor
  · rintro ⟨w,hw,hv⟩
    obtain ⟨v,ha,rfl⟩ := Finset.mem_map.mp hw
    have hb : v ∈ x.disjSum y := by simpa [join] using hv
    cases v with
    | inl p => exact Or.inl ⟨p,Finset.inl_mem_disjSum.mp ha,Finset.inl_mem_disjSum.mp hb⟩
    | inr p => exact Or.inr ⟨p,Finset.inr_mem_disjSum.mp ha,Finset.inr_mem_disjSum.mp hb⟩
  · rintro (⟨p,ha,hb⟩ | ⟨p,ha,hb⟩)
    · exact ⟨_,Finset.mem_map_of_mem _ (Finset.inl_mem_disjSum.mpr ha),
        Finset.mem_map_of_mem _ (Finset.inl_mem_disjSum.mpr hb)⟩
    · exact ⟨_,Finset.mem_map_of_mem _ (Finset.inr_mem_disjSum.mpr ha),
        Finset.mem_map_of_mem _ (Finset.inr_mem_disjSum.mpr hb)⟩

def row (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) (U : Finset (Fin n)) :=
  join (U ∩ available C k) (Finset.univ.filter fun p => C.gateVal U (head C k hk p) = true)

def selector (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) :=
  join B (Finset.univ.filter fun p => head C k hk p ∈ F)

def later (C : AndCountCircuit n) (k : Nat) (F : Finset (Fin C.size)) :=
  Finset.univ.filter fun p => tail C k p ∈ F

-- This is an actual repository circuit with n+k input vertices and C.size-k
-- gates. Input position n+j denotes old gate j for every j below k.
abbrev suffix (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) : AndCountCircuit (n+k) where
  size := C.size-k
  leftVars i := selector C k hk (C.leftVars (tail C k i)) (C.leftGates (tail C k i))
  rightVars i := selector C k hk (C.rightVars (tail C k i)) (C.rightGates (tail C k i))
  leftGates i := later C k (C.leftGates (tail C k i))
  rightGates i := later C k (C.rightGates (tail C k i))
  outVars := selector C k hk C.outVars C.outGates
  outGates := later C k C.outGates

theorem selector_hit (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) (U B : Finset (Fin n))
    (F : Finset (Fin C.size)) (allow : B ⊆ available C k) :
    hit (selector C k hk B F) (row C k hk U) ↔
      (∃ v ∈ B, v ∈ U) ∨ ∃ g ∈ F, g.val < k ∧ C.gateVal U g = true := by
  rw [selector,row,hit_join]
  simp only [hit,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro (⟨v,hv,hu,_⟩ | ⟨g,hg,hu⟩)
    · exact Or.inl ⟨v,hv,hu⟩
    · exact Or.inr ⟨head C k hk g,hg,g.isLt,hu⟩
  · rintro (⟨v,hv,hu⟩ | ⟨g,hg,lo,hu⟩)
    · exact Or.inl ⟨v,hv,hu,allow hv⟩
    · exact Or.inr ⟨⟨g.val,lo⟩,hg,hu⟩

private theorem side_agrees (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size)
    (U B : Finset (Fin n)) (F : Finset (Fin C.size)) (i : Fin (C.size-k))
    (allow : B ⊆ available C k)
    (prior : ∀ j : Fin (C.size-k), j < i →
      (suffix C k hk).gateVal (row C k hk U) j = C.gateVal U (tail C k j)) :
    sideTrue (row C k hk U) (selector C k hk B F) (later C k F) i
      ((suffix C k hk).gateVal (row C k hk U)) =
    sideTrue U B F (tail C k i) (C.gateVal U) := by
  apply decide_eq_decide.mpr
  change (hit _ _ ∨ _) ↔ _
  rw [selector_hit C k hk U B F allow]
  simp only [later, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ((h | ⟨g,hg,lo,hu⟩) | ⟨j,hj,lt,hu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨g,hg,by change g.val < k+i.val; omega,hu⟩
    · exact Or.inr ⟨tail C k j,hj,by change k+j.val < k+i.val; omega,(prior j lt) ▸ hu⟩
  · rintro (h | ⟨g,hg,lt,hu⟩)
    · exact Or.inl (Or.inl h)
    · by_cases lo : g.val < k
      · exact Or.inl (Or.inr ⟨g,hg,lo,hu⟩)
      · let j : Fin (C.size-k) := ⟨g.val-k,by omega⟩
        have he : tail C k j = g := by apply Fin.ext; change k+(g.val-k) = g.val; omega
        have lj : j < i := by change g.val-k < i.val; change g.val < k+i.val at lt; omega
        exact Or.inr ⟨j,he ▸ hg,lj,(prior j lj).trans (he ▸ hu)⟩

theorem gate_agrees (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) (cap : Cap C)
    (U : Finset (Fin n)) (i : Fin (C.size-k)) :
    (suffix C k hk).gateVal (row C k hk U) i = C.gateVal U (tail C k i) := by
  induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin (C.size-k) → Fin (C.size-k) → Prop)).induction) with
  | h i ih =>
    rw [PetersenCnfBridge.gate_equation (suffix C k hk) _ i,
      PetersenCnfBridge.gate_equation C U (tail C k i)]
    have both := suffix_available C cap k (tail C k i) (by change k ≤ k+i.val; omega)
    exact congrArg₂ Bool.and
      (side_agrees C k hk U _ _ i (fun _ h => both (Finset.mem_union_left _ h)) ih)
      (side_agrees C k hk U _ _ i (fun _ h => both (Finset.mem_union_right _ h)) ih)

theorem eval_agrees (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) (cap : Cap C)
    (out : C.outVars ⊆ available C k) (U : Finset (Fin n)) :
    (suffix C k hk).eval (row C k hk U) = C.eval U := by
  apply decide_eq_decide.mpr
  change (hit _ _ ∨ _) ↔ _
  rw [show (suffix C k hk).outVars = selector C k hk C.outVars C.outGates from rfl,
    selector_hit C k hk U _ _ out]
  change ((_ ∨ _) ∨ ∃ j ∈ later C k C.outGates, _) ↔ _
  simp only [later,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ((h | ⟨g,hg,_,hu⟩) | ⟨j,hj,hu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨g,hg,hu⟩
    · exact Or.inr ⟨tail C k j,hj,(gate_agrees C k hk cap U j) ▸ hu⟩
  · rintro (h | ⟨g,hg,hu⟩)
    · exact Or.inl (Or.inl h)
    · by_cases lo : g.val < k
      · exact Or.inl (Or.inr ⟨g,hg,lo,hu⟩)
      · let j : Fin (C.size-k) := ⟨g.val-k,by omega⟩
        have he : tail C k j = g := by apply Fin.ext; change k+(g.val-k) = g.val; omega
        exact Or.inr ⟨j,he ▸ hg,(gate_agrees C k hk cap U j).trans (he ▸ hu)⟩

theorem wellFormed (C : AndCountCircuit n) (k : Nat) (hk : k ≤ C.size) (wf : C.WellFormed) :
    (suffix C k hk).WellFormed := by
  intro i
  constructor <;> intro j hj
  · have mem : tail C k j ∈ C.leftGates (tail C k i) := by simpa [suffix,later] using hj
    have old := (wf (tail C k i)).1 (tail C k j) mem
    change k+j.val < k+i.val at old
    change j.val < i.val; omega
  · have mem : tail C k j ∈ C.rightGates (tail C k i) := by simpa [suffix,later] using hj
    have old := (wf (tail C k i)).2 (tail C k j) mem
    change k+j.val < k+i.val at old
    change j.val < i.val; omega

end PetersenSuffix
