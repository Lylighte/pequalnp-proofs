import NormalizedSuffix
import OneHelperCenters

namespace PetersenMixedStar

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenSuffix PetersenTailCnf PetersenFirstPins PetersenNormalized PetersenBoundary
open Petersen905 (related)

abbrev V := Fin 10
abbrev Input := Finset V
abbrev projected (P : AndCountCircuit 10) := row P P.size (Nat.le_refl _)

-- No inequality between x and y: a gate may select a signal on both sides.
def Blocked (P : AndCountCircuit 10) (U : Input) : Prop :=
  ∀ x ∈ projected P U, ∀ y ∈ projected P U, 10 ≤ x.val ∨ 10 ≤ y.val →
    ∃ N ∈ negatives, x ∈ projected P N ∧ y ∈ projected P N

def ForcedEdge (P : AndCountCircuit 10) (v w : V) : Prop :=
  ∃ U ∈ positives, Blocked P U ∧ ∀ a ∈ U, ∀ b ∈ U, related a b = true →
    (a=v ∧ b=w) ∨ (a=w ∧ b=v)

private theorem raw_mem_join (a : Finset (Fin n)) (b : Finset (Fin k)) (v : Fin n) :
    v.castAdd k ∈ join a b ↔ v ∈ a := by
  rw [← finSumFinEquiv_apply_left (n := k) v]
  simp [join]

private theorem raw_visible (C P : AndCountCircuit 10) (hk : P.size ≤ C.size)
    (front : Matches C P hk) (U B : Input) (F : Finset (Fin C.size))
    (x : Fin (10+P.size)) (raw : x.val < 10) (sel : x ∈ selector C P.size hk B F)
    (present : x ∈ projected P U) : ∃ v ∈ B, v ∈ U := by
  let v : V := ⟨x.val,raw⟩
  have eq : v.castAdd P.size = x := Fin.ext rfl
  rw [← eq] at sel present
  have hb := (raw_mem_join B _ v).mp sel
  rw [projected,← matched_row C P hk front U] at present
  have hu := (raw_mem_join (U ∩ available C P.size) _ v).mp present
  exact ⟨v,hb,(Finset.mem_inter.mp hu).1⟩

private theorem projected_side (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (i : Fin C.size) (later : P.size ≤ i.val) (U B : Input) (F : Finset (Fin C.size))
    (use : B ⊆ available C P.size) (wires : ∀ j ∈ F, j.val < P.size) :
    sideTrue U B F i (C.gateVal U) = true ↔ hit (selector C P.size hk B F) (projected P U) := by
  rw [projected,← matched_row C P hk front U,selector_hit C P.size hk U B F use]
  simp only [sideTrue,decide_eq_true_eq]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j,m,_,yes⟩
    exact ⟨j,m,wires j m,yes⟩
  · rintro ⟨j,m,low,yes⟩
    exact ⟨j,m,(show j.val < i.val from lt_of_lt_of_le low later),yes⟩

theorem terminal_gate (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (hc : Candidate C) (shape : Shape C P.size) (g : Fin C.size) (out : g ∈ C.outGates) (U : Input) :
    C.gateVal U g = true ↔
      hit (selector C P.size hk (C.leftVars g) (C.leftGates g)) (projected P U) ∧
      hit (selector C P.size hk (C.rightVars g) (C.rightGates g)) (projected P U) := by
  have atEnd := (shape.1 g).mp out
  have allow := suffix_available C hc.2.2.1 P.size g atEnd
  rw [PetersenCnfBridge.gate_equation C U g,Bool.and_eq_true]
  exact and_congr
    (projected_side C P hk front g atEnd U _ _ (fun _ m => allow (Finset.mem_union_left _ m))
      (fun j m => shape.2.2.1 g j (Or.inl m)))
    (projected_side C P hk front g atEnd U _ _ (fun _ m => allow (Finset.mem_union_right _ m))
      (fun j m => shape.2.2.1 g j (Or.inr m)))

theorem active_pair_bare (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (hc : Candidate C) (shape : Shape C P.size) (g : Fin C.size) (out : g ∈ C.outGates)
    (U : Input) (block : Blocked P U) (x y : Fin (10+P.size))
    (selX : x ∈ selector C P.size hk (C.leftVars g) (C.leftGates g))
    (onX : x ∈ projected P U)
    (selY : y ∈ selector C P.size hk (C.rightVars g) (C.rightGates g))
    (onY : y ∈ projected P U) : x.val < 10 ∧ y.val < 10 := by
  have unmixed : ¬(10 ≤ x.val ∨ 10 ≤ y.val) := by
    intro mixed
    obtain ⟨N,neg,zx,zy⟩ := block x onX y onY mixed
    have yes := (terminal_gate C P hk front hc shape g out N).mpr ⟨⟨x,selX,zx⟩,⟨y,selY,zy⟩⟩
    exact Bool.false_ne_true (((shape.2.1 g).mpr ((shape.1 g).mp out) N neg).symm.trans yes)
  omega

theorem fired_bare_edge (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (hc : Candidate C) (shape : Shape C P.size) (g : Fin C.size) (out : g ∈ C.outGates)
    (U : Input) (block : Blocked P U) (truth : C.gateVal U g = true) :
    ∃ a ∈ C.leftVars g, a ∈ U ∧ ∃ b ∈ C.rightVars g, b ∈ U ∧ related a b = true := by
  obtain ⟨⟨x,selX,onX⟩,⟨y,selY,onY⟩⟩ := (terminal_gate C P hk front hc shape g out U).mp truth
  have raw := active_pair_bare C P hk front hc shape g out U block x y selX onX selY onY
  obtain ⟨a,ha,au⟩ := raw_visible C P hk front U _ _ x raw.1 selX onX
  obtain ⟨b,hb,bu⟩ := raw_visible C P hk front U _ _ y raw.2 selY onY
  exact ⟨a,ha,au,b,hb,bu,PetersenOneHelper.rectangular C hc g out a b ha hb⟩

theorem fixed_center (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (hc : Candidate C) (shape : Shape C P.size) (g : Fin C.size) (out : g ∈ C.outGates) :
    ∃ center : V, (∀ a ∈ C.leftVars g, ∀ b ∈ C.rightVars g, a=center ∨ b=center) ∧
      ∀ U, Blocked P U → C.gateVal U g = true →
        ∃ a ∈ U, ∃ b ∈ U, related a b = true ∧ (a=center ∨ b=center) := by
  obtain ⟨c,star⟩ := Petersen905.starCenter _ _ (fun a ha b hb =>
    PetersenOneHelper.rectangular C hc g out a b ha hb)
  refine ⟨c,star,?_⟩
  intro U blk yes
  obtain ⟨a,ha,au,b,hb,bu,edge⟩ := fired_bare_edge C P hk front hc shape g out U blk yes
  exact ⟨a,au,b,bu,edge,star a ha b hb⟩

private theorem output_count (C : AndCountCircuit 10) (k : Nat) (shape : Shape C k) :
    C.outGates.card = C.size-k := by
  let e : Fin (C.size-k) ↪ Fin C.size :=
    ⟨tail C k,fun a b h => Fin.ext (by have q := congrArg (fun x : Fin C.size => x.val) h
                                       change k+a.val=k+b.val at q; omega)⟩
  have eq : Finset.univ.map e = C.outGates := by
    ext j
    rw [shape.1 j,Finset.mem_map]
    constructor
    · rintro ⟨i,_,rfl⟩
      change k ≤ k+i.val; omega
    · intro h
      let i : Fin (C.size-k) := ⟨j.val-k,by omega⟩
      exact ⟨i,Finset.mem_univ _,Fin.ext (by change k+(j.val-k)=j.val; omega)⟩
  rw [← eq,Finset.card_map,Finset.card_univ,Fintype.card_fin]

-- The same set of centers meets all forced edges, across all positive rows.
theorem cover_by_centers (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (hc : Candidate C) (shape : Shape C P.size) :
    ∃ S : Finset V, S.card ≤ C.size-P.size ∧ ∀ v w, ForcedEdge P v w → v ∈ S ∨ w ∈ S := by
  classical
  let center (g : Fin C.size) := if h : g ∈ C.outGates then
    (fixed_center C P hk front hc shape g h).choose else 0
  refine ⟨C.outGates.image center,Finset.card_image_le.trans (output_count C P.size shape).le,?_⟩
  intro v w force
  obtain ⟨U,hU,block,unique⟩ := force
  have on := ((separationIff C).mp hc.2.2.2).2 U hU
  rw [AndCountCircuit.eval,decide_eq_true_eq] at on
  rcases on with ⟨x,hx,_⟩ | ⟨g,out,yes⟩
  · simp [shape.2.2.2] at hx
  · have spec := (fixed_center C P hk front hc shape g out).choose_spec.2 U block yes
    obtain ⟨a,au,b,bu,edge,cent⟩ := spec
    have cm : center g ∈ C.outGates.image center := Finset.mem_image_of_mem center out
    have which : a=center g ∨ b=center g := by simpa [center,out] using cent
    rcases unique a au b bu edge with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> grind

theorem matching_bound {I : Type} [Fintype I] (C P : AndCountCircuit 10) (hk : P.size ≤ C.size)
    (front : Matches C P hk) (hc : Candidate C) (shape : Shape C P.size) (edge : I → V × V)
    (disjoint : ∀ i j v, (v=(edge i).1 ∨ v=(edge i).2) → (v=(edge j).1 ∨ v=(edge j).2) → i=j)
    (forced : ∀ i, ForcedEdge P (edge i).1 (edge i).2) : Fintype.card I ≤ C.size-P.size := by
  classical
  obtain ⟨S,bound,cover⟩ := cover_by_centers C P hk front hc shape
  have picked (i : I) : ∃ v : S, v.val=(edge i).1 ∨ v.val=(edge i).2 := by
    rcases cover _ _ (forced i) with a | b
    · exact ⟨⟨_,a⟩,Or.inl rfl⟩
    · exact ⟨⟨_,b⟩,Or.inr rfl⟩
  choose pick mem using picked
  have inj : Function.Injective pick := by
    intro i j eq
    exact disjoint i j (pick i).val (mem i) (eq ▸ mem j)
  exact (by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective pick inj :
    Fintype.card I ≤ S.card).trans bound

theorem forced_gate (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (hc : Candidate C) (shape : Shape C P.size) (v w : V) (force : ForcedEdge P v w) :
    ∃ g ∈ C.outGates, (v ∈ C.leftVars g ∧ w ∈ C.rightVars g) ∨
      (w ∈ C.leftVars g ∧ v ∈ C.rightVars g) := by
  obtain ⟨U,hU,block,unique⟩ := force
  have on := ((separationIff C).mp hc.2.2.2).2 U hU
  rw [AndCountCircuit.eval,decide_eq_true_eq] at on
  rcases on with ⟨x,hx,_⟩ | ⟨g,out,yes⟩
  · simp [shape.2.2.2] at hx
  · obtain ⟨a,ha,au,b,hb,bu,edge⟩ := fired_bare_edge C P hk front hc shape g out U block yes
    refine ⟨g,out,?_⟩
    rcases unique a au b bu edge with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨ha,hb⟩

-- If v is not a chosen center, all its distinct forced neighbors must be
-- centers of distinct suffix gates which use v. The prefix use count is
-- exactly the original per-gate count, including gates reading v on both sides.
theorem degree_bound (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (hc : Candidate C) (shape : Shape C P.size) (T : Finset V) (neighbors : V → Finset V)
    (forced : ∀ v ∈ T, ∀ w ∈ neighbors v, ForcedEdge P v w)
    (high : ∀ v ∈ T, 2 < (neighbors v).card + (uses P v).card) : T.card ≤ C.size-P.size := by
  classical
  let center (g : Fin C.size) := if h : g ∈ C.outGates then
    (fixed_center C P hk front hc shape g h).choose else 0
  have cs (g : Fin C.size) (out : g ∈ C.outGates) (a) (ha : a ∈ C.leftVars g)
      (b) (hb : b ∈ C.rightVars g) : a=center g ∨ b=center g := by
    simpa [center,out] using (fixed_center C P hk front hc shape g out).choose_spec.1 a ha b hb
  have all : T ⊆ C.outGates.image center := by
    intro v hv
    by_contra absent
    let S := (uses C v).filter fun i => P.size ≤ i.val
    have sub : neighbors v ⊆ S.image center := by
      intro w hw
      obtain ⟨g,out,cover⟩ := forced_gate C P hk front hc shape v w (forced v hv w hw)
      have no : v ≠ center g := fun e => absent (e ▸ Finset.mem_image_of_mem center out)
      have ge := (shape.1 g).mp out
      rcases cover with ⟨l,r⟩ | ⟨l,r⟩
      · exact Finset.mem_image.mpr ⟨g,Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl l⟩,ge⟩,((cs g out v l w r).resolve_left no).symm⟩
      · exact Finset.mem_image.mpr ⟨g,Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr r⟩,ge⟩,((cs g out w l v r).resolve_right no).symm⟩
    have bound := (Finset.card_le_card sub).trans Finset.card_image_le
    have old := prefix_count C P.size hk v
    simp only [front.left,front.right] at old
    change ((uses C v).filter (fun i => i.val < P.size)).card = (uses P v).card at old
    have partition := Finset.card_filter_add_card_filter_not (s := uses C v) (fun i => i.val < P.size)
    simp only [not_lt,old] at partition
    change (uses P v).card + S.card = (uses C v).card at partition
    have lim : (uses C v).card ≤ 2 := hc.2.2.1 v
    have hdeg := high v hv
    omega
  exact (Finset.card_le_card all).trans (Finset.card_image_le.trans (output_count C P.size shape).le)

-- Finite certificate interface. x=y is included in the two range loops.
def mixedBits (k : Nat) (pos : Nat) (neg : Fin 1024 → Nat) : Bool :=
  (List.finRange (10+k)).all fun x => (List.finRange (10+k)).all fun y =>
    if pos.testBit x.val && pos.testBit y.val && decide (10 ≤ x.val ∨ 10 ≤ y.val) then
      negativeMasks.any (fun m => (neg m).testBit x.val && (neg m).testBit y.val)
    else true

theorem blocked_of_bits (P : AndCountCircuit 10) (U : Input) (pos : Nat) (neg : Fin 1024 → Nat)
    (pRow : projected P U = bits (10+P.size) pos)
    (nRow : ∀ m ∈ negativeMasks, projected P (decode m) = bits (10+P.size) (neg m))
    (cert : mixedBits P.size pos neg = true) : Blocked P U := by
  intro x hx y hy mixed
  rw [pRow] at hx hy
  have testX := (Finset.mem_filter.mp hx).2
  have testY := (Finset.mem_filter.mp hy).2
  have cx := List.all_eq_true.mp cert x (List.mem_finRange x)
  have cxy := List.all_eq_true.mp cx y (List.mem_finRange y)
  simp only [testX,testY,mixed,decide_true,Bool.true_and,ite_true] at cxy
  obtain ⟨m,hm,on⟩ := List.any_eq_true.mp cxy
  have signs := Bool.and_eq_true_iff.mp on
  refine ⟨decode m,Finset.mem_image_of_mem _ (by simpa using hm),?_⟩
  rw [nRow m hm]
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,signs.1⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,signs.2⟩⟩

end PetersenMixedStar
