import DiagonalShapeTwo

namespace PetersenLightPolar

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenSuffix PetersenTailCnf PetersenFirstPins PetersenNormalized PetersenBoundary
open PetersenFootprintCenters PetersenFootprintPolar PetersenDiagonalStars
open PetersenMixedStar (Input)

def replacedPort (s : Nat) (p q : Port) : Term :=
  ⟨inlineVars s p,inlineVars s q,inlineGate s p,inlineGate s q⟩

private theorem sensed_replacement (s a b : Nat) (p : Port) (m : M) :
    sensed p (decode m) (h0 a b m) (side a b s m) ↔
      hit (inlineVars s p) (decode m) ∨ inlineGate s p = true ∧
        (hit (bits 10 a) (decode m) ∧ hit (bits 10 b) (decode m)) := by
  rcases p with ⟨vars,z,o⟩
  cases z <;> cases o <;> cases eq : s.testBit 10 <;>
    simp [-Finset.mem_union,sensed,side,h0,inlineVars,inlineGate,eq,raw_iff,hit_union] <;>
    unfold hit <;> grind only

theorem replacement (a b l r s : Nat) (C : AndCountCircuit 10) (hk : 2 ≤ C.size)
    (front : Matches C (gates a b l r) hk) (hc : Candidate C) (shape : Shape C 2)
    (negStep : ∀ m ∈ negativeMasks, side a b s m = true → h1 a b l r m = true)
    (posStep : ∀ m ∈ positiveMasks, h1 a b l r m = true → side a b s m = true) : False := by
  let bx : Box := ⟨a,b,l,l,r,r,0,0⟩
  let L := left C hk
  let R := right C hk
  let f (i : Fin (C.size-2)) := replacedPort s (L i) (R i)
  let A := bits 10 a
  let B := bits 10 b
  have eqv (m : M) : outputs L R (decode m) (h0 a b m) (side a b s m) ↔
      ∃ i, (f i).fires (decode m) (hit A (decode m) ∧ hit B (decode m)) := by
    apply exists_congr; intro i
    exact and_congr (sensed_replacement _ _ _ _ _) (sensed_replacement _ _ _ _ _)
  have old (m : M) := old_outputs bx l r C hk front shape m
  have labels := (separationIff C).mp hc.2.2.2
  have unsafeGate : ∃ n ∈ negatives, C.gateVal n (head C 2 hk 0) = true := by
    by_contra! no
    have bad := (shape.2.1 (head C 2 hk 0)).mp (fun U hu => Bool.eq_false_iff.mpr (no U hu))
    exact (by decide : ¬2 ≤ 0) bad
  obtain ⟨n,hn,on⟩ := unsafeGate
  obtain ⟨m,_,rfl⟩ : ∃ m ∈ negativeMasks, decode m = n := by simpa [negatives] using hn
  have eqg := (matched_gate C (gates a b l r) hk front (decode m) 0).trans (first_eval ..)
  have activeH : h0 a b m = true := eqg.symm.trans on
  have both := Bool.and_eq_true_iff.mp activeH
  have pos : ∀ U ∈ positives, ∃ i, (f i).fires U (hit A U ∧ hit B U) := by
    intro U hu
    obtain ⟨q,mem,rfl⟩ : ∃ q ∈ positiveMasks, decode q = U := by simpa [positives] using hu
    exact (eqv q).mp (outputs_mono L R _ _ _ _ (posStep q mem) ((old q).mp (labels.2 _ hu)))
  have neg : ∀ U ∈ negatives, ∀ i, ¬(f i).fires U (hit A U ∧ hit B U) := by
    intro U hu i fires
    obtain ⟨q,mem,rfl⟩ : ∃ q ∈ negativeMasks, decode q = U := by simpa [negatives] using hu
    have out := outputs_mono L R _ _ _ _ (negStep q mem) ((eqv q).mpr ⟨i,fires⟩)
    exact Bool.false_ne_true ((labels.1 _ hu).symm.trans ((old q).mpr out))
  obtain ⟨sketch⟩ := from_terminals (C.size-2) (by have lim := hc.2.1; omega) A B f
    ⟨decode m,hn,(raw_iff _ _).mp both.1,(raw_iff _ _).mp both.2⟩ pos neg
  exact sketch_impossible sketch

theorem box_polar (B : Box) (l r s : Nat) (member : Member B l r) (cert : polarCheck B s = true)
    (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (front : Matches C (gates B.a B.b l r) hk)
    (hc : Candidate C) (shape : Shape C 2) : False := by
  have checks := Bool.and_eq_true_iff.mp cert
  apply replacement B.a B.b l r s C hk front hc shape
  · intro m mem yes
    have ok := List.all_eq_true.mp checks.1 m mem
    simpa [yes,neg_eq B l r member m mem] using ok
  · intro m mem yes
    have hi := pos_upper B l r member m yes
    have ok := List.all_eq_true.mp checks.2 m mem
    simpa [hi] using ok

end PetersenLightPolar

#print axioms PetersenLightPolar.box_polar
