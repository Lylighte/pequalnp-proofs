import DiagonalNumericBridge
import FootprintPolar

namespace PetersenDiagonalShapeTwo

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PetersenSuffix PetersenTailCnf PetersenFirstPins PetersenNormalized PetersenBoundary
open PetersenMixedStar (Input)
open PetersenFootprintCenters PetersenFootprintPolar PetersenDiagonalStars

def merge (S B : Input) (reads : Bool) := if reads then B ∪ S else B

private theorem merged (S B U : Input) (reads : Bool) :
    hit (merge S B reads) U ↔ hit B U ∨ reads=true ∧ hit S U := by
  cases reads <;> simp [merge]

def bareSide (s l : Nat) := merge (bits 10 s) (bits 10 l) (l.testBit 10)

private theorem side_spec (s l : Nat) (m : M) :
    side s s l m = true ↔ hit (bareSide s l) (decode m) := by
  rw [bareSide,merged]
  simp only [side,h0,Bool.and_self,Bool.or_eq_true,Bool.and_eq_true,raw_iff,hit]

def joinPorts (s : Nat) (p q : Port) : Term :=
  ⟨merge (bits 10 s) p.vars p.z,merge (bits 10 s) q.vars q.z,p.o,q.o⟩

private theorem active (p : Port) (s l r : Nat) (m : M) :
    sensed p (decode m) (h0 s s m) (h1 s s l r m) ↔
    hit (merge (bits 10 s) p.vars p.z) (decode m) ∨
      p.o=true ∧ (hit (bareSide s l) (decode m) ∧ hit (bareSide s r) (decode m)) := by
  rw [merged]
  simp only [sensed,h0,h1,Bool.and_self,Bool.and_eq_true,side_spec,raw_iff,hit,or_assoc]

theorem no_candidate (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (hc : Candidate C)
    (shape : Shape C 2) (s : Fin 1024) (first : FirstSides C s s) : False := by
  obtain ⟨l,r,front⟩ := actual_prefix C hk hc.1 s s first
  let bx : Box := ⟨s,s,l,l,r,r,0,0⟩
  let f (i : Fin (C.size-2)) := joinPorts s (left C hk i) (right C hk i)
  let A := bareSide s l
  let B := bareSide s r
  have eqv (m : M) : C.eval (decode m) = true ↔ ∃ i, (f i).fires (decode m)
      (hit A (decode m) ∧ hit B (decode m)) := by
    refine (old_outputs bx l r C hk front shape m).trans ?_
    apply exists_congr; intro i
    exact and_congr (active _ s l r m) (active _ s l r m)
  have unsafeGate : ∃ n ∈ negatives, C.gateVal n (head C 2 hk 1) = true := by
    by_contra! no
    have bad := (shape.2.1 (head C 2 hk 1)).mp (fun U hu => Bool.eq_false_iff.mpr (no U hu))
    exact (by decide : ¬2 ≤ 1) bad
  obtain ⟨n,hn,on⟩ := unsafeGate
  obtain ⟨m,_,rfl⟩ : ∃ m ∈ negativeMasks, decode m = n := by simpa [negatives] using hn
  have eqg := (matched_gate C (gates s s l r) hk front (decode m) 1).trans (second_eval ..)
  have activeH : h1 s s l r m = true := eqg.symm.trans on
  have both := Bool.and_eq_true_iff.mp activeH
  have pos : ∀ U ∈ positives, ∃ i, (f i).fires U (hit A U ∧ hit B U) := by
    intro U hu
    obtain ⟨q,_,rfl⟩ : ∃ q ∈ positiveMasks, decode q = U := by simpa [positives] using hu
    exact (eqv q).mp (((separationIff C).mp hc.2.2.2).2 _ hu)
  have neg : ∀ U ∈ negatives, ∀ i, ¬(f i).fires U (hit A U ∧ hit B U) := by
    intro U hu i fires
    obtain ⟨q,_,rfl⟩ : ∃ q ∈ negativeMasks, decode q = U := by simpa [negatives] using hu
    exact Bool.false_ne_true ((((separationIff C).mp hc.2.2.2).1 _ hu).symm.trans
      ((eqv q).mpr ⟨i,fires⟩))
  obtain ⟨sketch⟩ := from_terminals (C.size-2) (by have lim := hc.2.1; omega) A B f
    ⟨decode m,hn,(side_spec _ _ _).mp both.1,(side_spec _ _ _).mp both.2⟩ pos neg
  exact sketch_impossible sketch

end PetersenDiagonalShapeTwo

#print axioms PetersenDiagonalShapeTwo.no_candidate
