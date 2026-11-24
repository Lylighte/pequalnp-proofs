import EnvelopeMask

namespace PetersenSecondCube.Envelope

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit PetersenEquivariance
open PetersenFirstPins PetersenBoundary PetersenAutomorphisms PetersenOrbitCover PetersenNormalized

def orbitFits (s : Group) (k : Fin 120) (a b : Mask) : Prop :=
  fitsLoose s (move (permutation k) a) (move (permutation k) b)
instance (s : Group) (k : Fin 120) (a b : Mask) : Decidable (orbitFits s k a b) := by
  unfold orbitFits; infer_instance

theorem orbit_excludes (s : Group) (all : refutesLoose s ⟨0,2047,0,2047⟩)
    (k : Fin 120) (a b : Mask) (fit : orbitFits s k a b) (C : AndCountCircuit 10)
    (hk : 2 ≤ C.size) (sc : FirstSides C a b) (hc : Candidate C) (shape : Shape C 2) : False := by
  let e := permutation k
  let R := relabel C e
  have aut : Auto e := preservesGraph k
  have cap (v) : bareCount R v ≤ 2 := by
    obtain ⟨w,rfl⟩ := e.surjective v
    exact (relabelBare C e w).trans_le (hc.2.2.1 w)
  have hR : Candidate R := ⟨(relabelWF C e).mpr hc.1,hc.2.1,cap,relabelSeparates _ C e aut hc.2.2.2⟩
  obtain ⟨pos,hl,hr⟩ := sc
  have sides : FirstSides R (move e a) (move e b) :=
    ⟨pos,by simp [R,hl,decode_move],by simp [R,hr,decode_move]⟩
  exact fixed_invalid _ _ (all _ _ fit) R hk sides hR (shapeRelabel C 2 e aut shape)

end PetersenSecondCube.Envelope
