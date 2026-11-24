import EnvelopeOrbit

namespace PetersenSecondCube.Envelope.Atlas

open PEqualNP.AndCount PetersenFirstPins PetersenNormalized PetersenBoundary

structure Entry where
  a : Fin 1024
  b : Fin 1024
  k : Fin 120
  deriving DecidableEq

def excludes (r : Entry) := ∀ (C : AndCountCircuit 10), 2 ≤ C.size → FirstSides C r.a r.b →
  Candidate C → Shape C 2 → False

theorem localProof (s : Group) (Q : Rect) (bytes : String)
    (h : program s Q (bytes.toList.map (fun c => c.toNat-65))=true) : refutesLoose s Q :=
  program_loose s Q _ h

theorem members (s : Group) (root : refutesLoose s ⟨0,2047,0,2047⟩) (rs : List Entry)
    (ok : rs.all (fun r => decide (orbitFits s r.k r.a r.b))=true) :
    ∀ r∈rs, excludes r := by
  intro r hr
  exact orbit_excludes s root r.k r.a r.b (of_decide_eq_true (List.all_eq_true.mp ok r hr))

theorem combine (L R : List Entry) (l : ∀ r∈L, excludes r) (r : ∀ t∈R, excludes t) :
    ∀ t∈L++R, excludes t := fun t h => (List.mem_append.mp h).elim (l t) (r t)

end PetersenSecondCube.Envelope.Atlas
