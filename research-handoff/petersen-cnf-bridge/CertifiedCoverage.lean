import OrbitCoverage
import ProductionOrder
import Upstream635

namespace PetersenOrbitCover

open PEqualNP.AndCount PetersenFirstPins

theorem fiveBound : FiveBound := by
  intro C wf sep
  apply (PEqualNP.Outside.L_meta_635 Petersen905.graph ?_).2 C wf
  · intro I independent maximal
    exact sep I independent (fun w hw => by
      obtain ⟨v,hv,adj⟩ := maximal w hw
      exact ⟨v,hv,adj.symm⟩)
  · ext p
    induction p using Sym2.inductionOn with
    | _ a b => simp [SimpleGraph.mem_edgeSet, Petersen905.adjacency, Petersen905.related,
        Petersen905.edges]

theorem cover : (∃ C, Candidate C) → ∃ C l r, Candidate C ∧ Kept l r ∧ FirstSides C l r :=
  coverage fiveBound

theorem of_kept_unsat
    (cases : ∀ l r, Kept l r → (PetersenProduction.lratCase l r).Unsat) :
    PetersenSubmissionBridge.PostedStatement :=
  PetersenProduction.of_lrat_cases Kept cover cases

end PetersenOrbitCover
