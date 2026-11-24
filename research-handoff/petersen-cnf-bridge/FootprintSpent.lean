import FootprintCenters

namespace PetersenFootprintCenters

open PEqualNP.AndCount PetersenSuffix PetersenTailCnf PetersenFirstPins PetersenNormalized
open PetersenBoundary PetersenMixedStar

theorem forced_available (C P : AndCountCircuit 10) (hk : P.size ≤ C.size) (front : Matches C P hk)
    (hc : Candidate C) (shape : Shape C P.size) (v w : V) (edge : ForcedEdge P v w) :
    (uses P v).card < 2 ∧ (uses P w).card < 2 := by
  obtain ⟨g,out,pair⟩ := forced_gate C P hk front hc shape v w edge
  have ok := suffix_available C hc.2.2.1 P.size g ((shape.1 g).mp out)
  rw [matched_available C P hk front] at ok
  have limited (x : V) (h : x ∈ C.leftVars g ∪ C.rightVars g) : (uses P x).card < 2 := by
    have small := (Finset.mem_filter.mp (ok h)).2
    have cut : ((uses P x).filter (fun i => i.val < P.size)) = uses P x :=
      Finset.filter_eq_self.mpr (fun i _ => i.isLt)
    rwa [cut] at small
  rcases pair with ⟨hv,hw⟩ | ⟨hw,hv⟩
  · exact ⟨limited v (Finset.mem_union_left _ hv),limited w (Finset.mem_union_right _ hw)⟩
  · exact ⟨limited v (Finset.mem_union_right _ hv),limited w (Finset.mem_union_left _ hw)⟩

theorem box_spent (B : Box) (l r : Nat) (member : Member B l r) (C : AndCountCircuit 10)
    (hk : 2 ≤ C.size) (front : Matches C (gates B.a B.b l r) hk) (hc : Candidate C) (shape : Shape C 2)
    (p : M) (v w : V) (edge : RowEdge p v w) (blocked : blockedBits B p = true)
    (spent : 2 ≤ count B.a B.b B.ll B.rl v ∨ 2 ≤ count B.a B.b B.ll B.rl w) : False := by
  have limits := forced_available C (gates B.a B.b l r) hk front hc shape v w
    (forces B l r member p v w blocked edge)
  rw [use_count B.a B.b l r v,use_count B.a B.b l r w] at limits
  have hv := count_mono B.a B.b B.ll B.rl l r member.ll member.rl v
  have hw := count_mono B.a B.b B.ll B.rl l r member.ll member.rl w
  omega

end PetersenFootprintCenters
