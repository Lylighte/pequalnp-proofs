import LooseControl
namespace Cycle1414Sensitivity.Loose
open PEqualNP.Outside.L_meta_1414_aux
private theorem finite : ∀ m : Fin 128, candidate.eval (List.ofFn (atMask m)) =
    ((!atMask m 4) && (!atMask m 5)) := by decide +kernel
theorem value (x : Fin 7 → Bool) : candidate.eval (List.ofFn x) = ((!x 4) && (!x 5)) := by
  obtain ⟨m,rfl⟩ := listed x
  exact finite m
theorem fixed (y z : Fin 7 → Bool) (agree : ∀ i, i ≠ 0 → y i=z i) :
    candidate.eval (List.ofFn y) = candidate.eval (List.ofFn z) := by
  rw [value,value,agree 4 (by decide),agree 5 (by decide)]
end Cycle1414Sensitivity.Loose
#print axioms Cycle1414Sensitivity.Loose.fixed
