import Residual
import TightControl
namespace Cycle1414Sensitivity.Control
open PEqualNP.Outside.L_meta_1414_aux
theorem standard (p q : Fin 7) (different : p ≠ q) (b : Bool) :
    ∃ y z : Fin 7 → Bool, y p=false ∧ z p=true ∧ y q=b ∧ z q=b ∧
      (∀ i, i≠p → y i=z i) ∧ candidate.eval (List.ofFn y)=false ∧ candidate.eval (List.ofFn z)=true :=
  Cycle1414Sensitivity.circuit candidate cycleOK p q different b
end Cycle1414Sensitivity.Control
#print axioms Cycle1414Sensitivity.Control.standard
