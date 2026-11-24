import PEqualNP.Defs

namespace Cycle1414Sensitivity
open PEqualNP.CircuitLowerBounds
abbrev Input := Fin 7 → Bool
abbrev Edge (x : Input) := ∃ i : Fin 7, x i = true ∧ x (i + 1) = true

def lower (q r : Fin 7) (b : Bool) : Input := fun i => (b && decide (i=q)) || decide (i=r)
def raise (x : Input) (p : Fin 7) : Input := fun i => x i || decide (i=p)

set_option maxHeartbeats 5000000 in
theorem shortWitness : ∀ p q : Fin 7, p ≠ q → ∀ b : Bool, ∃ r : Fin 7,
    lower q r b p = false ∧ lower q r b q = b ∧ ¬ Edge (lower q r b) ∧ Edge (raise (lower q r b) p) := by
  decide +kernel

theorem residual (p q : Fin 7) (distinct : p ≠ q) (b : Bool) :
    ∃ y z : Input, y p = false ∧ z p = true ∧ y q = b ∧ z q = b ∧
      (∀ i, i ≠ p → y i = z i) ∧ ¬ Edge y ∧ Edge z := by
  obtain ⟨r,lo,hq,no,yes⟩ := shortWitness p q distinct b
  refine ⟨lower q r b,raise (lower q r b) p,lo,?_,hq,?_,?_,no,yes⟩
  · simp [raise]
  · simp [raise,Ne.symm distinct,hq]
  · intro i hi
    simp [raise,hi]

theorem circuit (C : Circuit) (correct : ∀ x : Input, C.eval (List.ofFn x) = true ↔ Edge x)
    (p q : Fin 7) (distinct : p ≠ q) (b : Bool) :
    ∃ y z : Input, y p = false ∧ z p = true ∧ y q = b ∧ z q = b ∧
      (∀ i, i ≠ p → y i = z i) ∧ C.eval (List.ofFn y) = false ∧ C.eval (List.ofFn z) = true := by
  obtain ⟨y,z,lo,hi,yq,zq,agree,no,yes⟩ := residual p q distinct b
  exact ⟨y,z,lo,hi,yq,zq,agree,Bool.eq_false_iff.mpr (fun h => no ((correct y).mp h)), (correct z).mpr yes⟩

end Cycle1414Sensitivity
