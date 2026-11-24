import Mathlib
import Std.Sat.CNF.Relabel

namespace PetersenDimacs

-- Typed alternatives follow the allocation sequence of the six-gate encoder.
-- Signal is a raw vertex or a predecessor gate, Side 0 is left, Side 1 is right.
abbrev Gate := Fin 6
abbrev Vertex := Fin 10
abbrev Side := Fin 2
abbrev Row := Fin 115
abbrev Signal (g : Gate) := Vertex ⊕ Fin g.val
abbrev Selector := (g : Gate) × (Side × Signal g)
-- For each side: one product per predecessor followed by the side OR.
-- After both sides, a single gate AND.
abbrev LocalWire (g : Gate) := (Side × (Fin g.val ⊕ Fin 1)) ⊕ Fin 1
abbrev RowWire := ((g : Gate) × LocalWire g) ⊕ (Gate ⊕ Fin 1)
-- Selector, output gate selector, bare occurrence, or a row-local wire.
abbrev Variable := Selector ⊕ (Gate ⊕ ((Vertex × Gate) ⊕ (Row × RowWire)))

def selectEquiv : Selector ≃ Fin 150 :=
  (Equiv.sigmaCongrRight (fun g : Gate =>
    ((Equiv.refl Side).prodCongr (finSumFinEquiv : Signal g ≃ Fin (10+g.val))).trans
      finProdFinEquiv)).trans (finSigmaFinEquiv.trans (finCongr (by decide +kernel)))

def gateWireEquiv (g : Gate) : LocalWire g ≃ Fin (2*(g.val+1)+1) :=
  ((((Equiv.refl Side).prodCongr (finSumFinEquiv : Fin g.val ⊕ Fin 1 ≃ Fin (g.val+1))).trans
      finProdFinEquiv).sumCongr (Equiv.refl (Fin 1))).trans finSumFinEquiv

def rowGateEquiv : ((g : Gate) × LocalWire g) ≃ Fin 48 :=
  (Equiv.sigmaCongrRight gateWireEquiv).trans
    (finSigmaFinEquiv.trans (finCongr (by decide +kernel)))

def rowEquiv : RowWire ≃ Fin 55 :=
  (rowGateEquiv.sumCongr (finSumFinEquiv : Gate ⊕ Fin 1 ≃ Fin 7)).trans finSumFinEquiv

def index : Variable ≃ Fin 6541 := by
  let rows := ((Equiv.refl Row).prodCongr rowEquiv).trans finProdFinEquiv
  let useAndRows := ((finProdFinEquiv : Vertex × Gate ≃ Fin 60).sumCongr rows).trans finSumFinEquiv
  let outputsAndRest := ((Equiv.refl Gate).sumCongr useAndRows).trans finSumFinEquiv
  exact (selectEquiv.sumCongr outputsAndRest).trans finSumFinEquiv

def id (v : Variable) : ℕ := 1+(index v).val

theorem id_injective : Function.Injective id := by
  intro x y h
  apply index.injective
  apply Fin.ext
  simpa [id] using h

theorem id_range (d : ℕ) : (∃ v, id v = d) ↔ 1 ≤ d ∧ d ≤ 6541 := by
  constructor
  · rintro ⟨v,rfl⟩
    have h := (index v).isLt
    unfold id
    omega
  · rintro ⟨lo,hi⟩
    let f : Fin 6541 := ⟨d-1,by omega⟩
    refine ⟨index.symm f,?_⟩
    simp [id,f]
    omega

def selectOffset : Selector → ℕ
  | ⟨g,s,.inl v⟩ => g.val*(19+g.val) + s.val*(10+g.val) + v.val
  | ⟨g,s,.inr h⟩ => g.val*(19+g.val) + s.val*(10+g.val) + (10+h.val)

def rowOffset : RowWire → ℕ
  | .inl ⟨g,.inl (s,.inl h)⟩ => g.val*(g.val+2) + s.val*(g.val+1) + h.val
  | .inl ⟨g,.inl (s,.inr _)⟩ => g.val*(g.val+2) + s.val*(g.val+1) + g.val
  | .inl ⟨g,.inr _⟩ => g.val*(g.val+2) + 2*g.val+2
  | .inr (.inl g) => 48+g.val
  | .inr (.inr _) => 54

-- Only the 150 selector offsets and 55 row offsets are finite checks. The
-- 115 repeated row blocks are handled symbolically below.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem select_offset_checked : ∀ v : Selector, (selectEquiv v).val = selectOffset v := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem row_offset_checked : ∀ v : RowWire, (rowEquiv v).val = rowOffset v := by decide +kernel

def closedId : Variable → ℕ
  | .inl s => 1+selectOffset s
  | .inr (.inl g) => 151+g.val
  | .inr (.inr (.inl (v,g))) => 157+6*v.val+g.val
  | .inr (.inr (.inr (r,w))) => 217+55*r.val+rowOffset w

theorem closedId_eq_id (v : Variable) : closedId v = id v := by
  rcases v with s | g | ⟨v,g⟩ | ⟨r,w⟩
  · change 1+selectOffset s = 1+(selectEquiv s).val
    rw [select_offset_checked]
  · change 151+g.val = 1+(150+g.val)
    omega
  · change 157+6*v.val+g.val = 1+(150+(6+(g.val+6*v.val)))
    omega
  · change 217+55*r.val+rowOffset w = 1+(150+(6+(60+((rowEquiv w).val+55*r.val))))
    rw [row_offset_checked]
    omega

theorem closedId_injective : Function.Injective closedId := by
  simpa only [funext closedId_eq_id] using id_injective

theorem eval_after_renaming (f : Std.Sat.CNF Variable) (a : ℕ → Bool) :
    (f.relabel closedId).eval a = f.eval (a ∘ closedId) := by simp

theorem unsat_after_renaming (f : Std.Sat.CNF Variable) :
    (f.relabel closedId).Unsat ↔ f.Unsat :=
  Std.Sat.CNF.unsat_relabel_iff fun _ _ h => closedId_injective h

end PetersenDimacs
