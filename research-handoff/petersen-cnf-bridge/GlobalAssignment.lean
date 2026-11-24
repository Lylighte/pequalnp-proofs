import CircuitBridge
import ExportDimacs

namespace PetersenGlobal

open Std.Sat PetersenCnfBridge PetersenDimacs PetersenExport

def point (r : Row) : Nat × Bool := points[r.val]?.getD (0,false)
def pointSet (r : Row) : Finset Vertex := Finset.univ.filter (fun v => (point r).1.testBit v.val)

structure Values where
  atom : Gate → Side → Vertex → Bool
  wire : (g : Gate) → Side → Fin g.val → Bool
  out : Gate → Bool
  gate : Row → Gate → Bool

def earlier {g : Gate} (h : Fin g.val) : Gate := ⟨h.val, by omega⟩

def bitSide (d : Values) (r : Row) (g : Gate) (s : Side) : Bool :=
  decide ((∃ v : Vertex, (point r).1.testBit v.val = true ∧ d.atom g s v = true) ∨
    ∃ h : Fin g.val, d.wire g s h = true ∧ d.gate r (earlier h) = true)

def bitResult (d : Values) (r : Row) : Bool :=
  decide (∃ g : Gate, d.out g = true ∧ d.gate r g = true)

def bitUsed (d : Values) (v : Vertex) (g : Gate) := d.atom g 0 v || d.atom g 1 v

def assignment (d : Values) : Variable → Bool
  | .inl ⟨g,s,.inl v⟩ => d.atom g s v
  | .inl ⟨g,s,.inr h⟩ => d.wire g s h
  | .inr (.inl g) => d.out g
  | .inr (.inr (.inl (v,g))) => bitUsed d v g
  | .inr (.inr (.inr (r,.inl ⟨g,.inl (s,.inl h)⟩))) => d.wire g s h && d.gate r (earlier h)
  | .inr (.inr (.inr (r,.inl ⟨g,.inl (s,.inr _)⟩))) => bitSide d r g s
  | .inr (.inr (.inr (r,.inl ⟨g,.inr _⟩))) => d.gate r g
  | .inr (.inr (.inr (r,.inr (.inl g)))) => d.out g && d.gate r g
  | .inr (.inr (.inr (r,.inr (.inr _)))) => bitResult d r

theorem cap_holds (d : Values) (cap : ∀ v, tripleClauses (bitUsed d v)) :
    ∀ f ∈ capBlocks, f.eval (assignment d) = true := by
  simp only [capBlocks,List.forall_mem_flatMap,List.forall_mem_append,List.forall_mem_map,
    List.forall_mem_filter,List.mem_finRange, true_implies, decide_eq_true_eq]
  intro v
  constructor
  · intro g
    rw [orBlock_valid]
    simp [used,bare,assignment,bitUsed]
  · intro a b hba c hcb
    have why := cap v a b c hcb hba
    simpa [pack, CNF.eval, packClause,used,assignment] using why

theorem row_holds (d : Values) (r : Row)
    (gate_ok : ∀ g, d.gate r g = (bitSide d r g 0 && bitSide d r g 1))
    (label_ok : bitResult d r = (point r).2) :
    ∀ f ∈ rowBlocks r (point r).1 (point r).2, f.eval (assignment d) = true := by
  simp only [rowBlocks,List.forall_mem_flatMap,List.forall_mem_append,List.forall_mem_map,
    List.forall_mem_cons,List.not_mem_nil, false_implies, implies_true, and_true,
    List.mem_finRange,true_implies]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro g
    constructor
    · intro s
      constructor
      · intro h
        exact (andBlock_valid ..).mpr rfl
      · rw [orBlock_valid]
        simp [bitSide,assignment,sideV,rwVar,bare,productV,earlier,List.mem_finRange,
          or_and_right,exists_or]
        grind
    · exact (andBlock_valid ..).mpr (gate_ok g)
  · intro g
    exact (andBlock_valid ..).mpr rfl
  · constructor
    · rw [orBlock_valid]
      simp [bitResult,result,outProduct,assignment,rwVar,List.mem_finRange]
    · simp [pack,CNF.eval,packClause,assignment,result,rwVar,label_ok]

private theorem gather {α : Type} (ls : List (CNF α)) (a : α → Bool)
    (h : ∀ f ∈ ls, f.eval a = true) :
    (⟨ls.toArray.flatMap CNF.clauses⟩ : CNF α).eval a = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro c hc
  obtain ⟨f,hf,hm⟩ := Array.mem_flatMap.mp hc
  exact (Array.all_eq_true_iff_forall_mem.mp (h f (by simpa using hf))) c hm

theorem all_holds (d : Values) (cap : ∀ v, tripleClauses (bitUsed d v))
    (gate_ok : ∀ r g, d.gate r g = (bitSide d r g 0 && bitSide d r g 1))
    (labels : ∀ r, bitResult d r = (point r).2) :
    symbolicFormula.eval (assignment d) = true := by
  have each : ∀ f ∈ capBlocks ++ (List.finRange 115).flatMap
      (fun r => rowBlocks r (point r).1 (point r).2), f.eval (assignment d) = true := by
    rw [List.forall_mem_append]
    exact ⟨cap_holds d cap, List.forall_mem_flatMap.mpr
      fun r _ => row_holds d r (gate_ok r) (labels r)⟩
  exact gather _ _ each

end PetersenGlobal
