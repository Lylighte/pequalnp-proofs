import FirstGatePins
import Std.Sat.CNF.Dimacs
import Std.Tactic.BVDecide.LRAT.Checker

namespace PetersenProduction

open Std.Sat PetersenCnfBridge PetersenDimacs PetersenExport PetersenFirstPins

-- The JS disjunction emits its binary clauses before its long clause.
-- In all the other multi-clause blocks the first clause is already binary.
def reorder (cs : List (CNF.Clause α)) : List (CNF.Clause α) :=
  match cs with
  | [] => []
  | c :: rest => if 2 < c.size then rest ++ [c] else c :: rest

def productionBlock (f : CNF α) : CNF α :=
  ⟨((reorder f.clauses.toList).map fun c => CNF.Clause.ofLiterals c.literals.reverse).toArray⟩

theorem reorder_all (cs : List (CNF.Clause α)) (p : CNF.Clause α → Bool) :
    (reorder cs).all p = cs.all p := by
  cases cs with
  | nil => rfl
  | cons c cs => simp [reorder, apply_ite (List.all · p), Bool.and_comm]

theorem block_eval (f : CNF α) (a : α → Bool) :
    (productionBlock f).eval a = f.eval a := by
  simp [productionBlock, CNF.eval, List.all_map, Function.comp_def,
    CNF.Clause.eval, reorder_all]

def sourceBlocks : List (CNF Variable) :=
  capBlocks ++ (List.finRange 115).flatMap fun r =>
    let p := points[r.val]?.getD (0,false)
    rowBlocks r p.1 p.2

def formula : CNF Variable :=
  ⟨sourceBlocks.toArray.flatMap (fun f => (productionBlock f).clauses)⟩

private theorem flatten_eval (fs : List (CNF α)) (a : α → Bool) :
    (⟨fs.toArray.flatMap (fun f => (productionBlock f).clauses)⟩ : CNF α).eval a =
    (⟨fs.toArray.flatMap CNF.clauses⟩ : CNF α).eval a := by
  simp only [CNF.eval, Array.all_flatMap]
  change (fs.toArray.all (fun f => (productionBlock f).eval a)) =
    fs.toArray.all (fun f => f.eval a)
  simp only [block_eval]

theorem formula_eval (a : Variable → Bool) : formula.eval a = symbolicFormula.eval a :=
  flatten_eval sourceBlocks a

def numberedBase := formula.relabel closedId
def numberedCase (l r : Mask) := (formula ++ pins l r).relabel closedId

theorem numbered_eval (a : Nat → Bool) :
    numberedBase.eval a = (symbolicFormula.relabel closedId).eval a := by
  simpa only [numberedBase, eval_after_renaming] using formula_eval (a ∘ closedId)

theorem case_eval (l r : Mask) (a : Nat → Bool) :
    (numberedCase l r).eval a = (numbered l r).eval a := by
  simp only [numberedCase, numbered, pinned, eval_after_renaming, CNF.eval_append, formula_eval]

theorem of_production_cases (kept : Mask → Mask → Prop)
    (cover : (∃ C, Candidate C) → ∃ C l r, Candidate C ∧ kept l r ∧ FirstSides C l r)
    (unsat : ∀ l r, kept l r → (numberedCase l r).Unsat) :
    PetersenSubmissionBridge.PostedStatement := by
  apply of_numbered_cases kept cover
  intro l r hk a
  rw [← case_eval]
  exact unsat l r hk a

-- Lean's LRAT reader and CNF.dimacs use 0-based Nat atoms and print atom + 1.
def atomId (v : Variable) : Nat := closedId v - 1
def lratBase : CNF Nat := formula.relabel atomId
def lratCase (l r : Mask) : CNF Nat := (formula ++ pins l r).relabel atomId

theorem dimacs_atom (v : Variable) : atomId v + 1 = closedId v := by
  simp only [atomId, closedId_eq_id, PetersenDimacs.id]
  omega

theorem atom_injective : Function.Injective atomId := by
  intro x y h
  apply closedId_injective
  rw [← dimacs_atom x, ← dimacs_atom y, h]

-- This is the physical order of all twenty LRAT atoms for every pinned case.
theorem pin_layout (l r : Mask) :
    ((pins l r).relabel atomId).clauses.toList.map CNF.Clause.literals =
      (List.finRange 2).flatMap (fun s => (List.finRange 10).map (fun v =>
        [(s.val * 10 + v.val, (if s = 0 then l else r).val.testBit v.val)])) := by
  simp [pins, pack, packClause, CNF.relabel,
    atomId, closedId, bare, selectOffset, List.map_flatMap, List.map_map, Function.comp_def]

theorem of_lrat_cases (kept : Mask → Mask → Prop)
    (cover : (∃ C, Candidate C) → ∃ C l r, Candidate C ∧ kept l r ∧ FirstSides C l r)
    (unsat : ∀ l r, kept l r → (lratCase l r).Unsat) :
    PetersenSubmissionBridge.PostedStatement := by
  apply of_production_cases kept cover
  intro l r hk
  apply (unsat_after_renaming _).mpr
  exact (CNF.unsat_relabel_iff (f := formula ++ pins l r)
    (fun _ _ h => atom_injective h)).mp (unsat l r hk)

end PetersenProduction

namespace PetersenTrace

open Std.Tactic.BVDecide PetersenProduction PetersenFirstPins

theorem of_checked_lrat (kept : Mask → Mask → Prop)
    (cover : (∃ C, Candidate C) → ∃ C l r, Candidate C ∧ kept l r ∧ FirstSides C l r)
    (certificates : ∀ l r, kept l r → ∃ t, LRAT.check t (lratCase l r) = true) :
    PetersenSubmissionBridge.PostedStatement := by
  apply of_lrat_cases kept cover
  intro l r hk
  obtain ⟨t, ok⟩ := certificates l r hk
  exact LRAT.check_sound t (lratCase l r) ok

end PetersenTrace
