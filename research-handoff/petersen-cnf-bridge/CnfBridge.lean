import Mathlib
import Std.Sat.CNF.Sat
import PEqualNP.Defs.AndCountCircuit

namespace PetersenCnfBridge

open Std.Sat
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

variable {α : Type}

def packClause : List (Literal α) → CNF.Clause α
  | [] => .empty
  | (x, p) :: xs => (packClause xs).add x p

def pack (xs : List (List (Literal α))) : CNF α :=
  ⟨(xs.map packClause).toArray⟩

theorem packClause_valid (a : α → Bool) (ls : List (Literal α)) :
    (packClause ls).eval a = true ↔ ∃ l ∈ ls, a l.1 = l.2 := by
  induction ls with
  | nil => simp [packClause]
  | cons l ls ih =>
    rcases l with ⟨x,p⟩
    simp [packClause, ih]

theorem pack_valid (a : α → Bool) (ls : List (List (Literal α))) :
    (pack ls).eval a = true ↔ ∀ c ∈ ls, ∃ l ∈ c, a l.1 = l.2 := by
  simp [pack, CNF.eval, packClause_valid]

def andBlock (x y z : α) : CNF α := pack [
  [(z,false),(x,true)], [(z,false),(y,true)], [(z,true),(x,false),(y,false)]]

theorem andBlock_valid (a : α → Bool) (x y z : α) :
    (andBlock x y z).eval a = true ↔ a z = (a x && a y) := by
  cases hx : a x <;> cases hy : a y <;> cases hz : a z <;>
    simp [andBlock, pack, CNF.eval, packClause, hx, hy, hz]

def orBlock (xs : List α) (z : α) : CNF α := pack
  (((z,false) :: xs.map (fun x => (x,true))) ::
    xs.map (fun x => [(x,false),(z,true)]))

theorem orBlock_valid (a : α → Bool) (xs : List α) (z : α) :
    (orBlock xs z).eval a = true ↔ (a z = true ↔ ∃ x ∈ xs, a x = true) := by
  rw [orBlock, pack_valid]
  cases hz : a z <;> simp [hz, exists_or]

-- The positive inputs are fresh atoms of the left summand. The right summand
-- is a fresh Tseitin output. The value of every input is preserved.
theorem extend_or_assignment (a : α → Bool) (xs : List α) :
    ∃ b : Sum α Unit → Bool, (∀ x, b (.inl x) = a x) ∧
      (orBlock (xs.map Sum.inl) (.inr ())).eval b = true := by
  refine ⟨Sum.elim a (fun _ => xs.any a), fun _ => rfl, ?_⟩
  rw [orBlock_valid]
  simp

theorem extend_and_assignment (a : α → Bool) (x y : α) :
    ∃ b : Sum α Unit → Bool, (∀ j, b (.inl j) = a j) ∧
      (andBlock (.inl x) (.inl y) (.inr ())).eval b = true := by
  refine ⟨Sum.elim a (fun _ => a x && a y), fun _ => rfl, ?_⟩
  exact (andBlock_valid ..).2 rfl

-- The JS triple loop emits (¬a ∨ ¬b ∨ ¬c) once with c < b < a.
def tripleClauses {k : ℕ} (used : Fin k → Bool) : Prop :=
  ∀ a b c : Fin k, c < b → b < a →
    (packClause [(a,false),(b,false),(c,false)]).eval used = true

theorem tripleClauses_iff {k : ℕ} (used : Fin k → Bool) :
    tripleClauses used ↔ (Finset.univ.filter (fun i => used i = true)).card ≤ 2 := by
  have bits (a b c : Fin k) :
      (packClause [(a,false),(b,false),(c,false)]).eval used = true ↔
        used a = false ∨ used b = false ∨ used c = false := by simp [packClause_valid]
  simp only [tripleClauses, bits]
  constructor
  · intro h
    by_contra! hc
    obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
    rcases lt_or_gt_of_ne hab with h₁ | h₁ <;>
      rcases lt_or_gt_of_ne hac with h₂ | h₂ <;>
      rcases lt_or_gt_of_ne hbc with h₃ | h₃ <;> first
      | exact absurd (h a b c (by omega) (by omega)) (by simp [ha,hb,hc])
      | exact absurd (h a c b (by omega) (by omega)) (by simp [ha,hb,hc])
      | exact absurd (h b a c (by omega) (by omega)) (by simp [ha,hb,hc])
      | exact absurd (h b c a (by omega) (by omega)) (by simp [ha,hb,hc])
      | exact absurd (h c a b (by omega) (by omega)) (by simp [ha,hb,hc])
      | exact absurd (h c b a (by omega) (by omega)) (by simp [ha,hb,hc])
  · intro bound a b c hcb hba
    by_contra! hn
    have mem (i : Fin k) (hi : used i = true) :
        i ∈ Finset.univ.filter (fun j => used j = true) := by simp [hi]
    have more := Finset.two_lt_card_iff.mpr
      ⟨a,b,c,mem a (by simpa using hn.1),mem b (by simpa using hn.2.1),
        mem c (by simpa using hn.2.2),by omega,by omega,by omega⟩
    omega

theorem circuit_occurrences {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    tripleClauses (fun i => decide (v ∈ C.leftVars i ∨ v ∈ C.rightVars i)) ↔
      (Finset.univ.filter (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2 := by
  rw [tripleClauses_iff]
  simp

inductive SideAtom (n k : ℕ)
  | raw (v : Fin n)
  | link (j : Fin k)
  | previous (j : Fin k)
  | product (j : Fin k)
  | result

open SideAtom

def sideInputs {n k : ℕ} (U : Finset (Fin n)) (i : Fin k) : List (SideAtom n k) :=
  (U.sort (· ≤ ·)).map raw ++ ((Finset.univ.filter (fun j : Fin k => j < i)).sort (· ≤ ·)).map product

def sideAssignment {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val : Fin k → Bool) : SideAtom n k → Bool
  | .raw v => decide (v ∈ B)
  | .link j => decide (j ∈ F)
  | .previous j => val j
  | .product j => decide (j ∈ F) && val j
  | .result => sideTrue U B F i val

theorem side_assignment_satisfies {n k : ℕ} (U B : Finset (Fin n))
    (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool) :
    (∀ j < i, (andBlock (.link j) (.previous j) (.product j)).eval
      (sideAssignment U B F i val) = true) ∧
    (orBlock (sideInputs U i) .result).eval (sideAssignment U B F i val) = true := by
  constructor
  · intro j _
    exact (andBlock_valid ..).2 rfl
  · rw [orBlock_valid]
    simp [sideInputs, sideAssignment, sideTrue, or_and_right, exists_or]
    grind

theorem side_assignment_forces_result {n k : ℕ} (U : Finset (Fin n)) (i : Fin k)
    (a : SideAtom n k → Bool)
    (products : ∀ j < i, (andBlock (.link j) (.previous j) (.product j)).eval a = true)
    (output : (orBlock (sideInputs U i) .result).eval a = true) :
    a .result =
      sideTrue U (Finset.univ.filter (fun v => a (.raw v) = true))
        (Finset.univ.filter (fun j => a (.link j) = true)) i (fun j => a (.previous j)) := by
  apply Bool.eq_iff_iff.mpr
  rw [(orBlock_valid ..).mp output]
  have hw (j : Fin k) (hj : j < i) :
      a (.product j) = (a (.link j) && a (.previous j)) :=
    (andBlock_valid ..).mp (products j hj)
  simp [sideTrue, sideInputs]
  aesop

end PetersenCnfBridge
