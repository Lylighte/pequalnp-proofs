import SecondCube

namespace PetersenSecondCube

open PEqualNP.AndCount PetersenSuffix PetersenFirstPins PetersenNormalized PetersenFootprintCenters

def off (Q : Rect) (right : Bool) (i : Fin 11) : Rect :=
  if right then {Q with rh := Q.rh ^^^ 2^i.val} else {Q with lh := Q.lh ^^^ 2^i.val}
def on (Q : Rect) (right : Bool) (i : Fin 11) : Rect :=
  if right then {Q with rl := Q.rl ||| 2^i.val} else {Q with ll := Q.ll ||| 2^i.val}

private theorem offHi (a hi : Nat) (sub : Sub a hi) (i : Fin 11) (none : a.testBit i.val = false) :
    Sub a (hi ^^^ 2^i.val) := by
  intro j q
  have ne : i.val ≠ j.val := fun eq => Bool.false_ne_true ((eq ▸ none).symm.trans q)
  simp [Nat.testBit_xor,Nat.testBit_two_pow_of_ne ne,sub j q]

private theorem onLo (lo a : Nat) (sub : Sub lo a) (i : Fin 11) (one : a.testBit i.val = true) :
    Sub (lo ||| 2^i.val) a := by
  intro j q
  by_cases eq : i.val = j.val
  · exact eq ▸ one
  · simp only [Nat.testBit_or,Nat.testBit_two_pow_of_ne eq,Bool.or_false] at q
    exact sub j q

theorem choose_side (Q : Rect) (l r : Nat) (mem : Within Q l r) (right : Bool) (i : Fin 11) :
    Within (off Q right i) l r ∨ Within (on Q right i) l r := by
  cases right
  · cases h : l.testBit i.val
    · exact Or.inl ⟨mem.ll,offHi l Q.lh mem.lh i h,mem.rl,mem.rh⟩
    · exact Or.inr ⟨onLo Q.ll l mem.ll i h,mem.lh,mem.rl,mem.rh⟩
  · cases h : r.testBit i.val
    · exact Or.inl ⟨mem.ll,mem.lh,mem.rl,offHi r Q.rh mem.rh i h⟩
    · exact Or.inr ⟨mem.ll,mem.lh,onLo Q.rl r mem.rl i h,mem.rh⟩

inductive Tree where
  | leaf (why : Witness)
  | branch (right : Bool) (i : Fin 11) (zero one : Tree)

def checks (a b : Nat) : Tree → Rect → Bool
  | .leaf w, Q => witnessOK a b Q w
  | .branch right i z t,Q => checks a b z (off Q right i) && checks a b t (on Q right i)

theorem tree_sound (a b : Nat) (l r : Nat) (C : AndCountCircuit 10) (hk : 2 ≤ C.size)
    (front : Matches C (gates a b l r) hk) (hc : Candidate C) (shape : Shape C 2) (tree : Tree)
    (Q : Rect) (mem : Within Q l r) (valid : checks a b tree Q = true) : False := by
  induction tree generalizing Q with
  | leaf w => exact leaf_sound a b Q l r mem C hk front hc shape w valid
  | branch right i z t hz ht =>
    have both := Bool.and_eq_true_iff.mp valid
    rcases choose_side Q l r mem right i with c | c
    · exact hz _ c both.1
    · exact ht _ c both.2

theorem excludes_first (a b : Fin 1024) (tree : Tree) (valid : checks a b tree allRect = true)
    (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (first : FirstSides C a b)
    (hc : Candidate C) (shape : Shape C 2) : False := by
  obtain ⟨l,r,front⟩ := actual_prefix C hk hc.1 a b first
  exact tree_sound a b l r C hk front hc shape tree allRect (start l r) valid

end PetersenSecondCube
