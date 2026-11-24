import CubeTailTickets

namespace PetersenSecondCube

open PetersenFootprintCenters PetersenBoundary
open PetersenMixedStar (V)

-- Clearing only row bits shared by the two prefixes works also when the
-- upper selector bit of the second gate is set.
def code (a b ll rl : Nat) (m : M) (z : Bool) : Nat :=
  (m.val ^^^ (m.val &&& ((a ||| b) &&& (ll ||| rl)))) |||
    (if h0 a b m then 1024 else 0) ||| (if z then 2048 else 0)

private theorem smallBits : ∀ v : V, (1024:Nat).testBit v.val=false ∧
    (2048:Nat).testBit v.val=false := by decide +kernel

theorem code_spec (a b ll rl : Nat) (m : M) (z : Bool) (x : Fin 12) :
    (code a b ll rl m z).testBit x.val = view a b ll rl m z x := by
  refine Fin.addCases (m:=10) (n:=2) (fun v => ?_) (fun j => ?_) x
  · simp only [view,Fin.addCases_left]
    change (code a b ll rl m z).testBit v.val = (m.val.testBit v.val && decide (count a b ll rl v < 2))
    have flags (s : Bool) : ((if s then 1024 else 0):Nat).testBit v.val=false ∧
        ((if s then 2048 else 0):Nat).testBit v.val=false := by
      cases s <;> simp [smallBits]
    simp only [code,Nat.testBit_or,Nat.testBit_xor,Nat.testBit_and,
      (flags _).1,(flags _).2,Bool.or_false,count,seen]
    have table (on x y : Bool) : (on ^^ (on && (x && y))) =
        (on && decide (x.toNat+y.toNat < 2)) := by
      cases on <;> cases x <;> cases y <;> rfl
    exact table _ _ _
  · have off10 : m.val.testBit 10=false := Nat.testBit_lt_two_pow m.isLt
    have off11 : m.val.testBit 11=false := Nat.testBit_lt_two_pow (m.isLt.trans_le (by decide : 1024≤2^11))
    fin_cases j
    · change (code a b ll rl m z).testBit 10 = h0 a b m
      cases h : h0 a b m <;> cases z <;> simp [code,h,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,off10] <;> decide
    · change (code a b ll rl m z).testBit 11 = z
      cases h : h0 a b m <;> cases z <;> simp [code,h,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,off11] <;> decide

def pcode (a b : Nat) (Q : Rect) (m : M) := code a b Q.ll Q.rl m (h1 a b Q.lh Q.rh m)
def ncode (a b : Nat) (Q : Rect) (m : M) := code a b Q.ll Q.rl m (h1 a b Q.ll Q.rl m)

def gather (f : M → Nat) (i : Nat) : List M → Nat
  | [] => 0
  | m :: ms => (if (f m).testBit i then f m else 0) ||| gather f i ms

theorem gather_spec (f : M → Nat) (i j : Nat) (ms : List M) :
    (gather f i ms).testBit j=true ↔ ∃ m∈ms, (f m).testBit j=true ∧ (f m).testBit i=true := by
  induction ms with
  | nil => simp [gather]
  | cons m ms ih =>
    rw [gather,Nat.testBit_or,Bool.or_eq_true,ih]
    cases eq : (f m).testBit i <;> simp [eq]

def neighbors (a b : Nat) (Q : Rect) (y : Fin 12) := gather (ncode a b Q) y.val negativeMasks

theorem numeric_neighbors (a b : Nat) (Q : Rect) (x y : Fin 12) :
    (neighbors a b Q y).testBit x.val=true ↔ ∃ m∈negativeMasks,
      negative a b Q m x=true ∧ negative a b Q m y=true := by
  simp only [neighbors,gather_spec,ncode,code_spec,negative]

end PetersenSecondCube
