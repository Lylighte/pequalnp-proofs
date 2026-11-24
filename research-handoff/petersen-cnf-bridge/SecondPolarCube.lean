import SecondPacked
import FootprintPolar
import SecondFootprintGroups

namespace PetersenSecondCube

open PEqualNP.AndCount PetersenSuffix PetersenFirstPins PetersenNormalized
open PetersenBoundary PetersenFootprintCenters PetersenFootprintPolar PetersenSecondGroups

def Invalid (a b : Nat) (Q : Rect) := ∀ l r : Fin 2048, Within Q l r →
  ∀ (C : AndCountCircuit 10) (hk : 2 ≤ C.size), Matches C (gates a b l r) hk → Candidate C → Shape C 2 → False

def packedAt (a b : Nat) (table : Array Mark) (q : Rect) (data : List Nat) :=
  match readTree table 23 data with
  | some (t,[]) => checks a b t q
  | _ => false

theorem packed_invalid (a b : Nat) (table : Array Mark) (Q : Rect) (data : List Nat)
    (valid : packedAt a b table Q data = true) : Invalid a b Q := by
  intro l r within C hk front hc shape
  unfold packedAt at valid
  split at valid
  next t _ => exact tree_sound a b l r C hk front hc shape t Q within valid
  next => contradiction

def polarAt (a b : Nat) (Q : Rect) (s : Nat) :=
  negativeMasks.all (fun m => !side a b s m || h1 a b Q.ll Q.rl m) &&
  positiveMasks.all (fun m => !h1 a b Q.lh Q.rh m || side a b s m)

theorem polar_invalid (a b : Nat) (Q : Rect) (s : Nat) (valid : polarAt a b Q s = true) :
    Invalid a b Q := by
  intro l r within C hk front hc shape
  let B := box a b Q l r
  have bm : Member B l r := member a b Q l r within
  have tests := Bool.and_eq_true_iff.mp valid
  have cert : polarCheck B s = true := by
    refine Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr ?_,tests.2⟩
    intro m hm
    change (!side a b s m || negSecond B m) = true
    rw [← neg_eq B l r bm m hm]
    have low := List.all_eq_true.mp tests.1 m hm
    rw [Bool.or_eq_true] at low ⊢
    rcases low with no | yes
    · exact Or.inl no
    · apply Or.inr
      obtain ⟨lhs,rhs⟩ := Bool.and_eq_true_iff.mp yes
      exact Bool.and_eq_true_iff.mpr ⟨side_mono _ _ _ _ within.ll m lhs,side_mono _ _ _ _ within.rl m rhs⟩
  exact box_polar B l r s bm cert C hk front hc shape

theorem split_invalid (a b : Nat) (Q : Rect) (right : Bool) (i : Fin 11)
    (z : Invalid a b (off Q right i)) (o : Invalid a b (on Q right i)) : Invalid a b Q := by
  intro l r inside C hk front hc shape
  rcases choose_side Q l r inside right i with m | m
  · exact z l r m C hk front hc shape
  · exact o l r m C hk front hc shape

theorem fixed_invalid (a b : Fin 1024) (valid : Invalid a b allRect)
    (C : AndCountCircuit 10) (hk : 2 ≤ C.size) (first : FirstSides C a b) (hc : Candidate C) (shape : Shape C 2) : False := by
  obtain ⟨l,r,front⟩ := actual_prefix C hk hc.1 a b first
  exact valid l r (start l r) C hk front hc shape

theorem all_groups_invalid (a b : Nat) (valid : Invalid a b allRect) (x y : Bin) : Refuted (pair a b x y) :=
  fun l r _ C hk front hc shape => valid l r (start l r) C hk front hc shape

end PetersenSecondCube
