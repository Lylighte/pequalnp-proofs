import BatchLeaves
import UnifiedModes

namespace PetersenSecondCube.Batch

open PetersenBoundary PetersenFootprintCenters
open PetersenSecondCube.Unified (Tickets)

def verifyTree (a b : Nat) (row : Fin r → Mark) (tail : Fin t → Tickets) : Unified.Tree r t → Rect → Bool
  | .automaticSpent,Q => spentBit a b Q
  | .automaticCenters,Q => centerBit a b Q
  | .branch side bit z o,Q =>
    verifyTree a b row tail z (off Q side bit) && verifyTree a b row tail o (on Q side bit)
  | tree,Q => Unified.verify a b row tail tree Q

theorem verify_sound (a b : Nat) (row : Fin r → Mark) (tail : Fin t → Tickets)
    (edges : ∀ i, RowEdge (row i).p (row i).v (row i).w)
    (good : ∀ i j,(tail i).rows j ∈ positiveMasks) (tree : Unified.Tree r t) (Q : Rect)
    (pass : verifyTree a b row tail tree Q=true) : Invalid a b Q := by
  induction tree generalizing Q with
  | automaticSpent => exact spent_sound _ _ _ pass
  | automaticCenters => exact centers_sound _ _ _ pass
  | branch side bit z o zz oo =>
    exact split_invalid a b Q side bit (zz _ (Bool.and_eq_true_iff.mp pass).1) (oo _ (Bool.and_eq_true_iff.mp pass).2)
  | spent i => exact Unified.sound _ _ row tail edges good (.spent i) Q pass
  | centers es => exact Unified.sound _ _ row tail edges good (.centers es) Q pass
  | polar i => exact Unified.sound _ _ row tail edges good (.polar i) Q pass
  | tickets i => exact Unified.sound _ _ row tail edges good (.tickets i) Q pass
  | safe => exact Unified.sound _ _ row tail edges good .safe Q pass

def stream (a b : Nat) (Q : Rect) (row : Fin r → Mark) (tail : Fin t → Tickets)
    (tags ports ids : List Nat) :=
  match Unified.readStream r t tags ports ids [] with
  | none => false
  | some tree => verifyTree a b row tail tree Q

theorem stream_sound (a b : Nat) (Q : Rect) (row : Fin r → Mark) (tail : Fin t → Tickets)
    (edges : ∀ i, RowEdge (row i).p (row i).v (row i).w)
    (good : ∀ i j, (tail i).rows j∈positiveMasks) (tags ports ids : List Nat)
    (pass : stream a b Q row tail tags ports ids=true) : Invalid a b Q := by
  unfold stream at pass
  split at pass
  next => contradiction
  next tree _ => exact verify_sound _ _ row tail edges good tree Q pass

end PetersenSecondCube.Batch

namespace PetersenSecondCube.BatchProbe
open UnifiedShardStream
run_cmd Lean.logInfo m!"BASE_BEGIN {← IO.monoMsNow}"
theorem ordinary : Invalid 3 50 ⟨4,2047,4,13⟩ := Unified.stream_sound 3 50 ⟨4,2047,4,13⟩ rows tails row_valid tail_valid [46,23,47,23,10,23,9,8,23,7,23,6,46,3,14,46,47,22,14,10,23,9,23,8,23,7,23,6,23,3,11,46,22,47,10,23,9,23,8,23,7,23,6,23,3,11,23,14,1,22,23,11,0,22,5,22,4] [4,12,4,4] [0,1,1] (by decide +kernel)
run_cmd Lean.logInfo m!"BASE_END {← IO.monoMsNow}"
run_cmd Lean.logInfo m!"BATCH_BEGIN {← IO.monoMsNow}"
theorem packed : Invalid 3 50 ⟨4,2047,4,13⟩ := Batch.stream_sound 3 50 ⟨4,2047,4,13⟩ rows tails row_valid tail_valid [46,23,47,23,10,23,9,8,23,7,23,6,46,3,14,46,47,22,14,10,23,9,23,8,23,7,23,6,23,3,11,46,22,47,10,23,9,23,8,23,7,23,6,23,3,11,23,14,1,22,23,11,0,22,5,22,4] [4,12,4,4] [0,1,1] (by decide +kernel)
run_cmd Lean.logInfo m!"BATCH_END {← IO.monoMsNow}"
end PetersenSecondCube.BatchProbe
#print axioms PetersenSecondCube.BatchProbe.packed
