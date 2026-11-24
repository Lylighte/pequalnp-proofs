import CubeSharedMarks

namespace PetersenSecondCube

open PetersenFirstPins PetersenBoundary PetersenFootprintCenters

def candidates (a b : Nat) (Q : Rect) (row : Fin t → Mark) :=
  let c0 := neighbors a b Q 10
  let c1 := neighbors a b Q 11
  (List.finRange t).filter (fun i => compactMark a b Q c0 c1 (row i))

def autoSpent (a b : Nat) (Q : Rect) (row : Fin t → Mark) :=
  (candidates a b Q row).any fun i =>
    decide (2 ≤ count a b Q.ll Q.rl (row i).v ∨ 2 ≤ count a b Q.ll Q.rl (row i).w)

def autoCenters (a b : Nat) (Q : Rect) (row : Fin t → Mark) :=
  decide (4 < (large a b Q ((candidates a b Q row).map row)).card)

theorem auto_spent_invalid (a b : Nat) (Q : Rect) (row : Fin t → Mark)
    (edges : ∀ i, RowEdge (row i).p (row i).v (row i).w)
    (good : autoSpent a b Q row=true) : Invalid a b Q := by
  obtain ⟨i,ih,on⟩ := List.any_eq_true.mp good
  have mark := (List.mem_filter.mp ih).2
  apply indexed_spent a b Q row edges i
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simpa [wrows] using mark,on⟩

theorem auto_centers_invalid (a b : Nat) (Q : Rect) (row : Fin t → Mark)
    (edges : ∀ i, RowEdge (row i).p (row i).v (row i).w)
    (good : autoCenters a b Q row=true) : Invalid a b Q := by
  apply indexed_centers a b Q row edges (candidates a b Q row)
  apply Bool.and_eq_true_iff.mpr
  refine ⟨List.all_eq_true.mpr ?_,good⟩
  intro e mem
  obtain ⟨i,ih,rfl⟩ := List.mem_map.mp mem
  exact (List.mem_filter.mp ih).2

end PetersenSecondCube


namespace PetersenSecondCube.Unified

open PetersenFirstPins PetersenBoundary PetersenFootprintCenters

structure Tickets where
  n : Nat
  cap : Nat
  rows : Fin n → M
  order : List (Fin 12)

inductive Tree (r t : Nat) where
  | spent (row : Fin r)
  | centers (es : List (Fin r))
  | automaticSpent
  | automaticCenters
  | polar (port : Nat)
  | safe
  | tickets (id : Fin t)
  | branch (side : Bool) (bit : Fin 11) (zero one : Tree r t)

def verify (a b : Nat) (row : Fin r → Mark) (tail : Fin t → Tickets) : Tree r t → Rect → Bool
  | .spent i,Q => compact a b Q (.spent (row i))
  | .centers es,Q => compact a b Q (.centers (es.map row))
  | .automaticSpent,Q => autoSpent a b Q row
  | .automaticCenters,Q => autoCenters a b Q row
  | .polar port,Q => polarAt a b Q port
  | .safe,Q => negativeMasks.all (fun m => !h0 a b m) || negativeMasks.all (fun m => !h1 a b Q.lh Q.rh m)
  | .tickets i,Q =>
    let w := tail i
    decide (4*w.cap<w.n) && verifyFast w.n w.cap (fun j => pcode a b Q (w.rows j)) (neighbors a b Q) w.order 4095 0
  | .branch side bit z o,Q => verify a b row tail z (off Q side bit) && verify a b row tail o (on Q side bit)

theorem sound (a b : Nat) (row : Fin r → Mark) (tail : Fin t → Tickets)
    (edges : ∀ i, RowEdge (row i).p (row i).v (row i).w)
    (good : ∀ i j,(tail i).rows j ∈ positiveMasks) (tree : Tree r t) (Q : Rect)
    (pass : verify a b row tail tree Q=true) : Invalid a b Q := by
  induction tree generalizing Q with
  | spent i => exact indexed_spent a b Q row edges i pass
  | centers es => exact indexed_centers a b Q row edges es pass
  | automaticSpent => exact auto_spent_invalid a b Q row edges pass
  | automaticCenters => exact auto_centers_invalid a b Q row edges pass
  | polar port => exact light_polar_rectangle a b Q port pass
  | safe =>
    apply safe_invalid
    rcases Bool.or_eq_true_iff.mp pass with first | second
    · exact Or.inl (fun m hm => by simpa using List.all_eq_true.mp first m hm)
    · exact Or.inr (fun m hm => by simpa using List.all_eq_true.mp second m hm)
  | tickets i =>
    exact fast_ticket_invalid a b Q _ _ (tail i).rows (tail i).order (good i)
      (Bool.and_eq_true_iff.mp pass).2 (of_decide_eq_true (Bool.and_eq_true_iff.mp pass).1)
  | branch side bit z o zero one =>
    exact split_invalid a b Q side bit (zero _ (Bool.and_eq_true_iff.mp pass).1)
      (one _ (Bool.and_eq_true_iff.mp pass).2)

end PetersenSecondCube.Unified


namespace PetersenSecondCube.Unified

open PetersenBoundary PetersenFootprintCenters

-- The compact directory stores postfix trees. The two operand streams are
-- consumed in left-to-right leaf order. Successful decoding requires exact
-- consumption, one completed tree, and an in-range tail witness index.
def readStream (r t : Nat) : List Nat → List Nat → List Nat → List (Tree r t) → Option (Tree r t)
  | [],[],[],[v] => some v
  | [],_,_,_ => none
  | tag :: rest,ports,ids,stack =>
    if tag<22 then
      match stack with
      | one :: zero :: st => readStream r t rest ports ids
          (.branch (decide (11≤tag)) ⟨tag%11, Nat.mod_lt _ (by decide)⟩ zero one :: st)
      | _ => none
    else if tag=22 then readStream r t rest ports ids (.automaticSpent :: stack)
    else if tag=23 then readStream r t rest ports ids (.automaticCenters :: stack)
    else if tag=45 then readStream r t rest ports ids (.safe :: stack)
    else if tag=46 then
      match ports with
      | p :: ps => readStream r t rest ps ids (.polar p :: stack)
      | [] => none
    else if tag=47 then
      match ids with
      | i :: is => if hi:i<t then readStream r t rest ports is (.tickets ⟨i,hi⟩ :: stack) else none
      | [] => none
    else none

def streamCheck (a b : Nat) (Q : Rect) (row : Fin r → Mark) (tail : Fin t → Tickets)
    (tags ports ids : List Nat) :=
  match readStream r t tags ports ids [] with
  | none => false
  | some tree => verify a b row tail tree Q

theorem stream_sound (a b : Nat) (Q : Rect) (row : Fin r → Mark) (tail : Fin t → Tickets)
    (edges : ∀ i, RowEdge (row i).p (row i).v (row i).w)
    (good : ∀ i j, (tail i).rows j∈positiveMasks) (tags ports ids : List Nat)
    (pass : streamCheck a b Q row tail tags ports ids=true) : Invalid a b Q := by
  unfold streamCheck at pass
  split at pass
  next => contradiction
  next tree _ => exact sound _ _ row tail edges good tree Q pass

end PetersenSecondCube.Unified

namespace PetersenSecondCube.UnifiedShard
open PEqualNP.AndCount PetersenFirstPins PetersenNormalized
open PetersenBoundary PetersenFootprintCenters
open PetersenSecondCube.Unified (Tickets)
set_option maxRecDepth 24000
set_option maxHeartbeats 30000000
local instance : Inhabited Mark := ⟨⟨0,0,0⟩⟩
def table : Array Mark := #[⟨139,0,1⟩,⟨387,0,1⟩,⟨523,0,1⟩,⟨771,0,1⟩,⟨54,1,2⟩,⟨278,1,2⟩,⟨550,1,2⟩,⟨774,1,2⟩,⟨77,2,3⟩,⟨108,2,3⟩,⟨525,2,3⟩,⟨556,2,3⟩,⟨58,3,4⟩,⟨120,3,4⟩,⟨154,3,4⟩,⟨216,3,4⟩,⟨85,4,0⟩,⟨209,4,0⟩,⟨277,4,0⟩,⟨401,4,0⟩,⟨101,0,5⟩,⟨105,0,5⟩,⟨553,0,5⟩,⟨549,0,5⟩,⟨114,1,6⟩,⟨106,1,6⟩,⟨202,1,6⟩,⟨210,1,6⟩,⟨197,2,7⟩,⟨212,2,7⟩,⟨404,2,7⟩,⟨389,2,7⟩,⟨394,3,8⟩,⟨393,3,8⟩,⟨777,3,8⟩,⟨778,3,8⟩,⟨562,4,9⟩,⟨788,4,9⟩,⟨564,4,9⟩,⟨786,4,9⟩,⟨178,5,7⟩,⟨232,5,7⟩,⟨170,5,7⟩,⟨240,5,7⟩,⟨650,7,9⟩,⟨897,7,9⟩,⟨649,7,9⟩,⟨898,7,9⟩,⟨581,9,6⟩,⟨616,9,6⟩,⟨585,9,6⟩,⟨612,9,6⟩,⟨325,6,8⟩,⟨464,6,8⟩,⟨340,6,8⟩,⟨449,6,8⟩,⟨306,8,5⟩,⟨308,8,5⟩,⟨804,8,5⟩,⟨802,8,5⟩]
def rows (i : Fin 60) := table[i.val]!
theorem row_valid : ∀ i, RowEdge (rows i).p (rows i).v (rows i).w := by decide +kernel
def tails : Fin 2 → Tickets := ![⟨5,1,![58,306,581,139,197],[6,7,4,3,5,11,0,1,9,2,10,8]⟩,⟨9,2,![562,58,178,277,325,581,394,178,277],[4,8,2,1,9,11,10,7,3,5,6]⟩]
theorem tail_valid : ∀ i j, (tails i).rows j∈positiveMasks := by decide +kernel

run_cmd Lean.logInfo m!"UnifiedShard_BEGIN {← IO.monoMsNow}"
def dn0 : Unified.Tree 60 2 := (.branch false 4 (.branch false 5 (.branch false 0 (.branch false 1 (.branch true 0 (.branch true 3 (.polar 4) (.branch false 3 (.branch false 6 (.branch false 7 (.branch false 8 (.centers [13,33,36,41,45,48,55,56]) (.branch false 9 (.branch false 10 (.tickets 0) (.centers [8,13,28,36,41,46,50])) (.centers [13,34,36,41,45,56]))) (.centers [8,13,28,36,45,48])) (.centers [8,13,28,36,43,45,48])) (.polar 12))) (.branch false 3 (.branch false 6 (.branch false 7 (.branch false 8 (.branch false 9 (.branch false 10 (.polar 4) (.branch true 3 (.tickets 1) (.spent 0))) (.centers [8,13,33,36,41,47,55,56])) (.centers [13,28,36,41,45,48,53,56])) (.centers [8,13,28,33,36,46,48])) (.centers [8,13,28,33,36,43,46,48])) (.centers [8,13,28,36,43,46,48]))) (.branch true 3 (.branch true 0 (.polar 4) (.branch false 3 (.branch false 6 (.branch false 7 (.branch false 8 (.branch false 9 (.branch false 10 (.spent 19) (.tickets 1)) (.centers [8,13,33,36,41,44,55,56])) (.centers [13,28,32,36,41,44,49,56])) (.centers [8,13,28,33,36,46,49])) (.centers [8,13,28,33,36,41,46,49])) (.centers [8,13,28,36,41,46,49]))) (.centers [8,13,28,36,43,47,48]))) (.branch true 0 (.spent 1) (.centers [8,13,28,33,36,43,46,48]))) (.spent 43)) (.spent 36))
theorem n0 : Invalid 3 50 ⟨4,2047,4,13⟩ := Unified.sound 3 50 rows tails row_valid tail_valid dn0 ⟨4,2047,4,13⟩ (by decide +kernel)

run_cmd Lean.logInfo m!"UnifiedShard_END {← IO.monoMsNow}"
theorem excludes : Invalid 3 50 ⟨4,2047,4,13⟩ := n0
end PetersenSecondCube.UnifiedShard
#print axioms PetersenSecondCube.UnifiedShard.excludes

namespace PetersenSecondCube.UnifiedShardStream
open PEqualNP.AndCount PetersenFirstPins PetersenNormalized
open PetersenBoundary PetersenFootprintCenters
open PetersenSecondCube.Unified (Tickets)
set_option maxRecDepth 24000
set_option maxHeartbeats 30000000
local instance : Inhabited Mark := ⟨⟨0,0,0⟩⟩
def table : Array Mark := #[⟨139,0,1⟩,⟨387,0,1⟩,⟨523,0,1⟩,⟨771,0,1⟩,⟨54,1,2⟩,⟨278,1,2⟩,⟨550,1,2⟩,⟨774,1,2⟩,⟨77,2,3⟩,⟨108,2,3⟩,⟨525,2,3⟩,⟨556,2,3⟩,⟨58,3,4⟩,⟨120,3,4⟩,⟨154,3,4⟩,⟨216,3,4⟩,⟨85,4,0⟩,⟨209,4,0⟩,⟨277,4,0⟩,⟨401,4,0⟩,⟨101,0,5⟩,⟨105,0,5⟩,⟨553,0,5⟩,⟨549,0,5⟩,⟨114,1,6⟩,⟨106,1,6⟩,⟨202,1,6⟩,⟨210,1,6⟩,⟨197,2,7⟩,⟨212,2,7⟩,⟨404,2,7⟩,⟨389,2,7⟩,⟨394,3,8⟩,⟨393,3,8⟩,⟨777,3,8⟩,⟨778,3,8⟩,⟨562,4,9⟩,⟨788,4,9⟩,⟨564,4,9⟩,⟨786,4,9⟩,⟨178,5,7⟩,⟨232,5,7⟩,⟨170,5,7⟩,⟨240,5,7⟩,⟨650,7,9⟩,⟨897,7,9⟩,⟨649,7,9⟩,⟨898,7,9⟩,⟨581,9,6⟩,⟨616,9,6⟩,⟨585,9,6⟩,⟨612,9,6⟩,⟨325,6,8⟩,⟨464,6,8⟩,⟨340,6,8⟩,⟨449,6,8⟩,⟨306,8,5⟩,⟨308,8,5⟩,⟨804,8,5⟩,⟨802,8,5⟩]
def rows (i : Fin 60) := table[i.val]!
theorem row_valid : ∀ i, RowEdge (rows i).p (rows i).v (rows i).w := by decide +kernel
def tails : Fin 2 → Tickets := ![⟨5,1,![58,306,581,139,197],[6,7,4,3,5,11,0,1,9,2,10,8]⟩,⟨9,2,![562,58,178,277,325,581,394,178,277],[4,8,2,1,9,11,10,7,3,5,6]⟩]
theorem tail_valid : ∀ i j, (tails i).rows j∈positiveMasks := by decide +kernel

run_cmd Lean.logInfo m!"UnifiedShardStream_BEGIN {← IO.monoMsNow}"
theorem n0 : Invalid 3 50 ⟨4,2047,4,13⟩ := Unified.stream_sound 3 50 ⟨4,2047,4,13⟩ rows tails row_valid tail_valid [46,23,47,23,10,23,9,8,23,7,23,6,46,3,14,46,47,22,14,10,23,9,23,8,23,7,23,6,23,3,11,46,22,47,10,23,9,23,8,23,7,23,6,23,3,11,23,14,1,22,23,11,0,22,5,22,4] [4,12,4,4] [0,1,1] (by decide +kernel)

run_cmd Lean.logInfo m!"UnifiedShardStream_END {← IO.monoMsNow}"
theorem excludes : Invalid 3 50 ⟨4,2047,4,13⟩ := n0
end PetersenSecondCube.UnifiedShardStream
#print axioms PetersenSecondCube.UnifiedShardStream.excludes
