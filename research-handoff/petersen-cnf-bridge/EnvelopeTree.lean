import RootEnvelope

namespace PetersenSecondCube.Envelope

inductive Branch where
  | spent
  | centers
  | fork (right : Bool) (i : Fin 11) (z o : Branch)

def parse : List Nat → List Branch → Option Branch
  | [],[tree] => some tree
  | [],_ => none
  | tag::xs,stack =>
    if tag=22 then parse xs (.spent::stack)
    else if tag=23 then parse xs (.centers::stack)
    else if tag<22 then
      match stack with
      | o::z::rest => parse xs (.fork (decide (11≤tag)) ⟨tag%11,Nat.mod_lt _ (by decide)⟩ z o::rest)
      | _ => none
    else none

def verify (s : Group) : Branch → Rect → Bool
  | .spent,Q => spent s Q
  | .centers,Q => centers s Q
  | .fork side i z o,Q => verify s z (off Q side i) && verify s o (on Q side i)

theorem split (s : Group) (Q : Rect) (side : Bool) (i : Fin 11)
    (z : refutes s (off Q side i)) (o : refutes s (on Q side i)) : refutes s Q :=
  fun a b fit => split_invalid a b Q side i (z a b fit) (o a b fit)

theorem sound (s : Group) (t : Branch) (Q : Rect) (ok : verify s t Q=true) : refutes s Q := by
  induction t generalizing Q with
  | spent => exact spent_sound _ _ ok
  | centers => exact centers_sound _ _ ok
  | fork side i l r hl hr => exact split s Q side i (hl _ (Bool.and_eq_true_iff.mp ok).1) (hr _ (Bool.and_eq_true_iff.mp ok).2)

def program (s : Group) (Q : Rect) (tokens : List Nat) :=
  match parse tokens [] with
  | some t => verify s t Q
  | none => false

theorem program_sound (s : Group) (Q : Rect) (tokens : List Nat) (ok : program s Q tokens=true) :
    refutes s Q := by
  unfold program at ok
  split at ok
  next t _ => exact sound s t Q ok
  next => contradiction

end PetersenSecondCube.Envelope
