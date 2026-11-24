import SecondTree

namespace PetersenSecondCube

open PEqualNP.AndCount PetersenFirstPins PetersenNormalized

-- 0..21 split on a bit of the left/right selector; 22 denotes one spent
-- witness. A token 23+n introduces n private positive rows for a degree bound.
def readMark (table : Array Mark) (xs : List Nat) : Option (Mark × List Nat) := do
  let i :: rest := xs | none
  return (← table[i]?,rest)

def readMarks (table : Array Mark) : Nat → List Nat → Option (List Mark × List Nat)
  | 0,xs => some ([],xs)
  | n+1,xs => do
    let (m,ys) ← readMark table xs
    let (ms,zs) ← readMarks table n ys
    return (m::ms,zs)

def readTree (table : Array Mark) : Nat → List Nat → Option (Tree × List Nat)
  | 0,_ => none
  | _+1,[] => none
  | fuel+1,t::xs => do
    if t < 22 then
      let (z,ys) ← readTree table fuel xs
      let (o,zs) ← readTree table fuel ys
      return (.branch (decide (11≤t)) ⟨t%11,Nat.mod_lt _ (by decide)⟩ z o,zs)
    else if t = 22 then
      let (m,ys) ← readMark table xs
      return (.leaf (.spent m),ys)
    else
      let (ms,ys) ← readMarks table (t-23) xs
      return (.leaf (.centers ms),ys)

def checkBytes (a b : Nat) (table : Array Mark) (bytes : List Nat) :=
  match readTree table 23 bytes with
  | some (t,[]) => checks a b t allRect
  | _ => false

theorem bytes_exclude (a b : Fin 1024) (table : Array Mark) (bytes : List Nat)
    (valid : checkBytes a b table bytes = true) (C : AndCountCircuit 10) (hk : 2 ≤ C.size)
    (first : FirstSides C a b) (hc : Candidate C) (shape : Shape C 2) : False := by
  unfold checkBytes at valid
  split at valid
  next t _ => exact excludes_first a b t valid C hk first hc shape
  next => contradiction

end PetersenSecondCube
