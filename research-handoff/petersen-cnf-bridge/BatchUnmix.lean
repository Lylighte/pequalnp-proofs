import CubeBitCode

namespace PetersenSecondCube.Batch

open PetersenBoundary PetersenFootprintCenters
open PetersenMixedStar (V)

def gatherBits (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x ||| gatherBits f xs

theorem gatherBits_bit (f : α → Nat) (xs : List α) (i : Nat) :
    (gatherBits f xs).testBit i=true ↔ ∃ x∈xs, (f x).testBit i=true := by
  induction xs with
  | nil => simp [gatherBits]
  | cons x xs ih => simp [gatherBits,Nat.testBit_or,ih]

def rawColumn (columns : V → Nat) (s : Nat) :=
  gatherBits (fun v : V => if s.testBit v.val then columns v else 0) (List.finRange 10)

theorem rawColumn_spec (columns : V → Nat) (s : Nat) (j : Nat) (m : M)
    (eqs : ∀ v : V, (columns v).testBit j=m.val.testBit v.val) :
    (rawColumn columns s).testBit j=raw s m := by
  apply Bool.eq_iff_iff.mpr
  rw [rawColumn,gatherBits_bit,raw_iff]
  constructor
  · rintro ⟨v,_,on⟩
    cases eq : s.testBit v.val <;> simp [eq,eqs] at on
    exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,on⟩⟩
  · rintro ⟨v,vs,vm⟩
    exact ⟨v,List.mem_finRange _,by simpa [(Finset.mem_filter.mp vs).2,eqs] using (Finset.mem_filter.mp vm).2⟩

def source (col : V → Nat) (a b : Nat) := rawColumn col a &&& rawColumn col b
def sideCol (col : V → Nat) (first s : Nat) :=
  rawColumn col s ||| (if s.testBit 10 then first else 0)
def projectedCol (col : V → Nat) (a b ll rl lhs rhs : Nat) (x : Fin 12) :=
  let first := source col a b
  let next := sideCol col first lhs &&& sideCol col first rhs
  Fin.addCases (m:=10) (n:=2) (motive:=fun _ => Nat)
    (fun v : V => if count a b ll rl v < 2 then col v else 0)
    (fun j => ![first,next] j) x

theorem projected_spec (col : V → Nat) (a b ll rl lhs rhs : Nat) (j : Nat) (m : M)
    (eqs : ∀ v : V, (col v).testBit j=m.val.testBit v.val) (x : Fin 12) :
    (projectedCol col a b ll rl lhs rhs x).testBit j=view a b ll rl m (h1 a b lhs rhs m) x := by
  have c (s : Nat) := rawColumn_spec col s j m eqs
  have fst : (source col a b).testBit j=h0 a b m := by simp [source,Nat.testBit_and,c,h0]
  have sideE (s : Nat) : (sideCol col (source col a b) s).testBit j=side a b s m := by
    cases e : s.testBit 10 <;> simp [sideCol,side,Nat.testBit_or,e,fst,c]
  refine Fin.addCases (m:=10) (n:=2) (fun v => ?_) (fun h => ?_) x
  · simp only [projectedCol,view,Fin.addCases_left]
    by_cases yes : count a b ll rl v<2 <;> simp [yes,eqs]
  · simp only [projectedCol,view,Fin.addCases_right]
    fin_cases h
    · exact fst
    · exact (Nat.testBit_and ..).trans (congrArg₂ Bool.and (sideE lhs) (sideE rhs))

-- A row with both h and x visible is mixed exactly when the pair has no common
-- negative. Every private row is handled simultaneously by these 24 word tests.
def unpaired (p n : Fin 12 → Nat) (h : Fin 12) := gatherBits
  (fun x : Fin 12 => if n h &&& n x = 0 then p x else 0) (List.finRange 12)
def mixedRows (p n : Fin 12 → Nat) := (p 10 &&& unpaired p n 10) ||| (p 11 &&& unpaired p n 11)

private theorem witnesses (p n : Fin 12 → Nat) (h x : Fin 12) (j : Nat)
    (absent : (p h &&& unpaired p n h).testBit j=false)
    (ah : (p h).testBit j=true) (ax : (p x).testBit j=true) : n h &&& n x ≠ 0 := by
  intro none
  have hit : (unpaired p n h).testBit j=true :=
    (gatherBits_bit ..).mpr ⟨x,List.mem_finRange x,by simpa [none] using ax⟩
  simp [Nat.testBit_and,ah,hit] at absent

theorem unmixed (a b : Nat) (Q : Rect) (m : M) (j : Nat) (p n : Fin 12 → Nat)
    (upper : ∀ x, positive a b Q m x=true → (p x).testBit j=true)
    (lower : ∀ x y, n x &&& n y ≠ 0 → ∃ w∈negativeMasks,
      negative a b Q w x=true ∧ negative a b Q w y=true)
    (absent : (mixedRows p n).testBit j=false) : unmix a b Q m=true := by
  have off : (p 10 &&& unpaired p n 10).testBit j=false ∧ (p 11 &&& unpaired p n 11).testBit j=false := by
    simpa [mixedRows,Nat.testBit_or] using absent
  apply List.all_eq_true.mpr; intro g _
  let x := Fin.natAdd 10 g
  by_cases hx : positive a b Q m x=true
  · apply Bool.or_eq_true_iff.mpr; right
    apply List.all_eq_true.mpr; intro y _
    by_cases hy : positive a b Q m y=true
    · apply Bool.or_eq_true_iff.mpr; right
      have sn : n x &&& n y ≠ 0 := by
        fin_cases g
        · exact witnesses _ _ _ _ _ off.1 (upper _ hx) (upper _ hy)
        · exact witnesses _ _ _ _ _ off.2 (upper _ hx) (upper _ hy)
      obtain ⟨w,hm,wx,wy⟩ := lower x y sn
      exact List.any_eq_true.mpr ⟨w,hm,Bool.and_eq_true_iff.mpr ⟨wx,wy⟩⟩
    · simp [Bool.eq_false_iff.mpr hy]
  · change (!positive a b Q m x || _) = true; simp [Bool.eq_false_iff.mpr hx]

end PetersenSecondCube.Batch
