import DiagonalFinite

namespace PetersenDiagonalStars

open PetersenBoundary
open Petersen905 (related)
open PetersenMixedStar (V Input)
open PetersenTailCnf (hit)

def starHit (T U : Input) := ∃ v ∈ T, v ∈ U ∧ ∃ w ∈ U, related v w = true

structure Sketch where
  T : Input
  J : Input
  A : Input
  B : Input
  O : Input
  small : T.card ≤ 4
  pos (U : Input) : U ∈ positives → ¬starHit T U → hit A U ∧ hit B U ∧ hit O U
  neg (U : Input) : U ∈ negatives → ¬(hit A U ∧ hit B U ∧ hit O U)
  subset : J ⊆ T
  plain (U : Input) : U ∈ positives → hit O U ∨ starHit J U
  supports : T.card=4 → ∀ v ∈ O, ∃ c ∈ T, c ∉ J ∧ (c=v ∨ related c v = true)

structure Term where
  l : Input
  r : Input
  left : Bool
  right : Bool

def Term.reads (f : Term) := f.left || f.right
def Term.opp (f : Term) := (if f.left then f.r else ∅) ∪ (if f.right then f.l else ∅)
def Term.fires (f : Term) (U : Input) (h : Prop) :=
  (hit f.l U ∨ f.left=true ∧ h) ∧ (hit f.r U ∨ f.right=true ∧ h)

private theorem expand (f : Term) (U : Input) (h : Prop) (one : ¬ (f.left=true ∧ f.right=true)) :
    f.fires U h ↔ (hit f.l U ∧ hit f.r U) ∨ h ∧ hit f.opp U := by
  rcases f with ⟨l,r,left,right⟩
  cases left <;> cases right <;> simp [Term.fires,Term.opp] at * <;> grind only

private theorem flip (a b : V) : related a b = related b a := by
  revert a b; decide +kernel

theorem from_terminals (k : Nat) (bound : k≤4) (A B : Input) (f : Fin k → Term)
    (unsafeRow : ∃ n ∈ negatives, hit A n ∧ hit B n)
    (pos : ∀ U ∈ positives, ∃ i, (f i).fires U (hit A U ∧ hit B U))
    (neg : ∀ U ∈ negatives, ∀ i, ¬(f i).fires U (hit A U ∧ hit B U)) : Nonempty Sketch := by
  classical
  have single (i : Fin k) : ¬((f i).left=true ∧ (f i).right=true) := by
    obtain ⟨u,hu,aux⟩ := unsafeRow
    intro both
    exact neg u hu i ⟨Or.inr ⟨both.1,aux⟩,Or.inr ⟨both.2,aux⟩⟩
  have rect (i : Fin k) (x) (xl : x∈(f i).l) (y) (yr : y∈(f i).r) : related x y=true := by
    by_contra no
    obtain ⟨j,hx,hy⟩ := Petersen905.jointlyPresent x y (Bool.eq_false_iff.mpr no)
    have n : Petersen905.rows j ∈ negatives := (negativeIff _).mpr (Petersen905.rowsGood j)
    exact neg _ n i ⟨Or.inl ⟨x,xl,hx⟩,Or.inl ⟨y,yr,hy⟩⟩
  choose center star using (fun i => Petersen905.starCenter _ _ (rect i))
  let D := Finset.univ.filter (fun i : Fin k => (f i).l.Nonempty ∧ (f i).r.Nonempty)
  let E := D.filter (fun i => (f i).reads = false)
  let T := D.image center
  let J := E.image center
  let O := Finset.univ.biUnion (fun i => (f i).opp)
  have sizeD : D.card ≤ k := by simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (Fin k)))
  have sizeT : T.card ≤ D.card := Finset.card_image_le
  have source (i : Fin k) (U : Input) (yes : hit (f i).l U ∧ hit (f i).r U) :
      i∈D ∧ center i ∈ U ∧ ∃ y ∈ U, related (center i) y = true := by
    obtain ⟨⟨x,xl,xu⟩,⟨y,yr,yu⟩⟩ := yes
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x,xl⟩,⟨y,yr⟩⟩,?_⟩
    have edge := rect i x xl y yr
    rcases star i x xl y yr with h | h
    · rw [← h]; exact ⟨xu,y,yu,edge⟩
    · rw [← h]; exact ⟨yu,x,xu,(flip y x).trans edge⟩
  have subset (i) : (f i).opp ⊆ O := fun _ m => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,m⟩
  have liftHit (i) (U : Input) (h : hit (f i).opp U) : hit O U := by
    obtain ⟨v,m,on⟩ := h; exact ⟨v,subset i m,on⟩
  refine ⟨⟨T,J,A,B,O,sizeT.trans (sizeD.trans bound),?_,?_,?_,?_,?_⟩⟩
  · intro U hu absent
    obtain ⟨i,on⟩ := pos U hu
    rcases (expand _ _ _ (single i)).mp on with bare | aux
    · obtain ⟨mem,c,pair⟩ := source i U bare
      exact False.elim (absent ⟨center i,Finset.mem_image_of_mem center mem,c,pair⟩)
    · exact ⟨aux.1.1,aux.1.2,liftHit i U aux.2⟩
  · intro U hu ⟨a,b,v,vo,vu⟩
    obtain ⟨i,_,m⟩ := Finset.mem_biUnion.mp vo
    exact neg U hu i ((expand _ _ _ (single i)).mpr (Or.inr ⟨⟨a,b⟩,v,m,vu⟩))
  · exact Finset.image_mono center (Finset.filter_subset _ _)
  · intro U hu
    obtain ⟨i,on⟩ := pos U hu
    rcases (expand _ _ _ (single i)).mp on with bare | aux
    · by_cases read : (f i).reads=true
      · left; apply liftHit i
        rcases Bool.or_eq_true_iff.mp read with l | r
        · obtain ⟨v,vr,vu⟩ := bare.2; exact ⟨v,Finset.mem_union_left _ (by simpa [l] using vr),vu⟩
        · obtain ⟨v,vl,vu⟩ := bare.1; exact ⟨v,Finset.mem_union_right _ (by simpa [r] using vl),vu⟩
      · obtain ⟨m,c,y⟩ := source i U bare
        exact Or.inr ⟨center i,Finset.mem_image_of_mem center
          (Finset.mem_filter.mpr ⟨m,Bool.eq_false_iff.mpr read⟩),c,y⟩
    · exact Or.inl (liftHit i U aux.2)
  · intro four v vo
    have eqD : D.card = k := by omega
    have all : D = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by simp [eqD])
    have inj : Set.InjOn center D := Finset.card_image_iff.mp (show T.card = D.card by omega)
    obtain ⟨i,_,vi⟩ := Finset.mem_biUnion.mp vo
    have di : i ∈ D := all ▸ Finset.mem_univ i
    obtain ⟨hasL,hasR⟩ := (Finset.mem_filter.mp di).2
    have read : (f i).reads=true := by
      by_contra h
      have both : (f i).left = false ∧ (f i).right = false := by
        have off := Bool.eq_false_iff.mpr h; simpa [Term.reads] using off
      simp [Term.opp,both.1,both.2] at vi
    have absent : center i ∉ J := by
      intro m
      obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp m
      have h := Finset.mem_filter.mp hj
      have same := inj h.1 di eq; subst j
      simp [read] at h
    refine ⟨center i,Finset.mem_image_of_mem center di,absent,?_⟩
    rcases Finset.mem_union.mp vi with r | l
    · have vr : v ∈ (f i).r := by
        cases eq : (f i).left <;> simp_all
      obtain ⟨x,xl⟩ := hasL
      rcases star i x xl v vr with eq | eq
      · exact Or.inr (eq ▸ rect i x xl v vr)
      · exact Or.inl eq.symm
    · have vl : v ∈ (f i).l := by
        cases eq : (f i).right <;> simp_all
      obtain ⟨y,yr⟩ := hasR
      rcases star i v vl y yr with eq | eq
      · exact Or.inl eq.symm
      · exact Or.inr (eq ▸ (flip y v).trans (rect i v vl y yr))

end PetersenDiagonalStars
