import PEqualNP.Defs

namespace Plane920
open PEqualNP.CircuitLowerBounds
abbrev V := Fin 13
abbrev Input := V → Bool
def line (w : V) := ({0,1,3,9} : Finset V).image (fun u => u+w)
def supp (x : Input) := Finset.univ.filter (fun i => x i=true)
def co (w : V) : Input := fun v => decide (v ∉ line w)
def up (w v : V) : Input := fun i => co w i || decide (i=v)
def target (w : V) (x : Input) := decide (∃ i ∈ line w, x i=true)
def read (gs : List Gate) (idx : Nat) (x : Input) := (Circuit.mk gs idx).eval (List.ofFn x)
abbrev Correct (gs : List Gate) (out : V → Nat) :=
  ∀ w x, 9 ≤ (supp x).card → read gs (out w) x = target w x

theorem line_size : ∀ w, (line w).card = 4 := by decide +kernel
theorem co_weight : ∀ w, (supp (co w)).card = 9 := by decide +kernel
theorem co_table : ∀ w t, target w (co t) = decide (w≠t) := by decide +kernel
theorem up_weight : ∀ w v, v ∈ line w → (supp (up w v)).card=10 := by decide +kernel
theorem up_table : ∀ w v, v ∈ line w → ∀ t, target t (up w v)=true := by decide +kernel
theorem raw_mismatch : ∀ w v, ∃ t, co t v ≠ target w (co t) := by decide +kernel
theorem on_row : ∀ w, ∃ t, target w (co t)=true := by decide +kernel

theorem target_false {w : V} {x : Input} (heavy : 9 ≤ (supp x).card) :
    target w x = false ↔ x = co w := by
  constructor
  · intro h
    have incl : supp x ⊆ supp (co w) := by
      intro v hv
      have on := (Finset.mem_filter.mp hv).2
      have no : v ∉ line w := by
        intro here
        have yes : target w x = true := decide_eq_true ⟨v,here,on⟩
        exact Bool.false_ne_true (h.symm.trans yes)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true no⟩
    have eq : supp x = supp (co w) := Finset.eq_of_subset_of_card_le incl (by simpa only [co_weight] using heavy)
    funext v
    apply Bool.eq_iff_iff.mpr
    have mem : v ∈ supp x ↔ v ∈ supp (co w) := eq ▸ Iff.rfl
    simpa only [supp,Finset.mem_filter,Finset.mem_univ,true_and] using mem
  · rintro rfl
    simpa using co_table w w

theorem boundary {gs : List Gate} {out : V → Nat} (h : Correct gs out) (w t : V) :
    read gs (out w) (co t) = decide (w≠t) :=
  (h w _ ((co_weight t).ge)).trans (co_table w t)

theorem star {gs : List Gate} {out : V → Nat} (h : Correct gs out) (w v : V) (hv : v ∈ line w) :
    read gs (out w) (co w)=false ∧ (∀ t, read gs (out t) (up w v)=true) ∧
      (∀ t, t≠w → read gs (out t) (co w)=true) := by
  refine ⟨by simpa using boundary h w w,?_,?_⟩
  · intro t
    exact (h t _ (by rw [up_weight w v hv]; decide)).trans (up_table w v hv t)
  · intro t diff
    simpa [diff] using boundary h t w

def run (gs : List Gate) (xs : List Bool) := (Circuit.mk gs 0).wires xs
def bit (g : Gate) (xs : List Bool) := g.op.eval (g.inputs.map (fun w => xs.getD w false))
theorem trailing (gs : List Gate) (xs : List Bool) :
    ∃ ys, run gs xs = xs ++ ys ∧ ys.length = gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[],by simp [run,Circuit.wires],rfl⟩
  | cons g gs ih =>
    obtain ⟨ys,eq,len⟩ := ih (xs++[bit g xs])
    exact ⟨bit g xs :: ys,by change run gs (xs++[bit g xs]) = xs ++ (bit g xs :: ys); simpa only [List.append_assoc,List.singleton_append] using eq,by simp [len]⟩

theorem raw_read (gs : List Gate) (x : Input) (v : V) : read gs v.val x = x v := by
  obtain ⟨ys,eq,_⟩ := trailing gs (List.ofFn x)
  change (run gs (List.ofFn x)).getD v.val false = _
  rw [eq,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa only [List.length_ofFn] using v.isLt),
    List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using v.isLt)]
  exact List.getElem_ofFn _

theorem high_read (gs : List Gate) (x : Input) (i : Nat) (hi : 13 + gs.length ≤ i) : read gs i x = false := by
  obtain ⟨ys,eq,len⟩ := trailing gs (List.ofFn x)
  change (run gs (List.ofFn x)).getD i false = _
  rw [eq,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa only [List.length_append,List.length_ofFn,len] using hi)]
  rfl

theorem output_bounds {gs : List Gate} {out : V → Nat} (h : Correct gs out) (w : V) :
    13 ≤ out w ∧ out w < 13+gs.length := by
  constructor
  · by_contra! low
    let v : V := ⟨out w,low⟩
    obtain ⟨t,bad⟩ := raw_mismatch w v
    exact bad ((raw_read gs (co t) v).symm.trans (h w _ (co_weight t).ge))
  · by_contra! high
    obtain ⟨t,on⟩ := on_row w
    exact Bool.false_ne_true ((high_read gs (co t) (out w) high).symm.trans ((h w _ (co_weight t).ge).trans on))

theorem separate {gs : List Gate} {out : V → Nat} (h : Correct gs out) : Function.Injective out := by
  intro a b eq
  by_contra diff
  have x := boundary h a a
  have y := boundary h b a
  rw [eq] at x
  simp [Ne.symm diff,x] at y

theorem thirteen {gs : List Gate} {out : V → Nat} (h : Correct gs out) : 13 ≤ gs.length := by
  let f (w : V) : Fin gs.length := ⟨out w-13,by have := output_bounds h w; omega⟩
  have inj : Function.Injective f := by
    intro a b eq
    apply separate h
    have d := congrArg Fin.val eq
    change out a-13 = out b-13 at d
    have := output_bounds h a
    have := output_bounds h b
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f inj
end Plane920

namespace Plane920.OrSupport
open PEqualNP.CircuitLowerBounds
abbrev SetV := Finset V
def hit (x : Input) (s : SetV) := decide (∃ v ∈ s, x v = true)
theorem empty_hit (x : Input) : hit x ∅ = false := by simp [hit]
theorem union_hit (x : Input) (s t : SetV) : hit x (s∪t) = (hit x s || hit x t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [hit,decide_eq_true_eq,Finset.mem_union,Bool.or_eq_true]
  aesop

def gather (xs : List SetV) : List Nat → SetV
  | [] => ∅
  | w::ws => xs.getD w ∅ ∪ gather xs ws
def start : List SetV := List.ofFn (fun v : V => {v})
def emit (xs : List SetV) : List Gate → List SetV
  | [] => []
  | g::gs => let s := gather xs g.inputs; s :: emit (xs++[s]) gs

theorem hit_get (x : Input) (xs : List SetV) (i : Nat) :
    (xs.map (hit x)).getD i false = hit x (xs.getD i ∅) := by
  induction xs generalizing i with
  | nil => simp [empty_hit]
  | cons a xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem gathered (x : Input) (xs : List SetV) (ins : List Nat) :
    (ins.map (fun w => (xs.map (hit x)).getD w false)).any id = hit x (gather xs ins) := by
  induction ins with
  | nil => simp [gather,empty_hit]
  | cons a t ih => simp only [gather,union_hit,List.map_cons,List.any_cons,id_eq,hit_get,←ih]

theorem runs (gs : List Gate) (ops : ∀ g∈gs, g.op=.or) (xs : List SetV) (x : Input) :
    run gs (xs.map (hit x)) = (xs++emit xs gs).map (hit x) := by
  induction gs generalizing xs with
  | nil => simp [run,Circuit.wires,emit]
  | cons g gs ih =>
    let s := gather xs g.inputs
    have go : g.op = .or := ops g (by simp)
    have val : bit g (xs.map (hit x)) = hit x s := by
      unfold bit
      rw [go]; exact gathered x xs g.inputs
    change run gs (xs.map (hit x) ++ [bit g (xs.map (hit x))]) = _
    rw [val,← List.map_singleton (f := hit x) (a := s),← List.map_append,
      ih (fun h mh => ops h (by simp [mh])) (xs++[s])]
    simp [emit,s]

theorem initial (x : Input) : start.map (hit x) = List.ofFn x := by
  rw [start,List.map_ofFn]
  congr 1
  funext v
  simp [hit]

def source (gs : List Gate) (idx : Nat) := (start++emit start gs).getD idx ∅
theorem evaluates (gs : List Gate) (ops : ∀ g∈gs, g.op=.or) (idx : Nat) (x : Input) :
    read gs idx x = hit x (source gs idx) := by
  change (run gs (List.ofFn x)).getD idx false = _
  rw [←initial x,runs gs ops start x,hit_get]
  rfl

theorem exact_support {gs : List Gate} {out : V → Nat} (ops : ∀ g ∈ gs, g.op=.or)
    (h : Correct gs out) (w : V) : source gs (out w) = line w := by
  let S := source gs (out w)
  have zeros : hit (co w) S = false := by
    rw [← evaluates gs ops]; simpa using boundary h w w
  have sub : S ⊆ line w := by
    intro v hv
    by_contra missing
    have on : hit (co w) S = true := decide_eq_true ⟨v,hv,decide_eq_true missing⟩
    exact Bool.false_ne_true (zeros.symm.trans on)
  apply Finset.Subset.antisymm sub
  intro v hv
  have yes : hit (up w v) S = true := (evaluates gs ops _ _).symm.trans ((star h w v hv).2.1 w)
  obtain ⟨t,ht,htv⟩ := of_decide_eq_true yes
  have lo : co w t = false := by simp [co,sub ht]
  have eq : t = v := by simpa only [up,lo,Bool.false_or,decide_eq_true_eq] using htv
  exact eq ▸ ht
end Plane920.OrSupport

namespace Plane920.OrSupport

abbrev Own (L s : SetV) := s ⊆ L ∧ 1 < s.card
def marks (L : SetV) (xs : List SetV) := xs.filter (fun s => decide (Own L s))
def Inv (L : SetV) (xs : List SetV) := ∀ s ∈ xs, s ⊆ L →
  (marks L xs).length < 3 → s.card ≤ (marks L xs).length+1
abbrev Present (xs : List SetV) (s : SetV) := s=∅ ∨ s∈xs

theorem readable (xs : List SetV) (i : Nat) : Present xs (xs.getD i ∅) := by
  by_cases h : i<xs.length
  · right; rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]; exact List.getElem_mem _
  · left; simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem binary (xs : List SetV) (ins : List Nat) (arity : ins.length≤2) :
    ∃ u v, Present xs u ∧ Present xs v ∧ gather xs ins = u∪v := by
  cases ins with
  | nil => exact ⟨∅,∅,Or.inl rfl,Or.inl rfl,by simp [gather]⟩
  | cons i more =>
    cases more with
    | nil => exact ⟨xs.getD i ∅,∅,readable xs i,Or.inl rfl,rfl⟩
    | cons j final =>
      cases final with
      | nil => exact ⟨xs.getD i ∅,xs.getD j ∅,readable xs i,readable xs j,by simp [gather]⟩
      | cons k rem => simp at arity

theorem only_one {L : SetV} {xs : List SetV} {u v : SetV} (low : (marks L xs).length ≤ 1)
    (hu : Present xs u) (hv : Present xs v) (pu : Own L u) (pv : Own L v) : u=v := by
  have put {s : SetV} (hs : Present xs s) (ps : Own L s) : s ∈ (marks L xs).toFinset := by
    rcases hs with rfl|mem
    · have z := ps.2; simp at z
    · exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨mem,decide_eq_true ps⟩)
  exact Finset.card_le_one.mp ((List.toFinset_card_le _).trans low) _ (put hu pu) _ (put hv pv)

theorem step {L : SetV} {xs : List SetV} {u v : SetV} (prior : Inv L xs)
    (hu : Present xs u) (hv : Present xs v) : Inv L (xs++[u∪v]) := by
  intro s mem sub small
  let n := (marks L xs).length
  let m := (marks L (xs++[u∪v])).length
  have count : m = n + (if Own L (u∪v) then 1 else 0) := by
    by_cases qual : Own L (u∪v) <;> simp [m,n,marks,qual]
    intro lu lv
    exact Nat.le_of_not_gt (fun sz => qual ⟨Finset.union_subset lu lv,sz⟩)
  change m < 3 at small
  change s.card ≤ m+1
  have le : n≤m := by rw [count]; omega
  have bound {s : SetV} (hs : Present xs s) (hin : s⊆L) : s.card ≤ n+1 := by
    rcases hs with rfl|hm
    · simp
    · exact prior s hm hin (lt_of_le_of_lt le small)
  rcases List.mem_append.mp mem with old|fresh
  · exact (bound (Or.inr old) sub).trans (by omega)
  obtain rfl : s=u∪v := List.mem_singleton.mp fresh
  have inside := Finset.union_subset_iff.mp sub
  have ub := bound hu inside.1
  have vb := bound hv inside.2
  by_cases large : 1 < (u∪v).card
  · have q : Own L (u∪v) := ⟨sub,large⟩
    rw [ite_eq_left q] at count
    have rare : n ≤ 1 := by omega
    by_cases bigU : 1 < u.card
    · by_cases bigV : 1 < v.card
      · have same := only_one rare hu hv ⟨inside.1,bigU⟩ ⟨inside.2,bigV⟩
        rw [same,Finset.union_idempotent]
        omega
      · exact (Finset.card_union_le _ _).trans (by omega)
    · exact (Finset.card_union_le _ _).trans (by omega)
  · omega

theorem initial_inv (L : SetV) : Inv L start := by
  intro s mem _ _
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
  simp

theorem last_inv (L : SetV) (gs : List PEqualNP.CircuitLowerBounds.Gate) (arity : ∀ g∈gs, g.inputs.length≤2)
    (xs : List SetV) (beginning : Inv L xs) : Inv L (xs++emit xs gs) := by
  induction gs generalizing xs with
  | nil => simpa [emit] using beginning
  | cons g gs ih =>
    obtain ⟨u,v,hu,hv,eq⟩ := binary xs g.inputs (arity _ (by simp))
    have inv : Inv L (xs++[gather xs g.inputs]) := eq ▸ step beginning hu hv
    have final := ih (fun h hm => arity h (by simp [hm])) _ inv
    simpa [emit] using final

theorem three_runs {gs : List PEqualNP.CircuitLowerBounds.Gate} {out : V → Nat}
    (ops : ∀ g∈gs, g.op=.or) (arity : ∀ g∈gs,g.inputs.length≤2) (h : Correct gs out) (w : V) :
    3 ≤ (marks (line w) (start++emit start gs)).length := by
  have total := last_inv (line w) gs arity start (initial_inv _)
  have exactS := exact_support ops h w
  have inlist : line w ∈ start++emit start gs := by
    have hr := readable (start++emit start gs) (out w)
    change Present _ (source gs (out w)) at hr
    rw [exactS] at hr
    rcases hr with impossible|right
    · have z := line_size w; rw [impossible] at z; contradiction
    · exact right
  by_contra! small
  have size := total (line w) inlist (Finset.Subset.refl _) small
  rw [line_size] at size
  omega

end Plane920.OrSupport

namespace Plane920.OrSupport
open PEqualNP.CircuitLowerBounds

theorem line_pair : ∀ a b : V, a≠b → ((line a)∩(line b)).card ≤ 1 := by decide +kernel

end Plane920.OrSupport

namespace Plane920.Pencil
open PEqualNP.CircuitLowerBounds Plane920.OrSupport

def supportTail (frozen : Finset Nat) (xs : List SetV) : List Gate → List SetV
  | [] => []
  | g::gs =>
    let s := if xs.length ∈ frozen then ∅ else gather xs g.inputs
    s :: supportTail frozen (xs++[s]) gs

def support (frozen : Finset Nat) (gs : List Gate) (i : Nat) :=
  (start++supportTail frozen start gs).getD i ∅

theorem read_append {α : Type} (xs : List α) (a d : α) (i : Nat) :
    (xs++[a]).getD i d = if i=xs.length then a else xs.getD i d := by
  induction xs generalizing i with
  | nil => cases i <;> simp
  | cons x xs ih => cases i with
    | zero => simp
    | succ i => simpa only [List.cons_append,List.getD_cons_succ,List.length_cons,Nat.add_one_inj] using ih i

theorem next_read (g : Gate) (gs : List Gate) (xs : List Bool) :
    (run (g::gs) xs).getD xs.length false = bit g xs := by
  obtain ⟨rest,eq,_⟩ := trailing gs (xs++[bit g xs])
  change (run gs (xs++[bit g xs])).getD xs.length false = _
  rw [eq,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp),←List.getD_eq_getElem?_getD,read_append]
  simp

abbrev Agree (x y : Input) (s : SetV) := ∀ v∈s, x v=y v
def Valid (x y : Input) (as bs : List Bool) (xs : List SetV) :=
  as.length=xs.length ∧ bs.length=xs.length ∧
    ∀ i, Agree x y (xs.getD i ∅) → as.getD i false = bs.getD i false

theorem advance {x y : Input} {as bs : List Bool} {xs : List SetV} (prev : Valid x y as bs xs)
    (a b : Bool) (s : SetV) (cert : Agree x y s → a=b) : Valid x y (as++[a]) (bs++[b]) (xs++[s]) := by
  refine ⟨by simp [prev.1],by simp [prev.2.1],?_⟩
  intro i
  by_cases on : i = xs.length
  · simpa only [read_append,prev.1,prev.2.1,ite_eq_left on] using cert
  · simpa only [read_append,prev.1,prev.2.1,ite_eq_right on] using prev.2.2 i

theorem gather_mem (xs : List SetV) (ins : List Nat) {i : Nat} (member : i∈ins) :
    xs.getD i ∅ ⊆ gather xs ins := by
  induction ins with
  | nil => simp at member
  | cons j js ih =>
    rcases List.mem_cons.mp member with rfl|h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

theorem transfer (f : Finset Nat) (gs : List Gate) (x y : Input) (as bs : List Bool) (xs : List SetV)
    (initial : Valid x y as bs xs) (freeze : ∀ i∈f, (run gs as).getD i false=(run gs bs).getD i false) :
    Valid x y (run gs as) (run gs bs) (xs++supportTail f xs gs) := by
  induction gs generalizing xs as bs with
  | nil => simpa [run,Circuit.wires,supportTail] using initial
  | cons g gs ih =>
    let s := if xs.length ∈ f then ∅ else gather xs g.inputs
    have gsame (ok : Agree x y s) : bit g as=bit g bs := by
      by_cases drop : xs.length ∈ f
      · have eq := freeze xs.length drop
        simpa only [← initial.1, next_read] using (show (run (g::gs) as).getD as.length false=(run (g::gs) bs).getD bs.length false from initial.1.symm ▸ initial.2.1.symm ▸ eq)
      · have share : Agree x y (gather xs g.inputs) := by simpa [s,drop] using ok
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i used
        exact initial.2.2 i (fun v h => share v (gather_mem xs g.inputs used h))
    have after := advance initial (bit g as) (bit g bs) s gsame
    have final := ih (as++[bit g as]) (bs++[bit g bs]) (xs++[s]) after freeze
    change Valid x y (run gs (as++[bit g as])) (run gs (bs++[bit g bs])) _
    simpa only [supportTail,List.append_assoc,List.singleton_append,s] using final

theorem start_valid (x y : Input) : Valid x y (List.ofFn x) (List.ofFn y) start := by
  refine ⟨by simp [start],by simp [start],?_⟩
  intro i agree
  by_cases hi : i < 13
  · let v : V := ⟨i,hi⟩
    have raw (x : Input) : (List.ofFn x).getD i false = x v := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hi)]
      exact List.getElem_ofFn _
    have anchor : start.getD i ∅ = {v} := by
      rw [start,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hi)]
      exact List.getElem_ofFn _
    rw [raw x,raw y]
    exact agree v (by rw [anchor]; exact Finset.mem_singleton_self v)
  · have away (x : Input) : (List.ofFn x).getD i false = false := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)]; rfl
    rw [away x,away y]

theorem separated_wires (f : Finset Nat) (gs : List Gate) (x y : Input)
    (freeze : ∀ i∈f, read gs i x=read gs i y) (i : Nat)
    (agree : Agree x y (support f gs i)) : read gs i x = read gs i y :=
  (transfer f gs x y _ _ start (start_valid x y) freeze).2.2 i agree

def outsiders (p : V) := Finset.univ.filter (fun w : V => p∉line w)
def frozen (out : V → Nat) (p : V) := (outsiders p).image out
theorem nine : ∀ p, (outsiders p).card=9 := by decide +kernel
theorem nine_gates {gs : List Gate} {out : V → Nat} (h : Correct gs out) (p : V) :
    (frozen out p).card = 9 ∧ ∀ i ∈ frozen out p, 13 ≤ i ∧ i < 13 + gs.length := by
  refine ⟨(Finset.card_image_of_injective _ (separate h)).trans (nine p),?_⟩
  rintro i hi
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hi
  exact output_bounds h w

theorem requires {gs : List Gate} {out : V → Nat} (h : Correct gs out) (p w : V) (inLine : p∈line w) :
    line w ⊆ support (frozen out p) gs (out w) := by
  intro v hv
  by_contra missing
  have rows := star h w v hv
  have frozenSame : ∀ i∈frozen out p, read gs i (co w)=read gs i (up w v) := by
    intro i hi
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hi
    have ne : t≠w := fun eq => (Finset.mem_filter.mp ht).2 (eq ▸ inLine)
    exact (rows.2.2 t ne).trans (rows.2.1 t).symm
  have equal := separated_wires _ gs (co w) (up w v) frozenSame (out w) (by
    intro i hi
    have ne : i≠v := fun eq => missing (eq ▸ hi)
    simp [up,ne])
  exact Bool.false_ne_true (rows.1.symm.trans (equal.trans (rows.2.1 w)))
end Plane920.Pencil

namespace Plane920.Pencil
open PEqualNP.CircuitLowerBounds Plane920.OrSupport

def colors (f : V → V) := Finset.univ.image f
def Hom (f : V → V) (s : SetV) := ∀ a∈s, ∀ b∈s, f a=f b
def Uniform (f : V → V) (xs : List SetV) := ∀ s∈xs, Hom f s

theorem empty_hom (f : V → V) : Hom f ∅ := by intro a h; simp at h
theorem available_hom {f : V → V} {xs : List SetV} (h : Uniform f xs) {s : SetV} (read : Present xs s) : Hom f s := by
  rcases read with rfl|hr
  · exact empty_hom _
  · exact h _ hr

noncomputable def pivot (f : V → V) (s : SetV) : V := if ne : s.Nonempty then f ne.choose else 0
theorem unique_color {f : V → V} {s : SetV} (h : Hom f s) {i : V} (mem : i∈s) : f i = pivot f s := by
  have ne : s.Nonempty := ⟨i,mem⟩
  simpa only [pivot,dite_eq_left ne] using h i mem ne.choose ne.choose_spec

theorem merge {f : V → V} {xs : List SetV} {u v : SetV} (old : Uniform f xs)
    (ua : Present xs u) (va : Present xs v) :
    ∃ g : V → V, Uniform g (xs++[u∪v]) ∧ (colors f).card ≤ (colors g).card+1 := by
  let a := pivot f u
  let b := pivot f v
  let adjust (t : V) := if t=b then a else t
  let g := adjust ∘ f
  have A : adjust a = a := by by_cases e : a=b <;> simp [adjust,e]
  have B : adjust b = a := by simp [adjust]
  have homogeneous {i : V} (h : i∈u∪v) : g i=a := by
    rcases Finset.mem_union.mp h with iu|iv
    · exact (congrArg adjust (unique_color (available_hom old ua) iu)).trans A
    · exact (congrArg adjust (unique_color (available_hom old va) iv)).trans B
  refine ⟨g,?_,?_⟩
  · intro s hs
    rcases List.mem_append.mp hs with orig|new
    · exact fun i hi j hj => congrArg adjust (old s orig i hi j hj)
    · obtain rfl := List.mem_singleton.mp new
      exact fun i hi j hj => (homogeneous hi).trans (homogeneous hj).symm
  · have incl : colors f ⊆ insert b (colors g) := by
      intro t ht
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
      by_cases eq : f i=b
      · exact Finset.mem_insert.mpr (Or.inl eq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simp [g,adjust,eq]⟩))
    exact (Finset.card_le_card incl).trans (Finset.card_insert_le _ _)

def paid (z : Finset Nat) (i n : Nat) := Finset.Ico i (i+n) \ z
theorem paid_step (z : Finset Nat) (i n : Nat) :
    (paid z i (n+1)).card = (paid z (i+1) n).card + (if i∈z then 0 else 1) := by
  have unseen : i ∉ paid z (i+1) n := by simp [paid]
  by_cases stopped : i∈z
  · have eq : paid z i (n+1) = paid z (i+1) n := by
      ext k
      simp only [paid,Finset.mem_sdiff,Finset.mem_Ico]
      by_cases same : k=i
      · subst k; simp [stopped]
      · have lo : i ≤ k ↔ i+1 ≤ k := by omega
        have hi : i+(n+1) = (i+1)+n := by omega
        rw [lo,hi]
    simp [eq,stopped]
  · have eq : paid z i (n+1) = insert i (paid z (i+1) n) := by
      ext k
      simp only [paid,Finset.mem_sdiff,Finset.mem_Ico,Finset.mem_insert]
      by_cases same : k=i
      · subst k; simp [stopped]
      · have lo : i ≤ k ↔ i+1 ≤ k := by omega
        have hi : i+(n+1) = (i+1)+n := by omega
        rw [lo,hi]; simp only [same,false_or]
    simp [eq,stopped,unseen]

theorem components (gs : List Gate) (arity : ∀ g∈gs, g.inputs.length ≤ 2) (z : Finset Nat)
    (xs : List SetV) (f : V → V) (initial : Uniform f xs) :
    ∃ g : V → V, Uniform g (xs++supportTail z xs gs) ∧
      (colors f).card ≤ (colors g).card + (paid z xs.length gs.length).card := by
  induction gs generalizing xs f with
  | nil => exact ⟨f,by simpa [supportTail] using initial,by simp [paid]⟩
  | cons gate gs ih =>
    let s := if xs.length ∈ z then ∅ else gather xs gate.inputs
    have one : ∃ k : V → V, Uniform k (xs++[s]) ∧
        (colors f).card ≤ (colors k).card+(if xs.length∈z then 0 else 1) := by
      by_cases frozen : xs.length ∈ z
      · refine ⟨f,?_,by simp [frozen]⟩
        intro t ht
        rcases List.mem_append.mp ht with prev|fresh
        · exact initial t prev
        · obtain rfl := List.mem_singleton.mp fresh
          simpa [s,frozen] using empty_hom f
      · obtain ⟨u,v,hu,hv,eq⟩ := binary xs gate.inputs (arity _ (by simp))
        simpa only [s,ite_eq_right frozen,eq] using merge initial hu hv
    obtain ⟨k,hk,cost⟩ := one
    obtain ⟨g,hg,rest⟩ := ih (fun a ma => arity a (by simp [ma])) (xs++[s]) k hk
    refine ⟨g,by simpa only [supportTail,List.append_assoc,List.singleton_append,s] using hg,?_⟩
    simp only [List.length_append,List.length_singleton] at rest
    rw [List.length_cons,paid_step]
    omega

theorem pencil_covers : ∀ p v : V, ∃ w : V, p∈line w ∧ v∈line w := by decide +kernel

theorem twenty_one {gs : List Gate} {out : V → Nat} (arity : ∀ g∈gs, g.inputs.length ≤ 2)
    (h : Correct gs out) : 21 ≤ gs.length := by
  let p : V := 0
  let z := frozen out p
  have initial : Uniform id start := by
    intro s mem
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro i hi j hj
    change i=j
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  obtain ⟨g,endState,paidEnough⟩ := components gs arity z start id initial
  have total : ∀ v, g v = g p := by
    intro v
    obtain ⟨w,hp,hv⟩ := pencil_covers p v
    have necessary := requires h p w hp
    have hm := available_hom endState (readable (start++supportTail z start gs) (out w))
    exact hm v (necessary hv) p (necessary hp)
  have single : (colors g).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    exact (total i).trans (total j).symm
  have size : (colors (id : V → V)).card=13 := by decide +kernel
  have len : start.length=13 := by simp [start]
  rw [size,len] at paidEnough
  have excl := nine_gates h p
  have sub : z ⊆ Finset.Ico 13 (13+gs.length) := fun i zi => Finset.mem_Ico.mpr (excl.2 i zi)
  have count : (paid z 13 gs.length).card = gs.length-9 := by
    rw [paid,Finset.card_sdiff_of_subset sub,Nat.card_Ico,excl.1]
    omega
  rw [count] at paidEnough
  omega

end Plane920.Pencil

namespace Plane920.Pencil
open PEqualNP.CircuitLowerBounds Plane920.OrSupport

theorem tail_len (z : Finset Nat) (xs : List SetV) (gs : List Gate) :
    (supportTail z xs gs).length=gs.length := by
  induction gs generalizing xs with
  | nil => rfl
  | cons a b ih => simp [supportTail,ih]
theorem tail_append (z : Finset Nat) (xs : List SetV) (pre suf : List Gate) :
    supportTail z xs (pre++suf) = supportTail z xs pre ++
      supportTail z (xs++supportTail z xs pre) suf := by
  induction pre generalizing xs with
  | nil => simp [supportTail]
  | cons a t ih => simp only [List.cons_append,supportTail,ih,List.append_assoc,List.nil_append]

theorem unchanged {z y : Finset Nat} (xs : List SetV) (gs : List Gate)
    (same : ∀ i, xs.length ≤ i → i < xs.length + gs.length → (i ∈ z ↔ i ∈ y)) :
    supportTail z xs gs = supportTail y xs gs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons a gs ih =>
    have eq := same xs.length (by omega) (by simp)
    simp only [supportTail,eq,List.cons.injEq,true_and]
    apply ih
    intro i lo hi
    simp only [List.length_append,List.length_singleton] at lo hi
    apply same i (by omega) (by simp; omega)

theorem after_prefix (z : Finset Nat) (xs : List SetV) (pre : List Gate) (g : Gate) (post : List Gate) :
    (xs++supportTail z xs (pre++g::post)).getD (xs.length+pre.length) ∅ =
    (if xs.length+pre.length∈z then ∅ else gather (xs++supportTail z xs pre) g.inputs) := by
  let base := xs++supportTail z xs pre
  have len : base.length=xs.length+pre.length := by simp [base,tail_len]
  rw [tail_append,←List.append_assoc]
  change (base++(_ :: _)).getD (xs.length+pre.length) ∅ = _
  rw [←len,List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega),Nat.sub_self]
  simp [base,tail_len]

def terminals (out : V → Nat) := Finset.univ.image out

theorem terminal_support {gs : List Gate} {out : V → Nat} (h : Correct gs out)
    (w : V) (j : Fin gs.length) (wire : 13+j.val = out w) :
    line w ⊆ gather (start++supportTail (terminals out) start (gs.take j.val)) gs[j.val].inputs := by
  let z := terminals out
  let y := z.erase (out w)
  let left := gs.take j.val
  let right := gs.drop (j.val+1)
  have len : left.length=j.val := by simp [left]
  have n : start.length=13 := by simp [start]
  have cut : left++gs[j.val]::right = gs := by
    simp [left,right]
  have prefixEq : supportTail y start left = supportTail z start left := by
    apply unchanged
    intro i lo hi
    rw [n,len,wire] at hi
    simp [y,ne_of_lt hi]
  have see : support y gs (out w) = gather (start++supportTail z start left) gs[j.val].inputs := by
    unfold support
    conv_lhs => rw [←cut]
    have num : out w=start.length+left.length := by rw [n,len,wire]
    rw [num,after_prefix,←num,ite_eq_right (show out w∉y from Finset.notMem_erase _ _),prefixEq]
  rw [←show gather (start++supportTail z start left) gs[j.val].inputs =
    gather (start++supportTail (terminals out) start (gs.take j.val)) gs[j.val].inputs from rfl,←see]
  intro v hv
  by_contra missing
  have rows := star h w v hv
  have fixed : ∀ i∈y, read gs i (co w)=read gs i (up w v) := by
    intro i hi
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hi
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp mem
    have diff : t≠w := fun e => ne (congrArg out e)
    exact (rows.2.2 t diff).trans (rows.2.1 t).symm
  have bad := separated_wires y gs (co w) (up w v) fixed (out w) (by
    intro i mem
    have ne : i≠v := fun eq => missing (eq ▸ mem)
    simp [up,ne])
  exact Bool.false_ne_true (rows.1.symm.trans (bad.trans (rows.2.1 w)))

end Plane920.Pencil

namespace Plane920.Pencil
open PEqualNP.CircuitLowerBounds Plane920.OrSupport

def two_colors (f : V → V) := ∀ w : V, ∃ a b : V, ∀ v∈line w, f v=a ∨ f v=b
theorem meet : ∀ a b : V, ∃ p, p∈line a ∧ p∈line b := by decide +kernel

theorem no_four (f : V → V) (bound : two_colors f) : (colors f).card ≤ 3 := by
  by_contra! big
  obtain ⟨a,b,c,d,ma,mb,mc,md,ab,ac,ad,bc,bd,cd⟩ := Finset.three_lt_card_iff.mp big
  obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp ma
  obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp mb
  obtain ⟨C,_,rfl⟩ := Finset.mem_image.mp mc
  obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp md
  obtain ⟨u,ua,ub⟩ := pencil_covers A B
  obtain ⟨v,vc,vd⟩ := pencil_covers C D
  obtain ⟨p,up,vp⟩ := meet u v
  have two {w i j k : V} (hi : i∈line w) (hj : j∈line w) (hk : k∈line w) (diff : f i ≠ f j) :
      f k=f i ∨ f k=f j := by
    obtain ⟨x,y,hy⟩ := bound w
    have si := hy i hi
    have sj := hy j hj
    have sk := hy k hk
    grind
  have ucol := two ua ub up ab
  have vcol := two vc vd vp cd
  grind

theorem prefix_uniform {z : Finset Nat} {xs : List SetV} {f : V → V} (gs : List Gate)
    (all : Uniform f (xs++supportTail z xs gs)) (n : Nat) :
    Uniform f (xs++supportTail z xs (gs.take n)) := by
  intro s hs
  apply all
  rw [show xs++supportTail z xs gs = (xs++supportTail z xs (gs.take n)) ++ supportTail z (xs++supportTail z xs (gs.take n)) (gs.drop n) by
    conv_lhs => rw [←List.take_append_drop n gs,tail_append,←List.append_assoc]]
  exact List.mem_append_left _ hs

theorem output_colors {gs : List Gate} {out : V → Nat} {f : V → V}
    (arity : ∀ g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (all : Uniform f (start++supportTail (terminals out) start gs)) : two_colors f := by
  intro w
  have valid := output_bounds h w
  let j : Fin gs.length := ⟨out w-13,by omega⟩
  have atWire : 13+j.val=out w := by change 13+(out w-13)=out w; omega
  let initial := start++supportTail (terminals out) start (gs.take j.val)
  have uni : Uniform f initial := prefix_uniform gs all j.val
  obtain ⟨u,v,hu,hv,prod⟩ := binary initial gs[j.val].inputs (arity _ (List.getElem_mem _))
  have ru := available_hom uni hu
  have rv := available_hom uni hv
  refine ⟨pivot f u,pivot f v,?_⟩
  intro p hp
  have needs : p∈gather initial gs[j.val].inputs := terminal_support h w j atWire hp
  rw [prod] at needs
  exact (Finset.mem_union.mp needs).imp (unique_color ru) (unique_color rv)

theorem twenty_three {gs : List Gate} {out : V → Nat} (arity : ∀ g∈gs,g.inputs.length≤2)
    (h : Correct gs out) : 23 ≤ gs.length := by
  have initial : Uniform id start := by
    intro s mem
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro i hi j hj
    change i=j
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  obtain ⟨f,uni,cost⟩ := components gs arity (terminals out) start id initial
  have cap := no_four f (output_colors arity h uni)
  have n : (colors (id : V → V)).card=13 := by decide
  have len : start.length=13 := by simp [start]
  rw [n,len] at cost
  have occupied : terminals out ⊆ Finset.Ico 13 (13+gs.length) := by
    intro i hi
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr (output_bounds h w)
  have thirteen : (terminals out).card=13 :=
    (Finset.card_image_of_injective _ (separate h)).trans (by decide)
  rw [paid,Finset.card_sdiff_of_subset occupied,Nat.card_Ico,thirteen] at cost
  omega
end Plane920.Pencil

namespace Plane920.Nine
open PEqualNP.CircuitLowerBounds

abbrev R (a b : Bool) := a=true → b=true
theorem get_mono {as bs : List Bool} (h : List.Forall₂ R as bs) (i : Nat) : R (as.getD i false) (bs.getD i false) := by
  induction h generalizing i with
  | nil => exact fun z => z
  | cons head tail ih => cases i with
    | zero => exact head
    | succ i => exact ih i

theorem gates_mono {as bs : List Bool} (h : List.Forall₂ R as bs) (ins : List Nat) :
    R ((ins.map (fun i => as.getD i false)).all id) ((ins.map (fun i => bs.getD i false)).all id) ∧
    R ((ins.map (fun i => as.getD i false)).any id) ((ins.map (fun i => bs.getD i false)).any id) := by
  induction ins with
  | nil => exact ⟨id,id⟩
  | cons i rest ih =>
    simp only [List.map_cons,List.all_cons,List.any_cons,id_eq,R,Bool.and_eq_true,Bool.or_eq_true]
    exact ⟨fun q => ⟨get_mono h i q.1,ih.1 q.2⟩,fun q => q.imp (get_mono h i) ih.2⟩


end Plane920.Nine

namespace Plane920.Parse
open PEqualNP.CircuitLowerBounds
abbrev S := Finset V
def missing (s : S) : Input := fun v => decide (v∉s)
def accepts (gs : List Gate) (wire : Nat) (s : S) := read gs wire (missing s) = false

theorem complement (s : S) : supp (missing s) = Finset.univ \ s := by ext v; simp [supp,missing]

theorem statement {gs : List Gate} {out : V → Nat} (h : Correct gs out) {w : V} {s : S}
    (small : s.card ≤ 4) : accepts gs (out w) s ↔ s=line w := by
  have heavy : 9 ≤ (supp (missing s)).card := by
    rw [complement,Finset.card_sdiff_of_subset (Finset.subset_univ s)]
    have thirteen : (Finset.univ : S).card=13 := by decide
    omega
  unfold accepts
  rw [h w _ heavy,target_false heavy]
  constructor
  · intro eq; ext v
    have atv := congrFun eq v
    simp only [missing,co,decide_eq_decide] at atv
    exact not_iff_not.mp atv
  · rintro rfl; rfl


end Plane920.Parse

namespace Plane920.Parse
open PEqualNP.CircuitLowerBounds

theorem stable (gs : List Gate) (xs : List Bool) (w : Nat) (early : w<xs.length) :
    (run gs xs).getD w false = xs.getD w false := by
  obtain ⟨t,eq,_⟩ := trailing gs xs
  rw [eq,List.getD_eq_getElem?_getD,List.getElem?_append_left early,←List.getD_eq_getElem?_getD]


end Plane920.Parse

namespace Plane920.Parse
open PEqualNP.CircuitLowerBounds

def outIndex {gs : List Gate} {out : V → Nat} (correct : Correct gs out) (w : V) : Fin gs.length :=
  ⟨out w-13,by have := output_bounds correct w; omega⟩
theorem index_eq {gs : List Gate} {out : V → Nat} (h : Correct gs out) (v : V) :
    13+(outIndex h v).val=out v := by change 13+(out v-13)=out v; have := (output_bounds h v).1; omega


end Plane920.Parse

namespace Plane920.Terminal
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport

def overwrite (z : Finset Nat) : List Gate → List Bool → List Bool
  | [],xs => xs
  | g::gs,xs => overwrite z gs (xs++[if xs.length ∈ z then true else bit g xs])

theorem width (z : Finset Nat) (gs : List Gate) (xs : List Bool) : (overwrite z gs xs).length=xs.length+gs.length := by
  induction gs generalizing xs with
  | nil => simp [overwrite]
  | cons g gs ih => simp [overwrite,ih]; omega

theorem run_join (a b : List Gate) (xs : List Bool) : run (a++b) xs = run b (run a xs) := by
  simp only [run,Circuit.wires,List.foldl_append]
theorem run_length (a : List Gate) (xs : List Bool) : (run a xs).length=xs.length+a.length := by
  obtain ⟨ys,eq,len⟩ := trailing a xs
  simp [eq,len]

theorem actual (gs : List Gate) (j : Fin gs.length) (x : Input) :
    read gs (13+j.val) x = bit gs[j.val] (run (gs.take j.val) (List.ofFn x)) := by
  let left := gs.take j.val
  let right := gs.drop (j.val+1)
  have split : left++gs[j.val]::right=gs := by simp [left,right]
  have sz : (run left (List.ofFn x)).length=13+j.val := by simp [run_length,left]
  change (run gs (List.ofFn x)).getD (13+j.val) false = _
  have full := congrArg (fun gates => run gates (List.ofFn x)) split.symm
  rw [full,run_join,←sz,next_read]

theorem agrees (z : Finset Nat) (gs : List Gate) (xs : List Bool)
    (same : ∀ i ∈ z, xs.length ≤ i → i < xs.length+gs.length → (run gs xs).getD i false=true) :
    overwrite z gs xs = run gs xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    have rep : (if xs.length ∈ z then true else bit g xs)=bit g xs := by
      by_cases h : xs.length∈z
      · simp only [ite_eq_left h]
        exact (next_read g gs xs).symm.trans (same _ h (by omega) (by simp))
          |>.symm
      · simp [h]
    change overwrite z gs (xs++[_]) = run gs (xs++[bit g xs])
    rw [rep]
    apply ih
    intro i hz lo hi
    simp only [List.length_append,List.length_singleton] at lo hi
    apply same i hz (by omega) (by simp; omega)

theorem mono_overwrite (gs : List Gate) (basis : ∀ g∈gs,g.op=.and ∨ g.op=.or)
    (z : Finset Nat) (xs ys : List Bool) (inc : List.Forall₂ Nine.R xs ys) :
    List.Forall₂ Nine.R (run gs xs) (overwrite z gs ys) := by
  induction gs generalizing xs ys with
  | nil => exact inc
  | cons g gs ih =>
    have plain : Nine.R (bit g xs) (bit g ys) := by
      rcases basis g (by simp) with a|b
      · simpa only [bit,a,GateOp.eval] using (Nine.gates_mono inc g.inputs).1
      · simpa only [bit,b,GateOp.eval] using (Nine.gates_mono inc g.inputs).2
    have newbit : Nine.R (bit g xs) (if ys.length∈z then true else bit g ys) := by
      split
      · exact fun _ => rfl
      · exact plain
    exact ih (fun a ma => basis a (by simp [ma])) _ _ (List.rel_append inc (.cons newbit .nil))

def value (gs : List Gate) (out : V → Nat) (j : Fin gs.length) (x : Input) :=
  bit gs[j.val] (overwrite (terminals out) (gs.take j.val) (List.ofFn x))

theorem normalized {gs : List Gate} {out : V → Nat} (basis : ∀ g∈gs,g.op=.and ∨ g.op=.or)
    (h : Correct gs out) (w : V) (j : Fin gs.length) (index : 13+j.val=out w) (x : Input)
    (heavy : 9≤(supp x).card) : value gs out j x=target w x := by
  by_cases no : target w x=false
  · have eq := (target_false heavy).mp no
    let left := gs.take j.val
    have same : overwrite (terminals out) left (List.ofFn x)=run left (List.ofFn x) := by
      apply agrees
      intro i hi lo bound
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hi
      have size : (run left (List.ofFn x)).length=13+j.val := by simp [run_length,left]
      have early : out t<13+j.val := by simpa [left] using bound
      have tdiff : t≠w := fun same => by rw [same,←index] at early; omega
      have on := (boundary h t w).trans (decide_eq_true tdiff)
      rw [←eq] at on
      have full : run gs (List.ofFn x) = run (gs.drop j.val) (run left (List.ofFn x)) := by
        conv_lhs => rw [←List.take_append_drop j.val gs,run_join]
      change (run gs (List.ofFn x)).getD (out t) false=true at on
      rw [full,Parse.stable _ _ _ (by rw [size]; exact early)] at on
      exact on
    change bit gs[j.val] (overwrite (terminals out) left (List.ofFn x))=_
    rw [same,← actual gs j x,index]
    exact h _ _ heavy
  · have eq : target w x=true := Bool.eq_true_of_not_eq_false no
    have on := (h w x heavy).trans eq
    rw [←index,actual] at on
    have before := mono_overwrite (gs.take j.val) (fun g mem => basis g (List.mem_of_mem_take mem)) (terminals out)
      (List.ofFn x) (List.ofFn x) (List.forall₂_same.mpr (fun _ _ => id))
    have step : Nine.R (bit gs[j.val] (run (gs.take j.val) (List.ofFn x))) (value gs out j x) := by
      rcases basis gs[j.val] (List.getElem_mem _) with a|b
      · simpa only [bit,value,a,GateOp.eval] using (Nine.gates_mono before gs[j.val].inputs).1
      · simpa only [bit,value,b,GateOp.eval] using (Nine.gates_mono before gs[j.val].inputs).2
    exact (step on).trans eq.symm

theorem supported (z : Finset Nat) (gs : List Gate) (x y : Input) (as bs : List Bool) (xs : List SetV)
    (init : Valid x y as bs xs) :
    Valid x y (overwrite z gs as) (overwrite z gs bs) (xs++supportTail z xs gs) := by
  induction gs generalizing as bs xs with
  | nil => simpa [overwrite,supportTail] using init
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    let a := if as.length∈z then true else bit g as
    let b := if bs.length∈z then true else bit g bs
    have next (ok : Agree x y s) : a=b := by
      by_cases drop : xs.length∈z
      · simp [a,b,init.1,init.2.1,drop]
      · simp only [a,b,init.1,init.2.1,ite_eq_right drop]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i used
        have use : Agree x y (gather xs g.inputs) := by simpa [s,drop] using ok
        exact init.2.2 i (fun v hv => use v (gather_mem xs g.inputs used hv))
    have prev := advance init a b s next
    have endState := ih (as++[a]) (bs++[b]) (xs++[s]) prev
    simpa only [overwrite,supportTail,a,b,s,List.append_assoc,List.singleton_append] using endState

end Plane920.Terminal

namespace Plane920.Terminal
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse
abbrev Region := Finset V
def Active (f : Input → Bool) (s : Region) := f (missing s)=false
def Local (f : Input → Bool) (u : Region) := ∀ x y : Input, Agree x y u → f x=f y

theorem same_on {u : Region} {s t : Region} (eq : ∀ i∈u, i∈s ↔ i∈t) :
    Agree (missing s) (missing t) u := by
  intro i hi
  simp only [missing,decide_eq_decide]
  exact not_congr (eq i hi)

theorem project {f : Input → Bool} {u : Region} (localF : Local f u) (s : Region) :
    f (missing (s∩u)) = f (missing s) :=
  localF _ _ (same_on (fun i h => by simp [h]))

def Minimal (f : Input→Bool) (T : Region) :=
  Active f T ∧ ∀ U : Region, Active f U → U.card ≤ T.card → U=T

theorem crossing {a b : Input→Bool} {u v : Region} {w : V} (af : Local a u) (bf : Local b v)
    (unjoined : Disjoint u v) (covers : line w ⊆ u∪v) (leftOn : (line w∩u).Nonempty)
    (rightOn : (line w∩v).Nonempty) (eqval :
      (∀ s : Region, s.card≤4 → (Active a s ∨ Active b s ↔ s=line w)) ∨
      (∀ s : Region, s.card≤4 → (Active a s ∧ Active b s ↔ s=line w))) :
    Minimal a (line w∩u) ∧ Minimal b (line w∩v) := by
  let T := line w∩u
  let C := line w∩v
  have un : T∪C=line w := by
    ext i; simp only [T,C,Finset.mem_union,Finset.mem_inter]; constructor
    · rintro (h|h) <;> exact h.1
    · intro h
      exact (Finset.mem_union.mp (covers h)).imp (fun e=>⟨h,e⟩) (fun e=>⟨h,e⟩)
  have sep : Disjoint T C := unjoined.mono Finset.inter_subset_right Finset.inter_subset_right
  have sizes : T.card+C.card=4 := by rw [←Finset.card_union_of_disjoint sep,un,line_size]
  have ts : T≠line w := by
    intro e
    obtain ⟨i,hi⟩ := rightOn
    have hL := (Finset.mem_inter.mp hi).1
    have ht : i∈T := e ▸ hL
    exact Finset.disjoint_left.mp unjoined (Finset.mem_inter.mp ht).2 (Finset.mem_inter.mp hi).2
  have cs : C≠line w := by
    intro e
    obtain ⟨i,hi⟩ := leftOn
    have hL := (Finset.mem_inter.mp hi).1
    have hc : i∈C := e ▸ hL
    exact Finset.disjoint_left.mp unjoined (Finset.mem_inter.mp hi).2 (Finset.mem_inter.mp hc).2
  have zeros {f : Input→Bool} {s : Region} (loc : Local f s) (aL : Active f (line w)) :
      Active f (line w∩s) := (project loc (line w)).trans aL
  rcases eqval with weak|both
  · rcases (weak (line w) (line_size w).le).mpr rfl with l|r
    · exact False.elim (ts ((weak T (by omega)).mp (Or.inl (zeros af l))))
    · exact False.elim (cs ((weak C (by omega)).mp (Or.inr (zeros bf r))))
  · have ready := (both (line w) (line_size w).le).mpr rfl
    have A := zeros af ready.1
    have B := zeros bf ready.2
    have main (f g : Input→Bool) (U W : Region) (locf : Local f U) (locg : Local g W)
        (dis : Disjoint U W) (fOn : Active f (line w∩U)) (gOn : Active g (line w∩W))
        (sums : (line w∩U).card+(line w∩W).card=4)
        (law : ∀ x : Region, x.card≤4 → Active f x ∧ Active g x → x=line w) :
        Minimal f (line w∩U) := by
      refine ⟨fOn,?_⟩
      intro X hits size
      let mix := (X∩U) ∪ (line w∩W)
      have cU : (X∩U).card≤X.card := Finset.card_le_card Finset.inter_subset_left
      have small : mix.card≤4 := (Finset.card_union_le _ _).trans (by omega)
      have h1 : f (missing mix)=f (missing X) := locf _ _ (same_on (by
        intro i hi
        have nw : i∉W := Finset.disjoint_left.mp dis hi
        simp [mix,hi,nw]))
      have h2 : g (missing mix)=g (missing (line w∩W)) := locg _ _ (same_on (by
        intro i hi
        have nu : i∉U := Finset.disjoint_left.mp dis.symm hi
        simp [mix,hi,nu]))
      have eq := law mix small ⟨h1.trans hits,h2.trans gOn⟩
      have included : line w∩U ⊆ X := by
        intro i hi
        have inM : i∈mix := eq ▸ (Finset.mem_inter.mp hi).1
        rcases Finset.mem_union.mp inM with a|b
        · exact (Finset.mem_inter.mp a).1
        · exact False.elim (Finset.disjoint_left.mp dis (Finset.mem_inter.mp hi).2 (Finset.mem_inter.mp b).2)
      exact (Finset.eq_of_subset_of_card_le included size).symm
    exact ⟨main a b u v af bf unjoined A B sizes (fun x h => (both x h).mp),
      main b a v u bf af unjoined.symm B A (by simpa only [Nat.add_comm] using sizes)
        (fun x h data => (both x h).mp data.symm)⟩
end Plane920.Terminal

namespace Plane920.Terminal
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse

def live (gs : List Gate) (out : V → Nat) (j : Fin gs.length) (i : Nat) (x : Input) :=
  (overwrite (terminals out) (gs.take j.val) (List.ofFn x)).getD i false
def region (gs : List Gate) (out : V → Nat) (j : Fin gs.length) (i : Nat) :=
  (start++supportTail (terminals out) start (gs.take j.val)).getD i ∅
def globalWire (gs : List Gate) (out : V → Nat) (i : Nat) (x : Input) :=
  (overwrite (terminals out) gs (List.ofFn x)).getD i false

theorem live_local (gs : List Gate) (out : V → Nat) (j : Fin gs.length) (i : Nat) :
    Local (live gs out j i) (region gs out j i) := by
  intro x y eq
  exact (supported _ (gs.take _) x y _ _ start (start_valid x y)).2.2 i eq

theorem ov_append (z : Finset Nat) (a b : List Gate) (xs : List Bool) :
    overwrite z (a++b) xs = overwrite z b (overwrite z a xs) := by
  induction a generalizing xs with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append,overwrite,ih]

theorem ov_stable (z : Finset Nat) (gs : List Gate) (xs : List Bool) (i : Nat) (early : i<xs.length) :
    (overwrite z gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (overwrite z gs (xs++[_])).getD i false = _
    rw [ih _ (by simp; omega),read_append,ite_eq_right (Nat.ne_of_lt early)]

theorem sem_prefix (gs : List Gate) (out : V → Nat) (j : Fin gs.length) (i : Nat) (good : i<13+j.val) :
    live gs out j i = globalWire gs out i := by
  funext x
  unfold globalWire live
  have split := congrArg (fun g => overwrite (terminals out) g (List.ofFn x)) (List.take_append_drop j.val gs).symm
  rw [split,ov_append,ov_stable _ (gs.drop j.val) _ _ (by simpa only [width,List.length_ofFn,List.length_take,Nat.min_eq_left j.isLt.le] using good)]

theorem frozen_high (gs : List Gate) (z : Finset Nat) (xs : List Bool) (i : Nat)
    (zi : i∈z) (lo : xs.length ≤ i) (hi : i<xs.length+gs.length) : (overwrite z gs xs).getD i false=true := by
  induction gs generalizing xs with
  | nil => simp at hi; omega
  | cons g gs ih =>
    change (overwrite z gs (xs++[_])).getD i false=_
    by_cases atI : i=xs.length
    · rw [ov_stable _ _ _ _ (by simp; omega),read_append,ite_eq_left atI,←atI,ite_eq_left zi]
    · apply ih
      · simp; omega
      · simp only [List.length_cons] at hi
        simp; omega

theorem hidden {gs : List Gate} {out : V → Nat} (j : Fin gs.length) (i : Nat) {T : Region}
    (m : Minimal (live gs out j i) T) (big : 2≤T.card) :
    i∈paid (terminals out) 13 gs.length ∧ Minimal (globalWire gs out i) T := by
  have good : i<13+j.val := by
    by_contra! no
    have on : Active (live gs out j i) ∅ := by
      simp only [Active,live,List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simpa only [width,List.length_ofFn,List.length_take,Nat.min_eq_left j.isLt.le] using no)]
      rfl
    have empty := m.2 _ on (by simp)
    rw [←empty] at big
    simp at big
  rw [sem_prefix _ _ _ _ good] at m
  have raw : 13 ≤ i := by
    by_contra! lo
    let v : V := ⟨i,lo⟩
    have on : Active (globalWire gs out i) {v} := by
      unfold Active globalWire
      rw [ov_stable _ _ _ _ (by simpa only [List.length_ofFn] using lo)]
      have rawAt (x : Input) : (List.ofFn x).getD i false = x v := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using lo)]
        exact List.getElem_ofFn _
      rw [rawAt]
      simp [missing]
    have small := m.2 ({v} : Region) on (by rw [Finset.card_singleton]; omega)
    rw [←small,Finset.card_singleton] at big
    omega
  have nz : i∉terminals out := by
    intro present
    have on := m.1
    have off := frozen_high gs _ (List.ofFn (missing T)) i present (by simpa only [List.length_ofFn] using raw)
      (by simp only [List.length_ofFn]; omega)
    exact Bool.false_ne_true (on.symm.trans off)
  exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨raw,by omega⟩,nz⟩,m⟩

theorem minima_eq {f : Input→Bool} {s t : Region} (h : Minimal f s) (k : Minimal f t) : s=t := by
  rcases le_total s.card t.card with a|a
  · exact k.2 s h.1 a
  · exact (h.2 t k.1 a).symm
end Plane920.Terminal

namespace Plane920.Terminal
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse

def Varied (f : V → V) (L : Region) := ∃ a∈L, ∃ b∈L, f a ≠ f b
theorem varied (f : V→V) (bicol : two_colors f) (three : 3 ≤ (colors f).card) (w : V) :
    Varied f (line w) := by
  by_contra none
  unfold Varied at none
  push Not at none
  obtain ⟨p,hp,_⟩ := meet w w
  have pair (i j : V) (dif : f i≠f j) : f p=f i ∨ f p=f j := by
    obtain ⟨t,hi,hj⟩ := pencil_covers i j
    obtain ⟨m,mt,mw⟩ := meet t w
    obtain ⟨a,b,which⟩ := bicol t
    have one := which i hi
    have two := which j hj
    have mid := which m mt
    have same := none p hp m mw
    grind
  obtain ⟨a,b,c,ma,mb,mc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp (by omega : 2<(colors f).card)
  obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp ma
  obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp mb
  obtain ⟨C,_,rfl⟩ := Finset.mem_image.mp mc
  have p1 := pair A B ab
  have p2 := pair A C ac
  have p3 := pair B C bc
  grind

theorem binary_indices {xs : List SetV} {ins : List Nat} {f : V→V} {L : Region}
    (arity : ins.length≤2) (uni : Uniform f xs) (cover : L⊆gather xs ins) (diff : Varied f L) :
    ∃ a b : Nat, ins=[a,b] := by
  obtain ⟨i,hi,j,hj,ne⟩ := diff
  cases ins with
  | nil => simpa [gather] using cover hi
  | cons a tail =>
    cases tail with
    | nil =>
      have all : L⊆xs.getD a ∅ := by simpa [gather] using cover
      have hom := available_hom uni (readable xs a)
      exact False.elim (ne (hom i (all hi) j (all hj)))
    | cons b tail =>
      cases tail with
      | nil => exact ⟨_,_,rfl⟩
      | cons c tail => simp at arity

theorem separate_regions {u v L : Region} {f : V→V} (hu : Hom f u) (hv : Hom f v)
    (cover : L⊆u∪v) (diff : Varied f L) :
    Disjoint u v ∧ (L∩u).Nonempty ∧ (L∩v).Nonempty := by
  obtain ⟨p,lp,q,lq,ne⟩ := diff
  have P := Finset.mem_union.mp (cover lp)
  have Q := Finset.mem_union.mp (cover lq)
  have hits {a b : Region} (hom : Hom f b) (left : p∈a ∨ p∈b) (right : q∈a ∨ q∈b) :
      (L∩a).Nonempty := by
    rcases left with h|h
    · exact ⟨p,Finset.mem_inter.mpr ⟨lp,h⟩⟩
    rcases right with k|k
    · exact ⟨q,Finset.mem_inter.mpr ⟨lq,k⟩⟩
    exact False.elim (ne (hom p h q k))
  have U := hits hv P Q
  have W := hits hu P.symm Q.symm
  refine ⟨Finset.disjoint_left.mpr ?_,U,W⟩
  intro x xu xv
  have eq (i : V) (inL : i∈L) : f i=f x := by
    rcases Finset.mem_union.mp (cover inL) with a|b
    · exact hu i a x xu
    · exact hv i b x xv
  exact ne ((eq p lp).trans (eq q lq).symm)

theorem large_slice {u v : Region} {w : V} (cover : line w⊆u∪v) :
    2≤(line w∩u).card ∨ 2≤(line w∩v).card := by
  have sub : line w⊆(line w∩u)∪(line w∩v) := by
    intro i hi
    exact Finset.mem_union.mpr ((Finset.mem_union.mp (cover hi)).imp
      (fun h => Finset.mem_inter.mpr ⟨hi,h⟩) (fun h => Finset.mem_inter.mpr ⟨hi,h⟩))
  have len := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [line_size] at len
  omega
end Plane920.Terminal

namespace Plane920.Terminal
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse

theorem charged {gs : List Gate} {out : V → Nat} {f : V→V}
    (basis : ∀ g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) {w : V} (mixed : Varied f (line w)) :
    ∃ i∈paid (terminals out) 13 gs.length, ∃ T : Region, 2≤T.card ∧ T⊆line w ∧ Minimal (globalWire gs out i) T := by
  let j := outIndex h w
  have ind : 13+j.val=out w := index_eq h w
  let xs := start++supportTail (terminals out) start (gs.take j.val)
  have uni' : Uniform f xs := prefix_uniform gs uni j.val
  have cover : line w⊆gather xs gs[j.val].inputs := terminal_support h w j ind
  obtain ⟨a,b,ids⟩ := binary_indices (arity _ (List.getElem_mem _)) uni' cover mixed
  let u := region gs out j a
  let v := region gs out j b
  have uv : line w⊆u∪v := by simpa only [u,v,region,xs,ids,gather,Finset.union_empty] using cover
  have hu : Hom f u := available_hom uni' (readable xs a)
  have hv : Hom f v := available_hom uni' (readable xs b)
  obtain ⟨disjoint,left,right⟩ := separate_regions hu hv uv mixed
  have law (s : Region) (small : s.card≤4) : value gs out j (missing s)=false ↔ s=line w := by
    have weight : 9≤(supp (missing s)).card := by
      rw [complement,Finset.card_sdiff_of_subset (Finset.subset_univ s)]
      have total : (Finset.univ : Region).card=13 := by decide
      omega
    rw [normalized basis h w j ind _ weight,←h w _ weight]
    exact statement h small
  have gates :
      (∀ s : Region, s.card≤4 → (Active (live gs out j a) s ∨ Active (live gs out j b) s ↔ s=line w)) ∨
      (∀ s : Region, s.card≤4 → (Active (live gs out j a) s ∧ Active (live gs out j b) s ↔ s=line w)) := by
    rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
    · left
      intro s small
      have logic (p q : Bool) : (p=false ∨ q=false) ↔ (p && q)=false := by cases p <;> cases q <;> decide
      exact (logic _ _).trans (by simpa [value,bit,ids,gate,GateOp.eval,live] using law s small)
    · right
      intro s small
      simpa [Active,value,bit,ids,gate,GateOp.eval,live] using law s small
  obtain ⟨ma,mb⟩ := crossing (live_local gs out j a) (live_local gs out j b) disjoint uv left right gates
  rcases large_slice uv with big|big
  · obtain ⟨mem,minimal⟩ := hidden j a ma big
    exact ⟨a,mem,_,big,Finset.inter_subset_left,minimal⟩
  · obtain ⟨mem,minimal⟩ := hidden j b mb big
    exact ⟨b,mem,_,big,Finset.inter_subset_left,minimal⟩

theorem hidden_count {gs : List Gate} {out : V→Nat} (h : Correct gs out) :
    (paid (terminals out) 13 gs.length).card=gs.length-13 := by
  have occupied : terminals out⊆Finset.Ico 13 (13+gs.length) := by
    intro i hi
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr (output_bounds h w)
  have size : (terminals out).card=13 := (Finset.card_image_of_injective _ (separate h)).trans (by decide)
  rw [paid,Finset.card_sdiff_of_subset occupied,Nat.card_Ico,size]
  omega

theorem three_implies_twenty_six {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (triple : 3≤(colors f).card) :
    26≤gs.length := by
  classical
  have bi := output_colors arity h uni
  choose wire mem T big sub m using fun w => charged basis arity h uni (varied f bi triple w)
  have different : Function.Injective wire := by
    intro a b same
    by_contra ne
    have p := m a
    rw [same] at p
    have eq := minima_eq p (m b)
    have overlap : T a⊆line a∩line b := Finset.subset_inter (sub a) (eq ▸ sub b)
    have lim := (Finset.card_le_card overlap).trans (OrSupport.line_pair a b ne)
    have large := big a
    omega
  have all : Finset.univ.image wire ⊆ paid (terminals out) 13 gs.length := by
    intro i hi
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hi
    exact mem w
  have total := Finset.card_le_card all
  rw [Finset.card_image_of_injective _ different,hidden_count h] at total
  have n : (Finset.univ : Finset V).card=13 := by decide
  omega

theorem twenty_four {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) :
    24≤gs.length := by
  have initial : Uniform id start := by
    intro s mem
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro i hi j hj
    change i=j
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  obtain ⟨f,uni,cost⟩ := components gs arity (terminals out) start id initial
  have n : (colors (id : V→V)).card=13 := by decide
  have len : start.length=13 := by simp [start]
  rw [n,len,hidden_count h] at cost
  by_contra! small
  have triple : 3≤(colors f).card := by omega
  have lower := three_implies_twenty_six basis arity h uni triple
  omega
end Plane920.Terminal

namespace Plane920.Cut
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal

def block (f : V→V) (c : V) := Finset.univ.filter (fun x : V => f x=c)
def degree (A : Region) (w : V) := (line w∩A).card
def weight (t : Nat) := min t (4-t)
noncomputable def reserved (gs : List Gate) (out : V→Nat) (w : V) : Finset Nat := by
  classical
  exact (paid (terminals out) 13 gs.length).filter (fun i => ∃ T : Region, 2≤T.card ∧ T⊆line w ∧ Minimal (globalWire gs out i) T)

theorem block_hom {f : V→V} {s : Region} (h : Hom f s) (c : V) : s⊆block f c ∨ Disjoint s (block f c) := by
  classical
  by_cases yes : ∃ x∈s, f x=c
  · obtain ⟨x,hx,hc⟩ := yes
    exact Or.inl (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(h i hi x hx).trans hc⟩)
  · exact Or.inr (Finset.disjoint_left.mpr (fun {a} ha hb => yes ⟨_,ha,(Finset.mem_filter.mp hb).2⟩))

theorem diff_of_degree (f : V→V) (c w : V) (lo : 0<degree (block f c) w) (hi : degree (block f c) w<4) :
    Varied f (line w) := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp lo
  have outside : (line w \ block f c).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff,Finset.inter_comm]
    change 0 < (line w).card-degree (block f c) w
    rw [line_size]
    omega
  obtain ⟨b,hb⟩ := outside
  obtain ⟨la,ca⟩ := Finset.mem_inter.mp ha
  obtain ⟨lb,cb⟩ := Finset.mem_sdiff.mp hb
  exact ⟨a,la,b,lb,fun e => cb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e ▸ (Finset.mem_filter.mp ca).2⟩)⟩

theorem half_size {f : V→V} {s : Region} (h : Hom f s) (w c : V) (half : degree (block f c) w=2) :
    (line w∩s).card≤2 := by
  rcases block_hom h c with sub|sep
  · exact (Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) sub)).trans half.le
  · have inc : line w∩s ⊆ line w \ block f c := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1,Finset.disjoint_left.mp sep (Finset.mem_inter.mp hx).2⟩
    have bound := Finset.card_le_card inc
    rw [Finset.card_sdiff,Finset.inter_comm (block f c),line_size] at bound
    change (line w∩s).card ≤ 4-degree (block f c) w at bound
    omega
theorem balanced {gs : List Gate} {out : V → Nat} {f : V→V}
    (basis : ∀ g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (w c : V) (half : degree (block f c) w=2) :
    2≤(reserved gs out w).card := by
  classical
  have mixed := diff_of_degree f c w (by omega) (by omega)
  let j := outIndex h w
  have ind : 13+j.val=out w := index_eq h w
  let xs := start++supportTail (terminals out) start (gs.take j.val)
  have uni' : Uniform f xs := prefix_uniform gs uni j.val
  have cover : line w⊆gather xs gs[j.val].inputs := terminal_support h w j ind
  obtain ⟨a,b,ids⟩ := binary_indices (arity _ (List.getElem_mem _)) uni' cover mixed
  let u := region gs out j a
  let v := region gs out j b
  have uv : line w⊆u∪v := by simpa only [u,v,region,xs,ids,gather,Finset.union_empty] using cover
  have hu : Hom f u := available_hom uni' (readable xs a)
  have hv : Hom f v := available_hom uni' (readable xs b)
  obtain ⟨disjoint,left,right⟩ := separate_regions hu hv uv mixed
  have law (s : Region) (small : s.card≤4) : value gs out j (missing s)=false ↔ s=line w := by
    have weight : 9≤(supp (missing s)).card := by
      rw [complement,Finset.card_sdiff_of_subset (Finset.subset_univ s)]
      have total : (Finset.univ : Region).card=13 := by decide
      omega
    rw [normalized basis h w j ind _ weight,←h w _ weight]
    exact statement h small
  have gates :
      (∀ s : Region, s.card≤4 → (Active (live gs out j a) s ∨ Active (live gs out j b) s ↔ s=line w)) ∨
      (∀ s : Region, s.card≤4 → (Active (live gs out j a) s ∧ Active (live gs out j b) s ↔ s=line w)) := by
    rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
    · left
      intro s small
      have logic (p q : Bool) : (p=false ∨ q=false) ↔ (p && q)=false := by cases p <;> cases q <;> decide
      exact (logic _ _).trans (by simpa [value,bit,ids,gate,GateOp.eval,live] using law s small)
    · right
      intro s small
      simpa [Active,value,bit,ids,gate,GateOp.eval,live] using law s small
  obtain ⟨ma,mb⟩ := crossing (live_local gs out j a) (live_local gs out j b) disjoint uv left right gates
  have acap := half_size hu w c half
  have bcap := half_size hv w c half
  have coverAll : line w ⊆ (line w∩u) ∪ (line w∩v) := by
    intro x hx
    exact Finset.mem_union.mpr ((Finset.mem_union.mp (uv hx)).imp
      (fun e => Finset.mem_inter.mpr ⟨hx,e⟩) (fun e => Finset.mem_inter.mpr ⟨hx,e⟩))
  have four := (Finset.card_le_card coverAll).trans (Finset.card_union_le _ _)
  rw [line_size] at four
  have bigA : 2≤(line w∩u).card := by omega
  have bigB : 2≤(line w∩v).card := by omega
  obtain ⟨pa,xa⟩ := hidden j a ma bigA
  obtain ⟨pb,xb⟩ := hidden j b mb bigB
  have ne : a≠b := by
    intro eq
    have sets : u=v := congrArg (region gs out j) eq
    obtain ⟨x,hx⟩ := left
    have xu := (Finset.mem_inter.mp hx).2
    exact Finset.disjoint_left.mp disjoint xu (sets ▸ xu)
  have memA : a∈reserved gs out w := Finset.mem_filter.mpr ⟨pa,_,bigA,Finset.inter_subset_left,xa⟩
  have memB : b∈reserved gs out w := Finset.mem_filter.mpr ⟨pb,_,bigB,Finset.inter_subset_left,xb⟩
  exact Finset.one_lt_card.mpr ⟨a,memA,b,memB,ne⟩
end Plane920.Cut

namespace Plane920.Cut
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal

theorem slice_budget {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (c : V) :
    ∑ w : V, weight (degree (block f c) w) ≤ gs.length-13 := by
  classical
  have each (w : V) : weight (degree (block f c) w) ≤ (reserved gs out w).card := by
    let t := degree (block f c) w
    have upper : t≤4 := (Finset.card_le_card Finset.inter_subset_left).trans (line_size w).le
    by_cases half : t=2
    · change min t (4-t) ≤ _
      have q := balanced basis arity h uni w c half
      omega
    by_cases empty : t=0 ∨ t=4
    · change min t (4-t) ≤ _
      omega
    have mixed := diff_of_degree f c w (by change 0<t; omega) (by change t<4; omega)
    obtain ⟨i,mem,T,big,sub,m⟩ := charged basis arity h uni mixed
    have has : i∈reserved gs out w := Finset.mem_filter.mpr ⟨mem,T,big,sub,m⟩
    have positive := Finset.card_pos.mpr ⟨i,has⟩
    change min t (4-t) ≤ _
    omega
  have disjoint {a b : V} (ne : a≠b) : Disjoint (reserved gs out a) (reserved gs out b) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨T,big,sub,own⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨U,_,sub',own'⟩ := (Finset.mem_filter.mp hj).2
    have eq := minima_eq own own'
    have inc := Finset.subset_inter sub (show T⊆line b from eq ▸ sub')
    have lim := (Finset.card_le_card inc).trans (OrSupport.line_pair a b ne)
    omega
  have all : Finset.univ.biUnion (reserved gs out) ⊆ paid (terminals out) 13 gs.length := by
    intro i hi
    obtain ⟨w,_,mem⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp mem).1
  have cap := Finset.card_le_card all
  rw [Finset.card_biUnion (fun _ _ _ _ ne => disjoint ne),hidden_count h] at cap
  exact (Finset.sum_le_sum (fun w _ => each w)).trans cap

theorem incidences : ∀ p : V, (Finset.univ.filter (fun w : V => p∈line w)).card=4 := by decide +kernel
theorem joins : ∀ p q : V, p≠q → (Finset.univ.filter (fun w : V => p∈line w ∧ q∈line w)).card=1 := by decide +kernel

theorem degree_sum (A : Region) : ∑w : V, degree A w = 4*A.card := by
  classical
  have point (w : V) : degree A w = ∑ x∈A, if x∈line w then 1 else 0 := by
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext x
    simp [and_comm]
  simp_rw [point]
  rw [Finset.sum_comm]
  simp [Finset.sum_boole,incidences,Nat.mul_comm]

def ordered (B : Region) := ∑ x∈B, ∑ y∈B, if x≠y then 1 else 0
theorem ordered_card (B : Region) : ordered B=B.card*(B.card-1) := by
  classical
  have per (x : V) (hx : x∈B) : (∑ y∈B, if x≠y then 1 else 0) = B.card-1 := by
    rw [Finset.sum_boole,←Finset.card_erase_of_mem hx]
    apply congrArg Finset.card
    ext y
    simp [and_comm,ne_comm]
  unfold ordered
  rw [Finset.sum_congr rfl per]
  simp

theorem pair_sum (A : Region) : ∑ w : V, degree A w*(degree A w-1)=A.card*(A.card-1) := by
  classical
  let P (w x y : V) := if x≠y ∧ x∈line w ∧ y∈line w then 1 else 0
  have spin (w : V) : degree A w*(degree A w-1) = ∑x∈A, ∑y∈A, P w x y := by
    unfold degree
    rw [←ordered_card (line w∩A)]
    unfold ordered
    have setEq : line w∩A = A.filter (fun x => x∈line w) := by ext x; simp [and_comm]
    rw [setEq,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases yes : x∈line w
    · rw [ite_eq_left yes,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases mem : y∈line w <;> simp [P,yes,mem]
    · simp [P,yes]
  have pair (x y : V) : (∑w : V, P w x y) = if x≠y then 1 else 0 := by
    by_cases diff : x≠y
    · simpa [P,diff,Finset.sum_boole] using joins x y diff
    · simp [P,diff]
  simp_rw [spin]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x∈A, ∑y∈A, ∑ w : V, P w x y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ordered A := by simp_rw [pair]; rfl
    _ = _ := ordered_card A
end Plane920.Cut

namespace Plane920.Cut
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal

theorem cut_inequality {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (c : V) :
    12*(block f c).card ≤ 3*(gs.length-13)+(block f c).card*((block f c).card-1) := by
  let A := block f c
  have point (t : Nat) (cap : t≤4) : 3*t≤3*weight t+t*(t-1) := by interval_cases t <;> decide
  have bound := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun w _ =>
    point (degree A w) ((Finset.card_le_card Finset.inter_subset_left).trans (line_size w).le))
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,degree_sum,pair_sum] at bound
  have limited := slice_budget basis arity h uni c
  change ∑w : V, weight (degree A w) ≤ _ at limited
  change 12*A.card ≤ 3*(gs.length-13)+A.card*(A.card-1)
  omega

theorem at_most_three {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (c : V) (small : (block f c).card≤6)
    (limit : gs.length≤24) : (block f c).card≤3 := by
  have bound := cut_inequality basis arity h uni c
  generalize (block f c).card=k at *
  interval_cases k <;> omega

theorem triple_collinear {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (c : V) (three : (block f c).card=3)
    (limit : gs.length≤24) : ∃w : V, block f c⊆line w := by
  by_contra! no
  let A := block f c
  have sm (w : V) : degree A w≤2 := by
    by_contra! hi
    have sub : line w∩A⊆A := Finset.inter_subset_right
    have back := Finset.eq_of_subset_of_card_le sub (by change (block f c).card ≤ degree A w; omega)
    apply no w
    change A⊆line w
    rw [←back]
    exact Finset.inter_subset_left
  have exactW (w : V) : weight (degree A w)=degree A w := by unfold weight; have := sm w; omega
  have budget := slice_budget basis arity h uni c
  change ∑w : V, weight (degree A w) ≤ _ at budget
  simp_rw [exactW] at budget
  rw [degree_sum,show A.card=3 from three] at budget
  omega

theorem residual_twenty_four {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤24) : ∃ (f : V→V) (c : V),
      Uniform f (start++supportTail (terminals out) start gs) ∧ (colors f).card=2 ∧
      1≤(block f c).card ∧ (block f c).card≤3 ∧ ((block f c).card=3 → ∃w, block f c⊆line w) := by
  have initial : Uniform id start := by
    intro s mem
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro i hi j hj
    change i=j
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  obtain ⟨f,uni,cost⟩ := components gs arity (terminals out) start id initial
  have count : (colors (id : V→V)).card=13 := by decide
  have len : start.length=13 := by simp [start]
  rw [count,len,hidden_count h] at cost
  have two : (colors f).card=2 := by
    by_contra! no
    have three : 3≤(colors f).card := by omega
    have lo := three_implies_twenty_six basis arity h uni three
    omega
  obtain ⟨a,b,ne,actual⟩ := Finset.card_eq_two.mp two
  have union : block f a ∪ block f b = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have mem : f i∈colors f := Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
    rw [actual] at mem
    simpa [block] using mem
  have disjoint : Disjoint (block f a) (block f b) := by
    apply Finset.disjoint_left.mpr
    intro x ha hb
    exact ne (((Finset.mem_filter.mp ha).2).symm.trans (Finset.mem_filter.mp hb).2)
  have sum : (block f a).card+(block f b).card=13 := by
    rw [←Finset.card_union_of_disjoint disjoint,union]; decide
  have pos (c : V) (mem : c∈colors f) : 1≤(block f c).card := by
    obtain ⟨x,_,eq⟩ := Finset.mem_image.mp mem
    exact Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩⟩
  have pick : ∃ c, c∈colors f ∧ (block f c).card≤6 := by
    by_cases sm : (block f a).card≤6
    · exact ⟨a,by rw [actual]; simp,sm⟩
    · exact ⟨b,by rw [actual]; simp,by omega⟩
  obtain ⟨c,mem,small⟩ := pick
  exact ⟨f,c,uni,two,pos c mem,at_most_three basis arity h uni c small limit,
    fun t => triple_collinear basis arity h uni c t limit⟩
end Plane920.Cut

namespace Plane920.Cut
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal

theorem minimum_support {f : Input→Bool} {s U : Region} (loc : Local f s) (m : Minimal f U) : U⊆s := by
  have eq := m.2 (U∩s) ((project loc _).trans m.1) (Finset.card_le_card Finset.inter_subset_left)
  rw [←eq]
  exact Finset.inter_subset_right

theorem glob_local (gs : List Gate) (out : V→Nat) (i : Nat) :
    Local (globalWire gs out i) (support (terminals out) gs i) := by
  intro x y same
  exact (supported _ gs x y _ _ start (start_valid x y)).2.2 i same

theorem original_support (gs : List Gate) (z : Finset Nat) (i : Nat) (early : i<13) : (support z gs i).card=1 := by
  let x : V := ⟨i,early⟩
  unfold support
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa [start] using early),
    List.getElem?_eq_getElem (by simpa [start] using early)]
  change (start[i]).card=1
  have index : start[i]={x} := List.getElem_ofFn _
  rw [index,Finset.card_singleton]

theorem support_zero {gs : List Gate} {z : Finset Nat} {i : Nat}
    (lo : 13 ≤ i) (hi : i<13+gs.length) (zi : i∈z) : support z gs i=∅ := by
  let j : Fin gs.length := ⟨i-13,by omega⟩
  let pre := gs.take j.val
  let post := gs.drop (j.val+1)
  have eq : pre++gs[j.val]::post=gs := by simp [pre,post]
  have idx : start.length+pre.length=i := by
    have len : start.length=13 := by simp [start]
    rw [len,show pre.length=j.val by simp [pre]]
    change 13+(i-13)=i
    omega
  unfold support
  have evaluated := after_prefix z start pre gs[j.val] post
  rw [eq,idx,ite_eq_left zi] at evaluated
  exact evaluated

theorem index_present {gs : List Gate} {out : V→Nat} {i : Nat} (hi : 2≤(support (terminals out) gs i).card) :
    i∈paid (terminals out) 13 gs.length := by
  have raw : 13 ≤ i := by
    by_contra! small
    have := original_support gs (terminals out) i small
    omega
  have range : i<13+gs.length := by
    by_contra! high
    have empty : support (terminals out) gs i=∅ := by
      unfold support
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa only [List.length_append,tail_len,show start.length=13 from by simp [start]] using high)]
      rfl
    simp [empty] at hi
  have nz : i∉terminals out := fun inZ => by simp [support_zero raw range inZ] at hi
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨raw,range⟩,nz⟩

theorem line_driver {gs : List Gate} {out : V→Nat} {f : V→V}
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (w c : V) (mono : line w⊆block f c) :
    ∃ i∈paid (terminals out) 13 gs.length, support (terminals out) gs i⊆block f c := by
  let j := outIndex h w
  let pre := gs.take j.val
  let xs := start++supportTail (terminals out) start pre
  have uniform : Uniform f xs := prefix_uniform gs uni j.val
  have cover : line w⊆gather xs gs[j.val].inputs := terminal_support h w j (index_eq h w)
  obtain ⟨u,v,hu,hv,uv⟩ := binary xs gs[j.val].inputs (arity _ (List.getElem_mem _))
  rw [uv] at cover
  have one : ∃s : Region, Present xs s ∧ 2≤(line w∩s).card := by
    rcases large_slice cover with left|right
    · exact ⟨u,hu,left⟩
    · exact ⟨v,hv,right⟩
  obtain ⟨s,present,big⟩ := one
  have nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0<2) big)
  obtain ⟨p,hp⟩ := nonempty
  have hom := available_hom uniform present
  have subset : s⊆block f c := by
    intro q hq
    have on : f p=c := (Finset.mem_filter.mp (mono (Finset.mem_inter.mp hp).1)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hom q hq p (Finset.mem_inter.mp hp).2).trans on⟩
  obtain emp|inXs := present
  · simp [emp] at hp
  obtain ⟨i,lt,eq⟩ := List.mem_iff_getElem.mp inXs
  have eq' : support (terminals out) gs i=s := by
    unfold support
    have split : start++supportTail (terminals out) start gs =
        xs++supportTail (terminals out) xs (gs.drop j.val) := by
      conv_lhs => rw [←List.take_append_drop j.val gs,tail_append,←List.append_assoc]
    rw [split,List.getD_eq_getElem?_getD,List.getElem?_append_left lt,List.getElem?_eq_getElem lt]
    exact eq
  have hiddenWire := index_present (i := i) (gs := gs) (out := out) (by rw [eq']; exact big.trans (Finset.card_le_card Finset.inter_subset_right))
  exact ⟨i,hiddenWire,eq' ▸ subset⟩

theorem exclude_line_block {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (c w : V) (lineEq : block f c=line w) :
    26≤gs.length := by
  classical
  obtain ⟨i,paidI,all⟩ := line_driver arity h uni w c (le_of_eq lineEq.symm)
  have dis (t : V) (ne : t≠w) : i∉reserved gs out t := by
    intro mem
    obtain ⟨T,big,sub,mini⟩ := (Finset.mem_filter.mp mem).2
    have su := (minimum_support (glob_local gs out i) mini).trans all
    rw [lineEq] at su
    have overlap := (Finset.card_le_card (Finset.subset_inter sub su)).trans (OrSupport.line_pair t w ne)
    omega
  let other := Finset.univ.erase w
  have charge (t : V) (inO : t∈other) :
      ∃j∈paid (terminals out) 13 gs.length, ∃T : Region, 2≤T.card ∧ T⊆line t ∧ Minimal (globalWire gs out j) T := by
    have ne : t≠w := (Finset.mem_erase.mp inO).1
    have deg : degree (block f c) t=1 := by
      rw [degree,lineEq]
      have cap := OrSupport.line_pair t w ne
      obtain ⟨p,pt,pw⟩ := meet t w
      have pos := Finset.card_pos.mpr ⟨p,Finset.mem_inter.mpr ⟨pt,pw⟩⟩
      omega
    exact charged basis arity h uni (diff_of_degree f c t (by omega) (by omega))
  choose wire mem T big sub own using charge
  let used := other.attach.image (fun t => wire t.val t.property)
  have injection : Function.Injective (fun t : {q // q∈other} => wire t.val t.property) := by
    intro a b same
    by_contra dif
    have n : a.val≠b.val := fun eq => dif (Subtype.ext eq)
    change wire a.val a.property=wire b.val b.property at same
    have mn := own a.val a.property
    rw [same] at mn
    have eq := minima_eq mn (own b.val b.property)
    have overlap := (Finset.card_le_card (Finset.subset_inter (sub a.val a.property)
      (show T a.val a.property⊆line b.val from eq ▸ sub b.val b.property))).trans (OrSupport.line_pair a.val b.val n)
    have large := big a.val a.property
    omega
  have size : used.card=12 := by
    rw [show used.card=other.attach.card from Finset.card_image_of_injective _ injection,Finset.card_attach,
      show other.card=(Finset.univ : Finset V).card-1 from Finset.card_erase_of_mem (Finset.mem_univ w)]
    decide
  have missing : i∉used := by
    intro seen
    obtain ⟨⟨t,ht⟩,_,eq⟩ := Finset.mem_image.mp seen
    apply dis t (Finset.mem_erase.mp ht).1
    rw [←eq]
    exact Finset.mem_filter.mpr ⟨mem t ht,T t ht,big t ht,sub t ht,own t ht⟩
  have incl : insert i used ⊆ paid (terminals out) 13 gs.length := by
    apply Finset.insert_subset paidI
    intro j hj
    obtain ⟨⟨t,ht⟩,_,rfl⟩ := Finset.mem_image.mp hj
    exact mem t ht
  have cap := Finset.card_le_card incl
  rw [Finset.card_insert_of_notMem missing,size,hidden_count h] at cap
  omega
end Plane920.Cut

namespace Plane920.Cut
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal

theorem thin_fours (A : Region) (four : A.card=4) (nonline : ∀w, A≠line w) :
    14 ≤ ∑w : V, weight (degree A w) := by
  classical
  let triples := Finset.univ.filter (fun w : V => degree A w=3)
  have unique : triples.card≤1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra dif
    have x3 := (Finset.mem_filter.mp hx).2
    have y3 := (Finset.mem_filter.mp hy).2
    have sub : (line x∩A)∪(line y∩A) ⊆ A := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have upper := Finset.card_le_card sub
    have count := Finset.card_union_add_card_inter (line x∩A) (line y∩A)
    have inter : (line x∩A)∩(line y∩A) ⊆ line x∩line y := Finset.inter_subset_inter Finset.inter_subset_left Finset.inter_subset_left
    have low := (Finset.card_le_card inter).trans (OrSupport.line_pair x y dif)
    change (line x∩A).card=3 at x3
    change (line y∩A).card=3 at y3
    omega
  have sm (w : V) : degree A w≤3 := by
    have lim : degree A w≤4 := (Finset.card_le_card Finset.inter_subset_right).trans four.le
    by_contra! hi
    have eqA : line w∩A=A := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by change A.card≤degree A w; omega)
    have eqL : line w∩A=line w := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by change (line w).card≤degree A w; rw [line_size]; omega)
    exact nonline w (eqA.symm.trans eqL)
  have exactW (w : V) : degree A w=weight (degree A w)+2*(if degree A w=3 then 1 else 0) := by
    have cap := sm w
    generalize degree A w=t at *
    interval_cases t <;> decide
  have eq : ∑w : V, degree A w =
      (∑w : V, weight (degree A w)) + 2*triples.card := by
    calc
      _ = ∑w : V, (weight (degree A w)+2*(if degree A w=3 then 1 else 0)) := Finset.sum_congr rfl (fun w _ => exactW w)
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_boole]; simp [triples]
  rw [degree_sum,four] at eq
  omega

theorem at_most_three_25 {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (c : V) (small : (block f c).card≤6)
    (limit : gs.length≤25) : (block f c).card≤3 := by
  have bound := cut_inequality basis arity h uni c
  have at4 : (block f c).card≤4 := by
    generalize (block f c).card=k at *
    interval_cases k <;> omega
  by_contra! hi
  have four : (block f c).card=4 := by omega
  by_cases lineCase : ∃w, block f c=line w
  · obtain ⟨w,eq⟩ := lineCase
    have lo := exclude_line_block basis arity h uni c w eq
    omega
  · have total := thin_fours (block f c) four (fun w eq => lineCase ⟨w,eq⟩)
    have lo := slice_budget basis arity h uni c
    omega

theorem residual_twenty_five {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (limit : gs.length≤25) :
    (colors f).card=1 ∨ ((colors f).card=2 ∧ ∃ c, 1≤(block f c).card ∧ (block f c).card≤3) := by
  have first : f 0∈colors f := Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  have positive := Finset.card_pos.mpr ⟨_,first⟩
  by_cases one : (colors f).card=1
  · exact Or.inl one
  right
  have two : (colors f).card=2 := by
    by_contra! no
    have three : 3≤(colors f).card := by omega
    have lo := three_implies_twenty_six basis arity h uni three
    omega
  refine ⟨two,?_⟩
  obtain ⟨a,b,ne,actual⟩ := Finset.card_eq_two.mp two
  have union : block f a ∪ block f b = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have mem : f i∈colors f := Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
    rw [actual] at mem
    simpa [block] using mem
  have disjoint : Disjoint (block f a) (block f b) := by
    apply Finset.disjoint_left.mpr
    intro x ha hb
    exact ne (((Finset.mem_filter.mp ha).2).symm.trans (Finset.mem_filter.mp hb).2)
  have sum : (block f a).card+(block f b).card=13 := by
    rw [←Finset.card_union_of_disjoint disjoint,union]; decide
  have pick : ∃ c, c∈colors f ∧ (block f c).card≤6 := by
    by_cases sm : (block f a).card≤6
    · exact ⟨a,by rw [actual]; simp,sm⟩
    · exact ⟨b,by rw [actual]; simp,by omega⟩
  obtain ⟨c,mem,small⟩ := pick
  obtain ⟨x,_,eq⟩ := Finset.mem_image.mp mem
  exact ⟨c,Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩⟩,
    at_most_three_25 basis arity h uni c small limit⟩
end Plane920.Cut

namespace Plane920.Forest
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal

def Splits (xs : List SetV) (ins : List Nat) : Prop := ∃ a b, ins=[a,b] ∧
  (xs.getD a ∅).Nonempty ∧ (xs.getD b ∅).Nonempty ∧ Disjoint (xs.getD a ∅) (xs.getD b ∅)

theorem no_split {f : V→V} {xs : List SetV} {ins : List Nat} (uni : Uniform f xs)
    (arity : ins.length≤2) (bad : ¬Splits xs ins) : Hom f (gather xs ins) := by
  cases ins with
  | nil => exact empty_hom _
  | cons a tail =>
    have A := available_hom uni (readable xs a)
    cases tail with
    | nil => simpa [gather] using A
    | cons b t =>
      cases t with
      | nil =>
        have B := available_hom uni (readable xs b)
        by_cases eA : (xs.getD a ∅).Nonempty
        · by_cases eB : (xs.getD b ∅).Nonempty
          · have shared : ¬Disjoint (xs.getD a ∅) (xs.getD b ∅) := fun d => bad ⟨a,b,rfl,eA,eB,d⟩
            obtain ⟨p,pa,pb⟩ := Finset.not_disjoint_iff.mp shared
            have eqP {i : V} (hi : i∈gather xs [a,b]) : f i=f p := by
              simp only [gather,Finset.union_empty,Finset.mem_union] at hi
              rcases hi with h|h
              · exact A i h p pa
              · exact B i h p pb
            exact fun _ hi _ hj => (eqP hi).trans (eqP hj).symm
          · simpa only [gather,Finset.union_empty,Finset.not_nonempty_iff_eq_empty.mp eB] using A
        · simpa only [gather,Finset.union_empty,Finset.empty_union,Finset.not_nonempty_iff_eq_empty.mp eA] using B
      | cons c rest => simp at arity

noncomputable def waste (z : Finset Nat) (xs : List SetV) : List Gate → Nat := by
  classical
  exact fun gs => match gs with
    | [] => 0
    | g::rest =>
      let s := if xs.length∈z then ∅ else gather xs g.inputs
      (if xs.length∉z ∧ ¬Splits xs g.inputs then 1 else 0) + waste z (xs++[s]) rest
termination_by gs => gs.length

theorem refined (gs : List Gate) (arity : ∀g∈gs,g.inputs.length≤2) (z : Finset Nat)
    (xs : List SetV) (f : V→V) (root : Uniform f xs) :
    ∃ k : V→V, Uniform k (xs++supportTail z xs gs) ∧
      (colors f).card+waste z xs gs ≤ (colors k).card+(paid z xs.length gs.length).card := by
  classical
  induction gs generalizing xs f with
  | nil => exact ⟨f,by simpa [supportTail] using root,by simp [waste,paid]⟩
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    let w : Nat := if xs.length∉z ∧ ¬Splits xs g.inputs then 1 else 0
    have same (hs : Hom f s) : Uniform f (xs++[s]) := by
      intro t ht
      rcases List.mem_append.mp ht with before|added
      · exact root t before
      · exact List.mem_singleton.mp added ▸ hs
    have step : ∃ k : V→V, Uniform k (xs++[s]) ∧
        (colors f).card+w ≤ (colors k).card+(if xs.length∈z then 0 else 1) := by
      by_cases held : xs.length∈z
      · exact ⟨f,same (by simpa [s,held] using empty_hom f),by simp [w,held]⟩
      · by_cases split : Splits xs g.inputs
        · obtain ⟨u,v,hu,hv,eq⟩ := binary xs g.inputs (arity _ (by simp))
          simpa [s,w,held,split,eq] using merge root hu hv
        · exact ⟨f,same (by simpa [s,held] using no_split root (arity _ (by simp)) split),by simp [w,held,split]⟩
    obtain ⟨k,uniform,stepCost⟩ := step
    obtain ⟨q,final,endCost⟩ := ih (fun t mem=>arity t (by simp [mem])) (xs++[s]) k uniform
    refine ⟨q,by simpa only [supportTail,List.append_assoc,List.singleton_append,s] using final,?_⟩
    have expr : waste z xs (g::gs)=w+waste z (xs++[s]) gs := by rw [waste]
    rw [expr,List.length_cons,paid_step]
    simp only [List.length_append,List.length_singleton] at endCost
    omega

theorem no_waste {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤24) : waste (terminals out) start gs=0 := by
  have initial : Uniform id start := by
    intro s mem
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro i hi j hj
    change i=j
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  obtain ⟨f,uni,cost⟩ := refined gs arity (terminals out) start id initial
  have n : (colors (id : V→V)).card=13 := by decide
  have len : start.length=13 := by simp [start]
  rw [n,len,hidden_count h] at cost
  by_contra! pos
  have three : 3≤(colors f).card := by omega
  have lo := three_implies_twenty_six basis arity h uni three
  omega

theorem at_gate (z : Finset Nat) (xs : List SetV) (gs : List Gate) (all : waste z xs gs=0)
    (j : Fin gs.length) (paidGate : xs.length+j.val∉z) :
    Splits (xs++supportTail z xs (gs.take j.val)) gs[j.val].inputs := by
  classical
  induction gs generalizing xs with
  | nil => exact Fin.elim0 j
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    let w : Nat := if xs.length∉z ∧ ¬Splits xs g.inputs then 1 else 0
    have eq : w+waste z (xs++[s]) gs=0 := by simpa only [w,s,waste] using all
    have noMore : waste z (xs++[s]) gs=0 := by omega
    cases j using Fin.cases with
    | zero =>
      have nz : xs.length∉z := by simpa using paidGate
      have yes : Splits xs g.inputs := by
        by_contra n
        have : w=1 := by simp [w,nz,n]
        omega
      simpa [supportTail] using yes
    | succ j =>
      have nz : (xs++[s]).length+j.val∉z := by
        simp only [List.length_append,List.length_singleton]
        simpa only [Fin.val_succ,Nat.add_right_comm,Nat.add_assoc,Nat.add_comm] using paidGate
      have relevant := ih (xs++[s]) noMore j nz
      simpa only [Fin.val_succ,List.take_succ_cons,supportTail,List.append_assoc,List.singleton_append,
        List.getElem_cons_succ,s] using relevant

theorem every_hidden_splits {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤24) (j : Fin gs.length) (hidden : 13+j.val∉terminals out) :
    Splits (start++supportTail (terminals out) start (gs.take j.val)) gs[j.val].inputs :=
  at_gate _ _ _ (no_waste basis arity h limit) j (by simpa [start] using hidden)
end Plane920.Forest

namespace Plane920.Forest
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut

theorem project_piece {f g k : Input→Bool} {u v T : Region} (af : Local f u) (bf : Local g v)
    (sep : Disjoint u v) (m : Minimal k T) (both : ∀s, Active k s ↔ Active f s ∧ Active g s) :
    Minimal f (T∩u) := by
  have accepted := (both T).mp m.1
  have F : Active f (T∩u) := (project af T).trans accepted.1
  have G : Active g (T∩v) := (project bf T).trans accepted.2
  have size : (T∩u).card+(T∩v).card≤T.card := by
    rw [←Finset.card_union_of_disjoint (sep.mono Finset.inter_subset_right Finset.inter_subset_right)]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  refine ⟨F,?_⟩
  intro X FX sm
  let mix := (X∩u)∪(T∩v)
  have xu := Finset.card_le_card (Finset.inter_subset_left (s₁ := X) (s₂ := u))
  have valid : mix.card≤T.card := (Finset.card_union_le _ _).trans (by omega)
  have on1 : Active f mix := (af _ _ (same_on (by
    intro i hi
    have nv : i∉v := Finset.disjoint_left.mp sep hi
    simp [mix,hi,nv]))).trans FX
  have on2 : Active g mix := (bf _ _ (same_on (by
    intro i hi
    have nu : i∉u := Finset.disjoint_left.mp sep.symm hi
    simp [mix,hi,nu]))).trans G
  have eq := m.2 mix ((both mix).mpr ⟨on1,on2⟩) valid
  have inc : T∩u⊆X := by
    intro i hi
    have inM : i∈mix := eq ▸ (Finset.mem_inter.mp hi).1
    rcases Finset.mem_union.mp inM with l|r
    · exact (Finset.mem_inter.mp l).1
    · exact False.elim (Finset.disjoint_left.mp sep (Finset.mem_inter.mp hi).2 (Finset.mem_inter.mp r).2)
  exact (Finset.eq_of_subset_of_card_le inc sm).symm

theorem lower_child {f g k : Input→Bool} {u v T : Region} (af : Local f u) (bf : Local g v)
    (sep : Disjoint u v) (m : Minimal k T) (big : 3≤T.card)
    (law : (∀s, Active k s ↔ Active f s ∨ Active g s) ∨ (∀s, Active k s ↔ Active f s ∧ Active g s)) :
    ∃U⊆T, 2≤U.card ∧ (Minimal f U ∨ Minimal g U) := by
  rcases law with any|both
  · rcases (any T).mp m.1 with F|G
    · exact ⟨T,Finset.Subset.refl _,by omega,Or.inl ⟨F,fun X on sm => m.2 X ((any X).mpr (Or.inl on)) sm⟩⟩
    · exact ⟨T,Finset.Subset.refl _,by omega,Or.inr ⟨G,fun X on sm => m.2 X ((any X).mpr (Or.inr on)) sm⟩⟩
  · have left := project_piece af bf sep m both
    have right := project_piece bf af sep.symm m (fun s => (both s).trans and_comm)
    let U := (T∩u)∪(T∩v)
    have subset : U⊆T := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    have l : Active f U := (af _ _ (same_on (by
      intro i hi
      have nv : i∉v := Finset.disjoint_left.mp sep hi
      simp [U,hi,nv]))).trans left.1
    have r : Active g U := (bf _ _ (same_on (by
      intro i hi
      have nu : i∉u := Finset.disjoint_left.mp sep.symm hi
      simp [U,hi,nu]))).trans right.1
    have eq := m.2 U ((both _).mpr ⟨l,r⟩) (Finset.card_le_card subset)
    have num : T.card≤(T∩u).card+(T∩v).card := (congrArg Finset.card eq.symm).le.trans (Finset.card_union_le (T∩u) (T∩v))
    by_cases two : 2≤(T∩u).card
    · exact ⟨_,Finset.inter_subset_left,two,Or.inl left⟩
    · exact ⟨_,Finset.inter_subset_left,by omega,Or.inr right⟩

theorem stored_value {gs : List Gate} {out : V→Nat} (j : Fin gs.length) (nz : 13+j.val∉terminals out) :
    globalWire gs out (13+j.val) = value gs out j := by
  funext x
  let z := terminals out
  let pre := gs.take j.val
  let post := gs.drop (j.val+1)
  let xs := overwrite z pre (List.ofFn x)
  have n : xs.length=13+j.val := by simp [xs,pre,width]
  have cut : pre++gs[j.val]::post=gs := by simp [pre,post]
  change (overwrite z gs (List.ofFn x)).getD (13+j.val) false=bit gs[j.val] xs
  have whole := congrArg (fun g => overwrite z g (List.ofFn x)) cut.symm
  rw [whole,ov_append]
  change (overwrite z post (xs++[_])).getD (13+j.val) false=_
  rw [ov_stable _ _ _ _ (by simp only [List.length_append,List.length_singleton,n]; omega),
    read_append,n,ite_eq_left rfl,ite_eq_right nz]

theorem live_before {gs : List Gate} {out : V→Nat} (j : Fin gs.length) (i : Nat) {T : Region}
    (m : Minimal (live gs out j i) T) (big : 2≤T.card) : i<13+j.val := by
  by_contra! no
  have on : Active (live gs out j i) ∅ := by
    simp only [Active,live,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simpa only [width,List.length_ofFn,List.length_take,Nat.min_eq_left j.isLt.le] using no)]
    rfl
  have eq := m.2 _ on (by simp)
  rw [←eq] at big
  simp at big

theorem descend {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (limit : gs.length≤24)
    (i : Nat) (present : i∈paid (terminals out) 13 gs.length) {T : Region}
    (m : Minimal (globalWire gs out i) T) (big : 3≤T.card) :
    ∃ k < i, k∈paid (terminals out) 13 gs.length ∧ ∃ U⊆T, 2≤U.card ∧ Minimal (globalWire gs out k) U := by
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp present
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have notTerminal : 13+j.val∉terminals out := idx ▸ nz
  obtain ⟨a,b,ids,_,_,sep⟩ := every_hidden_splits basis arity h limit j notTerminal
  have same : globalWire gs out i = value gs out j := idx ▸ stored_value j notTerminal
  rw [same] at m
  have rule :
      (∀s, Active (value gs out j) s ↔ Active (live gs out j a) s ∨ Active (live gs out j b) s) ∨
      (∀s, Active (value gs out j) s ↔ Active (live gs out j a) s ∧ Active (live gs out j b) s) := by
    rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
    · left
      intro s
      have logic (p q : Bool) : (p && q)=false ↔ p=false ∨ q=false := by cases p <;> cases q <;> decide
      exact (by simpa [value,bit,ids,gate,GateOp.eval,Active,live] using logic (live gs out j a (missing s)) (live gs out j b (missing s)))
    · right
      intro s
      simp [Active,value,bit,ids,gate,GateOp.eval,live]
  obtain ⟨U,inc,size,child⟩ := lower_child (live_local gs out j a) (live_local gs out j b) sep m big rule
  have done (k : Nat) (s : Minimal (live gs out j k) U) : k < i ∧ k∈paid (terminals out) 13 gs.length ∧ Minimal (globalWire gs out k) U := by
    have before := live_before j k s size
    exact ⟨by omega,hidden j k s size⟩
  rcases child with A|B
  · obtain ⟨p,q,t⟩ := done a A
    exact ⟨a,p,q,U,inc,size,t⟩
  · obtain ⟨p,q,t⟩ := done b B
    exact ⟨b,p,q,U,inc,size,t⟩
end Plane920.Forest

namespace Plane920.Forest
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut

theorem operands {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) {w : V} (mixed : Varied f (line w)) :
    ∃ (a b : Nat) (U W : Region), U∪W=line w ∧ Disjoint U W ∧
      Minimal (live gs out (outIndex h w) a) U ∧ Minimal (live gs out (outIndex h w) b) W := by
  let j := outIndex h w
  have ind : 13+j.val=out w := index_eq h w
  let xs := start++supportTail (terminals out) start (gs.take j.val)
  have uni' : Uniform f xs := prefix_uniform gs uni j.val
  have cover : line w⊆gather xs gs[j.val].inputs := terminal_support h w j ind
  obtain ⟨a,b,ids⟩ := binary_indices (arity _ (List.getElem_mem _)) uni' cover mixed
  let u := region gs out j a
  let v := region gs out j b
  have uv : line w⊆u∪v := by simpa only [u,v,region,xs,ids,gather,Finset.union_empty] using cover
  have hu : Hom f u := available_hom uni' (readable xs a)
  have hv : Hom f v := available_hom uni' (readable xs b)
  obtain ⟨disjoint,left,right⟩ := separate_regions hu hv uv mixed
  have law (s : Region) (small : s.card≤4) : value gs out j (missing s)=false ↔ s=line w := by
    have weight : 9≤(supp (missing s)).card := by
      rw [complement,Finset.card_sdiff_of_subset (Finset.subset_univ s)]
      have total : (Finset.univ : Region).card=13 := by decide
      omega
    rw [normalized basis h w j ind _ weight,←h w _ weight]
    exact statement h small
  have gates :
      (∀ s : Region, s.card≤4 → (Active (live gs out j a) s ∨ Active (live gs out j b) s ↔ s=line w)) ∨
      (∀ s : Region, s.card≤4 → (Active (live gs out j a) s ∧ Active (live gs out j b) s ↔ s=line w)) := by
    rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
    · left
      intro s small
      have logic (p q : Bool) : (p=false ∨ q=false) ↔ (p && q)=false := by cases p <;> cases q <;> decide
      exact (logic _ _).trans (by simpa [value,bit,ids,gate,GateOp.eval,live] using law s small)
    · right
      intro s small
      simpa [Active,value,bit,ids,gate,GateOp.eval,live] using law s small
  obtain ⟨ma,mb⟩ := crossing (live_local gs out j a) (live_local gs out j b) disjoint uv left right gates
  refine ⟨a,b,line w∩u,line w∩v,?_,disjoint.mono Finset.inter_subset_right Finset.inter_subset_right,ma,mb⟩
  apply Finset.Subset.antisymm (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  intro i hi
  exact Finset.mem_union.mpr ((Finset.mem_union.mp (uv hi)).imp
    (fun e => Finset.mem_inter.mpr ⟨hi,e⟩) (fun e => Finset.mem_inter.mpr ⟨hi,e⟩))

theorem two_per_cross {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤24) (uni : Uniform f (start++supportTail (terminals out) start gs))
    {w : V} (mixed : Varied f (line w)) : 2≤(reserved gs out w).card := by
  classical
  let j := outIndex h w
  obtain ⟨a,b,U,W,un,sep,ma,mb⟩ := operands basis arity h uni mixed
  have cu : U⊆line w := un ▸ Finset.subset_union_left
  have cw : W⊆line w := un ▸ Finset.subset_union_right
  have sum : U.card+W.card=4 := by rw [←Finset.card_union_of_disjoint sep,un,line_size]
  have mem {k : Nat} {s : Region} (leg : k∈paid (terminals out) 13 gs.length) (size : 2≤s.card)
      (sub : s⊆line w) (m : Minimal (globalWire gs out k) s) : k∈reserved gs out w :=
    Finset.mem_filter.mpr ⟨leg,s,size,sub,m⟩
  have large {k : Nat} {s : Region} (big : 3≤s.card) (sub : s⊆line w) (signal : Minimal (live gs out j k) s) :
      2≤(reserved gs out w).card := by
    obtain ⟨inPaid,m⟩ := hidden j k signal (by omega)
    obtain ⟨other,lt,paidOther,T,ts,card,m2⟩ := descend basis arity h limit k inPaid m big
    exact Finset.one_lt_card.mpr ⟨other,mem paidOther card (ts.trans sub) m2,k,mem inPaid (by omega) sub m,lt.ne⟩
  by_cases largeU : 3≤U.card
  · exact large largeU cu ma
  by_cases largeW : 3≤W.card
  · exact large largeW cw mb
  have bu : 2≤U.card := by omega
  have bw : 2≤W.card := by omega
  obtain ⟨paidA,ma'⟩ := hidden j a ma bu
  obtain ⟨paidB,mb'⟩ := hidden j b mb bw
  have ne : a≠b := by
    intro eq
    rw [eq] at ma'
    have same := minima_eq ma' mb'
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0<2) bu)
    exact Finset.disjoint_left.mp sep hi (same ▸ hi)
  exact Finset.one_lt_card.mpr ⟨a,mem paidA bu cu ma',b,mem paidB bw cw mb',ne⟩

theorem reserved_budget {gs : List Gate} {out : V→Nat} (h : Correct gs out) (S : Region) :
    ∑w∈S, (reserved gs out w).card ≤ gs.length-13 := by
  classical
  have separate {w t : V} (ne : w≠t) : Disjoint (reserved gs out w) (reserved gs out t) := by
    apply Finset.disjoint_left.mpr
    intro i hw ht
    obtain ⟨T,big,sub,m⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨U,_,other,n⟩ := (Finset.mem_filter.mp ht).2
    have eq := minima_eq m n
    have cap := (Finset.card_le_card (Finset.subset_inter sub (show T⊆line t from eq ▸ other))).trans (OrSupport.line_pair w t ne)
    omega
  have incl : S.biUnion (reserved gs out)⊆paid (terminals out) 13 gs.length := by
    intro i hi
    obtain ⟨w,_,mem⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp mem).1
  have cost := Finset.card_le_card incl
  rw [Finset.card_biUnion (fun _ _ _ _ d => separate d),hidden_count h] at cost
  exact cost

theorem two_points_impossible {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤24) (uni : Uniform f (start++supportTail (terminals out) start gs)) (c : V)
    (small : (block f c).card≤3) : (block f c).card≤1 := by
  classical
  by_contra! many
  obtain ⟨p,hp,q,hq,diff⟩ := Finset.one_lt_card.mp many
  let pen (i : V) := Finset.univ.filter (fun w : V => i∈line w)
  let S := pen p ∪ pen q
  have inter : pen p∩pen q=Finset.univ.filter (fun w : V => p∈line w ∧ q∈line w) := by
    ext; simp [pen]
  have seven : S.card=7 := by
    have counts := Finset.card_union_add_card_inter (pen p) (pen q)
    rw [inter,joins p q diff,show (pen p).card=4 from incidences p,show (pen q).card=4 from incidences q] at counts
    change (pen p∪pen q).card=7
    omega
  have mixed (w : V) (mem : w∈S) : Varied f (line w) := by
    have has : (line w∩block f c).Nonempty := by
      rcases Finset.mem_union.mp mem with left|right
      · exact ⟨p,Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp left).2,hp⟩⟩
      · exact ⟨q,Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp right).2,hq⟩⟩
    have upper := Finset.card_le_card (Finset.inter_subset_right (s₁ := line w) (s₂ := block f c))
    exact diff_of_degree f c w (Finset.card_pos.mpr has) (by unfold degree; omega)
  have sum := Finset.sum_le_sum (fun w hw => two_per_cross basis arity h limit uni (mixed w hw))
  have lower : 14≤∑w∈S,(reserved gs out w).card := by simpa [seven] using sum
  have cap := reserved_budget h S
  omega

theorem only_singleton {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤24) : ∃ (f : V→V) (c p : V),
      Uniform f (start++supportTail (terminals out) start gs) ∧ (colors f).card=2 ∧ block f c={p} := by
  obtain ⟨f,c,uni,two,pos,sm,_⟩ := residual_twenty_four basis arity h limit
  have hi := two_points_impossible basis arity h limit uni c sm
  obtain ⟨p,single⟩ := Finset.card_eq_one.mp (show (block f c).card=1 by omega)
  exact ⟨f,c,p,uni,two,single⟩
end Plane920.Forest

namespace Plane920Depth

abbrev V := Fin 13
abbrev Points := Finset V
abbrev Signal := Points → Prop

def line (w : V) : Points := ({0, 1, 3, 9} : Points).image (fun p => p+w)

theorem line_card : ∀ w, (line w).card = 4 := by decide +kernel

theorem small_inter : ∀ i j : V, i ≠ j → ((line i) ∩ (line j)).card ≤ 1 := by
  decide +kernel
end Plane920Depth

namespace Plane920Signs
open Plane920Depth
def atom (s : Points) := s=Finset.univ ∨ s.card≤1
def op (b : Bool) (a c : Points) := if b then a∪c else a∩c
def weight (a b : Points) := (a \ b).card * (b \ a).card
theorem wflip (a b : Points) : weight a b = weight b a := Nat.mul_comm _ _
theorem nested {a b : Points} (ab : a⊆b) : weight a b=0 := by
  simp [weight,Finset.sdiff_eq_empty_iff_subset.mpr ab]
theorem raw {a b : Points} (ca : a.card≤1) (cb : b.card≤1) : weight a b≤1 := by
  have x := (Finset.card_le_card (Finset.sdiff_subset (s:=a) (t:=b))).trans ca
  have y := (Finset.card_le_card (Finset.sdiff_subset (s:=b) (t:=a))).trans cb
  exact Nat.mul_le_mul x y
theorem limited {a b : Points} {m n : Nat} (ca : a.card≤m) (cb : b.card≤n) :
    weight a b ≤ m*n := Nat.mul_le_mul ((Finset.card_le_card Finset.sdiff_subset).trans ca)
      ((Finset.card_le_card Finset.sdiff_subset).trans cb)
theorem top (a : Points) : weight a Finset.univ=0 := nested (Finset.subset_univ _)
theorem init_cost {a b : Points} (ha : atom a) (hb : atom b) : weight a b ≤ 1 := by
  rcases ha with rfl | a'; · rw [wflip,top]; decide
  rcases hb with rfl | b'; · rw [top]; decide
  exact raw a' b'
theorem op_bound {a b : Points} {m n : Nat}
    (ha : a=Finset.univ ∨ a.card≤m) (hb : b=Finset.univ ∨ b.card≤n) (o : Bool) :
    op o a b=Finset.univ ∨ (op o a b).card≤m+n := by
  cases o <;> simp only [op, Bool.false_eq_true, ite_false, ite_true]
  · rcases ha with rfl | ca
    · simpa using hb.imp_right (fun h => by omega)
    · exact Or.inr ((Finset.card_le_card Finset.inter_subset_left).trans (by omega))
  · rcases ha with rfl | ca
    · exact Or.inl (by simp)
    rcases hb with rfl | cb
    · exact Or.inl (by simp)
    exact Or.inr ((Finset.card_union_le a b).trans (Nat.add_le_add ca cb))
theorem one_cost {s a b : Points} (hs : s=Finset.univ ∨ s.card≤2)
    (ha : atom a ∨ a=s) (hb : atom b ∨ b=s) : weight a b≤2 := by
  rcases ha with ha|rfl <;> rcases hb with hb|rfl
  · exact (init_cost ha hb).trans (by decide)
  · rcases ha with rfl|ca
    · rw [wflip,top]; decide
    · rcases hs with rfl|cs
      · rw [top]; decide
      · exact limited ca cs
  · rw [wflip]
    rcases hb with rfl|cb
    · rw [wflip,top]; decide
    · rcases hs with rfl|cs
      · rw [top]; decide
      · exact limited cb cs
  · simp [weight]
theorem second_shape {s a b : Points} (hs : s=Finset.univ ∨ s.card≤2)
    (ha : atom a ∨ a=s) (hb : atom b ∨ b=s) (o : Bool) :
    op o a b=Finset.univ ∨ (op o a b).card≤2 ∨
       ((op o a b).card≤3 ∧ s⊆op o a b) := by
  rcases ha with ha|rfl <;> rcases hb with hb|rfl
  · exact (op_bound ha hb o).imp_right Or.inl
  · rcases ha with rfl|ca
    · cases o <;> simp [op]; tauto
    · cases o
      · right;left; exact (Finset.card_le_card Finset.inter_subset_left).trans (by omega)
      · rcases hs with rfl|cs
        · simp [op]
        · right;right;exact ⟨(Finset.card_union_le _ _).trans (by omega),Finset.subset_union_right⟩
  · rcases hb with rfl|cb
    · cases o <;> simp [op]; tauto
    · cases o
      · right;left; exact (Finset.card_le_card Finset.inter_subset_right).trans (by omega)
      · rcases hs with rfl|cs
        · simp [op]
        · right;right;exact ⟨(Finset.card_union_le _ _).trans (by omega),Finset.subset_union_left⟩
  · cases o <;> simp [op] <;> tauto
theorem mixed {s t a : Points}
    (hs : s=Finset.univ ∨ s.card≤2)
    (ht : t=Finset.univ ∨ t.card≤2 ∨ (t.card≤3 ∧ s⊆t))
    (ha : atom a ∨ a=s) : weight a t ≤ 4 := by
  rcases ht with rfl|ct|⟨ct,sub⟩
  · rw [top]; decide
  · rcases ha with (rfl|ca)|rfl
    · rw [wflip,top]; decide
    · exact (limited ca ct).trans (by decide)
    · rcases hs with rfl|cs
      · rw [wflip,top]; decide
      · exact limited cs ct
  · rcases ha with (rfl|ca)|rfl
    · rw [wflip,top]; decide
    · exact (limited ca ct).trans (by decide)
    · rw [nested sub]; decide

theorem last_cost {s t a b : Points}
    (hs : s=Finset.univ ∨ s.card≤2)
    (ht : t=Finset.univ ∨ t.card≤2 ∨ (t.card≤3 ∧ s⊆t))
    (ha : (atom a ∨ a=s) ∨ a=t) (hb : (atom b ∨ b=s) ∨ b=t) : weight a b≤4 := by
  rcases ha with ha|rfl <;> rcases hb with hb|rfl
  · exact (one_cost hs ha hb).trans (by decide)
  · exact mixed hs ht ha
  · rw [wflip]; exact mixed hs ht hb
  · simp [weight]

end Plane920Signs

namespace Plane920Ordered
open Plane920Depth Plane920Signs

def allowed (prev : List Points) (s : Points) := atom s ∨ s ∈ prev

def Valid (A B O : Nat → Points) (prev : List Points) : List Nat → Prop
  | [] => True
  | i::is => allowed prev (A i) ∧ allowed prev (B i) ∧
      (∃ b, O i = op b (A i) (B i)) ∧ Valid A B O (O i::prev) is

def Prior (E : Finset Nat) (O : Nat → Points) (i : Nat) (s : Points) :=
  atom s ∨ ∃ j ∈ E, j < i ∧ s=O j

theorem well (E : Finset Nat) (A B O : Nat → Points)
    (oper : ∀ i∈E, ∃ b, O i=op b (A i) (B i))
    (left : ∀ i∈E, Prior E O i (A i)) (right : ∀ i∈E, Prior E O i (B i))
    (ls past : List Nat) (sorted : ls.Pairwise (· < ·))
    (sub : ∀ j∈ls, j∈E) (cover : ∀ j∈E, j∈past ∨ j∈ls) :
    Valid A B O (past.map O) ls := by
  induction ls generalizing past with
  | nil => trivial
  | cons i is ih =>
    have ord := List.pairwise_cons.mp sorted
    have here := sub i (by simp)
    have pre {s : Points} (h : Prior E O i s) : allowed (past.map O) s := by
      rcases h with h|⟨j,je,ji,rfl⟩
      · exact Or.inl h
      · apply Or.inr
        apply List.mem_map_of_mem
        rcases cover j je with done | rest
        · exact done
        · rcases List.mem_cons.mp rest with rfl|later
          · omega
          · have := ord.1 j later
            omega
    refine ⟨pre (left i here),pre (right i here),oper i here,?_⟩
    apply ih (i::past) ord.2 (fun j hj => sub j (by simp [hj]))
    intro j je
    rcases cover j je with old|rest
    · exact Or.inl (by simp [old])
    · rcases List.mem_cons.mp rest with rfl|later
      · exact Or.inl (by simp)
      · exact Or.inr later

theorem list_cost (A B O : Nat → Points) (xs : List Nat) (h : Valid A B O [] xs)
    (len : xs.length ≤ 3) : (xs.map (fun i => weight (A i) (B i))).sum ≤ 7 := by
  cases xs with
  | nil => simp
  | cons i xs =>
    obtain ⟨ai,bi,⟨o,oi⟩,h⟩ := h
    have a0 : atom (A i) := by simpa [allowed] using ai
    have b0 : atom (B i) := by simpa [allowed] using bi
    have w0 := init_cost a0 b0
    have sh : O i=Finset.univ ∨ (O i).card≤2 := oi ▸ op_bound a0 b0 o
    cases xs with
    | nil => simpa using w0.trans (by decide : 1≤7)
    | cons j xs =>
      obtain ⟨aj,bj,⟨p,oj⟩,h⟩ := h
      have a1 : atom (A j) ∨ A j=O i := by simpa [allowed] using aj
      have b1 : atom (B j) ∨ B j=O i := by simpa [allowed] using bj
      have w1 := one_cost sh a1 b1
      have sj := second_shape sh a1 b1 p
      rw [←oj] at sj
      cases xs with
      | nil => simp; omega
      | cons k tail =>
        have empty : tail=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst tail
        obtain ⟨ak,bk,_⟩ := h
        have a2 : (atom (A k) ∨ A k=O i) ∨ A k=O j := by simpa [allowed, or_assoc, or_comm, or_left_comm] using ak
        have b2 : (atom (B k) ∨ B k=O i) ∨ B k=O j := by simpa [allowed, or_assoc, or_comm, or_left_comm] using bk
        have w2 := last_cost sh sj a2 b2
        simp; omega

theorem sum_weight (E : Finset Nat) (A B O : Nat → Points) (small : E.card≤3)
    (oper : ∀ i∈E, ∃ b, O i=op b (A i) (B i))
    (left : ∀ i∈E, Prior E O i (A i)) (right : ∀ i∈E, Prior E O i (B i)) :
    ∑ i∈E, weight (A i) (B i) ≤ 7 := by
  let l := E.sort (· ≤ ·)
  have hs : l.Pairwise (· < ·) := E.sortedLT_sort.pairwise
  have hw := well E A B O oper left right l [] hs
    (by intro j hj; simpa [l] using hj) (by intro j hj; simp [l,hj])
  have hc := list_cost A B O l hw (by simpa [l] using small)
  rw [←Finset.sum_map_toList]
  have ps := List.Perm.sum_eq ((E.sort_perm_toList (· ≤ ·)).map (fun i => weight (A i) (B i)))
  exact ps ▸ hc
theorem lines_by_weight (I : Finset V) (E : Finset Nat) (A B : Nat → Points)
    (evidence : ∀ l ∈ I, ∃ i ∈ E, ∃ x ∈ A i \ B i, ∃ y ∈ B i \ A i,
      x ∈ line l ∧ y ∈ line l) :
    I.card ≤ ∑ i∈E, weight (A i) (B i) := by
  classical
  let pairs (i : Nat) := (A i \ B i) ×ˢ (B i \ A i)
  let codes := E.sigma pairs
  choose g ge x hx y hy on using fun l : I => evidence l.val l.property
  let f (l : I) : codes := ⟨⟨g l, x l, y l⟩, Finset.mem_sigma.mpr
    ⟨ge l,Finset.mem_product.mpr ⟨hx l, hy l⟩⟩⟩
  have inj : Function.Injective f := by
    intro l m eq
    apply Subtype.ext
    by_contra ne
    have xx := congrArg (fun z : codes => z.val.2.1) eq
    have yy := congrArg (fun z : codes => z.val.2.2) eq
    change x l=x m at xx
    change y l=y m at yy
    have dif : x l≠y l := by
      intro same
      have no := (Finset.mem_sdiff.mp (hx l)).2
      exact no (same ▸ (Finset.mem_sdiff.mp (hy l)).1)
    have s : ({x l,y l} : Points) ⊆ line l.val ∩ line m.val := by
      apply Finset.insert_subset
      · exact Finset.mem_inter.mpr ⟨(on l).1, xx ▸ (on m).1⟩
      · exact Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨(on l).2, yy ▸ (on m).2⟩)
    have size := Finset.card_le_card s
    rw [Finset.card_pair dif] at size
    have := small_inter l.val m.val ne
    omega
  have bound := Fintype.card_le_of_injective f inj
  simpa [codes, pairs, Finset.card_sigma, Finset.card_product, weight] using bound

end Plane920Ordered

namespace Plane920.Forest
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut

def Conjunction (gs : List Gate) (i : Nat) := ∃ j : Fin gs.length, 13+j.val=i ∧ gs[j.val].op=.or
def Own (gs : List Gate) (out : V→Nat) (i : Nat) (T : Region) :=
  i∈paid (terminals out) 13 gs.length ∧ Minimal (globalWire gs out i) T
def Earliest (gs : List Gate) (out : V→Nat) (i : Nat) (T : Region) :=
  Own gs out i T ∧ ∀ k, Own gs out k T → i≤k

theorem first {gs : List Gate} {out : V→Nat} {T : Region} (yes : ∃i, Own gs out i T) :
    ∃i, Earliest gs out i T := by
  classical
  exact ⟨Nat.find yes,Nat.find_spec yes,fun k hk=>Nat.find_min' yes hk⟩

theorem exact_union {f g k : Input→Bool} {u v T : Region} (af : Local f u) (bf : Local g v)
    (sep : Disjoint u v) (m : Minimal k T) (both : ∀s, Active k s ↔ Active f s ∧ Active g s) :
    (T∩u)∪(T∩v)=T := by
  have left := project_piece af bf sep m both
  have right := project_piece bf af sep.symm m (fun s => (both s).trans and_comm)
  let U := (T∩u)∪(T∩v)
  have subset : U⊆T := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have l : Active f U := (af _ _ (same_on (by
    intro i hi
    have nv : i∉v := Finset.disjoint_left.mp sep hi
    simp [U,hi,nv]))).trans left.1
  have r : Active g U := (bf _ _ (same_on (by
    intro i hi
    have nu : i∉u := Finset.disjoint_left.mp sep.symm hi
    simp [U,hi,nu]))).trans right.1
  exact m.2 U ((both _).mpr ⟨l,r⟩) (Finset.card_le_card subset)

theorem first_and {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (limit : gs.length≤24)
    {i : Nat} {T : Region} (m : Earliest gs out i T) (size : 2≤T.card) :
    Conjunction gs i ∧ (T.card=3 → ∃j, ∃U⊆T, U.card=2 ∧ Own gs out j U) := by
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp m.1.1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  obtain ⟨a,b,ids,_,_,sep⟩ := every_hidden_splits basis arity h limit j nf
  let F := live gs out j a
  let G := live gs out j b
  let u := region gs out j a
  let v := region gs out j b
  change Disjoint u v at sep
  have same : globalWire gs out i = value gs out j := idx ▸ stored_value j nf
  have orig := m.1.2
  rw [same] at orig
  have early (t : Nat) (data : Minimal (live gs out j t) T) : False := by
    have earlier := live_before j t data size
    have own := hidden j t data size
    have minI := m.2 t own
    omega
  rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
  · have any (s : Region) : Active (value gs out j) s ↔ Active F s ∨ Active G s := by
      have logic (p q : Bool) : (p && q)=false ↔ p=false ∨ q=false := by cases p <;> cases q <;> decide
      simpa [F,G,value,bit,ids,gate,GateOp.eval,Active,live] using logic (F (missing s)) (G (missing s))
    rcases (any T).mp orig.1 with A|B
    · exact False.elim (early a ⟨A,fun X on sm => orig.2 X ((any X).mpr (Or.inl on)) sm⟩)
    · exact False.elim (early b ⟨B,fun X on sm => orig.2 X ((any X).mpr (Or.inr on)) sm⟩)
  · refine ⟨⟨j,idx,gate⟩,?_⟩
    intro three
    have both (s : Region) : Active (value gs out j) s ↔ Active F s ∧ Active G s := by
      simp [F,G,Active,value,bit,ids,gate,GateOp.eval,live]
    have af : Local F u := live_local _ _ _ _
    have bf : Local G v := live_local _ _ _ _
    have left := project_piece af bf sep orig both
    have right := project_piece bf af sep.symm orig (fun s => (both s).trans and_comm)
    have union := exact_union af bf sep orig both
    have disT : Disjoint (T∩u) (T∩v) := sep.mono Finset.inter_subset_right Finset.inter_subset_right
    have total : (T∩u).card+(T∩v).card=3 := by
      rw [←Finset.card_union_of_disjoint disT,union,three]
    have smaller {t : Nat} {s : Region} (leg : Minimal (live gs out j t) (T∩s)) : (T∩s).card<3 := by
      by_contra! large
      have eq := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (show T.card≤(T∩s).card by omega)
      rw [eq] at leg
      exact early t leg
    have a0 := smaller left
    have b0 := smaller right
    by_cases pair : (T∩u).card=2
    · exact ⟨a,_,Finset.inter_subset_left,pair,hidden j a left pair.ge⟩
    · have pair' : (T∩v).card=2 := by omega
      exact ⟨b,_,Finset.inter_subset_left,pair',hidden j b right pair'.ge⟩

theorem pair_and_triple {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (limit : gs.length≤24)
    {T : Region} (three : T.card=3) (yes : ∃i, Own gs out i T) :
    ∃ i j : Nat, Conjunction gs i ∧ Conjunction gs j ∧ Own gs out i T ∧
      ∃U⊆T, U.card=2 ∧ Own gs out j U := by
  obtain ⟨i,earliest⟩ := first yes
  obtain ⟨I,child⟩ := first_and basis arity h limit earliest (by omega)
  obtain ⟨k,U,sub,size,letter⟩ := child three
  obtain ⟨j,m⟩ := first (show ∃k, Own gs out k U from ⟨k,letter⟩)
  exact ⟨i,j,I,(first_and basis arity h limit m size.ge).1,earliest.1,U,sub,size,m.1⟩
end Plane920.Forest

namespace Plane920.Forest
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut

def pencil (p : V) := Finset.univ.filter (fun w : V => p∈line w)
noncomputable def protectedAt (gs : List Gate) (out : V→Nat) (w : V) : Finset Nat := by
  classical
  exact (reserved gs out w).filter (Conjunction gs)
noncomputable def locked (gs : List Gate) (out : V→Nat) (p : V) := (pencil p).biUnion (protectedAt gs out)
noncomputable def spare (gs : List Gate) (out : V→Nat) (p : V) := paid (terminals out) 13 gs.length \ locked gs out p

theorem singleton_triple {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) {c p w : V} (fiber : block f c={p})
    (inc : p∈line w) : ∃ T⊆line w, T.card=3 ∧ ∃i, Own gs out i T := by
  have deg : degree (block f c) w=1 := by simp [degree,fiber,inc]
  obtain ⟨a,b,U,W,un,sep,ma,mb⟩ := operands basis arity h uni (diff_of_degree f c w (by omega) (by omega))
  let j := outIndex h w
  have same (i : Nat) {X : Region} (m : Minimal (live gs out j i) X) (px : p∈X) : X.card=1 := by
    have sub := minimum_support (live_local gs out j i) m
    let xs := start++supportTail (terminals out) start (gs.take j.val)
    have homog : Hom f (region gs out j i) := available_hom (prefix_uniform gs uni j.val) (readable xs i)
    have cp : p∈block f c := by simp [fiber]
    have all : X⊆{p} := by
      intro x hx
      have col : f x=c := (homog x (sub hx) p (sub px)).trans (Finset.mem_filter.mp cp).2
      rw [←fiber]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,col⟩
    have eq := Finset.eq_of_subset_of_card_le all (by simp; exact ⟨p,px⟩)
    simp [eq]
  have size : U.card+W.card=4 := by rw [←Finset.card_union_of_disjoint sep,un,line_size]
  have full : p∈U∪W := un ▸ inc
  rcases Finset.mem_union.mp full with pu|pw
  · have one := same a ma pu
    exact ⟨W,un ▸ Finset.subset_union_right,by omega,b,hidden j b mb (by omega)⟩
  · have one := same b mb pw
    exact ⟨U,un ▸ Finset.subset_union_left,by omega,a,hidden j a ma (by omega)⟩

theorem locked_paid (gs : List Gate) (out : V→Nat) (p : V) : locked gs out p⊆paid (terminals out) 13 gs.length := by
  classical
  intro i hi
  obtain ⟨w,_,mem⟩ := Finset.mem_biUnion.mp hi
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp mem).1).1

theorem eight {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤24) (uni : Uniform f (start++supportTail (terminals out) start gs)) {c p : V} (fiber : block f c={p}) :
    8≤(locked gs out p).card ∧ (spare gs out p).card≤3 := by
  classical
  have lineCost (w : V) (hw : w∈pencil p) : 2≤(protectedAt gs out w).card := by
    obtain ⟨T,inL,num,signal⟩ := singleton_triple basis arity h uni fiber (Finset.mem_filter.mp hw).2
    obtain ⟨i,j,I,J,m,U,sub,size,n⟩ := pair_and_triple basis arity h limit num signal
    have typed {k : Nat} {S : Region} (bound : 2≤S.card) (inside : S⊆line w) (own : Own gs out k S) (gate : Conjunction gs k) :
        k∈protectedAt gs out w := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨own.1,S,bound,inside,own.2⟩,gate⟩
    have ne : i≠j := by
      rintro rfl
      have eq := minima_eq m.2 n.2
      rw [eq,size] at num
      contradiction
    exact Finset.one_lt_card.mpr ⟨i,typed (by omega) inL m I,j,typed size.ge (sub.trans inL) n J,ne⟩
  have disjoint {w t : V} (ne : w≠t) : Disjoint (protectedAt gs out w) (protectedAt gs out t) := by
    apply Finset.disjoint_left.mpr
    intro i hi hk
    obtain ⟨T,big,sub,m⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    obtain ⟨U,_,other,n⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    have eq := minima_eq m n
    have cap := (Finset.card_le_card (Finset.subset_inter sub (show T⊆line t from eq ▸ other))).trans (OrSupport.line_pair w t ne)
    omega
  have cost := Finset.sum_le_sum lineCost
  have four : (pencil p).card=4 := incidences p
  have eight : 8≤(locked gs out p).card := by
    rw [locked,Finset.card_biUnion (fun _ _ _ _ ne => disjoint ne)]
    simpa [four] using cost
  refine ⟨eight,?_⟩
  rw [spare,Finset.card_sdiff_of_subset (locked_paid _ _ _),hidden_count h]
  omega

theorem locked_off {gs : List Gate} {out : V→Nat} {p w : V} {i : Nat} {S : Region}
    (gate : i∈locked gs out p) (transverse : p∉line w) (sub : S⊆line w) (small : S.card≤2) :
    ¬Active (globalWire gs out i) S := by
  classical
  obtain ⟨t,ht,typed⟩ := Finset.mem_biUnion.mp gate
  obtain ⟨T,big,inT,m⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp typed).1).2
  intro on
  have eq := m.2 S on (by omega)
  have ne : w≠t := fun rel => transverse (rel ▸ (Finset.mem_filter.mp ht).2)
  have cap := (Finset.card_le_card (Finset.subset_inter sub (show S⊆line t from eq ▸ inT))).trans (OrSupport.line_pair w t ne)
  rw [eq] at cap
  omega

theorem locked_single {gs : List Gate} {out : V→Nat} {p : V} {i : Nat} (gate : i∈locked gs out p) (x : V) :
    ¬Active (globalWire gs out i) {x} := by
  classical
  obtain ⟨t,_,typed⟩ := Finset.mem_biUnion.mp gate
  obtain ⟨T,big,_,m⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp typed).1).2
  intro yes
  have eq := m.2 {x} yes (by rw [Finset.card_singleton]; omega)
  rw [←eq,Finset.card_singleton] at big
  omega
end Plane920.Forest

namespace Plane920.Forest
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut

def Hard (F : Input→Bool) (L : Region) := Active F L ∧ ∀x∈L, ¬Active F {x}

theorem ov_mono (gs : List Gate) (ops : ∀g∈gs,g.op=.and ∨ g.op=.or) (z : Finset Nat)
    (as bs : List Bool) (h : List.Forall₂ Nine.R as bs) : List.Forall₂ Nine.R (overwrite z gs as) (overwrite z gs bs) := by
  induction gs generalizing as bs with
  | nil => exact h
  | cons g gs ih =>
    have step : Nine.R (bit g as) (bit g bs) := by
      rcases ops g (by simp) with left|right
      · simpa only [bit,left,GateOp.eval] using (Nine.gates_mono h g.inputs).1
      · simpa only [bit,right,GateOp.eval] using (Nine.gates_mono h g.inputs).2
    have next : Nine.R (if as.length∈z then true else bit g as) (if bs.length∈z then true else bit g bs) := by
      rw [h.length_eq];split
      · exact id
      · exact step
    exact ih (fun t ht=>ops t (by simp [ht])) _ _ (List.rel_append h (.cons next .nil))

theorem grow_live {gs : List Gate} (ops : ∀g∈gs,g.op=.and ∨ g.op=.or) (out : V→Nat)
    (j : Fin gs.length) (i : Nat) {S T : Region} (sub : S⊆T) (yes : Active (live gs out j i) S) :
    Active (live gs out j i) T := by
  have input : List.Forall₂ Nine.R (List.ofFn (missing T)) (List.ofFn (missing S)) := by
    apply List.forall₂_of_length_eq_of_get (by simp only [List.length_ofFn])
    intro k hk h'
    rw [List.get_ofFn,List.get_ofFn]
    exact fun eq => decide_eq_true (fun e => of_decide_eq_true eq (sub e))
  have up := Nine.get_mono (ov_mono (gs.take j.val) (fun g mem=>ops g (List.mem_of_mem_take mem)) (terminals out) _ _ input) i
  by_contra no
  have got := up (Bool.eq_true_of_not_eq_false no)
  exact Bool.false_ne_true (yes.symm.trans got)

theorem raw_global (gs : List Gate) (out : V→Nat) (i : Nat) (raw : i<13) (x : Input) :
    globalWire gs out i x = x ⟨i,raw⟩ := by
  unfold globalWire
  rw [ov_stable _ _ _ _ (by simpa only [List.length_ofFn] using raw),
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using raw)]
  exact List.getElem_ofFn _

theorem missing_live (gs : List Gate) (out : V→Nat) (j : Fin gs.length) (i : Nat) (late : 13+j.val ≤ i)
    (x : Input) : live gs out j i x=false := by
  unfold live
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa only [width,List.length_ofFn,List.length_take,Nat.min_eq_left j.isLt.le] using late)]
  rfl

theorem hard_hidden {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {k : Nat} {L : Region}
    (pop : L.Nonempty) (m : Hard (live gs out j k) L) :
    k<13+j.val ∧ k∈paid (terminals out) 13 gs.length ∧ Hard (globalWire gs out k) L := by
  obtain ⟨p,hp⟩ := pop
  have early : k<13+j.val := by
    by_contra! late
    exact m.2 p hp (missing_live _ _ _ _ late _)
  rw [sem_prefix _ _ _ _ early] at m
  have lo : 13 ≤ k := by
    by_contra! raw
    let v : V := ⟨k,raw⟩
    have value := m.1
    unfold Active at value
    rw [raw_global _ _ _ raw] at value
    have mem : v∈L := by simpa [missing,v] using value
    apply m.2 v mem
    simp only [Active,raw_global _ _ _ raw,missing]
    simp [v]
  have free : k∉terminals out := by
    intro yes
    have high := frozen_high gs _ (List.ofFn (missing L)) k yes (by simpa only [List.length_ofFn] using lo)
      (by simp only [List.length_ofFn]; omega)
    exact Bool.false_ne_true (m.1.symm.trans high)
  exact ⟨early,Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨lo,by omega⟩,free⟩,m⟩

theorem small_union {gs : List Gate} (ops : ∀g∈gs,g.op=.and ∨ g.op=.or) (out : V→Nat) (j : Fin gs.length)
    (L : Region) (ins : List Nat) (each : ∀i∈ins, Active (live gs out j i) L → ∃x∈L, Active (live gs out j i) {x}) :
    ∃S⊆L, S.card ≤ ins.length ∧ ∀i∈ins, Active (live gs out j i) L → Active (live gs out j i) S := by
  induction ins with
  | nil => exact ⟨∅,Finset.empty_subset _,by simp,by simp⟩
  | cons i rest ih =>
    obtain ⟨T,sub,sm,holds⟩ := ih (fun k mem=>each k (by simp [mem]))
    by_cases active : Active (live gs out j i) L
    · obtain ⟨x,inL,on⟩ := each i (by simp) active
      refine ⟨insert x T,Finset.insert_subset inL sub,(Finset.card_insert_le _ _).trans (by simp; omega),?_⟩
      intro k mem yes
      rcases List.mem_cons.mp mem with rfl|later
      · exact grow_live ops _ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) on
      · exact grow_live ops _ _ _ (Finset.subset_insert _ _) (holds k later yes)
    · refine ⟨T,sub,by simp; omega,?_⟩
      intro k mem yes
      rcases List.mem_cons.mp mem with rfl|later
      · exact False.elim (active yes)
      · exact holds k later yes

theorem hard_exists {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (w : V) :
    ∃k, k∈paid (terminals out) 13 gs.length ∧ Hard (globalWire gs out k) (line w) := by
  let j := outIndex h w
  have law (S : Region) (size : S.card≤4) : Active (value gs out j) S ↔ S=line w := by
    have heavy : 9≤(supp (missing S)).card := by
      rw [complement,Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      have total : (Finset.univ : Region).card=13 := by decide
      omega
    rw [Active,normalized basis h w j (index_eq h w) _ heavy,←h w _ heavy]
    exact statement h size
  by_contra! absent
  have each (i : Nat) (_ : i∈gs[j.val].inputs) (yes : Active (live gs out j i) (line w)) :
      ∃x∈line w, Active (live gs out j i) {x} := by
    by_contra! no
    have pos : (line w).Nonempty := Finset.card_pos.mp (by rw [line_size]; decide)
    have hidden := hard_hidden pos ⟨yes,no⟩
    exact absent i hidden.2.1 hidden.2.2
  obtain ⟨S,sub,bound,same⟩ := small_union basis out j (line w) gs[j.val].inputs each
  have gateEq : value gs out j (missing S) = value gs out j (missing (line w)) := by
    apply congrArg gs[j.val].op.eval
    apply List.map_congr_left
    intro i used
    apply Bool.eq_iff_iff.mpr
    have eq : Active (live gs out j i) S ↔ Active (live gs out j i) (line w) :=
      ⟨grow_live basis _ _ _ sub, same i used⟩
    exact not_iff_not.mp (by simpa only [Active,live,Bool.not_eq_true] using eq)
  have small : S.card≤2 := bound.trans (arity _ (List.getElem_mem _))
  have exactS := (law S (by omega)).mp (gateEq.trans ((law _ (line_size w).le).mpr rfl))
  rw [exactS,line_size] at small
  omega
end Plane920.Forest

namespace Plane920.Forest
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut

def sign (F : Input→Bool) := Finset.univ.filter (fun x : V => F (missing {x})=false)
theorem sign_mem {F : Input→Bool} {x : V} : x∈sign F ↔ Active F {x} := by simp [sign,Active]
def sides (gs : List Gate) (i : Nat) := ((gs[i-13]?.map Gate.inputs).getD [])
def source (gs : List Gate) (out : V→Nat) (i side : Nat) (x : Input) :=
  (overwrite (terminals out) (gs.take (i-13)) (List.ofFn x)).getD ((sides gs i).getD side 0) false
def leftSide (gs : List Gate) (out : V→Nat) (i : Nat) := sign (source gs out i 0)
def rightSide (gs : List Gate) (out : V→Nat) (i : Nat) := sign (source gs out i 1)
def signal (gs : List Gate) (out : V→Nat) (i : Nat) := sign (globalWire gs out i)

theorem sides_at {gs : List Gate} {out : V→Nat} (j : Fin gs.length) {a b : Nat} (ids : gs[j.val].inputs=[a,b]) :
    source gs out (13+j.val) 0=live gs out j a ∧ source gs out (13+j.val) 1=live gs out j b := by
  have same : 13+j.val-13=j.val := by omega
  have s : sides gs (13+j.val)=[a,b] := by simp only [sides,same,List.getElem?_eq_getElem j.isLt,Option.map_some,Option.getD_some,ids]
  constructor <;> funext x <;> simp only [source,same,s,live,List.getD_cons_zero,List.getD_cons_succ]

theorem transverse_mark {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (limit : gs.length≤24) {p w : V} (outside : p∉line w) :
    ∃ i∈spare gs out p, ∃x∈line w, ∃y∈line w,
      x∈leftSide gs out i \ rightSide gs out i ∧ y∈rightSide gs out i \ leftSide gs out i := by
  classical
  let L := line w
  let P (k : Nat) := k∈paid (terminals out) 13 gs.length ∧ Hard (globalWire gs out k) L
  have init : ∃k, P k := hard_exists basis arity h w
  let i := Nat.find init
  have now : P i := Nat.find_spec init
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp now.1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  obtain ⟨a,b,ids,_,_,_⟩ := every_hidden_splits basis arity h limit j nf
  let F := live gs out j a
  let G := live gs out j b
  have same : globalWire gs out i = value gs out j := idx ▸ stored_value j nf
  have hard := now.2
  rw [same] at hard
  have pop : L.Nonempty := Finset.card_pos.mp (by change 0<(line w).card; rw [line_size]; decide)
  have each (k : Nat) (on : Active (live gs out j k) L) : ∃x∈L, Active (live gs out j k) {x} := by
    by_contra! none
    obtain ⟨earlier,inPaid,data⟩ := hard_hidden pop ⟨on,none⟩
    have lower : i≤k := Nat.find_min' init (show P k from ⟨inPaid,data⟩)
    omega
  rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
  · have any (s : Region) : Active (value gs out j) s ↔ Active F s ∨ Active G s := by
      have logic (q r : Bool) : (q && r)=false ↔ q=false ∨ r=false := by cases q <;> cases r <;> decide
      simpa [F,G,value,bit,ids,gate,GateOp.eval,Active,live] using logic (F (missing s)) (G (missing s))
    rcases (any L).mp hard.1 with A|B
    · obtain ⟨x,inL,yes⟩ := each a A
      exact False.elim (hard.2 x inL ((any _).mpr (Or.inl yes)))
    · obtain ⟨x,inL,yes⟩ := each b B
      exact False.elim (hard.2 x inL ((any _).mpr (Or.inr yes)))
  · have both (s : Region) : Active (value gs out j) s ↔ Active F s ∧ Active G s := by
      simp [F,G,value,bit,ids,gate,GateOp.eval,Active,live]
    obtain ⟨af,bg⟩ := (both L).mp hard.1
    obtain ⟨x,xL,xA⟩ := each a af
    obtain ⟨y,yL,yB⟩ := each b bg
    have nx : ¬Active G {x} := fun bad => hard.2 x xL ((both _).mpr ⟨xA,bad⟩)
    have ny : ¬Active F {y} := fun bad => hard.2 y yL ((both _).mpr ⟨bad,yB⟩)
    have pair : Active (globalWire gs out i) {x,y} := by
      rw [same]
      apply (both _).mpr
      exact ⟨grow_live basis _ _ _ (by simp) xA,grow_live basis _ _ _ (by simp) yB⟩
    have free : i∉locked gs out p := fun held => locked_off held outside (Finset.insert_subset xL (Finset.singleton_subset_iff.mpr yL))
      (Finset.card_insert_le _ _ |>.trans (by simp)) pair
    have lr := sides_at (out := out) j ids
    rw [idx] at lr
    have l : leftSide gs out i=sign F := congrArg sign lr.1
    have r : rightSide gs out i=sign G := congrArg sign lr.2
    refine ⟨i,Finset.mem_sdiff.mpr ⟨now.1,free⟩,x,xL,y,yL,?_⟩
    rw [l,r]
    exact ⟨Finset.mem_sdiff.mpr ⟨sign_mem.mpr xA,fun v=>nx (sign_mem.mp v)⟩,
      Finset.mem_sdiff.mpr ⟨sign_mem.mpr yB,fun v=>ny (sign_mem.mp v)⟩⟩
end Plane920.Forest

namespace Plane920.Forest
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut
open Plane920Ordered Plane920Signs

theorem sign_prior {gs : List Gate} {out : V→Nat} {p : V} (j : Fin gs.length) (k : Nat) :
    Prior (spare gs out p) (signal gs out) (13+j.val) (sign (live gs out j k)) := by
  classical
  by_cases before : k<13+j.val
  · rw [sem_prefix _ _ _ _ before]
    by_cases raw : k<13
    · left;right
      let v : V := ⟨k,raw⟩
      have eq : sign (globalWire gs out k)={v} := by
        ext x
        simp only [sign_mem,Active,raw_global _ _ _ raw,missing,Finset.mem_singleton]
        change decide (v≠x)=false ↔ x=v
        rw [decide_eq_false_iff_not,not_not]
        exact eq_comm
      simp [eq]
    by_cases held : k∈terminals out
    · left;right
      have eq : sign (globalWire gs out k)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have no := sign_mem.mp hx
        have off := frozen_high gs _ (List.ofFn (missing {x})) k held (by simp only [List.length_ofFn]; omega)
          (by simp only [List.length_ofFn]; omega)
        exact Bool.false_ne_true (no.symm.trans off)
      simp [eq]
    by_cases lockedK : k∈locked gs out p
    · left;right
      have eq : sign (globalWire gs out k)=∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun x hx=>locked_single lockedK x (sign_mem.mp hx))
      simp [eq]
    right
    have kpaid : k∈paid (terminals out) 13 gs.length := Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,held⟩
    exact ⟨k,Finset.mem_sdiff.mpr ⟨kpaid,lockedK⟩,before,rfl⟩
  · left;left
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    exact sign_mem.mpr (missing_live _ _ _ _ (by omega) _)

theorem spare_step {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (limit : gs.length≤24) {p : V} {i : Nat}
    (eligible : i∈spare gs out p) :
    (∃ b, signal gs out i=op b (leftSide gs out i) (rightSide gs out i)) ∧
    Prior (spare gs out p) (signal gs out) i (leftSide gs out i) ∧ Prior (spare gs out p) (signal gs out) i (rightSide gs out i) := by
  classical
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp eligible).1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  obtain ⟨a,b,ids,_,_,_⟩ := every_hidden_splits basis arity h limit j nf
  have lr := sides_at (out := out) j ids
  rw [idx] at lr
  have left : leftSide gs out i=sign (live gs out j a) := congrArg sign lr.1
  have right : rightSide gs out i=sign (live gs out j b) := congrArg sign lr.2
  have full : globalWire gs out i=value gs out j := idx ▸ stored_value j nf
  rw [left,right]
  refine ⟨?_,idx ▸ sign_prior j a,idx ▸ sign_prior j b⟩
  rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
  · refine ⟨true,?_⟩
    ext x
    have law (q r : Bool) : ((q && r)=false ↔ q=false ∨ r=false) := by cases q <;> cases r <;> decide
    simpa [signal,sign_mem,op,full,Active,value,bit,ids,gate,GateOp.eval,live] using
      law (live gs out j a (missing {x})) (live gs out j b (missing {x}))
  · refine ⟨false,?_⟩
    ext x
    simp [signal,sign_mem,op,full,Active,value,bit,ids,gate,GateOp.eval,live]

theorem twenty_five {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) :
    25≤gs.length := by
  by_contra! limit
  have small : gs.length≤24 := by omega
  obtain ⟨f,c,p,uni,_,fiber⟩ := only_singleton basis arity h small
  let E := spare gs out p
  let A := leftSide gs out
  let B := rightSide gs out
  let O := signal gs out
  have bound := (eight basis arity h small uni fiber).2
  have step (i : Nat) (mem : i∈E) := spare_step basis arity h small mem
  have high := sum_weight E A B O bound (fun i hi => (step i hi).1)
    (fun i hi => (step i hi).2.1) (fun i hi => (step i hi).2.2)
  have low : (outsiders p).card≤∑i∈E, Plane920Signs.weight (A i) (B i) := by
    apply lines_by_weight
    intro w hw
    have on : p∉line w := (Finset.mem_filter.mp hw).2
    obtain ⟨i,ei,x,xL,y,yL,xa,yb⟩ := transverse_mark basis arity h small on
    exact ⟨i,ei,x,xa,y,yb,xL,yL⟩
  rw [nine] at low
  omega
end Plane920.Forest

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest

noncomputable def defects (z : Finset Nat) (xs : List SetV) : List Gate → Finset Nat := by
  classical
  exact fun gs => match gs with
    | [] => ∅
    | g::rest =>
      let s := if xs.length∈z then ∅ else gather xs g.inputs
      let more := defects z (xs++[s]) rest
      if xs.length∉z ∧ ¬Splits xs g.inputs then insert xs.length more else more
termination_by gs => gs.length

theorem defect_range (z : Finset Nat) (xs : List SetV) (gs : List Gate) {k : Nat} (mem : k∈defects z xs gs) :
    xs.length≤k := by
  classical
  induction gs generalizing xs with
  | nil => simp [defects] at mem
  | cons g gs ih =>
    rw [defects] at mem
    split at mem
    · rcases Finset.mem_insert.mp mem with eq|m
      · omega
      · have lo := ih _ m
        simp only [List.length_append,List.length_singleton] at lo
        omega
    · have lo := ih _ mem
      simp only [List.length_append,List.length_singleton] at lo
      omega

theorem defect_card (z : Finset Nat) (xs : List SetV) (gs : List Gate) :
    (defects z xs gs).card=waste z xs gs := by
  classical
  induction gs generalizing xs with
  | nil => simp [waste,defects]
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    have fresh : xs.length∉defects z (xs++[s]) gs := by
      intro yes
      have low := defect_range _ _ _ yes
      simp [s] at low
    rw [defects,waste]
    change (if xs.length∉z ∧ ¬Splits xs g.inputs then insert xs.length (defects z (xs++[s]) gs)
      else defects z (xs++[s]) gs).card = _ + waste z (xs++[s]) gs
    split <;> simp [*,Nat.add_comm]

theorem defect_cases (z : Finset Nat) (xs : List SetV) (gs : List Gate)
    (j : Fin gs.length) (nz : xs.length+j.val∉z) :
    Splits (xs++supportTail z xs (gs.take j.val)) gs[j.val].inputs ∨ xs.length+j.val∈defects z xs gs := by
  classical
  induction gs generalizing xs with
  | nil => exact Fin.elim0 j
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    cases j using Fin.cases with
    | zero =>
      by_cases yes : Splits xs g.inputs
      · exact Or.inl (by simpa [supportTail] using yes)
      · have no : xs.length∉z := by simpa using nz
        right
        simp [defects,no,yes]
    | succ j =>
      have eq : (xs++[s]).length+j.val=xs.length+j.succ.val := by simp; omega
      have free : (xs++[s]).length+j.val∉z := eq ▸ nz
      rcases ih (xs++[s]) j free with y|n
      · left
        simpa only [Fin.val_succ,List.take_succ_cons,supportTail,List.append_assoc,List.singleton_append,
          List.getElem_cons_succ,s] using y
      · right
        rw [defects]
        rw [eq] at n
        split
        · exact Finset.mem_insert_of_mem n
        · exact n

theorem at_most_one {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤25) : (defects (terminals out) start gs).card≤1 := by
  rw [defect_card]
  have initial : Uniform id start := by
    intro s mem
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro i hi j hj
    change i=j
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  obtain ⟨f,uni,cost⟩ := refined gs arity (terminals out) start id initial
  have n : (colors (id : V→V)).card=13 := by decide
  have len : start.length=13 := by simp [start]
  rw [n,len,hidden_count h] at cost
  by_contra! many
  have three : 3≤(colors f).card := by omega
  have lo := three_implies_twenty_six basis arity h uni three
  omega
end Plane920.Forest26

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest
theorem descend_sound {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (i : Nat) (present : i∈paid (terminals out) 13 gs.length) {T : Region}
    (free : i∉defects (terminals out) start gs) (m : Minimal (globalWire gs out i) T) (big : 3≤T.card) :
    ∃ k < i, k∈paid (terminals out) 13 gs.length ∧ ∃ U⊆T, 2≤U.card ∧ Minimal (globalWire gs out k) U := by
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp present
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have notTerminal : 13+j.val∉terminals out := idx ▸ nz
  have cases' := defect_cases (terminals out) start gs j (by simpa [start] using notTerminal)
  have split := cases'.resolve_right (by simpa only [show start.length=13 from by simp [start],idx] using free)
  obtain ⟨a,b,ids,_,_,sep⟩ := split
  have same : globalWire gs out i = value gs out j := idx ▸ stored_value j notTerminal
  rw [same] at m
  have rule :
      (∀s, Active (value gs out j) s ↔ Active (live gs out j a) s ∨ Active (live gs out j b) s) ∨
      (∀s, Active (value gs out j) s ↔ Active (live gs out j a) s ∧ Active (live gs out j b) s) := by
    rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
    · left
      intro s
      have logic (p q : Bool) : (p && q)=false ↔ p=false ∨ q=false := by cases p <;> cases q <;> decide
      exact (by simpa [value,bit,ids,gate,GateOp.eval,Active,live] using logic (live gs out j a (missing s)) (live gs out j b (missing s)))
    · right
      intro s
      simp [Active,value,bit,ids,gate,GateOp.eval,live]
  obtain ⟨U,inc,size,child⟩ := lower_child (live_local gs out j a) (live_local gs out j b) sep m big rule
  have done (k : Nat) (s : Minimal (live gs out j k) U) : k < i ∧ k∈paid (terminals out) 13 gs.length ∧ Minimal (globalWire gs out k) U := by
    have before := live_before j k s size
    exact ⟨by omega,hidden j k s size⟩
  rcases child with A|B
  · obtain ⟨p,q,t⟩ := done a A
    exact ⟨a,p,q,U,inc,size,t⟩
  · obtain ⟨p,q,t⟩ := done b B
    exact ⟨b,p,q,U,inc,size,t⟩
theorem cross_debit {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs))
    {w : V} (mixed : Varied f (line w)) :
    2≤(reserved gs out w).card + (reserved gs out w∩defects (terminals out) start gs).card := by
  classical
  let j := outIndex h w
  obtain ⟨a,b,U,W,un,sep,ma,mb⟩ := operands basis arity h uni mixed
  have cu : U⊆line w := un ▸ Finset.subset_union_left
  have cw : W⊆line w := un ▸ Finset.subset_union_right
  have sum : U.card+W.card=4 := by rw [←Finset.card_union_of_disjoint sep,un,line_size]
  let R := reserved gs out w
  let D := defects (terminals out) start gs
  have mem {k : Nat} {s : Region} (leg : k∈paid (terminals out) 13 gs.length) (size : 2≤s.card)
      (sub : s⊆line w) (m : Minimal (globalWire gs out k) s) : k∈R :=
    Finset.mem_filter.mpr ⟨leg,s,size,sub,m⟩
  have large {k : Nat} {s : Region} (big : 3≤s.card) (sub : s⊆line w) (signal : Minimal (live gs out j k) s) :
      2≤R.card+(R∩D).card := by
    obtain ⟨inPaid,m⟩ := hidden j k signal (by omega)
    have member : k∈R := mem inPaid (by omega) sub m
    by_cases bad : k∈D
    · have one := Finset.card_pos.mpr ⟨k,member⟩
      have two := Finset.card_pos.mpr ⟨k,Finset.mem_inter.mpr ⟨member,bad⟩⟩
      omega
    · obtain ⟨other,lt,paidOther,T,ts,card,m2⟩ := descend_sound basis k inPaid bad m big
      have cost : 1<R.card := Finset.one_lt_card.mpr ⟨other,mem paidOther card (ts.trans sub) m2,k,member,lt.ne⟩
      omega
  by_cases largeU : 3≤U.card
  · exact large largeU cu ma
  by_cases largeW : 3≤W.card
  · exact large largeW cw mb
  have bu : 2≤U.card := by omega
  have bw : 2≤W.card := by omega
  obtain ⟨paidA,ma'⟩ := hidden j a ma bu
  obtain ⟨paidB,mb'⟩ := hidden j b mb bw
  have ne : a≠b := by
    intro eq
    rw [eq] at ma'
    have same := minima_eq ma' mb'
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0<2) bu)
    exact Finset.disjoint_left.mp sep hi (same ▸ hi)
  have cost : 1<R.card := Finset.one_lt_card.mpr ⟨a,mem paidA bu cu ma',b,mem paidB bw cw mb',ne⟩
  change 2≤R.card+(R∩D).card
  omega

theorem cross_budget {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (limit : gs.length≤25)
    (S : Region) (cross : ∀w∈S, Varied f (line w)) : 2*S.card≤gs.length-13+1 := by
  classical
  let D := defects (terminals out) start gs
  let R := reserved gs out
  let R' (w : V) := R w∩D
  have dis {a b : V} (ne : a≠b) : Disjoint (R a) (R b) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨T,big,sub,own⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨U,_,sub',own'⟩ := (Finset.mem_filter.mp hj).2
    have eq := minima_eq own own'
    have lim := (Finset.card_le_card (Finset.subset_inter sub (show T⊆line b from eq ▸ sub'))).trans (OrSupport.line_pair a b ne)
    omega
  have inc : S.biUnion R'⊆D := by
    intro i hi
    obtain ⟨w,_,mem⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_inter.mp mem).2
  have defectCost := Finset.card_le_card inc
  rw [Finset.card_biUnion (fun _ _ _ _ n => (dis n).mono Finset.inter_subset_left Finset.inter_subset_left)] at defectCost
  have bad : D.card≤1 := at_most_one basis arity h limit
  have extra : (∑w∈S,(R' w).card)≤1 := defectCost.trans bad
  have paidBound : (∑w∈S,(R w).card)≤gs.length-13 := reserved_budget h S
  have sum := Finset.sum_le_sum (fun w (hw : w∈S) => cross_debit basis arity h uni (cross w hw))
  change (∑_w∈S,(2:Nat))≤∑w∈S,((R w).card+(R' w).card) at sum
  rw [Finset.sum_add_distrib] at sum
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at sum
  omega

theorem two_points_impossible {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤25) (uni : Uniform f (start++supportTail (terminals out) start gs)) (c : V)
    (small : (block f c).card≤3) : (block f c).card≤1 := by
  classical
  by_contra! many
  obtain ⟨p,hp,q,hq,diff⟩ := Finset.one_lt_card.mp many
  let pen (i : V) := Finset.univ.filter (fun w : V => i∈line w)
  let S := pen p ∪ pen q
  have inter : pen p∩pen q=Finset.univ.filter (fun w : V => p∈line w ∧ q∈line w) := by ext; simp [pen]
  have seven : S.card=7 := by
    have counts := Finset.card_union_add_card_inter (pen p) (pen q)
    rw [inter,joins p q diff,show (pen p).card=4 from incidences p,show (pen q).card=4 from incidences q] at counts
    change (pen p∪pen q).card=7
    omega
  have mixed (w : V) (mem : w∈S) : Varied f (line w) := by
    have has : (line w∩block f c).Nonempty := by
      rcases Finset.mem_union.mp mem with left|right
      · exact ⟨p,Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp left).2,hp⟩⟩
      · exact ⟨q,Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp right).2,hq⟩⟩
    have upper := Finset.card_le_card (Finset.inter_subset_right (s₁ := line w) (s₂ := block f c))
    exact diff_of_degree f c w (Finset.card_pos.mpr has) (by unfold degree; omega)
  have total := cross_budget basis arity h uni limit S mixed
  omega

theorem residual {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (limit : gs.length≤25) :
    (colors f).card=1 ∨ ((colors f).card=2 ∧ ∃ c p : V, block f c={p}) := by
  rcases residual_twenty_five basis arity h uni limit with one|⟨two,c,pos,sm⟩
  · exact Or.inl one
  · have bound := two_points_impossible basis arity h limit uni c sm
    obtain ⟨p,eq⟩ := Finset.card_eq_one.mp (show (block f c).card=1 by omega)
    exact Or.inr ⟨two,c,p,eq⟩
end Plane920.Forest26

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest
open Plane920Ordered Plane920Signs
def Separated (gs : List Gate) (out : V→Nat) := ∀ j : Fin gs.length, 13+j.val∉terminals out →
  Splits (start++supportTail (terminals out) start (gs.take j.val)) gs[j.val].inputs
def disjoins : GateOp→Bool | .and => true | _ => false
def tag (gs : List Gate) (i : Nat) := (gs[i-13]?.map (fun g => disjoins g.op)).getD true
theorem tag_at (gs : List Gate) (j : Fin gs.length) : tag gs (13+j.val)=disjoins gs[j.val].op := by
  have eq : 13+j.val-13=j.val := by omega
  simp only [tag,eq,List.getElem?_eq_getElem j.isLt,Option.map_some,Option.getD_some]


theorem first_and {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (_arity : ∀g∈gs,g.inputs.length≤2) (_h : Correct gs out) (ok : Separated gs out)
    {i : Nat} {T : Region} (m : Earliest gs out i T) (size : 2≤T.card) :
    Conjunction gs i ∧ (T.card=3 → ∃j, ∃U⊆T, U.card=2 ∧ Own gs out j U) := by
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp m.1.1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  obtain ⟨a,b,ids,_,_,sep⟩ := ok j nf
  let F := live gs out j a
  let G := live gs out j b
  let u := region gs out j a
  let v := region gs out j b
  change Disjoint u v at sep
  have same : globalWire gs out i = value gs out j := idx ▸ stored_value j nf
  have orig := m.1.2
  rw [same] at orig
  have early (t : Nat) (data : Minimal (live gs out j t) T) : False := by
    have earlier := live_before j t data size
    have own := hidden j t data size
    have minI := m.2 t own
    omega
  rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
  · have any (s : Region) : Active (value gs out j) s ↔ Active F s ∨ Active G s := by
      have logic (p q : Bool) : (p && q)=false ↔ p=false ∨ q=false := by cases p <;> cases q <;> decide
      simpa [F,G,value,bit,ids,gate,GateOp.eval,Active,live] using logic (F (missing s)) (G (missing s))
    rcases (any T).mp orig.1 with A|B
    · exact False.elim (early a ⟨A,fun X on sm => orig.2 X ((any X).mpr (Or.inl on)) sm⟩)
    · exact False.elim (early b ⟨B,fun X on sm => orig.2 X ((any X).mpr (Or.inr on)) sm⟩)
  · refine ⟨⟨j,idx,gate⟩,?_⟩
    intro three
    have both (s : Region) : Active (value gs out j) s ↔ Active F s ∧ Active G s := by
      simp [F,G,Active,value,bit,ids,gate,GateOp.eval,live]
    have af : Local F u := live_local _ _ _ _
    have bf : Local G v := live_local _ _ _ _
    have left := project_piece af bf sep orig both
    have right := project_piece bf af sep.symm orig (fun s => (both s).trans and_comm)
    have union := exact_union af bf sep orig both
    have disT : Disjoint (T∩u) (T∩v) := sep.mono Finset.inter_subset_right Finset.inter_subset_right
    have total : (T∩u).card+(T∩v).card=3 := by
      rw [←Finset.card_union_of_disjoint disT,union,three]
    have smaller {t : Nat} {s : Region} (leg : Minimal (live gs out j t) (T∩s)) : (T∩s).card<3 := by
      by_contra! large
      have eq := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (show T.card≤(T∩s).card by omega)
      rw [eq] at leg
      exact early t leg
    have a0 := smaller left
    have b0 := smaller right
    by_cases pair : (T∩u).card=2
    · exact ⟨a,_,Finset.inter_subset_left,pair,hidden j a left pair.ge⟩
    · have pair' : (T∩v).card=2 := by omega
      exact ⟨b,_,Finset.inter_subset_left,pair',hidden j b right pair'.ge⟩


theorem pair_and_triple {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (ok : Separated gs out)
    {T : Region} (three : T.card=3) (yes : ∃i, Own gs out i T) :
    ∃ i j : Nat, Conjunction gs i ∧ Conjunction gs j ∧ Own gs out i T ∧
      ∃U⊆T, U.card=2 ∧ Own gs out j U := by
  obtain ⟨i,earliest⟩ := first yes
  obtain ⟨I,child⟩ := first_and basis arity h ok earliest (by omega)
  obtain ⟨k,U,sub,size,letter⟩ := child three
  obtain ⟨j,m⟩ := first (show ∃k, Own gs out k U from ⟨k,letter⟩)
  exact ⟨i,j,I,(first_and basis arity h ok m size.ge).1,earliest.1,U,sub,size,m.1⟩

theorem eight {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤25) (ok : Separated gs out) (uni : Uniform f (start++supportTail (terminals out) start gs)) {c p : V} (fiber : block f c={p}) :
    8≤(locked gs out p).card ∧ (spare gs out p).card≤4 := by
  classical
  have lineCost (w : V) (hw : w∈pencil p) : 2≤(protectedAt gs out w).card := by
    obtain ⟨T,inL,num,signal⟩ := singleton_triple basis arity h uni fiber (Finset.mem_filter.mp hw).2
    obtain ⟨i,j,I,J,m,U,sub,size,n⟩ := pair_and_triple basis arity h ok num signal
    have typed {k : Nat} {S : Region} (bound : 2≤S.card) (inside : S⊆line w) (own : Own gs out k S) (gate : Conjunction gs k) :
        k∈protectedAt gs out w := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨own.1,S,bound,inside,own.2⟩,gate⟩
    have ne : i≠j := by
      rintro rfl
      have eq := minima_eq m.2 n.2
      rw [eq,size] at num
      contradiction
    exact Finset.one_lt_card.mpr ⟨i,typed (by omega) inL m I,j,typed size.ge (sub.trans inL) n J,ne⟩
  have disjoint {w t : V} (ne : w≠t) : Disjoint (protectedAt gs out w) (protectedAt gs out t) := by
    apply Finset.disjoint_left.mpr
    intro i hi hk
    obtain ⟨T,big,sub,m⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    obtain ⟨U,_,other,n⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    have eq := minima_eq m n
    have cap := (Finset.card_le_card (Finset.subset_inter sub (show T⊆line t from eq ▸ other))).trans (OrSupport.line_pair w t ne)
    omega
  have cost := Finset.sum_le_sum lineCost
  have four : (pencil p).card=4 := incidences p
  have eight : 8≤(locked gs out p).card := by
    rw [locked,Finset.card_biUnion (fun _ _ _ _ ne => disjoint ne)]
    simpa [four] using cost
  refine ⟨eight,?_⟩
  rw [spare,Finset.card_sdiff_of_subset (locked_paid _ _ _),hidden_count h]
  omega


theorem transverse_mark {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (ok : Separated gs out) {p w : V} (outside : p∉line w) :
    ∃ i∈(spare gs out p).filter (fun k=>tag gs k=false), ∃x∈line w, ∃y∈line w,
      x∈leftSide gs out i \ rightSide gs out i ∧ y∈rightSide gs out i \ leftSide gs out i := by
  classical
  let L := line w
  let P (k : Nat) := k∈paid (terminals out) 13 gs.length ∧ Hard (globalWire gs out k) L
  have init : ∃k, P k := hard_exists basis arity h w
  let i := Nat.find init
  have now : P i := Nat.find_spec init
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp now.1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  obtain ⟨a,b,ids,_,_,_⟩ := ok j nf
  let F := live gs out j a
  let G := live gs out j b
  have same : globalWire gs out i = value gs out j := idx ▸ stored_value j nf
  have hard := now.2
  rw [same] at hard
  have pop : L.Nonempty := Finset.card_pos.mp (by change 0<(line w).card; rw [line_size]; decide)
  have each (k : Nat) (on : Active (live gs out j k) L) : ∃x∈L, Active (live gs out j k) {x} := by
    by_contra! none
    obtain ⟨earlier,inPaid,data⟩ := hard_hidden pop ⟨on,none⟩
    have lower : i≤k := Nat.find_min' init (show P k from ⟨inPaid,data⟩)
    omega
  rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
  · have any (s : Region) : Active (value gs out j) s ↔ Active F s ∨ Active G s := by
      have logic (q r : Bool) : (q && r)=false ↔ q=false ∨ r=false := by cases q <;> cases r <;> decide
      simpa [F,G,value,bit,ids,gate,GateOp.eval,Active,live] using logic (F (missing s)) (G (missing s))
    rcases (any L).mp hard.1 with A|B
    · obtain ⟨x,inL,yes⟩ := each a A
      exact False.elim (hard.2 x inL ((any _).mpr (Or.inl yes)))
    · obtain ⟨x,inL,yes⟩ := each b B
      exact False.elim (hard.2 x inL ((any _).mpr (Or.inr yes)))
  · have both (s : Region) : Active (value gs out j) s ↔ Active F s ∧ Active G s := by
      simp [F,G,value,bit,ids,gate,GateOp.eval,Active,live]
    obtain ⟨af,bg⟩ := (both L).mp hard.1
    obtain ⟨x,xL,xA⟩ := each a af
    obtain ⟨y,yL,yB⟩ := each b bg
    have nx : ¬Active G {x} := fun bad => hard.2 x xL ((both _).mpr ⟨xA,bad⟩)
    have ny : ¬Active F {y} := fun bad => hard.2 y yL ((both _).mpr ⟨bad,yB⟩)
    have pair : Active (globalWire gs out i) {x,y} := by
      rw [same]
      apply (both _).mpr
      exact ⟨grow_live basis _ _ _ (by simp) xA,grow_live basis _ _ _ (by simp) yB⟩
    have free : i∉locked gs out p := fun held => locked_off held outside (Finset.insert_subset xL (Finset.singleton_subset_iff.mpr yL))
      (Finset.card_insert_le _ _ |>.trans (by simp)) pair
    have lr := sides_at (out := out) j ids
    rw [idx] at lr
    have l : leftSide gs out i=sign F := congrArg sign lr.1
    have r : rightSide gs out i=sign G := congrArg sign lr.2
    have mark : tag gs i=false := by rw [←idx,tag_at,gate]; decide
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨now.1,free⟩,mark⟩,x,xL,y,yL,?_⟩
    rw [l,r]
    exact ⟨Finset.mem_sdiff.mpr ⟨sign_mem.mpr xA,fun v=>nx (sign_mem.mp v)⟩,
      Finset.mem_sdiff.mpr ⟨sign_mem.mpr yB,fun v=>ny (sign_mem.mp v)⟩⟩

theorem spare_step {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (_arity : ∀g∈gs,g.inputs.length≤2) (_h : Correct gs out) (ok : Separated gs out) {p : V} {i : Nat}
    (eligible : i∈spare gs out p) :
    (signal gs out i=op (tag gs i) (leftSide gs out i) (rightSide gs out i)) ∧
    Prior (spare gs out p) (signal gs out) i (leftSide gs out i) ∧ Prior (spare gs out p) (signal gs out) i (rightSide gs out i) := by
  classical
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp eligible).1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  obtain ⟨a,b,ids,_,_,_⟩ := ok j nf
  have lr := sides_at (out := out) j ids
  rw [idx] at lr
  have left : leftSide gs out i=sign (live gs out j a) := congrArg sign lr.1
  have right : rightSide gs out i=sign (live gs out j b) := congrArg sign lr.2
  have full : globalWire gs out i=value gs out j := idx ▸ stored_value j nf
  rw [left,right]
  refine ⟨?_,idx ▸ sign_prior j a,idx ▸ sign_prior j b⟩
  rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
  · have flag : tag gs i=true := by rw [←idx,tag_at,gate]; decide
    rw [flag]
    ext x
    have law (q r : Bool) : ((q && r)=false ↔ q=false ∨ r=false) := by cases q <;> cases r <;> decide
    simpa [signal,sign_mem,op,full,Active,value,bit,ids,gate,GateOp.eval,live] using
      law (live gs out j a (missing {x})) (live gs out j b (missing {x}))
  · have flag : tag gs i=false := by rw [←idx,tag_at,gate]; decide
    rw [flag]
    ext x
    simp [signal,sign_mem,op,full,Active,value,bit,ids,gate,GateOp.eval,live]


end Plane920.Forest26

namespace Plane920Four
open Plane920Depth Plane920Signs Plane920Ordered

abbrev available (xs : List Points) (s : Points) := allowed xs s

def Cover (xs : List Points) (k : Nat) := ∀ Q : Finset Points,
  (∀ q∈Q, available xs q ∧ q ≠ Finset.univ) → (Q.biUnion id).card ≤ Q.card+k

theorem base : Cover [] 0 := by
  intro Q ok
  calc
    _ ≤ ∑ q∈Q, (id q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q∈Q, 1 := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨a,ne⟩ := ok q hq
      have ha : atom q := by simpa [available,allowed] using a
      exact ha.resolve_left ne
    _ = _ := by simp

theorem extend {xs : List Points} {k : Nat} {a b : Points} (h : Cover xs k)
    (av : available xs a) (bv : available xs b) (tag : Bool) :
    Cover (op tag a b :: xs) (k + if tag then 1 else 0) := by
  classical
  let o := op tag a b
  intro Q ok
  have old (q : Points) (hq : q∈Q) (ne : q≠o) : available xs q ∧ q≠Finset.univ := by
    obtain ⟨known,small⟩ := ok q hq
    refine ⟨?_,small⟩
    rcases known with at0 | prior
    · exact Or.inl at0
    · exact Or.inr ((List.mem_cons.mp prior).resolve_left ne)
  by_cases eq : o∈Q
  · let R := Q.erase o
    have rold (q : Points) (hq : q∈R) : available xs q ∧ q≠Finset.univ :=
      old q (Finset.mem_erase.mp hq).2 (Finset.mem_erase.mp hq).1
    have rcard : R.card+1=Q.card := Finset.card_erase_add_one eq
    have osmall := (ok o eq).2
    have transfer (P : Finset Points)
        (pre : ∀ q∈P,available xs q ∧ q≠Finset.univ)
        (sub : o ⊆ P.biUnion id) :
        (Q.biUnion id).card ≤ R.card + P.card + k := by
      have inc : Q.biUnion id ⊆ (R∪P).biUnion id := by
        intro x hx
        obtain ⟨q,hq,xq⟩ := Finset.mem_biUnion.mp hx
        by_cases same : q=o
        · subst q
          obtain ⟨p,hp,xp⟩ := Finset.mem_biUnion.mp (sub xq)
          exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_union_right _ hp,xp⟩
        · exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨same,hq⟩),xq⟩
      have bound := h (R∪P) (by
        intro q hq
        exact (Finset.mem_union.mp hq).elim (rold q) (pre q))
      have upper := Finset.card_union_le R P
      exact (Finset.card_le_card inc).trans (by omega)
    cases tag with
    | false =>
      have singleton (c : Points) (hc : available xs c) (sm : c ≠ Finset.univ) (sub : o ⊆ c) :
          (Q.biUnion id).card ≤ Q.card+k := by
        have v := transfer {c} (by simpa using And.intro hc sm) (by simpa using sub)
        simp only [Finset.card_singleton] at v
        omega
      by_cases asmall : a = Finset.univ
      · have bs : b ≠ Finset.univ := by
          intro topb
          exact osmall (by simp [o,op,asmall,topb])
        simpa using singleton b bv bs Finset.inter_subset_right
      · simpa using singleton a av asmall Finset.inter_subset_left
    | true =>
      have sa : a ≠ Finset.univ := by
        intro same
        exact osmall (by simp [o,op,same])
      have sb : b ≠ Finset.univ := by
        intro same
        exact osmall (by simp [o,op,same])
      have v := transfer {a,b} (by
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl|hc
        · exact ⟨av,sa⟩
        · obtain rfl := Finset.mem_singleton.mp hc
          exact ⟨bv,sb⟩) (by simp [o,op])
      have pc := Finset.card_le_two (a:=a) (b:=b)
      simp only [ite_true]
      omega
  · have v := h Q (fun q hq => old q hq (fun same => eq (same ▸ hq)))
    omega

theorem advance {A B O : Nat → Points} {tag : Nat → Bool} {xs : List Nat}
    (oper : ∀ i∈xs,O i=op (tag i) (A i) (B i)) (prev : List Points) (k : Nat)
    (cover : Cover prev k) (v : Valid A B O prev xs) :
    Cover (xs.reverse.map O ++ prev) (k+(xs.filter tag).length) := by
  induction xs generalizing prev k with
  | nil => simpa using cover
  | cons i is ih =>
    obtain ⟨av,bv,_,vrest⟩ := v
    have next := extend cover av bv (tag i)
    rw [← oper i (by simp)] at next
    have rest := ih (fun j hj => oper j (by simp [hj])) (O i::prev) _ next vrest
    cases hi : tag i <;> simpa [List.reverse_cons,List.filter_cons,hi,Nat.add_assoc,
      Nat.add_left_comm,Nat.add_comm] using rest

theorem pair_size {xs : List Points} {k : Nat} {a b : Points} (cov : Cover xs k)
    (av : available xs a) (bv : available xs b) (sa : a≠Finset.univ) (sb : b≠Finset.univ) :
    (a \ b).card + (b \ a).card ≤ k+2 := by
  classical
  have h := cov {a,b} (by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl|hc
    · exact ⟨av,sa⟩
    · obtain rfl := Finset.mem_singleton.mp hc
      exact ⟨bv,sb⟩)
  have hc := Finset.card_le_two (a:=a) (b:=b)
  simp only [Finset.biUnion_insert, Finset.singleton_biUnion, id_eq] at h
  have dis : Disjoint (a \ b) (b \ a) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have inc : (a \ b) ∪ (b \ a) ⊆ a∪b := Finset.union_subset_union Finset.sdiff_subset Finset.sdiff_subset
  have u := Finset.card_le_card inc
  rw [Finset.card_union_of_disjoint dis] at u
  omega

def maxWeight (k : Nat) : Nat := (k+2)^2 / 4

theorem weight_bound {xs : List Points} {k : Nat} {a b : Points} (cov : Cover xs k)
    (av : available xs a) (bv : available xs b) : weight a b ≤ maxWeight k := by
  classical
  by_cases sa : a=Finset.univ
  · rw [sa,wflip,top]; exact Nat.zero_le _
  by_cases sb : b=Finset.univ
  · rw [sb,top]; exact Nat.zero_le _
  have ps := pair_size cov av bv sa sb
  let u := (a \ b).card
  let v := (b \ a).card
  change u+v≤k+2 at ps
  change u*v ≤ (k+2)^2/4
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  have squares : 4*u*v ≤ (u+v)^2 := by
    rcases le_total u v with a|b
    · have h1 : v = u+(v-u) := by omega
      generalize v-u=d at h1
      rw [h1]
      nlinarith
    · have h1 : u = v+(u-v) := by omega
      generalize u-v=d at h1
      rw [h1]
      nlinarith
  have upper := Nat.pow_le_pow_left ps 2
  calc
    u*v*4 = 4*u*v := by ac_rfl
    _ ≤ _ := squares
    _ ≤ _ := upper

theorem sum_weight (E : Finset Nat) (A B O : Nat → Points) (tag : Nat → Bool)
    (small : E.card≤4) (oper : ∀ i∈E,O i=op (tag i) (A i) (B i))
    (left : ∀ i∈E,Prior E O i (A i)) (right : ∀ i∈E,Prior E O i (B i)) :
    ∑ i∈E.filter (fun j => tag j=false), weight (A i) (B i) ≤ 8 := by
  classical
  let ls := E.sort (· ≤ ·)
  let pool := ls.reverse.map O
  let k := (ls.filter tag).length
  let F := E.filter (fun j => tag j=false)
  have sorted : ls.Pairwise (· < ·) := E.sortedLT_sort.pairwise
  have mem (i : Nat) : i∈ls ↔ i∈E := by simp [ls]
  have ok := well E A B O (fun i hi => ⟨tag i,oper i hi⟩) left right ls [] sorted
    (fun i hi => (mem i).mp hi) (by intro i hi; simp [mem i,hi])
  have full : Cover pool k := by
    simpa [pool,k] using advance (fun i hi => oper i ((mem i).mp hi)) [] 0 base ok
  have avail {i s} (prior : Prior E O i s) : available pool s := by
    rcases prior with a|⟨j,hj,_,rfl⟩
    · exact Or.inl a
    · exact Or.inr (List.mem_map_of_mem (by simpa using (mem j).mpr hj))
  have w (i : Nat) (hi : i∈F) : weight (A i) (B i) ≤ maxWeight k := by
    have he := (Finset.mem_filter.mp hi).1
    exact weight_bound full (avail (left i he)) (avail (right i he))
  have sum := Finset.sum_le_sum w
  change (∑i∈F,weight (A i) (B i))≤8
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at sum
  have ks : k = (E.filter (fun j => tag j=true)).card := by
    have nod : ls.Nodup := E.sort_nodup _
    have card := List.toFinset_card_of_nodup (nod.filter tag)
    rw [List.toFinset_filter] at card
    simpa [k,ls] using card.symm
  have count : F.card+k=E.card := by
    rw [ks]
    have h := Finset.card_filter_add_card_filter_not (s:=E) (p:=fun j => tag j=false)
    simpa [F] using h
  have ks4 : k≤4 := by omega
  have f4 : F.card≤4-k := by omega
  apply sum.trans
  refine (Nat.mul_le_mul_right _ f4).trans ?_
  interval_cases k <;> decide

end Plane920Four

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest

theorem separated_singleton {gs : List Gate} {out : V→Nat} {f : V→V} {c p : V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (fiber : block f c={p}) (ok : Separated gs out) :
    26≤gs.length := by
  by_contra! below
  have cap : gs.length≤25 := by omega
  let E := spare gs out p
  let A := leftSide gs out
  let B := rightSide gs out
  let O := signal gs out
  let t := tag gs
  have small := (eight basis arity h cap ok uni fiber).2
  have step (i : Nat) (mem : i∈E) := spare_step basis arity h ok mem
  have high := Plane920Four.sum_weight E A B O t small (fun i hi => (step i hi).1)
    (fun i hi => (step i hi).2.1) (fun i hi => (step i hi).2.2)
  have low : (outsiders p).card≤∑i∈E.filter (fun j=>t j=false), Plane920Signs.weight (A i) (B i) := by
    apply Plane920Ordered.lines_by_weight
    intro w hw
    obtain ⟨i,ei,x,xL,y,yL,xa,yb⟩ := transverse_mark basis arity h ok (Finset.mem_filter.mp hw).2
    exact ⟨i,ei,x,xa,y,yb,xL,yL⟩
  rw [nine] at low
  omega

theorem residual_defective {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (cap : gs.length≤25) :
    (colors f).card=1 ∨ ((colors f).card=2 ∧ (∃ c p : V, block f c={p}) ∧ (defects (terminals out) start gs).card=1) := by
  rcases residual basis arity h uni cap with single|⟨two,c,p,fiber⟩
  · exact Or.inl single
  refine Or.inr ⟨two,⟨c,p,fiber⟩,?_⟩
  have upper := at_most_one basis arity h cap
  by_contra! diff
  have zero := Finset.card_eq_zero.mp (show (defects (terminals out) start gs).card=0 by omega)
  have sep : Separated gs out := by
    intro j nf
    apply (defect_cases _ _ _ j (by simpa [start] using nf)).resolve_right
    simp [zero]
  have lo := separated_singleton basis arity h uni fiber sep
  omega
end Plane920.Forest26

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest
open Plane920Ordered Plane920Signs

def padded (gs : List Gate) (out : V→Nat) (i n : Nat) : Input→Bool :=
  match sides gs i with
  | [] => fun _=> tag gs i
  | [_] => source gs out i 0
  | _::_::_ => source gs out i n
def lsign (gs : List Gate) (out : V→Nat) (i : Nat) := sign (padded gs out i 0)
def rsign (gs : List Gate) (out : V→Nat) (i : Nat) := sign (padded gs out i 1)

theorem operands_list (gs : List Gate) (j : Fin gs.length) : sides gs (13+j.val)=gs[j.val].inputs := by
  have eq : 13+j.val-13=j.val := by omega
  simp only [sides,eq,List.getElem?_eq_getElem j.isLt,Option.map_some,Option.getD_some]
theorem padded_binary {gs : List Gate} {out : V→Nat} {i a b : Nat} (ids : sides gs i=[a,b]) :
    lsign gs out i=leftSide gs out i ∧ rsign gs out i=rightSide gs out i := by simp [lsign,rsign,padded,ids,leftSide,rightSide]
theorem idemp (b : Bool) (s : Region) : op b s s=s := by cases b <;> simp [op]
theorem atom_const (b : Bool) : atom (sign (fun _=>b)) := by cases b <;> simp [atom,sign]

theorem all_spare_step {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) {p : V} {i : Nat} (el : i∈spare gs out p) :
    signal gs out i=op (tag gs i) (lsign gs out i) (rsign gs out i) ∧
    Prior (spare gs out p) (signal gs out) i (lsign gs out i) ∧ Prior (spare gs out p) (signal gs out) i (rsign gs out i) := by
  classical
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp el).1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  have full : globalWire gs out i=value gs out j := idx ▸ stored_value j nf
  have atSide : sides gs i=gs[j.val].inputs := (congrArg (sides gs) idx.symm).trans (operands_list gs j)
  have opTag : tag gs i=disjoins gs[j.val].op := (congrArg (tag gs) idx.symm).trans (tag_at gs j)
  cases ids : gs[j.val].inputs with
  | nil =>
    have s : sides gs i=[] := atSide.trans ids
    have result : globalWire gs out i=fun _=>tag gs i := by
      rw [full,opTag]
      funext x
      rcases basis gs[j.val] (List.getElem_mem _) with gate|gate <;> simp [value,bit,ids,gate,disjoins,GateOp.eval]
    have atom := atom_const (tag gs i)
    simp only [signal,result,lsign,rsign,padded,s,idemp]
    exact ⟨True.intro,Or.inl atom,Or.inl atom⟩
  | cons a more =>
    cases more with
    | nil =>
      have s := atSide.trans ids
      have result : globalWire gs out i=source gs out i 0 := by
        rw [full];funext x
        rcases basis gs[j.val] (List.getElem_mem _) with gate|gate <;>
          simp [Forest.source,s,value,bit,ids,gate,GateOp.eval,j]
      have prior : Prior (spare gs out p) (signal gs out) i (sign (source gs out i 0)) := by
        have eq : source gs out i 0=live gs out j a := by funext; simp [Forest.source,s,live,j]
        rw [eq]
        exact idx ▸ sign_prior j a
      simp only [signal,result,lsign,rsign,padded,s,idemp]
      exact ⟨True.intro,prior,prior⟩
    | cons b rem =>
      cases rem with
      | cons x xs => have bound := arity gs[j.val] (List.getElem_mem j.isLt); simp [ids] at bound
      | nil =>
        have pure := padded_binary (out := out) (atSide.trans ids)
        rw [pure.1,pure.2]
        have lr := sides_at (out := out) j ids
        rw [idx] at lr
        have l : leftSide gs out i=sign (live gs out j a) := congrArg sign lr.1
        have r : rightSide gs out i=sign (live gs out j b) := congrArg sign lr.2
        rw [l,r]
        refine ⟨?_,idx ▸ sign_prior j a,idx ▸ sign_prior j b⟩
        rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
        · rw [opTag,gate];ext x
          have law (q r : Bool) : ((q && r)=false ↔ q=false ∨ r=false) := by cases q <;> cases r <;> decide
          simpa [signal,sign_mem,op,disjoins,full,Active,value,bit,ids,gate,GateOp.eval,live] using
            law (live gs out j a (missing {x})) (live gs out j b (missing {x}))
        · rw [opTag,gate];ext x
          simp [signal,sign_mem,op,disjoins,full,Active,value,bit,ids,gate,GateOp.eval,live]

theorem hard_binary {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (j : Fin gs.length) {L : Region} (pop : L.Nonempty)
    (hard : Hard (value gs out j) L) (each : ∀k, Active (live gs out j k) L→∃x∈L, Active (live gs out j k) {x}) :
    ∃a b, gs[j.val].inputs=[a,b] := by
  cases ids : gs[j.val].inputs with
  | nil =>
    obtain ⟨x,hx⟩ := pop
    apply False.elim (hard.2 x hx ?_)
    simpa [Active,value,bit,ids] using hard.1
  | cons a tail =>
    cases tail with
    | nil =>
      have same : value gs out j=live gs out j a := by
        funext x
        rcases basis gs[j.val] (List.getElem_mem _) with gate|gate <;> simp [value,bit,ids,gate,GateOp.eval,live]
      rw [same] at hard
      obtain ⟨x,hx,on⟩ := each a hard.1
      exact False.elim (hard.2 x hx on)
    | cons b t =>
      cases t with
      | nil => exact ⟨a,b,rfl⟩
      | cons k ks => have bound := arity gs[j.val] (List.getElem_mem j.isLt); simp [ids] at bound
end Plane920.Forest26

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest
open Plane920Ordered Plane920Signs
theorem padded_mark {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) {p w : V} (outside : p∉line w) :
    ∃ i∈(spare gs out p).filter (fun k=>tag gs k=false), ∃x∈line w, ∃y∈line w,
      x∈lsign gs out i \ rsign gs out i ∧ y∈rsign gs out i \ lsign gs out i := by
  classical
  let L := line w
  let P (k : Nat) := k∈paid (terminals out) 13 gs.length ∧ Hard (globalWire gs out k) L
  have init : ∃k, P k := hard_exists basis arity h w
  let i := Nat.find init
  have now : P i := Nat.find_spec init
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp now.1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  have same : globalWire gs out i = value gs out j := idx ▸ stored_value j nf
  have hard := now.2
  rw [same] at hard
  have pop : L.Nonempty := Finset.card_pos.mp (by change 0<(line w).card; rw [line_size]; decide)
  have each (k : Nat) (on : Active (live gs out j k) L) : ∃x∈L, Active (live gs out j k) {x} := by
    by_contra! none
    obtain ⟨earlier,inPaid,data⟩ := hard_hidden pop ⟨on,none⟩
    have lower : i≤k := Nat.find_min' init (show P k from ⟨inPaid,data⟩)
    omega
  obtain ⟨a,b,ids⟩ := hard_binary basis arity j pop hard each
  let F := live gs out j a
  let G := live gs out j b
  have bin := padded_binary (out := out) ((congrArg (sides gs) idx.symm).trans ((operands_list gs j).trans ids))
  rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
  · have any (s : Region) : Active (value gs out j) s ↔ Active F s ∨ Active G s := by
      have logic (q r : Bool) : (q && r)=false ↔ q=false ∨ r=false := by cases q <;> cases r <;> decide
      simpa [F,G,value,bit,ids,gate,GateOp.eval,Active,live] using logic (F (missing s)) (G (missing s))
    rcases (any L).mp hard.1 with A|B
    · obtain ⟨x,inL,yes⟩ := each a A
      exact False.elim (hard.2 x inL ((any _).mpr (Or.inl yes)))
    · obtain ⟨x,inL,yes⟩ := each b B
      exact False.elim (hard.2 x inL ((any _).mpr (Or.inr yes)))
  · have both (s : Region) : Active (value gs out j) s ↔ Active F s ∧ Active G s := by
      simp [F,G,value,bit,ids,gate,GateOp.eval,Active,live]
    obtain ⟨af,bg⟩ := (both L).mp hard.1
    obtain ⟨x,xL,xA⟩ := each a af
    obtain ⟨y,yL,yB⟩ := each b bg
    have nx : ¬Active G {x} := fun bad => hard.2 x xL ((both _).mpr ⟨xA,bad⟩)
    have ny : ¬Active F {y} := fun bad => hard.2 y yL ((both _).mpr ⟨bad,yB⟩)
    have pair : Active (globalWire gs out i) {x,y} := by
      rw [same]
      apply (both _).mpr
      exact ⟨grow_live basis _ _ _ (by simp) xA,grow_live basis _ _ _ (by simp) yB⟩
    have free : i∉locked gs out p := fun held => locked_off held outside (Finset.insert_subset xL (Finset.singleton_subset_iff.mpr yL))
      (Finset.card_insert_le _ _ |>.trans (by simp)) pair
    have lr := sides_at (out := out) j ids
    rw [idx] at lr
    have l : leftSide gs out i=sign F := congrArg sign lr.1
    have r : rightSide gs out i=sign G := congrArg sign lr.2
    have mark : tag gs i=false := by rw [←idx,tag_at,gate]; decide
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨now.1,free⟩,mark⟩,x,xL,y,yL,?_⟩
    rw [bin.1,bin.2,l,r]
    exact ⟨Finset.mem_sdiff.mpr ⟨sign_mem.mpr xA,fun v=>nx (sign_mem.mp v)⟩,
      Finset.mem_sdiff.mpr ⟨sign_mem.mpr yB,fun v=>ny (sign_mem.mp v)⟩⟩


end Plane920.Forest26

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest

theorem genuine {gs : List Gate} {out : V→Nat} {T : Region} {i : Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2)
    (m : Earliest gs out i T) (size : 2≤T.card) :
    ∃ (j : Fin gs.length) (a b : Nat), 13+j.val=i ∧ gs[j.val].op=.or ∧ gs[j.val].inputs=[a,b] ∧
      (region gs out j a).Nonempty ∧ (region gs out j b).Nonempty := by
  obtain ⟨bounds,nz⟩ := Finset.mem_sdiff.mp m.1.1
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
  let j : Fin gs.length := ⟨i-13,by omega⟩
  have idx : 13+j.val=i := by change 13+(i-13)=i; omega
  have nf : 13+j.val∉terminals out := idx ▸ nz
  have same : globalWire gs out i=value gs out j := idx ▸ stored_value j nf
  have orig := m.1.2
  rw [same] at orig
  have early (k : Nat) (data : Minimal (live gs out j k) T) : False := by
    have lo := m.2 k (hidden j k data size)
    have hi := live_before j k data size
    omega
  cases ids : gs[j.val].inputs with
  | nil =>
    have empty : Active (value gs out j) ∅ := by simpa [value,Active,bit,ids] using orig.1
    have eq := orig.2 ∅ empty (by simp)
    rw [←eq] at size
    simp at size
  | cons a tail =>
    cases tail with
    | nil =>
      have copy : value gs out j=live gs out j a := by
        funext x
        rcases basis gs[j.val] (List.getElem_mem _) with gate|gate <;> simp [value,bit,ids,gate,GateOp.eval,live]
      rw [copy] at orig
      exact False.elim (early a orig)
    | cons b rest =>
      cases rest with
      | cons x xs => have bound := arity gs[j.val] (List.getElem_mem j.isLt); simp [ids] at bound
      | nil =>
        rcases basis gs[j.val] (List.getElem_mem _) with gate|gate
        · have any (s : Region) : Active (value gs out j) s ↔ Active (live gs out j a) s ∨ Active (live gs out j b) s := by
            have logic (q r : Bool) : (q && r)=false ↔ q=false ∨ r=false := by cases q <;> cases r <;> decide
            simpa [value,bit,ids,gate,GateOp.eval,Active,live] using logic (live gs out j a (missing s)) (live gs out j b (missing s))
          rcases (any T).mp orig.1 with A|B
          · exact False.elim (early a ⟨A,fun X on sm=>orig.2 X ((any X).mpr (Or.inl on)) sm⟩)
          · exact False.elim (early b ⟨B,fun X on sm=>orig.2 X ((any X).mpr (Or.inr on)) sm⟩)
        · have both (s : Region) : Active (value gs out j) s ↔ Active (live gs out j a) s ∧ Active (live gs out j b) s := by
            simp [value,bit,ids,gate,GateOp.eval,Active,live]
          have raw := (both T).mp orig.1
          have always (u : Nat) (empty : ¬(region gs out j u).Nonempty) (yes : Active (live gs out j u) T) :
              ∀s, Active (live gs out j u) s := by
            intro s
            have eq : region gs out j u=∅ := Finset.not_nonempty_iff_eq_empty.mp empty
            exact (live_local gs out j u _ _ (by rw [eq]; intro x impossible; simp at impossible)).trans yes
          refine ⟨j,a,b,idx,gate,ids,?_,?_⟩
          · by_contra bad
            exact early b ⟨raw.2,fun X x small => orig.2 X ((both X).mpr ⟨always a bad raw.1 X,x⟩) small⟩
          · by_contra bad
            exact early a ⟨raw.1,fun X x small => orig.2 X ((both X).mpr ⟨x,always b bad raw.2 X⟩) small⟩

theorem typed {gs : List Gate} {out : V→Nat} {T : Region} {i : Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2)
    (m : Earliest gs out i T) (size : 2≤T.card) : Conjunction gs i := by
  obtain ⟨j,_,_,idx,op,_⟩ := genuine basis arity m size
  exact ⟨j,idx,op⟩

theorem nondefect_pair {gs : List Gate} {out : V→Nat} {T : Region} {i : Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2)
    (m : Earliest gs out i T) (three : T.card=3) (free : i∉defects (terminals out) start gs) :
    ∃ U⊆T, U.card=2 ∧ ∃k, Own gs out k U ∧ Conjunction gs k := by
  obtain ⟨j,a,b,idx,gate,ids,_,_⟩ := genuine basis arity m (by omega)
  have nz := (Finset.mem_sdiff.mp m.1.1).2
  have nf : 13+j.val∉terminals out := idx ▸ nz
  have split := (defect_cases (terminals out) start gs j (by simpa [start] using nf)).resolve_right
    (by simpa only [show start.length=13 from by simp [start],idx] using free)
  obtain ⟨c,d,cd,_,_,sep0⟩ := split
  rw [ids,List.cons.injEq,List.cons.injEq] at cd
  obtain ⟨rfl,rfl,_⟩ := cd
  let u := region gs out j a
  let v := region gs out j b
  have sep : Disjoint u v := sep0
  have eq : globalWire gs out i=value gs out j := idx ▸ stored_value j nf
  have orig := m.1.2
  rw [eq] at orig
  have both (s : Region) : Active (value gs out j) s ↔ Active (live gs out j a) s ∧ Active (live gs out j b) s := by
    simp [Active,value,bit,ids,gate,GateOp.eval,live]
  have af : Local (live gs out j a) u := live_local gs out j a
  have bf : Local (live gs out j b) v := live_local gs out j b
  have left := project_piece af bf sep orig both
  have right := project_piece bf af sep.symm orig (fun s => (both s).trans and_comm)
  have union := exact_union af bf sep orig both
  have disT : Disjoint (T∩u) (T∩v) := sep.mono Finset.inter_subset_right Finset.inter_subset_right
  have total : (T∩u).card+(T∩v).card=3 := by
    rw [←Finset.card_union_of_disjoint disT,union,three]
  have smaller {k : Nat} {s : Region} (leg : Minimal (live gs out j k) (T∩s)) : (T∩s).card<3 := by
    by_contra! large
    have same := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (show T.card≤(T∩s).card by omega)
    rw [same] at leg
    have hi := live_before j k leg (by omega)
    have lo := m.2 k (hidden j k leg (by omega))
    omega
  have lo := smaller left
  have hi := smaller right
  have finish {k : Nat} {s : Region} (leg : Minimal (live gs out j k) (T∩s)) (size : (T∩s).card=2) :
      ∃ U⊆T, U.card=2 ∧ ∃k, Own gs out k U ∧ Conjunction gs k := by
    have sig := hidden j k leg size.ge
    obtain ⟨z,first⟩ := first (show ∃z, Own gs out z (T∩s) from ⟨k,sig⟩)
    exact ⟨_,Finset.inter_subset_left,size,z,first.1,typed basis arity first size.ge⟩
  by_cases pair : (T∩u).card=2
  · exact finish left pair
  · exact finish right (by omega)
end Plane920.Forest26

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest

theorem five_spare {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (p : V) : 5≤(spare gs out p).card := by
  by_contra! few
  let E := spare gs out p
  let A := lsign gs out
  let B := rsign gs out
  let O := signal gs out
  let t := tag gs
  have step (i : Nat) (mem : i∈E) := all_spare_step basis arity mem
  have small : E.card≤4 := by change (spare gs out p).card≤4; omega
  have upper := Plane920Four.sum_weight E A B O t small (fun i hi => (step i hi).1)
    (fun i hi => (step i hi).2.1) (fun i hi => (step i hi).2.2)
  have lower : (outsiders p).card≤∑i∈E.filter (fun j=>t j=false), Plane920Signs.weight (A i) (B i) := by
    apply Plane920Ordered.lines_by_weight
    intro w hw
    obtain ⟨i,ei,x,xL,y,yL,xa,yb⟩ := padded_mark basis arity h (Finset.mem_filter.mp hw).2
    exact ⟨i,ei,x,xa,y,yb,xL,yL⟩
  rw [nine] at lower
  omega

theorem pencil_root {gs : List Gate} {out : V→Nat} {f : V→V} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (uni : Uniform f (start++supportTail (terminals out) start gs))
    {c p : V} (fiber : block f c={p}) (w : V) (on : w∈pencil p) :
    ∃i, Earliest gs out i ((line w).erase p) := by
  obtain ⟨T,sub,num,i,own⟩ := singleton_triple basis arity h uni fiber (Finset.mem_filter.mp on).2
  let xs := start++supportTail (terminals out) start gs
  have hom : Hom f (support (terminals out) gs i) := available_hom uni (readable xs i)
  have included := minimum_support (glob_local gs out i) own.2
  have no : p∉T := by
    intro pt
    have cp : p∈block f c := by simp [fiber]
    have all : T⊆{p} := by
      intro x hx
      rw [←fiber]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hom x (included hx) p (included pt)).trans (Finset.mem_filter.mp cp).2⟩
    have small := Finset.card_le_card all
    rw [Finset.card_singleton,num] at small
    omega
  have inside : T⊆(line w).erase p := fun x hx=>Finset.mem_erase.mpr ⟨fun e=>no (e ▸ hx),sub hx⟩
  have eq := Finset.eq_of_subset_of_card_le inside (by rw [Finset.card_erase_of_mem (Finset.mem_filter.mp on).2,line_size,num])
  exact first ⟨i,eq ▸ own⟩

theorem protected_count {gs : List Gate} {out : V→Nat} (p : V) :
    (locked gs out p).card=∑w∈pencil p,(protectedAt gs out w).card := by
  classical
  apply Finset.card_biUnion
  intro w _ t _ ne
  apply Finset.disjoint_left.mpr
  intro i hi hk
  obtain ⟨T,big,sub,m⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  obtain ⟨U,_,other,n⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  have eq := minima_eq m n
  have cap := (Finset.card_le_card (Finset.subset_inter sub (show T⊆line t from eq ▸ other))).trans (OrSupport.line_pair w t ne)
  omega

theorem counts_at {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) {w p : V} (inW : w∈pencil p) {i : Nat}
    (m : Earliest gs out i ((line w).erase p)) :
    1≤(protectedAt gs out w).card ∧ (i∉defects (terminals out) start gs → 2≤(protectedAt gs out w).card) := by
  classical
  let T := (line w).erase p
  have three : T.card=3 := by rw [show T=(line w).erase p from rfl,Finset.card_erase_of_mem (Finset.mem_filter.mp inW).2,line_size]
  have keep {j : Nat} {U : Region} (big : 2≤U.card) (sub : U⊆line w) (data : Own gs out j U) (op : Conjunction gs j) :
      j∈protectedAt gs out w := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨data.1,U,big,sub,data.2⟩,op⟩
  have inT : T⊆line w := Finset.erase_subset _ _
  have root := keep (U := T) (by omega) inT m.1 (typed basis arity m (by change 2≤T.card; omega))
  refine ⟨Finset.card_pos.mpr ⟨i,root⟩,?_⟩
  intro good
  obtain ⟨U,sub,small,j,data,op⟩ := nondefect_pair basis arity m three good
  have ne : i≠j := by
    rintro rfl
    have eq := minima_eq m.1.2 data.2
    change T=U at eq
    rw [eq,small] at three
    exact (by decide : (2:Nat)≠3) three
  exact Finset.one_lt_card.mpr ⟨i,root,j,keep small.ge (sub.trans inT) data op,ne⟩

theorem defective_root {gs : List Gate} {out : V→Nat} {f : V→V} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (uni : Uniform f (start++supportTail (terminals out) start gs))
    (cap : gs.length≤25) {c p : V} (fiber : block f c={p}) :
    ∃w∈pencil p, ∃i∈defects (terminals out) start gs, Earliest gs out i ((line w).erase p) := by
  classical
  by_contra no
  have each (w : V) (on : w∈pencil p) : 2≤(protectedAt gs out w).card := by
    obtain ⟨i,root⟩ := pencil_root basis arity h uni fiber w on
    exact (counts_at basis arity on root).2 (fun bad => no ⟨w,on,i,bad,root⟩)
  have four : (pencil p).card=4 := incidences p
  have lo : 8≤(locked gs out p).card := by
    rw [protected_count]
    simpa [four] using Finset.sum_le_sum each
  have remaining := five_spare basis arity h p
  rw [spare,Finset.card_sdiff_of_subset (locked_paid _ _ _),hidden_count h] at remaining
  omega
end Plane920.Forest26

namespace Plane920.Forest26
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Parse Plane920.Terminal Plane920.Cut Plane920.Forest

theorem member_fails (z : Finset Nat) (xs : List SetV) (gs : List Gate) (j : Fin gs.length)
    (mem : xs.length+j.val∈defects z xs gs) : ¬Splits (xs++supportTail z xs (gs.take j.val)) gs[j.val].inputs := by
  classical
  induction gs generalizing xs with
  | nil => exact Fin.elim0 j
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    cases j using Fin.cases with
    | zero =>
      have noMore : xs.length∉defects z (xs++[s]) gs := by
        intro yes
        have impossible := defect_range _ _ _ yes
        simp at impossible
      rw [defects] at mem
      change xs.length+0∈(if xs.length∉z ∧ ¬Splits xs g.inputs then insert xs.length (defects z (xs++[s]) gs)
        else defects z (xs++[s]) gs) at mem
      by_cases bad : xs.length∉z ∧ ¬Splits xs g.inputs
      · simpa [supportTail] using bad.2
      · simp [bad,noMore] at mem
    | succ j =>
      have ne : xs.length+j.succ.val≠xs.length := by simp [Fin.val_succ]
      have same : (xs++[s]).length+j.val=xs.length+j.succ.val := by simp; omega
      have tail : xs.length+j.succ.val∈defects z (xs++[s]) gs := by
        rw [defects] at mem
        split at mem
        · exact (Finset.mem_insert.mp mem).resolve_left ne
        · exact mem
      have res := ih (xs++[s]) j (same ▸ tail)
      simpa only [Fin.val_succ,List.take_succ_cons,supportTail,List.append_assoc,List.singleton_append,List.getElem_cons_succ,s] using res

theorem exact_singleton {gs : List Gate} {out : V→Nat} {f : V→V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (uni : Uniform f (start++supportTail (terminals out) start gs)) (cap : gs.length≤25) {c p : V} (fiber : block f c={p}) :
    (locked gs out p).card=7 ∧ (spare gs out p).card=5 ∧
    ∃ (w : V) (j : Fin gs.length) (a b : Nat), p∈line w ∧
      defects (terminals out) start gs={13+j.val} ∧ Earliest gs out (13+j.val) ((line w).erase p) ∧
      gs[j.val].op=.or ∧ gs[j.val].inputs=[a,b] ∧ (region gs out j a∩region gs out j b).Nonempty := by
  classical
  let D := defects (terminals out) start gs
  obtain ⟨w,on,i,bad,root⟩ := defective_root basis arity h uni cap fiber
  have all : D={i} := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      exact Finset.mem_singleton.mpr (Finset.card_le_one.mp (at_most_one basis arity h cap) _ hk _ bad)
    · simp; exact ⟨i,bad⟩
  let P := pencil p
  let sz (t : V) := (protectedAt gs out t).card
  have many (t : V) (other : t∈P.erase w) : 2≤sz t := by
    obtain ⟨nw,mem⟩ := Finset.mem_erase.mp other
    obtain ⟨k,earliest⟩ := pencil_root basis arity h uni fiber t mem
    apply (counts_at basis arity mem earliest).2
    intro faulty
    have same : k=i := Finset.mem_singleton.mp (all ▸ (show k∈D from faulty))
    rw [same] at earliest
    have eq := minima_eq earliest.1.2 root.1.2
    have over := Finset.card_le_card (Finset.subset_inter (Finset.erase_subset _ _) (show (line t).erase p⊆line w from eq ▸ Finset.erase_subset _ _))
    have one := OrSupport.line_pair t w nw
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mp mem).2,line_size] at over
    omega
  have remain : (P.erase w).card=3 := by rw [Finset.card_erase_of_mem on,show P.card=4 from incidences p]
  have six : 6≤∑t∈P.erase w,sz t := by simpa [remain] using Finset.sum_le_sum many
  have one := (counts_at basis arity on root).1
  change 1≤sz w at one
  have sum := Finset.sum_erase_add P sz on
  have lockedEq : (locked gs out p).card=∑t∈P,sz t := protected_count p
  have spareEq : (spare gs out p).card=gs.length-13-(locked gs out p).card := by
    rw [spare,Finset.card_sdiff_of_subset (locked_paid _ _ _),hidden_count h]
  have at5 := five_spare basis arity h p
  refine ⟨by omega,by omega,?_⟩
  have three : ((line w).erase p).card=3 := by rw [Finset.card_erase_of_mem (Finset.mem_filter.mp on).2,line_size]
  obtain ⟨j,a,b,idx,gate,ids,av,bv⟩ := genuine basis arity root (by omega)
  have overlap : ¬Disjoint (region gs out j a) (region gs out j b) := by
    intro dis
    have atJ : start.length+j.val∈defects (terminals out) start gs := by simpa only [show start.length=13 from by simp [start],idx] using bad
    exact member_fails _ _ _ j atJ ⟨a,b,ids,av,bv,dis⟩
  obtain ⟨x,xa,xb⟩ := Finset.not_disjoint_iff.mp overlap
  exact ⟨w,j,a,b,(Finset.mem_filter.mp on).2,idx ▸ all,idx ▸ root,gate,ids,x,Finset.mem_inter.mpr ⟨xa,xb⟩⟩
end Plane920.Forest26

namespace Plane920.Component
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal

def joinsComponents (xs : List SetV) (ins : List Nat) : Prop := ∃f : V→V, Uniform f xs ∧ ¬Hom f (gather xs ins)
def Connected (gs : List Gate) (out : V→Nat) := ∀f : V→V, Uniform f (start++supportTail (terminals out) start gs) → (colors f).card=1

noncomputable def redundantCount (z : Finset Nat) (xs : List SetV) : List Gate → Nat := by
  classical
  exact fun gs => match gs with
    | [] => 0
    | g::rest =>
      let s := if xs.length∈z then ∅ else gather xs g.inputs
      (if xs.length∉z ∧ ¬joinsComponents xs g.inputs then 1 else 0) + redundantCount z (xs++[s]) rest
termination_by gs => gs.length

theorem refined (gs : List Gate) (arity : ∀g∈gs,g.inputs.length≤2) (z : Finset Nat)
    (xs : List SetV) (f : V→V) (root : Uniform f xs) :
    ∃ k : V→V, Uniform k (xs++supportTail z xs gs) ∧
      (colors f).card+redundantCount z xs gs ≤ (colors k).card+(paid z xs.length gs.length).card := by
  classical
  induction gs generalizing xs f with
  | nil => exact ⟨f,by simpa [supportTail] using root,by simp [redundantCount,paid]⟩
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    let w : Nat := if xs.length∉z ∧ ¬joinsComponents xs g.inputs then 1 else 0
    have same (hs : Hom f s) : Uniform f (xs++[s]) := by
      intro t ht
      rcases List.mem_append.mp ht with before|added
      · exact root t before
      · exact List.mem_singleton.mp added ▸ hs
    have step : ∃ k : V→V, Uniform k (xs++[s]) ∧
        (colors f).card+w ≤ (colors k).card+(if xs.length∈z then 0 else 1) := by
      by_cases held : xs.length∈z
      · exact ⟨f,same (by simpa [s,held] using empty_hom f),by simp [w,held]⟩
      · by_cases split : joinsComponents xs g.inputs
        · obtain ⟨u,v,hu,hv,eq⟩ := binary xs g.inputs (arity _ (by simp))
          simpa [s,w,held,split,eq] using merge root hu hv
        · exact ⟨f,same (by simp only [s,ite_eq_right held]; by_contra no; exact split ⟨f,root,no⟩),by simp [w,held,split]⟩
    obtain ⟨k,uniform,stepCost⟩ := step
    obtain ⟨q,final,endCost⟩ := ih (fun t mem=>arity t (by simp [mem])) (xs++[s]) k uniform
    refine ⟨q,by simpa only [supportTail,List.append_assoc,List.singleton_append,s] using final,?_⟩
    have expr : redundantCount z xs (g::gs)=w+redundantCount z (xs++[s]) gs := by rw [redundantCount]
    rw [expr,List.length_cons,paid_step]
    simp only [List.length_append,List.length_singleton] at endCost
    omega


noncomputable def redundantWires (z : Finset Nat) (xs : List SetV) : List Gate → Finset Nat := by
  classical
  exact fun gs => match gs with
    | [] => ∅
    | g::rest =>
      let s := if xs.length∈z then ∅ else gather xs g.inputs
      let more := redundantWires z (xs++[s]) rest
      if xs.length∉z ∧ ¬joinsComponents xs g.inputs then insert xs.length more else more
termination_by gs => gs.length

theorem redundant_range (z : Finset Nat) (xs : List SetV) (gs : List Gate) {k : Nat} (mem : k∈redundantWires z xs gs) :
    xs.length≤k := by
  classical
  induction gs generalizing xs with
  | nil => simp [redundantWires] at mem
  | cons g gs ih =>
    rw [redundantWires] at mem
    split at mem
    · rcases Finset.mem_insert.mp mem with eq|m
      · omega
      · have lo := ih _ m
        simp only [List.length_append,List.length_singleton] at lo
        omega
    · have lo := ih _ mem
      simp only [List.length_append,List.length_singleton] at lo
      omega

theorem redundant_card (z : Finset Nat) (xs : List SetV) (gs : List Gate) :
    (redundantWires z xs gs).card=redundantCount z xs gs := by
  classical
  induction gs generalizing xs with
  | nil => simp [redundantCount,redundantWires]
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    have fresh : xs.length∉redundantWires z (xs++[s]) gs := by
      intro yes
      have low := redundant_range _ _ _ yes
      simp [s] at low
    rw [redundantWires,redundantCount]
    change (if xs.length∉z ∧ ¬joinsComponents xs g.inputs then insert xs.length (redundantWires z (xs++[s]) gs)
      else redundantWires z (xs++[s]) gs).card = _ + redundantCount z (xs++[s]) gs
    split <;> simp [*,Nat.add_comm]

theorem redundant_cases (z : Finset Nat) (xs : List SetV) (gs : List Gate)
    (j : Fin gs.length) (nz : xs.length+j.val∉z) :
    joinsComponents (xs++supportTail z xs (gs.take j.val)) gs[j.val].inputs ∨ xs.length+j.val∈redundantWires z xs gs := by
  classical
  induction gs generalizing xs with
  | nil => exact Fin.elim0 j
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    cases j using Fin.cases with
    | zero =>
      by_cases yes : joinsComponents xs g.inputs
      · exact Or.inl (by simpa [supportTail] using yes)
      · have no : xs.length∉z := by simpa using nz
        right
        simp [redundantWires,no,yes]
    | succ j =>
      have eq : (xs++[s]).length+j.val=xs.length+j.succ.val := by simp; omega
      have free : (xs++[s]).length+j.val∉z := eq ▸ nz
      rcases ih (xs++[s]) j free with y|n
      · left
        simpa only [Fin.val_succ,List.take_succ_cons,supportTail,List.append_assoc,List.singleton_append,
          List.getElem_cons_succ,s] using y
      · right
        rw [redundantWires]
        rw [eq] at n
        split
        · exact Finset.mem_insert_of_mem n
        · exact n

theorem at_most_one {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (limit : gs.length≤25) : (redundantWires (terminals out) start gs).card≤1 := by
  rw [redundant_card]
  have initial : Uniform id start := by
    intro s mem
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro i hi j hj
    change i=j
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  obtain ⟨f,uni,cost⟩ := refined gs arity (terminals out) start id initial
  have n : (colors (id : V→V)).card=13 := by decide
  have len : start.length=13 := by simp [start]
  rw [n,len,hidden_count h] at cost
  by_contra! many
  have three : 3≤(colors f).card := by omega
  have lo := three_implies_twenty_six basis arity h uni three
  omega

end Plane920.Component

namespace Plane920.Component
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal

theorem overlap_is_redundant (z : Finset Nat) (xs : List SetV) (gs : List Gate)
    (arity : ∀g∈gs,g.inputs.length≤2) :
    Forest26.defects z xs gs⊆redundantWires z xs gs := by
  classical
  induction gs generalizing xs with
  | nil => simp [Forest26.defects,redundantWires]
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    let A := Forest26.defects z (xs++[s]) gs
    let B := redundantWires z (xs++[s]) gs
    have lower : A⊆B := ih (xs++[s]) (fun t mem=>arity t (by simp [mem]))
    have weaken (failure : ¬Forest.Splits xs g.inputs) : ¬joinsComponents xs g.inputs := by
      rintro ⟨f,uni,not⟩
      exact not (Forest.no_split uni (arity _ (by simp)) failure)
    rw [Forest26.defects,redundantWires]
    change (if xs.length∉z ∧ ¬Forest.Splits xs g.inputs then insert xs.length A else A) ⊆
      (if xs.length∉z ∧ ¬joinsComponents xs g.inputs then insert xs.length B else B)
    by_cases weak : xs.length∉z ∧ ¬Forest.Splits xs g.inputs
    · have strong : xs.length∉z ∧ ¬joinsComponents xs g.inputs := ⟨weak.1,weaken weak.2⟩
      simp only [ite_eq_left weak,ite_eq_left strong]
      exact Finset.insert_subset_insert _ lower
    · simp only [ite_eq_right weak]
      split
      · exact lower.trans (Finset.subset_insert _ _)
      · exact lower

theorem connected_redundant_empty {gs : List Gate} {out : V→Nat}
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (connected : Connected gs out)
    (cap : gs.length≤25) : redundantWires (terminals out) start gs=∅ := by
  apply Finset.card_eq_zero.mp
  rw [redundant_card]
  have initial : Uniform id start := by
    intro s mem
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro i hi j hj
    change i=j
    exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm
  obtain ⟨f,uni,cost⟩ := refined gs arity (terminals out) start id initial
  have n : (colors (id : V→V)).card=13 := by decide
  have len : start.length=13 := by simp [start]
  rw [n,len,connected f uni,hidden_count h] at cost
  omega

theorem joins_of_not_redundant {gs : List Gate} {out : V→Nat} (j : Fin gs.length) (free : 13+j.val∉terminals out)
    (needed : 13+j.val∉redundantWires (terminals out) start gs) :
    joinsComponents (start++supportTail (terminals out) start (gs.take j.val)) gs[j.val].inputs := by
  have len : start.length=13 := by simp [start]
  exact (redundant_cases _ _ _ j (by simpa only [len] using free)).resolve_right (by simpa only [len] using needed)

theorem tree_or_single_cycle {gs : List Gate} {out : V→Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (cap : gs.length≤25) :
    (Connected gs out ∧ redundantWires (terminals out) start gs=∅) ∨
    ∃ (f : V→V) (c p w : V) (j : Fin gs.length) (a b : Nat),
      Uniform f (start++supportTail (terminals out) start gs) ∧ (colors f).card=2 ∧ Cut.block f c={p} ∧
      (Forest.locked gs out p).card=7 ∧ (Forest.spare gs out p).card=5 ∧ p∈line w ∧
      redundantWires (terminals out) start gs={13+j.val} ∧ Forest.Earliest gs out (13+j.val) ((line w).erase p) ∧
      gs[j.val].op=.or ∧ gs[j.val].inputs=[a,b] ∧ (region gs out j a∩region gs out j b).Nonempty := by
  classical
  by_cases connected : Connected gs out
  · exact Or.inl ⟨connected,connected_redundant_empty arity h connected cap⟩
  · unfold Connected at connected
    push Not at connected
    obtain ⟨f,uni,nontrivial⟩ := connected
    obtain ⟨two,c,p,fiber⟩ := (Forest26.residual basis arity h uni cap).resolve_left nontrivial
    obtain ⟨seven,five,w,j,a,b,on,bad,first,gate,ids,common⟩ := Forest26.exact_singleton basis arity h uni cap fiber
    have seen : 13+j.val∈redundantWires (terminals out) start gs := overlap_is_redundant _ _ _ arity
      (by rw [bad];exact Finset.mem_singleton_self _)
    have only : redundantWires (terminals out) start gs={13+j.val} := by
      apply Finset.eq_of_subset_of_card_le
      · intro k hk
        exact Finset.mem_singleton.mpr (Finset.card_le_one.mp (at_most_one basis arity h cap) _ hk _ seen)
      · simp;exact ⟨_,seen⟩
    exact Or.inr ⟨f,c,p,w,j,a,b,uni,two,fiber,seven,five,on,only,first,gate,ids,common⟩
end Plane920.Component

namespace Plane920.Bypass
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.Terminal

def shift (r i : Nat) := if r < i then i-1 else i
def redirect (r q i : Nat) := if i=r then q else shift r i
def changeGate (r q : Nat) (g : Gate) : Gate := {g with inputs := g.inputs.map (redirect r q)}
def suffix (r : Nat) (pick : Nat→Nat) (next : Nat) : List Gate→List Gate
  | [] => []
  | g::gs => changeGate r (pick next) g :: suffix r pick (next+1) gs

theorem suffix_len (r : Nat) (pick : Nat→Nat) (next : Nat) (gs : List Gate) : (suffix r pick next gs).length=gs.length := by
  induction gs generalizing next with
  | nil => rfl
  | cons g gs ih => simp [suffix,ih]

theorem suffix_spec (r : Nat) (pick : Nat→Nat) (next : Nat) (gs : List Gate) (P : Gate→Prop)
    (stable : ∀g q, P g → P (changeGate r q g)) (valid : ∀g∈gs, P g) :
    ∀g∈suffix r pick next gs,P g := by
  induction gs generalizing next with
  | nil => simp [suffix]
  | cons g gs ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl|later
    · exact stable _ _ (valid _ (by simp))
    · exact ih _ (fun t ht=>valid _ (by simp [ht])) _ later

def Tracked (strict : Prop) (a b : Bool) := Nine.R a b ∧ (strict→a=b)
def State (strict : Prop) (r : Nat) (xs ys : List Bool) := ∀i, i≠r → Tracked strict (xs.getD i false) (ys.getD (shift r i) false)

theorem shift_last (r n : Nat) (prior : r<n+1) : shift r (n+1)=n := by simp [shift,prior]
theorem raise (r : Nat) (xs ys : List Bool) (x y : Bool) (shape : xs.length=ys.length+1) (prior : r<xs.length)
    {strict : Prop} (state : State strict r xs ys) (new : Tracked strict x y) : State strict r (xs++[x]) (ys++[y]) := by
  intro i ne
  rw [read_append,read_append]
  by_cases atI : i=xs.length
  · have spot : shift r i=ys.length := by rw [atI,shape,shift_last]; omega
    simpa only [ite_eq_left atI,ite_eq_left spot] using new
  · have away : shift r i≠ys.length := by unfold shift;split <;> omega
    simpa only [ite_eq_right atI,ite_eq_right away] using state i ne

theorem monotone (ins : List Nat) (f g : Nat→Bool) (h : ∀i, Nine.R (f i) (g i)) :
    Nine.R ((ins.map f).all id) ((ins.map g).all id) ∧ Nine.R ((ins.map f).any id) ((ins.map g).any id) := by
  induction ins with
  | nil => exact ⟨id,id⟩
  | cons i rest ih =>
    simp only [List.map_cons,List.all_cons,List.any_cons,id_eq,Nine.R,Bool.and_eq_true,Bool.or_eq_true]
    exact ⟨fun v=>⟨h i v.1,ih.1 v.2⟩,fun v=>v.imp (h i) ih.2⟩

theorem simulate (r focus : Nat) (strict : Prop) (pick : Nat→Nat) (gs : List Gate)
    (xs ys : List Bool) (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (shape : xs.length=ys.length+1) (past : r<xs.length) (state : State strict r xs ys)
    (choice : ∀n, pick n<r ∧ Nine.R (xs.getD r false) (ys.getD (pick n) false) ∧
      (strict→n=focus→ xs.getD r false=ys.getD (pick n) false))
    (other : strict → ∀n, xs.length≤n → n<xs.length+gs.length → n≠focus → (run gs xs).getD n false=true) :
    State strict r (run gs xs) (run (suffix r pick xs.length gs) ys) := by
  induction gs generalizing xs ys with
  | nil => exact state
  | cons g gs ih =>
    let a := bit g xs
    let b := bit (changeGate r (pick xs.length) g) ys
    have moved (i : Nat) : Nine.R (xs.getD i false) (ys.getD (redirect r (pick xs.length) i) false) := by
      by_cases e : i=r
      · simpa [redirect,e] using (choice xs.length).2.1
      · simpa only [redirect,ite_eq_right e] using (state i e).1
    have grows : Nine.R a b := by
      have parts := monotone g.inputs (fun i=>xs.getD i false) (fun i=>ys.getD (redirect r (pick xs.length) i) false) moved
      rcases basis g (by simp) with op|op
      · simpa only [a,b,bit,changeGate,op,List.map_map,Function.comp_def,GateOp.eval] using parts.1
      · simpa only [a,b,bit,changeGate,op,List.map_map,Function.comp_def,GateOp.eval] using parts.2
    have equal (on : strict) : a=b := by
      by_cases special : xs.length=focus
      · change g.op.eval (g.inputs.map _) = g.op.eval ((g.inputs.map _).map _)
        rw [List.map_map]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i _
        by_cases e : i=r
        · simpa only [e,redirect,ite_self,ite_true,Function.comp_apply] using (choice xs.length).2.2 on special
        · simpa only [redirect,ite_eq_right e,Function.comp_apply] using (state i e).2 on
      · have already := other on xs.length (by omega) (by simp) special
        have ax : a=true := (next_read g gs xs).symm.trans already
        exact ax.trans (grows ax).symm
    have more := ih (xs++[a]) (ys++[b]) (fun t mem=>basis t (by simp [mem]))
      (by simp; omega) (by simp; omega) (raise _ _ _ _ _ shape past state ⟨grows,equal⟩) (by
        intro n
        obtain ⟨prior,mono,equiv⟩ := choice n
        have xne : r≠xs.length := by omega
        have yne : pick n≠ys.length := by omega
        simpa only [read_append,ite_eq_right xne,ite_eq_right yne] using choice n) (by
        intro on n lo hi ne
        simp only [List.length_append,List.length_singleton] at lo hi
        exact other on n (by omega) (by simp;omega) ne)
    change State strict r (run gs (xs++[a])) (run (suffix r pick (xs.length+1) gs) (ys++[b]))
    simpa only [List.length_append,List.length_singleton] using more
end Plane920.Bypass

namespace Plane920.Bypass
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.Terminal

theorem initial (strict : Prop) (xs : List Bool) (v : Bool) : State strict xs.length (xs++[v]) xs := by
  intro i ne
  rw [read_append,ite_eq_right ne]
  unfold shift
  split
  · rename_i hi
    have one : xs.getD i false=false := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ i)]
    have two : xs.getD (i-1) false=false := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ i-1)]
    rw [one,two]
    exact ⟨id,fun _=>rfl⟩
  · exact ⟨id,fun _=>rfl⟩

theorem remove_last_and (pre : List Gate) (H : Gate) (post : List Gate) (out : V→Nat) {a b : Nat}
    (basis : ∀g∈pre++H::post,g.op=.and ∨ g.op=.or) (arity : ∀g∈pre++H::post,g.inputs.length≤2)
    (h : Correct (pre++H::post) out) (gate : H.op=.and) (ins : H.inputs=[a,b])
    (va : a<13+pre.length) (vb : b<13+pre.length) (hidden : 13+pre.length∉terminals out)
    (last : ∀ n, 13+pre.length<n → n<13+(pre++H::post).length → ∃w, out w=n) :
    ∃ (gs : List Gate) (o : V→Nat), gs.length+1=(pre++H::post).length ∧
      (∀g∈gs,g.op=.and ∨ g.op=.or) ∧ (∀g∈gs,g.inputs.length≤2) ∧ Correct gs o := by
  classical
  let r := 13+pre.length
  let before (x : Input) := run pre (List.ofFn x)
  have width (x : Input) : (before x).length=r := by simp [before,r,run_length]
  let pick (n : Nat) := if named : ∃w, out w=n then (if (before (co named.choose)).getD a false then b else a) else a
  have legal (n : Nat) : pick n=a ∨ pick n=b := by
    unfold pick
    split
    · split <;> simp
    · simp
  have choose_row (v : V) : pick (out v)=(if (before (co v)).getD a false then b else a) := by
    have named : ∃w, out w=out v := ⟨v,rfl⟩
    have eq : named.choose=v := separate h named.choose_spec
    simp only [pick,dite_eq_left named,eq]
  let new := pre++suffix r pick (r+1) post
  let name (w : V) := shift r (out w)
  have remaining {g : Gate} (m : g∈post) : g∈pre++H::post := by simp [m]
  have copied (P : Gate→Prop) (stable : ∀g n,P g→P (changeGate r n g)) (old : ∀g∈pre++H::post,P g) :
      ∀g∈new,P g := by
    intro g mem
    rcases List.mem_append.mp mem with first|later
    · exact old g (List.mem_append_left _ first)
    · exact suffix_spec r pick (r+1) post P stable (fun t ht=>old t (remaining ht)) g later
  refine ⟨new,name,by simp [new,suffix_len];omega,copied _ (by intro g n hh;exact hh) basis,
    copied _ (by intro g n hh; simpa [changeGate] using hh) arity,?_⟩
  intro w x heavy
  let X := before x
  let z := bit H X
  have lenX : X.length=r := width x
  have Z : z=(X.getD a false && X.getD b false) := by simp [z,bit,gate,ins,GateOp.eval]
  have original : run (pre++H::post) (List.ofFn x) = run post (X++[z]) := by rw [run_join];rfl
  have changed : run new (List.ofFn x)=run (suffix r pick (r+1) post) X := run_join _ _ _
  have sim := simulate r (out w) (x=co w) pick post (X++[z]) X (fun g m=>basis g (remaining m))
    (by simp) (by simp [lenX]) (by simpa only [lenX] using initial (x=co w) X z) (by
      intro n
      rw [read_append,ite_eq_left lenX.symm]
      have choose := legal n
      refine ⟨by rcases choose with e|e <;> rw [e] <;> omega,?_,?_⟩
      · rcases choose with eq|eq <;> rw [eq,Z] <;> intro yes
        · simp only [Bool.and_eq_true] at yes;exact yes.1
        · simp only [Bool.and_eq_true] at yes;exact yes.2
      · intro matchRow special
        rw [special,choose_row,Z]
        have aligned : (before (co w)).getD a false=X.getD a false := by rw [←matchRow]
        rw [aligned]
        by_cases act : X.getD a false=true
        · rw [ite_eq_left act,act];rfl
        · rw [ite_eq_right act,Bool.eq_false_of_not_eq_true act];rfl) (by
      intro matchRow n lo hi other
      have low : r<n := by simpa only [List.length_append,List.length_singleton,lenX,Nat.add_one_le_iff] using lo
      have high : n<13+(pre++H::post).length := by
        simp only [List.length_append,List.length_singleton,lenX] at hi
        simp only [List.length_append,List.length_cons]; dsimp [r] at hi; omega
      obtain ⟨v,vout⟩ := last n low high
      have ne : v≠w := fun eq=>other (vout.symm.trans (congrArg out eq))
      have on := (boundary h v w).trans (decide_eq_true ne)
      rw [←matchRow,vout] at on
      change (run (pre++H::post) (List.ofFn x)).getD n false=true at on
      exact original ▸ on)
  have excluded : r∉terminals out := hidden
  have notCut : out w≠r := fun eq => excluded (eq ▸ (show out w∈terminals out from Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩))
  have final := sim (out w) notCut
  change Tracked (x=co w) ((run post (X++[z])).getD (out w) false)
    ((run (suffix r pick (X++[z]).length post) X).getD (name w) false) at final
  rw [show (X++[z]).length=r+1 by simp [lenX],←original,←changed] at final
  change Tracked (x=co w) (read (pre++H::post) (out w) x) (read new (name w) x) at final
  cases val : target w x with
  | false => exact (final.2 ((target_false heavy).mp val)).symm.trans ((h w x heavy).trans val)
  | true => exact final.1 ((h w x heavy).trans val)
end Plane920.Bypass

namespace Plane920.Bypass
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component

def Last {gs : List Gate} (out : V→Nat) (j : Fin gs.length) :=
  13+j.val∉terminals out ∧ ∀n, 13+j.val<n → n<13+gs.length → n∈terminals out

theorem last_exists {gs : List Gate} {out : V→Nat} (h : Correct gs out) (many : 13<gs.length) :
    ∃j : Fin gs.length, Last out j := by
  let H := paid (terminals out) 13 gs.length
  have has : H.Nonempty := Finset.card_pos.mp (by rw [show H=paid (terminals out) 13 gs.length from rfl,hidden_count h];omega)
  let k := H.max' has
  have member : k∈H := H.max'_mem has
  obtain ⟨range,nz⟩ := Finset.mem_sdiff.mp member
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp range
  let j : Fin gs.length := ⟨k-13,by omega⟩
  have idx : 13+j.val=k := by change 13+(k-13)=k;omega
  refine ⟨j,idx ▸ nz,?_⟩
  intro n greater upper
  by_contra free
  have mem : n∈H := Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,upper⟩,free⟩
  have le := Finset.le_max' H n mem
  change n≤k at le
  omega

theorem nonempty_read {gs : List Gate} {out : V→Nat} (j : Fin gs.length) (a : Nat)
    (yes : (region gs out j a).Nonempty) : a<13+j.val := by
  by_contra! large
  have empty : region gs out j a=∅ := by
    unfold region
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by
      simpa only [List.length_append,tail_len,show start.length=13 from by simp [start],List.length_take,Nat.min_eq_left j.isLt.le] using large)];rfl
  simp [empty] at yes

theorem connected_split {gs : List Gate} {out : V→Nat} (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (j : Fin gs.length) (nz : 13+j.val∉terminals out) :
    Forest.Splits (start++supportTail (terminals out) start (gs.take j.val)) gs[j.val].inputs := by
  have empty := connected_redundant_empty arity h conn cap
  have needed := joins_of_not_redundant j nz (by simp [empty])
  obtain ⟨f,uni,not⟩ := needed
  by_contra bad
  exact not (Forest.no_split uni (arity _ (List.getElem_mem _)) bad)

theorem op_at_last {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (cap : gs.length≤25) (j : Fin gs.length)
    (last : Last out j) {a b : Nat} (ids : gs[j.val].inputs=[a,b]) (va : a<13+j.val) (vb : b<13+j.val) :
    gs[j.val].op=.or := by
  rcases basis _ (List.getElem_mem j.isLt) with isAnd|isOr
  · let pre := gs.take j.val
    let post := gs.drop (j.val+1)
    let gate := gs[j.val]
    have len : pre.length=j.val := by simp [pre]
    have split : pre++gate::post=gs := by simp [pre,post,gate]
    obtain ⟨small,o,size,b,a,h'⟩ := remove_last_and pre gate post out
      (by rw [split];exact basis) (by rw [split];exact arity) (by rw [split];exact h) isAnd ids
      (by rw [len];exact va) (by rw [len];exact vb) (by rw [len];exact last.1) (by
        rw [len,split]
        intro n greater lt
        obtain ⟨w,_,eq⟩ := Finset.mem_image.mp (last.2 n greater lt)
        exact ⟨w,eq⟩)
    have lower := Forest.twenty_five b a h'
    rw [split] at size
    omega
  · exact isOr

theorem connected_last_and {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (j : Fin gs.length) (last : Last out j) :
    gs[j.val].op=.or ∧ ∃a b, gs[j.val].inputs=[a,b] ∧ a<13+j.val ∧ b<13+j.val := by
  obtain ⟨a,b,ids,A,B,_⟩ := connected_split arity h conn cap j last.1
  have va := nonempty_read j a A
  have vb := nonempty_read j b B
  exact ⟨op_at_last basis arity h cap j last ids va vb,a,b,ids,va,vb⟩

theorem full_colors {gs : List Gate} {out : V→Nat} {f : V→V} (arity : ∀g∈gs,g.inputs.length≤2)
    (conn : Connected gs out) (j : Fin gs.length) (last : Last out j)
    (uni : Uniform f (start++supportTail (terminals out) start (gs.take j.val))) : (colors f).card≤2 := by
  let pre := gs.take j.val
  let post := gs.drop j.val
  let xs := start++supportTail (terminals out) start pre
  have split : pre++post=gs := List.take_append_drop j.val gs
  have n : xs.length=13+j.val := by simp only [xs,pre,List.length_append,tail_len,List.length_take,Nat.min_eq_left j.isLt.le,show start.length=13 from by simp [start]]
  obtain ⟨k,final,cost⟩ := components post (fun g hg =>arity g (List.mem_of_mem_drop hg)) (terminals out) xs f uni
  have whole : Uniform k (start++supportTail (terminals out) start gs) := by
    conv in supportTail _ _ gs => rw [←split,tail_append]
    simpa only [←List.append_assoc,xs] using final
  have unused : paid (terminals out) xs.length post.length ⊆ {13+j.val} := by
    intro i mem
    obtain ⟨lim,nz⟩ := Finset.mem_sdiff.mp mem
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp lim
    rw [n] at lo hi
    have ends : 13+j.val+post.length=13+gs.length := by simp [post]
    by_contra missing
    have diff := Finset.notMem_singleton.mp missing
    exact nz (last.2 i (by omega) (by omega))
  have upper := Finset.card_le_card unused
  rw [Finset.card_singleton] at upper
  rw [conn k whole] at cost
  omega
end Plane920.Bypass

namespace Plane920.Bypass
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse

def Allowed (A : Region) (H K : Input→Bool) := Local K A ∨ Local K (Finset.univ \ A) ∨ K=H

theorem cut_at_last {gs : List Gate} {out : V→Nat} (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (j : Fin gs.length) (last : Last out j) :
    ∃ (f : V→V) (c : V) (a b : Nat), Uniform f (start++supportTail (terminals out) start (gs.take j.val)) ∧
      (colors f).card=2 ∧ gs[j.val].inputs=[a,b] ∧ (region gs out j a).Nonempty ∧ (region gs out j b).Nonempty ∧
      region gs out j a⊆Cut.block f c ∧ region gs out j b⊆Finset.univ \ Cut.block f c := by
  let xs := start++supportTail (terminals out) start (gs.take j.val)
  obtain ⟨a,b,ids,nonA,nonB,_⟩ := connected_split arity h conn cap j last.1
  have empty := connected_redundant_empty arity h conn cap
  obtain ⟨f,uni,change⟩ := joins_of_not_redundant j last.1 (by simp [empty])
  let u := region gs out j a
  let v := region gs out j b
  change u.Nonempty at nonA
  change v.Nonempty at nonB
  have hu : Hom f u := available_hom uni (readable xs a)
  have hv : Hom f v := available_hom uni (readable xs b)
  let c := pivot f u
  let d := pivot f v
  have different : c≠d := by
    intro eq
    apply change
    have gathered : gather xs gs[j.val].inputs=u∪v := by simp only [ids,gather,Finset.union_empty,u,v,region,xs]
    change Hom f (gather xs gs[j.val].inputs)
    rw [gathered]
    have same (x : V) (mem : x∈u∪v) : f x=c := by
      rcases Finset.mem_union.mp mem with A|B
      · exact unique_color hu A
      · exact (unique_color hv B).trans eq.symm
    exact fun x xi y yi => (same x xi).trans (same y yi).symm
  have lower : 1<(colors f).card := by
    obtain ⟨x,hx⟩ := nonA
    obtain ⟨y,hy⟩ := nonB
    exact Finset.one_lt_card.mpr ⟨f x,Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,
      f y,Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩,fun eq=>different (((unique_color hu hx).symm.trans eq).trans (unique_color hv hy))⟩
  have upper := full_colors arity conn j last uni
  refine ⟨f,c,a,b,uni,by omega,ids,nonA,nonB,?_,?_⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,unique_color hu hx⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun bad=>different (((Finset.mem_filter.mp bad).2).symm.trans (unique_color hv hx))⟩

theorem local_enlarge {F : Input→Bool} {U A : Region} (localF : Local F U) (sub : U⊆A) : Local F A :=
  fun x y agree => localF x y (fun i hi=>agree i (sub hi))

theorem local_side {gs : List Gate} {out : V→Nat} {f : V→V} (j : Fin gs.length)
    (uni : Uniform f (start++supportTail (terminals out) start (gs.take j.val))) (c : V) (k : Nat) :
    Local (live gs out j k) (Cut.block f c) ∨ Local (live gs out j k) (Finset.univ \ Cut.block f c) := by
  let xs := start++supportTail (terminals out) start (gs.take j.val)
  have hom : Hom f (region gs out j k) := available_hom uni (readable xs k)
  rcases Cut.block_hom hom c with L|R
  · exact Or.inl (local_enlarge (live_local _ _ _ _) L)
  · exact Or.inr (local_enlarge (live_local _ _ _ _) (fun x mem=>Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _,Finset.disjoint_left.mp R mem⟩))

theorem all_reads {gs : List Gate} {out : V→Nat} {f : V→V} (j : Fin gs.length) (last : Last out j)
    (uni : Uniform f (start++supportTail (terminals out) start (gs.take j.val))) (c : V) (t : Fin gs.length) (k : Nat) :
    Allowed (Cut.block f c) (globalWire gs out (13+j.val)) (live gs out t k) := by
  by_cases valid : k<13+t.val
  · rw [sem_prefix _ _ _ _ valid]
    by_cases old : k<13+j.val
    · rw [←sem_prefix _ _ j _ old]
      exact (local_side j uni c k).imp_right Or.inl
    by_cases root : k=13+j.val
    · exact Or.inr (Or.inr (root ▸ rfl))
    have held := last.2 k (by omega) (by omega)
    left
    intro x y _
    have fixed (input : Input) : globalWire gs out k input=true := frozen_high gs _ (List.ofFn input) k held
      (by simp only [List.length_ofFn]; omega) (by simp only [List.length_ofFn]; omega)
    exact (fixed x).trans (fixed y).symm
  · left
    intro x y _
    exact (Forest.missing_live _ _ _ _ (by omega) x).trans (Forest.missing_live _ _ _ _ (by omega) y).symm

theorem surface {gs : List Gate} {out : V→Nat} {f : V→V} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (j : Fin gs.length) (last : Last out j)
    (uni : Uniform f (start++supportTail (terminals out) start (gs.take j.val))) (c w : V) :
    ∃F G : Input→Bool, Allowed (Cut.block f c) (globalWire gs out (13+j.val)) F ∧
      Allowed (Cut.block f c) (globalWire gs out (13+j.val)) G ∧
      ((∀s : Region, s.card≤4 → (Active F s ∨ Active G s ↔ s=line w)) ∨
       (∀s : Region, s.card≤4 → (Active F s ∧ Active G s ↔ s=line w))) := by
  let t := outIndex h w
  have law (s : Region) (sm : s.card≤4) : Active (value gs out t) s ↔ s=line w := by
    have heavy : 9≤(supp (missing s)).card := by
      rw [complement,Finset.card_sdiff_of_subset (Finset.subset_univ s)]
      have total : (Finset.univ : Region).card=13 := by decide
      omega
    rw [Active,normalized basis h w t (index_eq h w) _ heavy,←h w _ heavy]
    exact statement h sm
  cases ids : gs[t.val].inputs with
  | nil =>
    have fixed : Local (value gs out t) (Cut.block f c) := by intro x y _;simp [value,bit,ids]
    refine ⟨_,_,Or.inl fixed,Or.inl fixed,Or.inr ?_⟩
    intro s sm
    simpa only [and_self] using law s sm
  | cons a tail =>
    cases tail with
    | nil =>
      have eq : value gs out t=live gs out t a := by
        funext x
        rcases basis gs[t.val] (List.getElem_mem _) with gate|gate <;> simp [value,bit,ids,gate,GateOp.eval,live]
      have leg := all_reads j last uni c t a
      refine ⟨_,_,leg,leg,Or.inr ?_⟩
      intro s sm
      simpa only [eq,and_self] using law s sm
    | cons b tail =>
      cases tail with
      | cons x xs => have len := arity gs[t.val] (List.getElem_mem t.isLt);simp [ids] at len
      | nil =>
        refine ⟨_,_,all_reads j last uni c t a,all_reads j last uni c t b,?_⟩
        rcases basis gs[t.val] (List.getElem_mem _) with gate|gate
        · left
          intro s sm
          have logic (q r : Bool) : (q=false ∨ r=false) ↔ (q && r)=false := by cases q <;> cases r <;> decide
          exact (logic _ _).trans (by simpa [Active,value,bit,ids,gate,GateOp.eval,live] using law s sm)
        · right
          intro s sm
          simpa [Active,value,bit,ids,gate,GateOp.eval,live] using law s sm
end Plane920.Bypass

namespace Plane920.LastMerge
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Parse Plane920.Bypass

def Law (w : V) (F G : Input→Bool) : Prop :=
  (∀s : Region, s.card≤4 → (Active F s ∨ Active G s ↔ s=line w)) ∨
  (∀s : Region, s.card≤4 → (Active F s ∧ Active G s ↔ s=line w))
theorem flip {w : V} {F G : Input→Bool} (law : Law w F G) : Law w G F := by
  rcases law with any|both
  · exact Or.inl (fun s sm => or_comm.trans (any s sm))
  · exact Or.inr (fun s sm => and_comm.trans (both s sm))

theorem proper {w : V} {A B : Region} (dis : Disjoint A B) (hitB : (line w∩B).Nonempty) : line w∩A≠line w := by
  intro eq
  obtain ⟨x,hx⟩ := hitB
  have mem : x∈line w∩A := by rw [eq];exact (Finset.mem_inter.mp hx).1
  exact Finset.disjoint_left.mp dis (Finset.mem_inter.mp mem).2 (Finset.mem_inter.mp hx).2

theorem same_side {w : V} {A B : Region} {F G : Input→Bool} (lf : Local F A) (lg : Local G A)
    (dis : Disjoint A B) (hit : (line w∩B).Nonempty) (law : Law w F G) : False := by
  have small : (line w∩A).card≤4 := (Finset.card_le_card Finset.inter_subset_left).trans (line_size w).le
  have F' := project lf (line w)
  have G' := project lg (line w)
  have neq := proper dis hit
  rcases law with any|both
  · have old := (any (line w) (line_size w).le).mpr rfl
    exact neq ((any _ small).mp (old.imp (fun a=>F'.trans a) (fun b=>G'.trans b)))
  · have old := (both (line w) (line_size w).le).mpr rfl
    exact neq ((both _ small).mp ⟨F'.trans old.1,G'.trans old.2⟩)

theorem repeated_root {w : V} {A B : Region} {f g H : Input→Bool} (lf : Local f A) (lg : Local g B)
    (root : ∀S, Active H S ↔ Active f S ∧ Active g S) (dis : Disjoint A B) (cover : line w⊆A∪B)
    (ha : (line w∩A).Nonempty) (hb : (line w∩B).Nonempty) (law : Law w H H) :
    Minimal f (line w∩A) ∧ Minimal g (line w∩B) := by
  have only (S : Region) (sm : S.card≤4) : Active H S ↔ S=line w := by
    rcases law with any|both
    · simpa only [or_self] using any S sm
    · simpa only [and_self] using both S sm
  exact crossing lf lg dis cover ha hb (Or.inr (fun S sm=>(root S).symm.trans (only S sm)))

theorem mixed {w : V} {A B : Region} {f g H K : Input→Bool} (lf : Local f A) (lg : Local g B) (lk : Local K A)
    (root : ∀S, Active H S ↔ Active f S ∧ Active g S) (dis : Disjoint A B) (cover : line w⊆A∪B)
    (ha : (line w∩A).Nonempty) (hb : (line w∩B).Nonempty) (law : Law w H K) : Minimal g (line w∩B) := by
  rcases law with any|both
  · have on : Active H (line w) := by
      rcases (any (line w) (line_size w).le).mpr rfl with a|b
      · exact a
      · have small := (Finset.card_le_card (Finset.inter_subset_left (s₁ := line w) (s₂ := A))).trans (line_size w).le
        exact False.elim (proper dis hb ((any _ small).mp (Or.inr ((project lk (line w)).trans b))))
    have spec (S : Region) (sm : S.card≤4) : Active f S ∧ Active g S ↔ S=line w := by
      constructor
      · exact fun both => (any S sm).mp (Or.inl ((root S).mpr both))
      · rintro rfl;exact (root _).mp on
    exact (crossing lf lg dis cover ha hb (Or.inr spec)).2
  · let M : Input→Bool := fun x=>f x || K x
    have lm : Local M A := fun x y agree => congrArg₂ (· || ·) (lf x y agree) (lk x y agree)
    have active (S : Region) : Active M S ↔ Active f S ∧ Active K S := by simp [Active,M]
    have both' (S : Region) (sm : S.card≤4) : Active M S ∧ Active g S ↔ S=line w := by
      rw [←both S sm,root,active]
      tauto
    exact (crossing lm lg dis cover ha hb (Or.inr both')).2

def Early (gs : List Gate) (out : V→Nat) (j : Fin gs.length) (F : Input→Bool) :=
  (∃b : Bool,F=fun _=>b) ∨ ∃k<13+j.val,F=globalWire gs out k

def Visible (gs : List Gate) (out : V→Nat) (j : Fin gs.length) (A B : Region) (F : Input→Bool) :=
  (Local F A ∧ Early gs out j F) ∨ (Local F B ∧ Early gs out j F) ∨ F=globalWire gs out (13+j.val)

theorem visible_reads {gs : List Gate} {out : V→Nat} {f : V→V} (j : Fin gs.length) (last : Last out j)
    (uni : Uniform f (start++supportTail (terminals out) start (gs.take j.val))) (c : V) (t : Fin gs.length) (k : Nat) :
    Visible gs out j (Cut.block f c) (Finset.univ \ Cut.block f c) (live gs out t k) := by
  have const (F : Input→Bool) (b : Bool) (eq : F=fun _=>b) :
      Visible gs out j (Cut.block f c) (Finset.univ \ Cut.block f c) F := Or.inl ⟨by rw [eq];intro x y _;rfl,Or.inl ⟨b,eq⟩⟩
  by_cases valid : k<13+t.val
  · rw [sem_prefix _ _ _ _ valid]
    by_cases old : k<13+j.val
    · have sub := local_side j uni c k
      rw [sem_prefix _ _ j _ old] at sub
      rcases sub with a|b
      · exact Or.inl ⟨a,Or.inr ⟨k,old,rfl⟩⟩
      · exact Or.inr (Or.inl ⟨b,Or.inr ⟨k,old,rfl⟩⟩)
    by_cases root : k=13+j.val
    · exact Or.inr (Or.inr (root ▸ rfl))
    have held := last.2 k (by omega) (by omega)
    apply const _ true
    funext x
    exact frozen_high gs _ (List.ofFn x) k held (by simp only [List.length_ofFn];omega) (by simp only [List.length_ofFn];omega)
  · exact const _ false (funext (Forest.missing_live _ _ _ _ (by omega)))

end Plane920.LastMerge

namespace Plane920.LastMerge
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Parse Plane920.Bypass
theorem visible_surface {gs : List Gate} {out : V→Nat} {f : V→V} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (j : Fin gs.length) (last : Last out j)
    (uni : Uniform f (start++supportTail (terminals out) start (gs.take j.val))) (c w : V) :
    ∃F G : Input→Bool, Visible gs out j (Cut.block f c) (Finset.univ \ Cut.block f c) F ∧
      Visible gs out j (Cut.block f c) (Finset.univ \ Cut.block f c) G ∧
      ((∀s : Region, s.card≤4 → (Active F s ∨ Active G s ↔ s=line w)) ∨
       (∀s : Region, s.card≤4 → (Active F s ∧ Active G s ↔ s=line w))) := by
  let t := outIndex h w
  have law (s : Region) (sm : s.card≤4) : Active (value gs out t) s ↔ s=line w := by
    have heavy : 9≤(supp (missing s)).card := by
      rw [complement,Finset.card_sdiff_of_subset (Finset.subset_univ s)]
      have total : (Finset.univ : Region).card=13 := by decide
      omega
    rw [Active,normalized basis h w t (index_eq h w) _ heavy,←h w _ heavy]
    exact statement h sm
  cases ids : gs[t.val].inputs with
  | nil =>
    have fixed : Local (value gs out t) (Cut.block f c) := by intro x y _;simp [value,bit,ids]
    refine ⟨_,_,Or.inl ⟨fixed,Or.inl ⟨gs[t.val].op.eval [],by funext;simp [value,bit,ids]⟩⟩,Or.inl ⟨fixed,Or.inl ⟨gs[t.val].op.eval [],by funext;simp [value,bit,ids]⟩⟩,Or.inr ?_⟩
    intro s sm
    simpa only [and_self] using law s sm
  | cons a tail =>
    cases tail with
    | nil =>
      have eq : value gs out t=live gs out t a := by
        funext x
        rcases basis gs[t.val] (List.getElem_mem _) with gate|gate <;> simp [value,bit,ids,gate,GateOp.eval,live]
      have leg := visible_reads j last uni c t a
      refine ⟨_,_,leg,leg,Or.inr ?_⟩
      intro s sm
      simpa only [eq,and_self] using law s sm
    | cons b tail =>
      cases tail with
      | cons x xs => have len := arity gs[t.val] (List.getElem_mem t.isLt);simp [ids] at len
      | nil =>
        refine ⟨_,_,visible_reads j last uni c t a,visible_reads j last uni c t b,?_⟩
        rcases basis gs[t.val] (List.getElem_mem _) with gate|gate
        · left
          intro s sm
          have logic (q r : Bool) : (q=false ∨ r=false) ↔ (q && r)=false := by cases q <;> cases r <;> decide
          exact (logic _ _).trans (by simpa [Active,value,bit,ids,gate,GateOp.eval,live] using law s sm)
        · right
          intro s sm
          simpa [Active,value,bit,ids,gate,GateOp.eval,live] using law s sm
def Payment (gs : List Gate) (out : V→Nat) (j : Fin gs.length) (T : Region) := ∃F, Early gs out j F ∧ Minimal F T

theorem pay_wire {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {T : Region} (yes : Payment gs out j T)
    (size : 2≤T.card) : ∃i<13+j.val, i∈paid (terminals out) 13 gs.length ∧ Minimal (globalWire gs out i) T := by
  obtain ⟨F,early,m⟩ := yes
  rcases early with ⟨b,rfl⟩|⟨i,prev,rfl⟩
  · have eq := m.2 ∅ (show Active (fun _=>b) ∅ from m.1) (by simp)
    rw [←eq] at size; simp at size
  · have m' : Minimal (live gs out j i) T := by rw [sem_prefix _ _ _ _ prev];exact m
    exact ⟨i,prev,hidden j i m' size⟩

theorem triage {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A B : Region} {w : V} {f g : Input→Bool}
    (lf : Local f A) (lg : Local g B) (oldF : Early gs out j f) (oldG : Early gs out j g)
    (root : ∀S, Active (globalWire gs out (13+j.val)) S ↔ Active f S ∧ Active g S)
    (sep : Disjoint A B) (covers : line w⊆A∪B) (ha : (line w∩A).Nonempty) (hb : (line w∩B).Nonempty)
    (evidence : ∃F G, Visible gs out j A B F ∧ Visible gs out j A B G ∧ Law w F G) :
    (Payment gs out j (line w∩A) ∧ Payment gs out j (line w∩B)) ∨
      (Minimal f (line w∩A) ∧ Payment gs out j (line w∩A)) ∨ (Minimal g (line w∩B) ∧ Payment gs out j (line w∩B)) := by
  obtain ⟨F,G,left,right,law⟩ := evidence
  have sc : line w⊆B∪A := by rw [Finset.union_comm];exact covers
  have swapped (S) := (root S).trans and_comm
  have L (m : Minimal f (line w∩A)) : Minimal f (line w∩A) ∧ Payment gs out j (line w∩A) := ⟨m,f,oldF,m⟩
  have R (m : Minimal g (line w∩B)) : Minimal g (line w∩B) ∧ Payment gs out j (line w∩B) := ⟨m,g,oldG,m⟩
  rcases left with ⟨fA,fOld⟩|⟨fB,fOld⟩|rfl
  · rcases right with ⟨gA,gOld⟩|⟨gB,gOld⟩|rfl
    · exact False.elim (same_side fA gA sep hb law)
    · obtain ⟨x,y⟩ := crossing fA gB sep covers ha hb law
      exact Or.inl ⟨⟨_,fOld,x⟩,⟨_,gOld,y⟩⟩
    · exact Or.inr (Or.inr (R (mixed lf lg fA root sep covers ha hb (flip law))))
  · rcases right with ⟨gA,gOld⟩|⟨gB,gOld⟩|rfl
    · obtain ⟨x,y⟩ := crossing gA fB sep covers ha hb (flip law)
      exact Or.inl ⟨⟨_,gOld,x⟩,⟨_,fOld,y⟩⟩
    · exact False.elim (same_side fB gB sep.symm ha law)
    · exact Or.inr (Or.inl (L (mixed lg lf fB swapped sep.symm sc hb ha (flip law))))
  · rcases right with ⟨gA,gOld⟩|⟨gB,gOld⟩|rfl
    · exact Or.inr (Or.inr (R (mixed lf lg gA root sep covers ha hb law)))
    · exact Or.inr (Or.inl (L (mixed lg lf gB swapped sep.symm sc hb ha law)))
    · obtain ⟨x,y⟩ := repeated_root lf lg root sep covers ha hb law
      exact Or.inl ⟨⟨_,oldF,x⟩,⟨_,oldG,y⟩⟩

theorem actual_cut {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Component.Connected gs out) (cap : gs.length≤25) :
    ∃ (j : Fin gs.length) (A B : Region) (a b : Nat), Last out j ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A∪B=Finset.univ ∧
      gs[j.val].op=.or ∧ gs[j.val].inputs=[a,b] ∧ a<13+j.val ∧ b<13+j.val ∧ Local (live gs out j a) A ∧ Local (live gs out j b) B ∧
      ∀w : V, (line w∩A).Nonempty → (line w∩B).Nonempty →
        (Payment gs out j (line w∩A) ∧ Payment gs out j (line w∩B)) ∨
        (Minimal (live gs out j a) (line w∩A) ∧ Payment gs out j (line w∩A)) ∨
        (Minimal (live gs out j b) (line w∩B) ∧ Payment gs out j (line w∩B)) := by
  classical
  have lb := Forest.twenty_five basis arity h
  obtain ⟨j,last⟩ := last_exists h (by omega)
  obtain ⟨f,c,a,b,uni,_,ids,ha,hb,sa,sb⟩ := cut_at_last arity h conn cap j last
  let A := Cut.block f c
  let B := Finset.univ \ A
  have ba : A.Nonempty := ha.mono sa
  have bb : B.Nonempty := hb.mono sb
  have dis : Disjoint A B := Finset.disjoint_left.mpr (fun {x} ax bx=> (Finset.mem_sdiff.mp bx).2 ax)
  have union : A∪B=Finset.univ := by ext x;simp [B]
  have va := nonempty_read j a ha
  have vb := nonempty_read j b hb
  have gate := op_at_last basis arity h cap j last ids va vb
  have la : Local (live gs out j a) A := local_enlarge (live_local _ _ _ _) sa
  have lg : Local (live gs out j b) B := local_enlarge (live_local _ _ _ _) sb
  refine ⟨j,A,B,a,b,last,ba,bb,dis,union,gate,ids,va,vb,la,lg,?_⟩
  intro w x y
  apply triage la lg (Or.inr ⟨a,va,sem_prefix _ _ _ _ va⟩) (Or.inr ⟨b,vb,sem_prefix _ _ _ _ vb⟩) _ dis
    (by rw [union];exact Finset.subset_univ _) x y (visible_surface basis arity h j last uni c w)
  intro S
  rw [Forest.stored_value j last.1]
  simp [Active,value,bit,ids,gate,GateOp.eval,live]
end Plane920.LastMerge

namespace Plane920.LastMerge
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Forest Plane920.Parse Plane920.Bypass

def Adequate (A B : Region) (u v w : V) :=
  (line w∩A).Nonempty ∧ (line w∩B).Nonempty ∧
    (line w∩A≠line u∩A ∨ (line w∩A).card=3) ∧ (line w∩B≠line v∩B ∨ (line w∩B).card=3)

theorem designated (F : Input→Bool) (A : Region) : ∃v : V, ∀w, Minimal F (line w∩A) → line w∩A=line v∩A := by
  classical
  by_cases has : ∃w, Minimal F (line w∩A)
  · obtain ⟨v,h⟩ := has
    exact ⟨v,fun _ m=>minima_eq m h⟩
  · exact ⟨0,fun w m=>False.elim (has ⟨w,m⟩)⟩

theorem earlier_reserve {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {T : Region} {w : V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (sub : T⊆line w)
    (size : 2≤T.card) (yes : Payment gs out j T) :
    ∃ k∈protectedAt gs out w, Earliest gs out k T := by
  classical
  obtain ⟨i,_,paid,m⟩ := pay_wire yes size
  obtain ⟨k,top⟩ := first (show ∃k, Own gs out k T from ⟨i,paid,m⟩)
  exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨top.1.1,T,size,sub,top.1.2⟩,Forest26.typed basis arity top size⟩,top⟩

theorem two_for_three {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {T : Region} {w : V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2)
    (clean : Forest26.defects (terminals out) start gs=∅) (sub : T⊆line w)
    (size : T.card=3) (yes : Payment gs out j T) : 2≤(protectedAt gs out w).card := by
  classical
  obtain ⟨i,mem,top⟩ := earlier_reserve basis arity sub (by omega) yes
  obtain ⟨U,su,n,j,own,gate⟩ := Forest26.nondefect_pair basis arity top size (by simp [clean])
  have add : j∈protectedAt gs out w := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨own.1,U,n.ge,su.trans sub,own.2⟩,gate⟩
  have ne : i≠j := by
    intro eq
    have m := top.1.2
    rw [eq] at m
    have same := minima_eq m own.2
    have bad := size.symm.trans ((congrArg Finset.card same).trans n)
    exact (by decide : (3:Nat)≠2) bad
  exact Finset.one_lt_card.mpr ⟨i,mem,j,add,ne⟩

theorem two_sides {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A B : Region} {w : V}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2)
    (clean : Forest26.defects (terminals out) start gs=∅) (dis : Disjoint A B) (un : A∪B=Finset.univ)
    (ha : (line w∩A).Nonempty) (hb : (line w∩B).Nonempty) (yesA : Payment gs out j (line w∩A))
    (yesB : Payment gs out j (line w∩B)) : 2≤(protectedAt gs out w).card := by
  classical
  have split : (line w∩A)∪(line w∩B)=line w := by rw [←Finset.inter_union_distrib_left,un,Finset.inter_univ]
  have sep : Disjoint (line w∩A) (line w∩B) := dis.mono Finset.inter_subset_right Finset.inter_subset_right
  have sum : (line w∩A).card+(line w∩B).card=4 := by rw [←Finset.card_union_of_disjoint sep,split,line_size]
  have pa := Finset.card_pos.mpr ha
  have pb := Finset.card_pos.mpr hb
  by_cases sA : (line w∩A).card=3
  · exact two_for_three basis arity clean Finset.inter_subset_left sA yesA
  by_cases sB : (line w∩B).card=3
  · exact two_for_three basis arity clean Finset.inter_subset_left sB yesB
  obtain ⟨a,aMem,am⟩ := earlier_reserve basis arity Finset.inter_subset_left (by omega) yesA
  obtain ⟨b,bMem,bm⟩ := earlier_reserve basis arity Finset.inter_subset_left (by omega) yesB
  have ne : a≠b := by
    intro eq
    have m := am.1.2
    rw [eq] at m
    have same := minima_eq m bm.1.2
    obtain ⟨x,hx⟩ := ha
    exact Finset.disjoint_left.mp sep hx (same ▸ hx)
  exact Finset.one_lt_card.mpr ⟨a,aMem,b,bMem,ne⟩

def Prices (gs : List Gate) (out : V→Nat) (j : Fin gs.length) (A B : Region) (a b : Nat) := ∀w : V,
    (line w∩A).Nonempty → (line w∩B).Nonempty →
      (Payment gs out j (line w∩A) ∧ Payment gs out j (line w∩B)) ∨
      (Minimal (live gs out j a) (line w∩A) ∧ Payment gs out j (line w∩A)) ∨
      (Minimal (live gs out j b) (line w∩B) ∧ Payment gs out j (line w∩B))

theorem obstruction {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A B : Region} {a b : Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Component.Connected gs out) (cap : gs.length≤25) (sep : Disjoint A B) (un : A∪B=Finset.univ)
    (cut : Prices gs out j A B a b) :
    ∃u v : V, ∀p : V, ∃w : V, p∈line w ∧ ¬Adequate A B u v w := by
  classical
  obtain ⟨u,U⟩ := designated (live gs out j a) A
  obtain ⟨v,V'⟩ := designated (live gs out j b) B
  have clean : Forest26.defects (terminals out) start gs=∅ := Finset.subset_empty.mp
    ((Component.connected_redundant_empty arity h conn cap) ▸ Component.overlap_is_redundant (terminals out) start gs arity)
  refine ⟨u,v,?_⟩
  intro p
  by_contra! whole
  have per (w : V) (mem : w∈pencil p) : 2≤(protectedAt gs out w).card := by
    obtain ⟨ha,hb,ea,eb⟩ := whole w (Finset.mem_filter.mp mem).2
    rcases cut w ha hb with ⟨ra,rb⟩|⟨m,pay⟩|⟨m,pay⟩
    · exact two_sides basis arity clean sep un ha hb ra rb
    · have size := ea.resolve_left (not_not_intro (U w m))
      exact two_for_three basis arity clean Finset.inter_subset_left size pay
    · have size := eb.resolve_left (not_not_intro (V' w m))
      exact two_for_three basis arity clean Finset.inter_subset_left size pay
  have four : (pencil p).card=4 := Cut.incidences p
  have lo : 8≤(locked gs out p).card := by rw [Forest26.protected_count];simpa [four] using Finset.sum_le_sum per
  have rem := Forest26.five_spare basis arity h p
  rw [spare,Finset.card_sdiff_of_subset (locked_paid _ _ _),hidden_count h] at rem
  omega

theorem cut_pencils {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Component.Connected gs out) (cap : gs.length≤25) :
    ∃ (j : Fin gs.length) (A B : Region) (a b : Nat) (u v : V),
      Last out j ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A∪B=Finset.univ ∧
      gs[j.val].op=.or ∧ gs[j.val].inputs=[a,b] ∧ a<13+j.val ∧ b<13+j.val ∧
      Local (live gs out j a) A ∧ Local (live gs out j b) B ∧ Prices gs out j A B a b ∧
      ∀p : V, ∃w : V, p∈line w ∧ ¬Adequate A B u v w := by
  obtain ⟨j,A,B,a,b,last,al,bl,sep,un,gate,ins,va,vb,la,lb,cut⟩ := actual_cut basis arity h conn cap
  obtain ⟨u,v,forbid⟩ := obstruction basis arity h conn cap sep un cut
  exact ⟨j,A,B,a,b,u,v,last,al,bl,sep,un,gate,ins,va,vb,la,lb,cut,forbid⟩
end Plane920.LastMerge

namespace Plane920.LastMerge
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal
def fiveBlock : Region := {0,1,2,3,4}
def eightBlock : Region := Finset.univ \ fiveBlock
set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
theorem five_eight_check : ∀u v : V, ∃p : V, ∀w : V, p∈line w→Adequate fiveBlock eightBlock u v w := by
  unfold Adequate
  decide +kernel

theorem five_eight_forbidden {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {a b : Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Component.Connected gs out) (cut : Prices gs out j fiveBlock eightBlock a b) :
    26≤gs.length := by
  by_contra! small
  have dis : Disjoint fiveBlock eightBlock := Finset.disjoint_left.mpr (fun {x} hx hy => (Finset.mem_sdiff.mp hy).2 hx)
  have un : fiveBlock∪eightBlock=Finset.univ := by ext x;simp [eightBlock]
  obtain ⟨u,v,all⟩ := obstruction basis arity h conn (by omega) dis un cut
  obtain ⟨p,chosen⟩ := five_eight_check u v
  obtain ⟨w,on,impossible⟩ := all p
  exact impossible (chosen w on)
end Plane920.LastMerge

namespace Plane920.LastMerge
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal
def Excluded (A B : Region) := ∀u v : V, ∃p : V, ∀w : V, p∈line w→Adequate A B u v w
def consecutiveSix : Region := {0,1,2,3,4,5}
def otherSix : Region := {0,1,2,3,4,6}

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
theorem six_check : Excluded consecutiveSix (Finset.univ \ consecutiveSix) := by
  unfold Excluded Adequate
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
theorem other_six_check : Excluded otherSix (Finset.univ \ otherSix) := by
  unfold Excluded Adequate
  decide +kernel

structure Collineation where
  pts : V≃V
  lns : V≃V
  incidence : ∀w : V, (line w).map pts.toEmbedding=line (lns w)

theorem transport {A B : Region} (d : Collineation) (ex : Excluded A B) :
    Excluded (A.map d.pts.toEmbedding) (B.map d.pts.toEmbedding) := by
  intro u v
  obtain ⟨p,root⟩ := ex (d.lns.symm u) (d.lns.symm v)
  refine ⟨d.pts p,?_⟩
  intro w on
  have same (k : V) : line k=(line (d.lns.symm k)).map d.pts.toEmbedding := by rw [d.incidence,Equiv.apply_symm_apply]
  have original : p∈line (d.lns.symm w) := by
    rw [same w,Finset.mem_map_equiv,Equiv.symm_apply_apply] at on
    exact on
  have verified :=  root _ original
  unfold Adequate
  rw [same w,same u,same v]
  simpa only [Adequate,←Finset.map_inter,Finset.map_nonempty,ne_eq,Finset.map_inj,Finset.card_map] using verified

theorem swap {A B : Region} (ex : Excluded A B) : Excluded B A := by
  intro u v
  obtain ⟨p,root⟩ := ex v u
  refine ⟨p,?_⟩
  intro w on
  obtain ⟨ha,hb,ea,eb⟩ := root w on
  exact ⟨hb,ha,eb,ea⟩

theorem no_geometry {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {a b : Nat} {A B : Region}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Component.Connected gs out) (sep : Disjoint A B) (un : A∪B=Finset.univ)
    (cut : Prices gs out j A B a b) (bad : Excluded A B) : 26≤gs.length := by
  by_contra! small
  obtain ⟨u,v,all⟩ := obstruction basis arity h conn (by omega) sep un cut
  obtain ⟨p,safe⟩ := bad u v
  obtain ⟨w,on,impossible⟩ := all p
  exact impossible (safe w on)

theorem three_orbits (d : Collineation) (A : Region) (typ : A=fiveBlock ∨ A=consecutiveSix ∨ A=otherSix) :
    Excluded (A.map d.pts.toEmbedding) ((Finset.univ\A).map d.pts.toEmbedding) ∧
      Excluded ((Finset.univ\A).map d.pts.toEmbedding) (A.map d.pts.toEmbedding) := by
  have test : Excluded A (Finset.univ\A) := by
    rcases typ with rfl|rfl|rfl
    · exact five_eight_check
    · exact six_check
    · exact other_six_check
  exact ⟨transport d test,swap (transport d test)⟩
end Plane920.LastMerge

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component

def Intrinsic (U : Region) (xs : List SetV) := ∀f : V→V, Uniform f xs → Hom f U
def freeze (U : Region) (bg x : Input) : Input := fun i=>if i∈U then x i else bg i
def Source (N : Nat) (base : Input→List Bool) (F : Input→Bool) :=
  (∃b : Bool,F=fun _=>b) ∨ ∃ i<N, F=fun x=>(base x).getD i false
def Tracks (N : Nat) (base now : Input→List Bool) := ∀i, Source N base (fun x=>(now x).getD i false)
def Respects (vals : Input→List Bool) (sets : List SetV) := ∀x y : Input, Valid x y (vals x) (vals y) sets

theorem extend_intrinsic {U : Region} {xs : List SetV} (old : Intrinsic U xs) (more : List SetV) :
    Intrinsic U (xs++more) := fun f all=>old f (fun s hs=>all s (List.mem_append_left _ hs))

theorem parent_away {xs : List SetV} {U : Region} {a b : Nat} (intr : Intrinsic U xs)
    (join : joinsComponents xs [a,b]) : Disjoint (xs.getD a ∅) U ∨ Disjoint (xs.getD b ∅) U := by
  obtain ⟨f,uni,no⟩ := join
  have ha := available_hom uni (readable xs a)
  have hb := available_hom uni (readable xs b)
  have hu := intr f uni
  by_contra! neither
  obtain ⟨p,pa,pu⟩ := Finset.not_disjoint_iff.mp neither.1
  obtain ⟨q,qb,qu⟩ := Finset.not_disjoint_iff.mp neither.2
  apply no
  have same {x : V} (mem : x∈gather xs [a,b]) : f x=f p := by
    simp only [gather,Finset.union_empty,Finset.mem_union] at mem
    rcases mem with l|r
    · exact ha x l p pa
    · exact (hb x r q qb).trans (hu q qu p pu)
  exact fun _ hp _ hq => (same hp).trans (same hq).symm

theorem away_constant {U : Region} {xs : List SetV} {vals : Input→List Bool} (good : Respects vals xs)
    (bg : Input) (i : Nat) (away : Disjoint (xs.getD i ∅) U) :
    ∃b : Bool, (fun x=>(vals (freeze U bg x)).getD i false)=fun _=>b := by
  refine ⟨(vals bg).getD i false,?_⟩
  funext x
  exact (good (freeze U bg x) bg).2.2 i (fun t ht=>by simp [freeze,Finset.disjoint_left.mp away ht])

theorem chain_const {N : Nat} {base : Input→List Bool} {F G : Input→Bool}
    (sourceF : Source N base F) (sourceG : Source N base G)
    (stopped : (∃b : Bool,F=fun _=>b) ∨ (∃b : Bool,G=fun _=>b)) (choice : Bool) :
    Source N base (fun x=>if choice then F x || G x else F x && G x) := by
  rcases stopped with ⟨b,rfl⟩|⟨b,rfl⟩ <;> cases b <;> cases choice <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,Bool.false_or,Bool.or_false,Bool.false_and,Bool.and_false,
      Bool.true_or,Bool.or_true,Bool.true_and,Bool.and_true] <;>
    assumption

theorem expand {N : Nat} {base now : Input→List Bool} {next : Input→Bool} (sz : Nat)
    (width : ∀x,(now x).length=sz) (old : Tracks N base now) (new : Source N base next) :
    Tracks N base (fun x=>now x++[next x]) := by
  intro k
  by_cases same : k=sz
  · have eq : (fun x=>(now x++[next x]).getD k false)=next := by
      funext x;rw [read_append,width,ite_eq_left same]
    rw [eq];exact new
  · have eq : (fun x=>(now x++[next x]).getD k false)=(fun x=>(now x).getD k false) := by
      funext x;rw [read_append,width,ite_eq_right same]
    rw [eq];exact old k

theorem base_tracks (N : Nat) (now : Input→List Bool) (width : ∀x,(now x).length=N) : Tracks N now now := by
  intro i
  by_cases early : i<N
  · exact Or.inr ⟨i,early,rfl⟩
  · refine Or.inl ⟨false,?_⟩
    funext x
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by rw [width];omega)]; rfl

theorem zero_step (z : Finset Nat) (xs : List SetV) (g : Gate) (rest : List Gate)
    (empty : redundantWires z xs (g::rest)=∅) :
    (xs.length∉z → joinsComponents xs g.inputs) ∧
    redundantWires z (xs++[if xs.length∈z then ∅ else gather xs g.inputs]) rest=∅ := by
  classical
  rw [redundantWires] at empty
  split at empty
  · simp at empty
  · rename_i other
    exact ⟨fun notFrozen=>by by_contra noJoin;exact other ⟨notFrozen,noJoin⟩,empty⟩

theorem propagate (gs : List Gate) (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2)
    (z : Finset Nat) (U : Region) (bg : Input) (N : Nat) (base vals : Input→List Bool) (xs : List SetV)
    (good : Respects vals xs) (intr : Intrinsic U xs) (empty : redundantWires z xs gs=∅)
    (old : Tracks N base (fun x=>vals (freeze U bg x))) :
    Tracks N base (fun x=>overwrite z gs (vals (freeze U bg x))) := by
  induction gs generalizing vals xs with
  | nil => exact old
  | cons g gs ih =>
    let s := if xs.length∈z then ∅ else gather xs g.inputs
    let val (x : Input) := if xs.length∈z then true else bit g (vals x)
    let next (x : Input) := vals x++[val x]
    have size (x : Input) : (vals x).length=xs.length := (good x x).1
    have leg := zero_step z xs g gs empty
    have sig : Source N base (fun x=>val (freeze U bg x)) := by
      by_cases used : xs.length∈z
      · exact Or.inl ⟨true,by funext x;simp [val,used]⟩
      have join := leg.1 used
      have splits : Forest.Splits xs g.inputs := by
        by_contra not
        obtain ⟨f,uni,change⟩ := join
        exact change (Forest.no_split uni (arity g (by simp)) not)
      obtain ⟨a,b,ids,_,_,_⟩ := splits
      rw [ids] at join
      have single := (parent_away intr join).imp (away_constant good bg a) (away_constant good bg b)
      rcases basis g (by simp) with op|op
      · simpa only [val,ite_eq_right used,bit,ids,List.map_cons,List.map_nil,op,GateOp.eval,List.all_cons,List.all_nil,
          id_eq,Bool.and_true,Bool.false_eq_true,ite_false] using (chain_const (old a) (old b) single false)
      · simpa only [val,ite_eq_right used,bit,ids,List.map_cons,List.map_nil,op,GateOp.eval,List.any_cons,List.any_nil,
          id_eq,Bool.or_false,ite_true] using (chain_const (old a) (old b) single true)
    have nGood : Respects next (xs++[s]) := by
      intro x y
      have step := supported z [g] x y (vals x) (vals y) xs (good x y)
      simpa only [next,val,s,overwrite,supportTail,size] using step
    have full := ih (fun t mem=>basis t (by simp [mem])) (fun t mem=>arity t (by simp [mem])) next (xs++[s]) nGood
      (extend_intrinsic intr _) leg.2 (expand xs.length (fun x=>size (freeze U bg x)) old sig)
    simpa only [overwrite,next,val,size] using full
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse

theorem suffix_empty (z : Finset Nat) (xs : List SetV) (pre post : List Gate)
    (all : redundantWires z xs (pre++post)=∅) :
    redundantWires z (xs++supportTail z xs pre) post=∅ := by
  induction pre generalizing xs with
  | nil => simpa [supportTail] using all
  | cons g gs ih =>
    have next := (zero_step z xs g (gs++post) all).2
    simpa only [supportTail,List.append_assoc,List.singleton_append] using ih _ next

def prefixSets (gs : List Gate) (out : V→Nat) (n : Nat) := start++supportTail (terminals out) start (gs.take n)
def prefixVals (gs : List Gate) (out : V→Nat) (n : Nat) (x : Input) := overwrite (terminals out) (gs.take n) (List.ofFn x)
def sources (gs : List Gate) (out : V→Nat) (n : Nat) (U : Region) (bg : Input) :=
  Source (13+n) (fun x=>prefixVals gs out n (freeze U bg x))

theorem project_sources {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    {n : Nat} (bound : n≤gs.length) {U : Region} (intr : Intrinsic U (prefixSets gs out n)) (bg : Input) (k : Nat) :
    sources gs out n U bg (fun x=>globalWire gs out k (freeze U bg x)) := by
  let z := terminals out
  let pre := gs.take n
  let post := gs.drop n
  let vals := prefixVals gs out n
  let base := fun x=>vals (freeze U bg x)
  have total : pre++post=gs := List.take_append_drop n gs
  have good : Respects vals (prefixSets gs out n) := fun x y=>supported z pre x y _ _ _ (start_valid x y)
  have width0 (x : Input) : (base x).length=13+n := by simp [base,vals,prefixVals,width,Nat.min_eq_left bound]
  have red : redundantWires z (prefixSets gs out n) post=∅ := by
    apply suffix_empty z start pre post
    rw [total]
    exact connected_redundant_empty arity h conn cap
  have part {g : Gate} (mem : g∈post) : g∈gs := total ▸ List.mem_append_right _ mem
  have all := propagate post (fun g hg=>basis g (part hg)) (fun g hg=>arity g (part hg)) z U bg (13+n) base vals
    (prefixSets gs out n) good intr red (base_tracks _ _ width0)
  have same (x : Input) : overwrite z post (vals x)=overwrite z gs (List.ofFn x) := by
    rw [←total,ov_append]; rfl
  change Source (13+n) base (fun x=>(overwrite z gs (List.ofFn (freeze U bg x))).getD k false)
  simpa only [same] using all k

theorem project_live {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    {n : Nat} (bound : n≤gs.length) {U : Region} (intr : Intrinsic U (prefixSets gs out n)) (bg : Input)
    (t : Fin gs.length) (k : Nat) : sources gs out n U bg (fun x=>live gs out t k (freeze U bg x)) := by
  by_cases safe : k<13+t.val
  · rw [sem_prefix gs out t k safe]
    exact project_sources basis arity h conn cap bound intr bg k
  · exact Or.inl ⟨false,by funext x;exact Forest.missing_live gs out t k (by omega) _⟩

theorem missing_freeze (U L S : Region) (sub : S⊆U) :
    freeze U (missing L) (missing S)=missing (S∪(L\U)) := by
  funext v
  by_cases inside : v∈U
  · simp [freeze,missing,inside]
  · have no : v∉S := fun yes=>inside (sub yes)
    simp [freeze,missing,inside,no]

theorem restricted_target {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (h : Correct gs out) (w : V) {S U : Region} (sub : S⊆U) (sm : S.card≤(line w∩U).card) :
    value gs out (outIndex h w) (freeze U (missing (line w)) (missing S))=false ↔ S=line w∩U := by
  let L := line w
  have split : (L\U)∪(L∩U)=L := by ext x;simp
  have slices : Disjoint (L\U) (L∩U) := Finset.disjoint_left.mpr (fun {_} a b=>(Finset.mem_sdiff.mp a).2 (Finset.mem_inter.mp b).2)
  have count := Finset.card_union_of_disjoint slices
  rw [split] at count
  have four : L.card=4 := line_size w
  have total : (S∪(L\U)).card≤4 := by have := Finset.card_union_le S (L\U);change S.card≤(L∩U).card at sm; omega
  have heavy : 9≤(supp (missing (S∪(L\U)))).card := by
    rw [complement,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have thirteen : (Finset.univ : Region).card=13 := by decide
    omega
  rw [missing_freeze _ _ _ sub,normalized basis h w _ (index_eq h w) _ heavy,←h w _ heavy]
  change accepts gs (out w) (S∪(L\U)) ↔ S=L∩U
  rw [statement h total]
  constructor
  · intro eq
    ext x
    by_cases hu : x∈U
    · have atX := Finset.ext_iff.mp eq x
      simpa only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,hu,not_true_eq_false,and_false,or_false,and_true] using atX
    · simp [hu,show x∉S from fun yes=>hu (sub yes)]
  · intro eq;rw [eq,Finset.union_comm];exact split
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse
def Closed (U : Region) (xs : List SetV) := ∀i : Nat, xs.getD i ∅⊆U ∨ Disjoint (xs.getD i ∅) U

def Internal (gs : List Gate) (out : V→Nat) (n : Nat) (U : Region) (F : Input→Bool) :=
  (∃b : Bool, F=fun _=>b) ∨ ∃i<13+n, (prefixSets gs out n).getD i ∅⊆U ∧ F=fun x=>(prefixVals gs out n x).getD i false

theorem internal_of_source {gs : List Gate} {out : V→Nat} {n : Nat} {U : Region} {bg : Input} {F : Input→Bool}
    (whole : Closed U (prefixSets gs out n)) (cert : sources gs out n U bg F) : Internal gs out n U F := by
  rcases cert with const|⟨i,small,rfl⟩
  · exact Or.inl const
  have good : Respects (prefixVals gs out n) (prefixSets gs out n) := fun x y=>supported _ _ x y _ _ _ (start_valid x y)
  rcases whole i with inside|away
  · refine Or.inr ⟨i,small,inside,?_⟩
    funext x
    exact (good _ x).2.2 i (fun v hv=>by simp [freeze,inside hv])
  · exact Or.inl (away_constant good bg i away)

theorem disjunction_one {α : Type} {A B : α→Prop} {D : α→Prop} {p : α} (hp : D p)
    (law : ∀s, D s → (A s ∨ B s ↔ s=p)) :
    (∀s,D s → (A s ↔ s=p)) ∨ (∀s,D s → (B s ↔ s=p)) := by
  rcases (law p hp).2 rfl with left|right
  · exact Or.inl (fun s hs=>⟨fun yes=>(law s hs).1 (Or.inl yes),fun eq=>eq ▸ left⟩)
  · exact Or.inr (fun s hs=>⟨fun yes=>(law s hs).1 (Or.inr yes),fun eq=>eq ▸ right⟩)

theorem component_slices {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    {n : Nat} (bound : n≤gs.length) {U : Region} (intr : Intrinsic U (prefixSets gs out n))
    (whole : Closed U (prefixSets gs out n)) (w : V) :
    ∃F G : Input→Bool, Internal gs out n U F ∧ Internal gs out n U G ∧
      ∀S : Region, S⊆U → S.card≤(line w∩U).card → (Active F S ∧ Active G S ↔ S=line w∩U) := by
  let L := line w
  let t := outIndex h w
  let fx := freeze U (missing L)
  let wire (k : Nat) := fun x=>live gs out t k (fx x)
  let val := fun x=>value gs out t (fx x)
  have leg (k : Nat) : Internal gs out n U (wire k) := internal_of_source whole (project_live basis arity h conn cap bound intr _ t k)
  have law (S : Region) (sub : S⊆U) (small : S.card≤(line w∩U).card) : Active val S ↔ S=line w∩U :=
    restricted_target basis h w sub small
  cases ids : gs[t.val].inputs with
  | nil =>
    have const : Internal gs out n U val := Or.inl ⟨gs[t.val].op.eval [],by funext;simp [val,value,bit,ids]⟩
    refine ⟨val,val,const,const,?_⟩
    intro S sub small
    simpa only [and_self] using law S sub small
  | cons a tail =>
    cases tail with
    | nil =>
      have eq : val=wire a := by
        funext x
        rcases basis gs[t.val] (List.getElem_mem _) with gate|gate <;> simp [val,value,bit,ids,gate,GateOp.eval,wire,live]
      refine ⟨wire a,wire a,leg a,leg a,?_⟩
      intro S sub small
      simpa only [eq,and_self] using law S sub small
    | cons b tail =>
      cases tail with
      | cons c cs => have len := arity gs[t.val] (List.getElem_mem t.isLt);simp [ids] at len
      | nil =>
        rcases basis gs[t.val] (List.getElem_mem _) with gate|gate
        · let D := fun S : Region=>S⊆U ∧ S.card≤(line w∩U).card
          have one : ∀S : Region,D S → (Active (wire a) S ∨ Active (wire b) S ↔ S=line w∩U) := by
            intro S sm
            have logic (p q : Bool) : (p=false ∨ q=false) ↔ (p && q)=false := by cases p <;> cases q <;> decide
            exact (logic _ _).trans (by simpa [Active,wire,val,live,value,bit,ids,gate,GateOp.eval] using law S sm.1 sm.2)
          rcases disjunction_one (p:=line w∩U) (show D _ from ⟨Finset.inter_subset_right,le_rfl⟩) one with left|right
          · exact ⟨wire a,wire a,leg a,leg a,fun S sub small=>and_self_iff.trans (left S ⟨sub,small⟩)⟩
          · exact ⟨wire b,wire b,leg b,leg b,fun S sub small=>and_self_iff.trans (right S ⟨sub,small⟩)⟩
        · refine ⟨wire a,wire b,leg a,leg b,?_⟩
          intro S sub small
          simpa [Active,wire,val,live,value,bit,ids,gate,GateOp.eval] using law S sub small
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component
def Linked (xs : List SetV) (x y : V) := ∀f : V→V, Uniform f xs → f x=f y
noncomputable def block (xs : List SetV) (p : V) : Region := by
  classical
  exact Finset.univ.filter (Linked xs p)
theorem in_block {xs : List SetV} {p q : V} : q∈block xs p ↔ Linked xs p q := by
  classical
  simp [block]
theorem self_mem (xs : List SetV) (p : V) : p∈block xs p := in_block.mpr (fun _ _=>rfl)
theorem block_intr (xs : List SetV) (p : V) : Intrinsic (block xs p) xs :=
  fun f good _ hx _ hy=>((in_block.mp hx) f good).symm.trans ((in_block.mp hy) f good)
theorem block_whole (xs : List SetV) (p : V) : Closed (block xs p) xs := by
  intro i
  classical
  by_cases away : Disjoint (xs.getD i ∅) (block xs p)
  · exact Or.inr away
  obtain ⟨v,vs,vp⟩ := Finset.not_disjoint_iff.mp away
  exact Or.inl (fun x hx=>in_block.mpr (fun f good=>((in_block.mp vp) f good).trans ((available_hom good (readable xs i)) v vs x hx)))
theorem incl_at {xs : List SetV} {i : Nat} {p : V} (hp : p∈xs.getD i ∅) :
    xs.getD i ∅⊆block xs p := fun x hx=>in_block.mpr (fun _ good=>(available_hom good (readable xs i)) p hp x hx)

theorem combine_blocks {xs : List SetV} {A B a b : Region} {p q : V} (ca : Intrinsic A xs) (cb : Intrinsic B xs)
    (wa : Closed A xs) (wb : Closed B xs) (ap : a⊆A) (bp : b⊆B) (pa : p∈a) (qb : q∈b) :
    Intrinsic (A∪B) (xs++[a∪b]) ∧ Closed (A∪B) (xs++[a∪b]) := by
  constructor
  · intro f good
    have tail : Hom f (a∪b) := good _ (by simp)
    have old : Uniform f xs := fun t ht=>good t (List.mem_append_left _ ht)
    have bridge := tail p (Finset.mem_union_left b pa) q (Finset.mem_union_right a qb)
    have base (x : V) (mem : x∈A∪B) : f x=f p := by
      rcases Finset.mem_union.mp mem with left|right
      · exact ca f old x left p (ap pa)
      · exact (cb f old x right q (bp qb)).trans bridge.symm
    exact fun x hx y hy=>(base x hx).trans (base y hy).symm
  · intro i
    rw [read_append]
    split
    · exact Or.inl (Finset.union_subset_union ap bp)
    · rcases wa i with left|left
      · exact Or.inl (left.trans Finset.subset_union_left)
      rcases wb i with right|right
      · exact Or.inl (right.trans Finset.subset_union_right)
      · exact Or.inr (Finset.disjoint_union_right.mpr ⟨left,right⟩)

theorem genuine_blocks {xs : List SetV} {i k : Nat} (join : joinsComponents xs [i,k])
    (hi : (xs.getD i ∅).Nonempty) (hk : (xs.getD k ∅).Nonempty) :
    ∃ A B : Region, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ xs.getD i ∅⊆A ∧ xs.getD k ∅⊆B ∧
      Intrinsic A xs ∧ Closed A xs ∧ Intrinsic B xs ∧ Closed B xs ∧
      Intrinsic (A∪B) (xs++[gather xs [i,k]]) ∧ Closed (A∪B) (xs++[gather xs [i,k]]) := by
  obtain ⟨p,hp⟩ := hi
  obtain ⟨q,hq⟩ := hk
  let A := block xs p
  let B := block xs q
  have ap : xs.getD i ∅⊆A := incl_at hp
  have bp : xs.getD k ∅⊆B := incl_at hq
  have dis : Disjoint A B := by
    obtain ⟨f,good,no⟩ := join
    apply Finset.disjoint_left.mpr
    intro x xa xb
    have eq := ((in_block.mp xa) f good).trans ((in_block.mp xb) f good).symm
    apply no
    have fixed (v : V) (hv : v∈gather xs [i,k]) : f v=f p := by
      simp only [gather,Finset.union_empty,Finset.mem_union] at hv
      rcases hv with l|r
      · exact (available_hom good (readable xs i)) v l p hp
      · exact ((available_hom good (readable xs k)) v r q hq).trans eq.symm
    exact fun v hv w hw=>(fixed v hv).trans (fixed w hw).symm
  refine ⟨A,B,⟨p,ap hp⟩,⟨q,bp hq⟩,dis,ap,bp,block_intr _ _,block_whole _ _,block_intr _ _,block_whole _ _,?_⟩
  simpa only [gather,Finset.union_empty] using combine_blocks (block_intr xs p) (block_intr xs q) (block_whole xs p) (block_whole xs q) ap bp hp hq
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component

def Ready (gs : List Gate) (out : V→Nat) (n : Nat) (U : Region) :=
  Intrinsic U (prefixSets gs out n) ∧ Closed U (prefixSets gs out n)

theorem next_sets (gs : List Gate) (out : V→Nat) (j : Fin gs.length) (hide : 13+j.val∉terminals out) :
    prefixSets gs out (j.val+1)=prefixSets gs out j.val++[gather (prefixSets gs out j.val) gs[j.val].inputs] := by
  unfold prefixSets
  rw [List.take_succ_eq_append_getElem j.isLt,tail_append,←List.append_assoc]
  have len : (start++supportTail (terminals out) start (gs.take j.val)).length=13+j.val := by simp [start,tail_len];omega
  simp only [supportTail,len,ite_eq_right hide]

theorem actual_join {gs : List Gate} {out : V→Nat} (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (j : Fin gs.length) (hide : 13+j.val∉terminals out) :
    ∃ (a b : Nat) (A B : Region), gs[j.val].inputs=[a,b] ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      (region gs out j a).Nonempty ∧ (region gs out j b).Nonempty ∧ region gs out j a⊆A ∧ region gs out j b⊆B ∧
      Ready gs out j.val A ∧ Ready gs out j.val B ∧ Ready gs out (j.val+1) (A∪B) := by
  obtain ⟨a,b,ids,na,nb,_⟩ := Bypass.connected_split arity h conn cap j hide
  have red := connected_redundant_empty arity h conn cap
  have join := joins_of_not_redundant j hide (by simp [red])
  rw [ids] at join
  obtain ⟨A,B,ha,hb,dis,sa,sb,ia,wa,ib,wb,ic,wc⟩ := genuine_blocks join na nb
  refine ⟨a,b,A,B,ids,ha,hb,dis,na,nb,sa,sb,⟨ia,wa⟩,⟨ib,wb⟩,?_⟩
  unfold Ready
  rw [next_sets gs out j hide,ids]
  exact ⟨ic,wc⟩

def Realizes (gs : List Gate) (out : V→Nat) (n : Nat) (U : Region) := ∀w : V, ∃F G : Input→Bool,
    Internal gs out n U F ∧ Internal gs out n U G ∧
    ∀S : Region, S⊆U → S.card≤(line w∩U).card → (Active F S ∧ Active G S ↔ S=line w∩U)

theorem tree_slices {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (j : Fin gs.length) (hide : 13+j.val∉terminals out) :
    ∃ (a b : Nat) (A B : Region), gs[j.val].inputs=[a,b] ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      region gs out j a⊆A ∧ region gs out j b⊆B ∧
      Realizes gs out j.val A ∧ Realizes gs out j.val B ∧ Realizes gs out (j.val+1) (A∪B) := by
  obtain ⟨a,b,A,B,ids,ha,hb,dis,_,_,sa,sb,ra,rb,rc⟩ := actual_join arity h conn cap j hide
  exact ⟨a,b,A,B,ids,ha,hb,dis,sa,sb,
    component_slices basis arity h conn cap j.isLt.le ra.1 ra.2,
    component_slices basis arity h conn cap j.isLt.le rb.1 rb.2,
    component_slices basis arity h conn cap j.isLt rc.1 rc.2⟩
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse

def meet (F G : Input→Bool) : Input→Bool := fun x=>F x || G x
def join (F G : Input→Bool) : Input→Bool := fun x=>F x && G x
theorem meet_on (F G : Input→Bool) (S : Region) : Active (meet F G) S ↔ Active F S ∧ Active G S := by simp [Active,meet]
theorem join_on (F G : Input→Bool) (S : Region) : Active (join F G) S ↔ Active F S ∨ Active G S := by
  let a := F (missing S)
  let b := G (missing S)
  change (a && b)=false ↔ a=false ∨ b=false
  cases a <;> cases b <;> decide
theorem meet_local {F G : Input→Bool} {U : Region} (a : Local F U) (b : Local G U) : Local (meet F G) U :=
  fun x y eq=>congrArg₂ (· || ·) (a x y eq) (b x y eq)
theorem internal_local {gs : List Gate} {out : V→Nat} {n : Nat} {U : Region} {F : Input→Bool}
    (proof : Internal gs out n U F) : Local F U := by
  rcases proof with ⟨c,rfl⟩|⟨i,_,sub,rfl⟩
  · exact fun _ _ _=>rfl
  intro x y same
  exact (supported _ _ x y _ _ _ (start_valid x y)).2.2 i (fun v hv=>same v (sub hv))

theorem minimal_inside {F : Input→Bool} {U T : Region} (loc : Local F U) (min : Minimal F T) : T⊆U := by
  have eq := min.2 (T∩U) ((project loc T).trans min.1) (Finset.card_le_card Finset.inter_subset_left)
  exact eq ▸ Finset.inter_subset_right

theorem capture {F G : Input→Bool} {U T : Region} (lf : Local F U) (lg : Local G U) (sub : T⊆U)
    (law : ∀S : Region,S⊆U → S.card≤T.card → (Active F S ∧ Active G S ↔ S=T)) : Minimal (meet F G) T := by
  refine ⟨(meet_on F G T).2 ((law T sub le_rfl).2 rfl),?_⟩
  intro S on small
  have yes := (meet_on F G S).1 on
  have subS : S∩U⊆S := Finset.inter_subset_left
  have eq := (law (S∩U) Finset.inter_subset_right ((Finset.card_le_card subS).trans small)).1
    ⟨(project lf S).trans yes.1,(project lg S).trans yes.2⟩
  exact (Finset.eq_of_subset_of_card_le (eq ▸ subS) small).symm

theorem choose_active {H F G : Input→Bool} {T : Region} (m : Minimal H T)
    (law : ∀s,Active H s ↔ Active F s ∨ Active G s) : Minimal F T ∨ Minimal G T := by
  rcases (law T).1 m.1 with f|g
  · exact Or.inl ⟨f,fun S on small=>m.2 S ((law S).2 (Or.inl on)) small⟩
  · exact Or.inr ⟨g,fun S on small=>m.2 S ((law S).2 (Or.inr on)) small⟩

theorem piece_min {F G : Input→Bool} {A B T : Region} (lf : Local F A) (lg : Local G B)
    (sep : Disjoint A B) (m : Minimal (meet F G) T) : Minimal F (T∩A) ∧ Minimal G (T∩B) :=
  ⟨Forest.project_piece lf lg sep m (meet_on F G),Forest.project_piece lg lf sep.symm m (fun S=>(meet_on F G S).trans and_comm)⟩

theorem missed {A B T : Region} (sep : Disjoint A B) (cross : (T∩B).Nonempty) : ¬T⊆A := by
  obtain ⟨x,h⟩ := cross
  exact fun sub=>Finset.disjoint_left.mp sep (sub (Finset.mem_inter.mp h).1) (Finset.mem_inter.mp h).2

theorem mix_meet {F G H K : Input→Bool} {A B T : Region} (lf : Local F A) (lg : Local G B) (lk : Local K A)
    (sep : Disjoint A B) (m : Minimal (meet H K) T) (root : ∀S,Active H S ↔ Active F S ∧ Active G S) :
    Minimal G (T∩B) := by
  apply Forest.project_piece lg (meet_local lf lk) sep.symm m
  intro S
  rw [meet_on,root,meet_on]
  tauto

theorem mix_join {F G H K : Input→Bool} {A B T : Region} (lf : Local F A) (lg : Local G B) (lk : Local K A)
    (sep : Disjoint A B) (cross : (T∩B).Nonempty) (m : Minimal (meet H K) T)
    (root : ∀S,Active H S ↔ Active F S ∨ Active G S) : Minimal K (T∩A) ∧ Minimal G (T∩B) := by
  have disj (S : Region) : Active (meet H K) S ↔ Active (meet F K) S ∨ Active (meet K G) S := by
    simp only [meet_on,root]
    tauto
  rcases choose_active m disj with impossible|pair
  · exact False.elim (missed sep cross (minimal_inside (meet_local lf lk) impossible))
  · exact piece_min lk lg sep pair
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse
abbrev Signal := Input→Bool
def Visible (P Q : Signal→Prop) (H F : Signal) := P F ∨ Q F ∨ F=H
def Charge (P : Signal→Prop) (S : Region) := ∃F,P F ∧ Minimal F S
def Bill (dualAnd : Bool) (P Q : Signal→Prop) (f g : Signal) (X Y : Region) :=
  (Charge P X ∧ Charge Q Y) ∨ (dualAnd=true ∧ ((Minimal f X ∧ Charge P X) ∨ (Minimal g Y ∧ Charge Q Y)))

theorem same_meet (F : Signal) : meet F F=F := by funext x;simp [meet]
theorem switch_meet {F G : Signal} {T : Region} (m : Minimal (meet F G) T) : Minimal (meet G F) T := by
  have e : meet G F=meet F G := funext (fun x=>Bool.or_comm (G x) (F x))
  exact e ▸ m

theorem swapped {dualAnd : Bool} {P Q : Signal→Prop} {f g : Signal} {X Y : Region} :
    Bill dualAnd Q P g f Y X → Bill dualAnd P Q f g X Y := by
  intro yes
  rcases yes with ⟨a,b⟩|⟨good,left|right⟩
  · exact Or.inl ⟨b,a⟩
  · exact Or.inr ⟨good,Or.inr left⟩
  · exact Or.inr ⟨good,Or.inl right⟩

theorem charge_mixed {tag : Bool} {P Q : Signal→Prop} {f g H K : Signal} {A B T : Region}
    (lf : Local f A) (lg : Local g B) (lk : Local K A) (pk : P K) (qg : Q g)
    (sep : Disjoint A B) (cross : (T∩B).Nonempty) (m : Minimal (meet H K) T)
    (law : ∀S,Active H S ↔ (if tag then Active f S ∧ Active g S else Active f S ∨ Active g S)) :
    Bill tag P Q f g (T∩A) (T∩B) := by
  cases tag with
  | true =>
    have pay := mix_meet lf lg lk sep m (by simpa using law)
    exact Or.inr ⟨rfl,Or.inr ⟨pay,g,qg,pay⟩⟩
  | false =>
    obtain ⟨one,two⟩ := mix_join lf lg lk sep cross m (by simpa using law)
    exact Or.inl ⟨⟨K,pk,one⟩,⟨g,qg,two⟩⟩

theorem charge_cut {tag : Bool} {P Q : Signal→Prop} {f g H : Signal} {A B T : Region}
    (lp : ∀F,P F→Local F A) (lq : ∀F,Q F→Local F B) (pf : P f) (qg : Q g)
    (sep : Disjoint A B) (xa : (T∩A).Nonempty) (yb : (T∩B).Nonempty)
    (law : ∀S,Active H S ↔ (if tag then Active f S ∧ Active g S else Active f S ∨ Active g S))
    {F G : Signal} (first : Visible P Q H F) (second : Visible P Q H G) (m : Minimal (meet F G) T) :
    Bill tag P Q f g (T∩A) (T∩B) := by
  have left := lp _ pf
  have right := lq _ qg
  have rev (S) : Active H S ↔ (if tag then Active g S ∧ Active f S else Active g S ∨ Active f S) := by
    rw [law];cases tag <;> simp [and_comm,or_comm]
  have mixedA (K : Signal) (pk : P K) (one : Minimal (meet H K) T) :=
    charge_mixed left right (lp K pk) pk qg sep yb one law
  have mixedB (K : Signal) (qk : Q K) (one : Minimal (meet H K) T) :=
    swapped (charge_mixed right left (lq K qk) qk pf sep.symm xa one rev)
  rcases first with fp|fq|rfl
  · rcases second with gp|gq|rfl
    · exact False.elim (missed sep yb (minimal_inside (meet_local (lp _ fp) (lp _ gp)) m))
    · obtain ⟨a,b⟩ := piece_min (lp _ fp) (lq _ gq) sep m
      exact Or.inl ⟨⟨F,fp,a⟩,⟨G,gq,b⟩⟩
    · exact mixedA _ fp (switch_meet m)
  · rcases second with gp|gq|rfl
    · obtain ⟨a,b⟩ := piece_min (lp _ gp) (lq _ fq) sep (switch_meet m)
      exact Or.inl ⟨⟨G,gp,a⟩,⟨F,fq,b⟩⟩
    · exact False.elim (missed sep.symm xa (minimal_inside (meet_local (lq _ fq) (lq _ gq)) m))
    · exact mixedB _ fq (switch_meet m)
  · rcases second with gp|gq|rfl
    · exact mixedA _ gp m
    · exact mixedB _ gq m
    · rw [same_meet] at m
      cases tag with
      | false =>
        rcases choose_active m (by simpa using law) with one|two
        · exact False.elim (missed sep yb (minimal_inside left one))
        · exact False.elim (missed sep.symm xa (minimal_inside right two))
      | true =>
        have both := law
        simp only [ite_true] at both
        exact Or.inl ⟨⟨f,pf,Forest.project_piece left right sep m both⟩,
          ⟨g,qg,Forest.project_piece right left sep.symm m (fun S=>(both S).trans and_comm)⟩⟩
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse

theorem prefix_read {gs : List Gate} (out : V→Nat) {n k : Nat} (limit : n≤gs.length) (old : k<13+n) :
    (fun x=>(prefixVals gs out n x).getD k false)=globalWire gs out k := by
  funext x
  unfold prefixVals globalWire
  conv => rhs; rw [←List.take_append_drop n gs,ov_append]
  exact (ov_stable _ _ _ _ (by simp only [width,List.length_ofFn,List.length_take,Nat.min_eq_left limit];omega)).symm

theorem earlier {gs : List Gate} {out : V→Nat} {n i : Nat} {U : Region} (len : n≤gs.length) (old : i<13+n)
    (sub : (prefixSets gs out n).getD i ∅⊆U) : Internal gs out n U (globalWire gs out i) :=
  Or.inr ⟨i,old,sub,(prefix_read _ len old).symm⟩

theorem node_view {gs : List Gate} {out : V→Nat} {j : Fin gs.length} (hide : 13+j.val∉terminals out)
    {A B : Region} (wa : Ready gs out j.val A) (wb : Ready gs out j.val B)
    {F : Signal} (cert : Internal gs out (j.val+1) (A∪B) F) :
    Visible (Internal gs out j.val A) (Internal gs out j.val B) (globalWire gs out (13+j.val)) F := by
  rcases cert with fixed|⟨i,lim,sub,eq⟩
  · exact Or.inl (Or.inl fixed)
  rw [prefix_read out j.isLt lim] at eq
  by_cases atRoot : i=13+j.val
  · exact Or.inr (Or.inr (atRoot ▸ eq))
  have old : i<13+j.val := by omega
  have len : (prefixSets gs out j.val).length=13+j.val := by simp [prefixSets,start,tail_len];omega
  rw [next_sets gs out j hide,read_append,len,ite_eq_right atRoot] at sub
  rw [eq]
  rcases wa.2 i with inc|awayA
  · exact Or.inl (earlier j.isLt.le old inc)
  rcases wb.2 i with inc|awayB
  · exact Or.inr (Or.inl (earlier j.isLt.le old inc))
  · refine Or.inl (earlier j.isLt.le old (fun v hv=>?_))
    rcases Finset.mem_union.mp (sub hv) with a|b
    · exact a
    · exact False.elim (Finset.disjoint_left.mp awayB hv b)

def isDualAnd : GateOp→Bool
  | .or => true
  | _ => false

theorem merge_charges {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (j : Fin gs.length) (hide : 13+j.val∉terminals out) :
    ∃ (a b : Nat) (A B : Region), gs[j.val].inputs=[a,b] ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      region gs out j a⊆A ∧ region gs out j b⊆B ∧ Ready gs out j.val A ∧ Ready gs out j.val B ∧ Ready gs out (j.val+1) (A∪B) ∧
      ∀w : V, (line w∩A).Nonempty → (line w∩B).Nonempty →
      Bill (isDualAnd gs[j.val].op) (Internal gs out j.val A) (Internal gs out j.val B)
        (globalWire gs out a) (globalWire gs out b) (line w∩A) (line w∩B) := by
  obtain ⟨a,b,A,B,ids,ha,hb,dis,na,nb,sa,sb,ra,rb,rc⟩ := actual_join arity h conn cap j hide
  have va := Bypass.nonempty_read j a na
  have vb := Bypass.nonempty_read j b nb
  have pf := earlier j.isLt.le va sa
  have qg := earlier j.isLt.le vb sb
  let H := globalWire gs out (13+j.val)
  have op (S : Region) : Active H S ↔ (if isDualAnd gs[j.val].op then Active (globalWire gs out a) S ∧ Active (globalWire gs out b) S
      else Active (globalWire gs out a) S ∨ Active (globalWire gs out b) S) := by
    rw [←sem_prefix gs out j a va,←sem_prefix gs out j b vb]
    unfold H
    rw [Forest.stored_value j hide]
    rcases basis gs[j.val] (List.getElem_mem _) with tag|tag
    · simpa [Active,value,bit,ids,tag,isDualAnd,GateOp.eval,live,join] using join_on (live gs out j a) (live gs out j b) S
    · simp [Active,value,bit,ids,tag,isDualAnd,GateOp.eval,live]
  refine ⟨a,b,A,B,ids,ha,hb,dis,sa,sb,ra,rb,rc,?_⟩
  intro w onA onB
  let T := line w∩(A∪B)
  obtain ⟨F,G,one,two,law⟩ := component_slices basis arity h conn cap j.isLt rc.1 rc.2 w
  have m := capture (internal_local one) (internal_local two) Finset.inter_subset_right law
  have xa : T∩A=line w∩A := by ext x;simp [T]
  have yb : T∩B=line w∩B := by ext x;simp [T]
  have yes := charge_cut (fun _=>internal_local) (fun _=>internal_local) pf qg dis (xa.symm ▸ onA) (yb.symm ▸ onB) op
    (node_view hide ra rb one) (node_view hide ra rb two) m
  change Bill _ _ _ _ _ (T∩A) (T∩B) at yes
  simpa only [xa,yb] using yes
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse Plane920.Forest
open Plane920.Forest26
theorem earlier_pair {gs : List Gate} {out : V→Nat} {T : Region} {i : Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2)
    (m : Earliest gs out i T) (three : T.card=3) (free : i∉defects (terminals out) start gs) :
    ∃ U⊆T, U.card=2 ∧ ∃k < i, Own gs out k U ∧ Conjunction gs k := by
  obtain ⟨j,a,b,idx,gate,ids,_,_⟩ := genuine basis arity m (by omega)
  have nz := (Finset.mem_sdiff.mp m.1.1).2
  have nf : 13+j.val∉terminals out := idx ▸ nz
  have split := (defect_cases (terminals out) start gs j (by simpa [start] using nf)).resolve_right
    (by simpa only [show start.length=13 from by simp [start],idx] using free)
  obtain ⟨c,d,cd,_,_,sep0⟩ := split
  rw [ids,List.cons.injEq,List.cons.injEq] at cd
  obtain ⟨rfl,rfl,_⟩ := cd
  let u := region gs out j a
  let v := region gs out j b
  have sep : Disjoint u v := sep0
  have eq : globalWire gs out i=value gs out j := idx ▸ stored_value j nf
  have orig := m.1.2
  rw [eq] at orig
  have both (s : Region) : Active (value gs out j) s ↔ Active (live gs out j a) s ∧ Active (live gs out j b) s := by
    simp [Active,value,bit,ids,gate,GateOp.eval,live]
  have af : Local (live gs out j a) u := live_local gs out j a
  have bf : Local (live gs out j b) v := live_local gs out j b
  have left := project_piece af bf sep orig both
  have right := project_piece bf af sep.symm orig (fun s => (both s).trans and_comm)
  have union := exact_union af bf sep orig both
  have disT : Disjoint (T∩u) (T∩v) := sep.mono Finset.inter_subset_right Finset.inter_subset_right
  have total : (T∩u).card+(T∩v).card=3 := by
    rw [←Finset.card_union_of_disjoint disT,union,three]
  have smaller {k : Nat} {s : Region} (leg : Minimal (live gs out j k) (T∩s)) : (T∩s).card<3 := by
    by_contra! large
    have same := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (show T.card≤(T∩s).card by omega)
    rw [same] at leg
    have hi := live_before j k leg (by omega)
    have lo := m.2 k (hidden j k leg (by omega))
    omega
  have lo := smaller left
  have hi := smaller right
  have finish {k : Nat} {s : Region} (leg : Minimal (live gs out j k) (T∩s)) (size : (T∩s).card=2) :
      ∃ U⊆T, U.card=2 ∧ ∃k < i, Own gs out k U ∧ Conjunction gs k := by
    have sig := hidden j k leg size.ge
    obtain ⟨z,first⟩ := first (show ∃z, Own gs out z (T∩s) from ⟨k,sig⟩)
    exact ⟨_,Finset.inter_subset_left,size,z,lt_of_le_of_lt (first.2 k sig) (idx ▸ live_before j k leg size.ge),first.1,typed basis arity first size.ge⟩
  by_cases pair : (T∩u).card=2
  · exact finish left pair
  · exact finish right (by omega)

noncomputable def witnesses (gs : List Gate) (out : V→Nat) (j : Fin gs.length) (U T : Region) : Finset Nat := by
  classical
  exact (paid (terminals out) 13 gs.length).filter (fun k=>k<13+j.val ∧ Conjunction gs k ∧ region gs out j k⊆U ∧
    ∃W⊆T,2≤W.card ∧ Minimal (globalWire gs out k) W)

theorem localize_witness {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {U T W : Region} {k : Nat}
    (whole : Ready gs out j.val U) (st : T⊆U) (sub : W⊆T) (big : 2≤W.card) (prior : k<13+j.val)
    (own : Own gs out k W) (gate : Conjunction gs k) : k∈witnesses gs out j U T := by
  classical
  have localW : Local (globalWire gs out k) (region gs out j k) := sem_prefix gs out j k prior ▸ live_local _ _ _ _
  have within := minimal_inside localW own.2
  have inside : region gs out j k⊆U := by
    rcases whole.2 k with inc|away
    · exact inc
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<W.card by omega)
    exact False.elim (Finset.disjoint_left.mp away (within hx) (st (sub hx)))
  exact Finset.mem_filter.mpr ⟨own.1,prior,gate,inside,W,sub,big,own.2⟩

theorem internal_payment {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {U T : Region}
    (claim : Charge (Internal gs out j.val U) T) (big : 2≤T.card) : ∃ k<13+j.val, Own gs out k T := by
  obtain ⟨F,src,m⟩ := claim
  rcases src with ⟨b,rfl⟩|⟨k,bound,_,rfl⟩
  · have eq := m.2 ∅ (show Active (fun _=>b) ∅ from m.1) (by simp)
    rw [←eq] at big; simp at big
  · exact ⟨k,bound,hidden j k m big⟩

theorem physical_cost {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {U T : Region}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (ready : Ready gs out j.val U) (sub : T⊆U)
    (small : T.card≤3) (claim : Charge (Internal gs out j.val U) T) :
    T.card-1≤(witnesses gs out j U T).card := by
  classical
  by_cases big : 2≤T.card
  · obtain ⟨k,prev,own⟩ := internal_payment claim big
    obtain ⟨i,all⟩ := first (show ∃i,Own gs out i T from ⟨k,own⟩)
    have old : i<13+j.val := lt_of_le_of_lt (all.2 k own) prev
    have one := localize_witness ready sub (Finset.Subset.refl T) big old all.1 (Forest26.typed basis arity all big)
    by_cases three : T.card=3
    · have empty : Forest26.defects (terminals out) start gs=∅ := Finset.subset_empty.mp
        ((connected_redundant_empty arity h conn cap) ▸ overlap_is_redundant (terminals out) start gs arity)
      obtain ⟨W,ws,num,z,before,data,type⟩ := earlier_pair basis arity all three (by simp [empty])
      have two := localize_witness ready sub ws num.ge (before.trans old) data type
      have ne : i≠z := by
        rintro rfl
        have eq := minima_eq all.1.2 data.2
        exact (by decide : (3:Nat)≠2) (three.symm.trans ((congrArg Finset.card eq).trans num))
      have count := Finset.one_lt_card.mpr ⟨i,one,z,two,ne⟩
      omega
    · have count := Finset.card_pos.mpr ⟨i,one⟩
      omega
  · omega

theorem disjoint_costs {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {U V' T R : Region}
    (overlap : (T∩R).card≤1) : Disjoint (witnesses gs out j U T) (witnesses gs out j V' R) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k a b
  obtain ⟨W,wt,lo,m⟩ := (Finset.mem_filter.mp a).2.2.2.2
  obtain ⟨Q,qr,_,n⟩ := (Finset.mem_filter.mp b).2.2.2.2
  have eq := minima_eq m n
  have upper := Finset.card_le_card (Finset.subset_inter wt (show W⊆R from eq ▸ qr))
  omega
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse Plane920.Forest

noncomputable def pool (gs : List Gate) (out : V→Nat) (n : Nat) (U : Region) : Finset Nat := by
  classical
  let xs := prefixSets gs out n
  exact (paid (terminals out) 13 gs.length).filter (fun k=>k<13+n ∧ Conjunction gs k ∧
    (xs.getD k ∅).Nonempty ∧ xs.getD k ∅⊆U)

theorem in_pool {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {U T : Region} :
    witnesses gs out j U T⊆pool gs out j.val U := by
  classical
  intro k mem
  obtain ⟨paid,old,gate,inside,W,_,big,m⟩ := Finset.mem_filter.mp mem
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<W.card by omega)
  have localW : Local (globalWire gs out k) (region gs out j k) := sem_prefix gs out j k old ▸ live_local _ _ _ _
  exact Finset.mem_filter.mpr ⟨paid,old,gate,⟨x,minimal_inside localW m hx⟩,inside⟩

theorem sum_cost {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {U : Region}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (ready : Ready gs out j.val U) (E : Finset V)
    (small : ∀w∈E,(line w∩U).card≤3) (claims : ∀w∈E,Charge (Internal gs out j.val U) (line w∩U)) :
    ∑w∈E,((line w∩U).card-1)≤(pool gs out j.val U).card := by
  classical
  let set := fun w=>witnesses gs out j U (line w∩U)
  have sep {u v : V} (ne : u≠v) : Disjoint (set u) (set v) := by
    apply disjoint_costs
    have sub : (line u∩U)∩(line v∩U) ⊆ line u∩line v := fun x hx=>by
      obtain ⟨a,b⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp a).1,(Finset.mem_inter.mp b).1⟩
    exact (Finset.card_le_card sub).trans (OrSupport.line_pair u v ne)
  calc
    _ ≤ ∑w∈E,(set w).card := Finset.sum_le_sum (fun w mem=>physical_cost basis arity h conn cap ready
      Finset.inter_subset_right (small w mem) (claims w mem))
    _ = (E.biUnion set).card := (Finset.card_biUnion (fun _ _ _ _ ne=>sep ne)).symm
    _ ≤ _ := Finset.card_le_card (Finset.biUnion_subset.mpr (fun _ _=>in_pool))

theorem pool_disjoint (gs : List Gate) (out : V→Nat) (n : Nat) {A B : Region} (sep : Disjoint A B) :
    Disjoint (pool gs out n A) (pool gs out n B) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k ka kb
  obtain ⟨_,_,_,⟨p,hp⟩,sa⟩ := Finset.mem_filter.mp ka
  exact Finset.disjoint_left.mp sep (sa hp) ((Finset.mem_filter.mp kb).2.2.2.2 hp)

theorem growing {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A U : Region}
    (hide : 13+j.val∉terminals out) (inc : A⊆U) :
    pool gs out j.val A⊆pool gs out (j.val+1) U := by
  classical
  intro k mem
  obtain ⟨paid,old,gate,ne,sub⟩ := Finset.mem_filter.mp mem
  have same : (prefixSets gs out (j.val+1)).getD k ∅=(prefixSets gs out j.val).getD k ∅ := by
    have len : (prefixSets gs out j.val).length=13+j.val := by simp [prefixSets,start,tail_len];omega
    rw [next_sets gs out j hide,read_append,len,ite_eq_right (by omega)]
  apply Finset.mem_filter.mpr
  exact ⟨paid,by omega,gate,same ▸ ne,same ▸ (sub.trans inc)⟩

theorem parent_pool {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {a b : Nat} {A B : Region}
    (hide : 13+j.val∉terminals out) (ids : gs[j.val].inputs=[a,b]) (sa : region gs out j a⊆A)
    (sb : region gs out j b⊆B) (ha : (region gs out j a).Nonempty) (sep : Disjoint A B) :
    (pool gs out j.val A).card + (pool gs out j.val B).card + (if isDualAnd gs[j.val].op then 1 else 0) ≤
      (pool gs out (j.val+1) (A∪B)).card := by
  classical
  let pre := pool gs out j.val A ∪ pool gs out j.val B
  let next := pool gs out (j.val+1) (A∪B)
  have old : pre⊆next := Finset.union_subset (growing hide Finset.subset_union_left) (growing hide Finset.subset_union_right)
  have count : pre.card = (pool gs out j.val A).card+(pool gs out j.val B).card := Finset.card_union_of_disjoint (pool_disjoint gs out j.val sep)
  have inPre {k : Nat} (mem : k∈pre) : k<13+j.val := by
    rcases Finset.mem_union.mp mem with h|h <;> exact (Finset.mem_filter.mp h).2.1
  rw [←count]
  cases tag : isDualAnd gs[j.val].op with
  | false => simpa using Finset.card_le_card old
  | true =>
    have qual : Conjunction gs (13+j.val) := by
      refine ⟨j,rfl,?_⟩
      cases e : gs[j.val].op <;> simp [e,isDualAnd] at tag ⊢
    have raw : (prefixSets gs out (j.val+1)).getD (13+j.val) ∅ = region gs out j a∪region gs out j b := by
      have len : (prefixSets gs out j.val).length=13+j.val := by simp [prefixSets,start,tail_len];omega
      rw [next_sets gs out j hide,read_append,len,ite_eq_left rfl,ids]
      simp only [gather,Finset.union_empty,region,prefixSets]
    have fee : 13+j.val∈next := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by have := j.isLt;omega⟩,hide⟩,by omega,qual,?_,?_⟩
      · rw [raw];exact ha.mono Finset.subset_union_left
      · rw [raw];exact Finset.union_subset_union sa sb
    have enough := Finset.card_le_card (Finset.insert_subset fee old)
    rw [Finset.card_insert_of_notMem (fun x=>Nat.lt_irrefl _ (inPre x))] at enough
    exact enough
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse Plane920.Forest

def NativeRule (tag : Bool) (P Q : Signal→Prop) (f g H : Signal) (A B T : Region) :=
  ((T⊆A ∧ Charge P T) ∨ (T⊆B ∧ Charge Q T)) ∨
    (tag=true ∧ Minimal H T ∧ Minimal f (T∩A) ∧ Minimal g (T∩B) ∧ Charge P (T∩A) ∧ Charge Q (T∩B))

theorem native_cut {tag : Bool} {P Q : Signal→Prop} {f g H F : Signal} {A B T : Region}
    (lp : ∀F,P F→Local F A) (lq : ∀F,Q F→Local F B) (pf : P f) (qg : Q g) (sep : Disjoint A B)
    (op : ∀S,Active H S ↔ (if tag then Active f S ∧ Active g S else Active f S ∨ Active g S))
    (src : Visible P Q H F) (m : Minimal F T) : NativeRule tag P Q f g H A B T := by
  rcases src with left|right|rfl
  · exact Or.inl (Or.inl ⟨minimal_inside (lp _ left) m,F,left,m⟩)
  · exact Or.inl (Or.inr ⟨minimal_inside (lq _ right) m,F,right,m⟩)
  cases tag with
  | false =>
    rcases choose_active m (by simpa using op) with left|right
    · exact Or.inl (Or.inl ⟨minimal_inside (lp _ pf) left,f,pf,left⟩)
    · exact Or.inl (Or.inr ⟨minimal_inside (lq _ qg) right,g,qg,right⟩)
  | true =>
    have both := op
    simp only [ite_true] at both
    have a := project_piece (lp _ pf) (lq _ qg) sep m both
    have b := project_piece (lq _ qg) (lp _ pf) sep.symm m (fun S=>(both S).trans and_comm)
    exact Or.inr ⟨rfl,m,a,b,⟨f,pf,a⟩,⟨g,qg,b⟩⟩

theorem split_required {tag : Bool} {P Q : Signal→Prop} {f g H : Signal} {A B T : Region}
    (dis : Disjoint A B) (hasA : (T∩A).Nonempty) (hasB : (T∩B).Nonempty) (r : NativeRule tag P Q f g H A B T) :
    tag=true ∧ Minimal H T ∧ Minimal f (T∩A) ∧ Minimal g (T∩B) ∧ Charge P (T∩A) ∧ Charge Q (T∩B) := by
  rcases r with (left|right)|yes
  · exact False.elim (missed dis hasB left.1)
  · exact False.elim (missed dis.symm hasA right.1)
  · exact yes

theorem inherited_left {tag : Bool} {P Q : Signal→Prop} {f g H : Signal} {A B T : Region}
    (dis : Disjoint A B) (hasA : T.Nonempty) (sub : T⊆A) (r : NativeRule tag P Q f g H A B T) : Charge P T := by
  rcases r with (left|right)|yes
  · exact left.2
  · obtain ⟨v,hv⟩ := hasA
    exact False.elim (Finset.disjoint_left.mp dis (sub hv) (right.1 hv))
  · simpa only [Finset.inter_eq_left.mpr sub] using yes.2.2.2.2.1

theorem two_required {tag : Bool} {P Q : Signal→Prop} {f g H : Signal} {A B T S : Region}
    (dis : Disjoint A B) (ta : (T∩A).Nonempty) (tb : (T∩B).Nonempty) (sa : (S∩A).Nonempty) (sb : (S∩B).Nonempty)
    (rt : NativeRule tag P Q f g H A B T) (rs : NativeRule tag P Q f g H A B S) : T=S :=
  minima_eq (split_required dis ta tb rt).2.1 (split_required dis sa sb rs).2.1

theorem physical_rules {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (j : Fin gs.length) (hide : 13+j.val∉terminals out) :
    ∃ (a b : Nat) (A B : Region), gs[j.val].inputs=[a,b] ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      region gs out j a⊆A ∧ region gs out j b⊆B ∧ Ready gs out j.val A ∧ Ready gs out j.val B ∧ Ready gs out (j.val+1) (A∪B) ∧
      (∀w : V, (line w∩A).Nonempty → (line w∩B).Nonempty →
        Bill (isDualAnd gs[j.val].op) (Internal gs out j.val A) (Internal gs out j.val B)
          (globalWire gs out a) (globalWire gs out b) (line w∩A) (line w∩B)) ∧
      (∀T : Region, Charge (Internal gs out (j.val+1) (A∪B)) T →
        NativeRule (isDualAnd gs[j.val].op) (Internal gs out j.val A) (Internal gs out j.val B)
          (globalWire gs out a) (globalWire gs out b) (globalWire gs out (13+j.val)) A B T) := by
  obtain ⟨a,b,A,B,ids,ha,hb,dis,sa,sb,ra,rb,rc,cost⟩ := merge_charges basis arity h conn cap j hide
  obtain ⟨i,k,eq,na,nb,_⟩ := Bypass.connected_split arity h conn cap j hide
  rw [ids,List.cons.injEq,List.cons.injEq] at eq
  obtain ⟨rfl,rfl,_⟩ := eq
  have va := Bypass.nonempty_read j a na
  have vb := Bypass.nonempty_read j b nb
  have pf := earlier j.isLt.le va sa
  have qg := earlier j.isLt.le vb sb
  let H := globalWire gs out (13+j.val)
  have op (S : Region) : Active H S ↔ (if isDualAnd gs[j.val].op then Active (globalWire gs out a) S ∧ Active (globalWire gs out b) S
      else Active (globalWire gs out a) S ∨ Active (globalWire gs out b) S) := by
    rw [←sem_prefix gs out j a va,←sem_prefix gs out j b vb]
    unfold H
    rw [stored_value j hide]
    rcases basis gs[j.val] (List.getElem_mem _) with tag|tag
    · simpa [Active,value,bit,ids,tag,isDualAnd,GateOp.eval,live,join] using join_on (live gs out j a) (live gs out j b) S
    · simp [Active,value,bit,ids,tag,isDualAnd,GateOp.eval,live]
  refine ⟨a,b,A,B,ids,ha,hb,dis,sa,sb,ra,rb,rc,cost,?_⟩
  rintro T ⟨F,src,m⟩
  exact native_cut (fun _=>internal_local) (fun _=>internal_local) pf qg dis op (node_view hide ra rb src) m
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse Plane920.Forest

theorem closed_members {xs : List SetV} {U : Region} (h : Closed U xs) {s : Region} (mem : s∈xs) :
    s⊆U ∨ Disjoint s U := by
  obtain ⟨i,old,rfl⟩ := List.mem_iff_getElem.mp mem
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem old,Option.getD_some] using h i

def mark (U : Region) : V→V := fun i=>if i∈U then 1 else 0
theorem uniform_mark {xs : List SetV} {U : Region} (good : Closed U xs) : Uniform (mark U) xs := by
  intro s mem x hx y hy
  rcases closed_members good mem with inc|away
  · simp [mark,inc hx,inc hy]
  · simp [mark,Finset.disjoint_left.mp away hx,Finset.disjoint_left.mp away hy]

theorem intersecting_ready {xs : List SetV} {A B : Region} (a : Intrinsic A xs) (b : Closed B xs)
    {p : V} (pa : p∈A) (pb : p∈B) : A⊆B := by
  intro q qa
  have eq := a (mark B) (uniform_mark b) p pa q qa
  by_contra no
  simp [mark,pb,no] at eq

theorem old_closed {xs : List SetV} {s U : Region} (all : Closed U (xs++[s])) : Closed U xs := by
  intro i
  by_cases valid : i<xs.length
  · have := all i
    rwa [read_append,ite_eq_right (by omega)] at this
  · left
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt valid)]
    exact Finset.empty_subset _

theorem before_idle {xs : List SetV} {s U : Region} (all : Intrinsic U (xs++[s])) (closed : Closed U (xs++[s]))
    (apart : Disjoint s U) : Intrinsic U xs ∧ Closed U xs := by
  have old := old_closed closed
  refine ⟨?_,old⟩
  intro f good x hx y hy
  let paint : V→V := fun v=>if v∈U then f v else 0
  have marked : Uniform paint (xs++[s]) := by
    intro t mem
    rcases List.mem_append.mp mem with prior|same
    · intro a ha b hb
      rcases closed_members old prior with inc|away
      · simpa [paint,inc ha,inc hb] using good t prior a ha b hb
      · simp [paint,Finset.disjoint_left.mp away ha,Finset.disjoint_left.mp away hb]
    · have eq : t=s := List.mem_singleton.mp same
      subst t
      intro a ha b hb
      simp [paint,Finset.disjoint_left.mp apart ha,Finset.disjoint_left.mp apart hb]
  simpa [paint,hx,hy] using all paint marked x hx y hy

def added (gs : List Gate) (out : V→Nat) (j : Fin gs.length) : Region :=
  if 13+j.val∈terminals out then ∅ else gather (prefixSets gs out j.val) gs[j.val].inputs

theorem stage (gs : List Gate) (out : V→Nat) (j : Fin gs.length) :
    prefixSets gs out (j.val+1)=prefixSets gs out j.val++[added gs out j] := by
  unfold prefixSets added
  rw [List.take_succ_eq_append_getElem j.isLt,tail_append,←List.append_assoc]
  have len : (start++supportTail (terminals out) start (gs.take j.val)).length=13+j.val := by simp [start,tail_len];omega
  simp only [supportTail,len,prefixSets]

theorem empty_apart {X Y : Region} (away : Disjoint X Y) (sub : X⊆Y) : X=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Finset.disjoint_left.mp away hx (sub hx)

theorem unchanged_sources {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {U : Region}
    (away : Disjoint (added gs out j) U) {F : Signal} (src : Internal gs out (j.val+1) U F) :
    Internal gs out j.val U F := by
  rcases src with fixed|⟨i,lim,sub,rfl⟩
  · exact Or.inl fixed
  have len : (prefixSets gs out j.val).length=13+j.val := by simp [prefixSets,start,tail_len];omega
  rw [stage,read_append,len] at sub
  by_cases now : i=13+j.val
  · rw [ite_eq_left now] at sub
    have empty : added gs out j=∅ := empty_apart away sub
    have raw : (prefixSets gs out (j.val+1)).getD i ∅=∅ := by rw [stage,read_append,len,ite_eq_left now,empty]
    refine Or.inl ⟨(prefixVals gs out (j.val+1) (fun _=>false)).getD i false,?_⟩
    funext x
    have loc : Local (fun y=>(prefixVals gs out (j.val+1) y).getD i false) ((prefixSets gs out (j.val+1)).getD i ∅) :=
      fun y z eq=>(supported _ _ y z _ _ _ (start_valid y z)).2.2 i eq
    rw [raw] at loc
    exact loc x _ (fun _ hv=>False.elim ((Finset.notMem_empty _) hv))
  · rw [ite_eq_right now] at sub
    rw [prefix_read _ j.isLt lim]
    exact earlier j.isLt.le (by omega) sub

theorem pool_growth {gs : List Gate} {out : V→Nat} (j : Fin gs.length) (U : Region) :
    pool gs out j.val U⊆pool gs out (j.val+1) U := by
  classical
  intro i mem
  obtain ⟨paid,old,op,non,sub⟩ := Finset.mem_filter.mp mem
  have len : (prefixSets gs out j.val).length=13+j.val := by simp [prefixSets,start,tail_len];omega
  have eq : (prefixSets gs out (j.val+1)).getD i ∅=(prefixSets gs out j.val).getD i ∅ := by
    rw [stage,read_append,len,ite_eq_right (by omega)]
  exact Finset.mem_filter.mpr ⟨paid,by omega,op,eq ▸ non,eq ▸ sub⟩
theorem old_raw (gs : List Gate) (out : V→Nat) (j : Fin gs.length) {i : Nat} (prior : i<13+j.val) :
    (prefixSets gs out (j.val+1)).getD i ∅=(prefixSets gs out j.val).getD i ∅ := by
  have len : (prefixSets gs out j.val).length=13+j.val := by simp [prefixSets,start,tail_len];omega
  rw [stage,read_append,len,ite_eq_right (by omega)]

theorem pool_idle {gs : List Gate} {out : V→Nat} (j : Fin gs.length) {U : Region} (away : Disjoint (added gs out j) U) :
    pool gs out j.val U=pool gs out (j.val+1) U := by
  classical
  apply Finset.Subset.antisymm (pool_growth j U)
  intro i mem
  obtain ⟨paid,valid,op,non,sub⟩ := Finset.mem_filter.mp mem
  by_cases old : i<13+j.val
  · exact Finset.mem_filter.mpr ⟨paid,old,op,old_raw gs out j old ▸ non,old_raw gs out j old ▸ sub⟩
  have atRoot : i=13+j.val := by omega
  have len : (prefixSets gs out j.val).length=13+j.val := by simp [prefixSets,start,tail_len];omega
  have eq : (prefixSets gs out (j.val+1)).getD i ∅=added gs out j := by rw [stage,read_append,len,ite_eq_left atRoot]
  change ((prefixSets gs out (j.val+1)).getD i ∅).Nonempty at non
  change (prefixSets gs out (j.val+1)).getD i ∅⊆U at sub
  rw [eq] at non sub
  rw [empty_apart away sub] at non
  exact False.elim (Finset.not_nonempty_empty non)

theorem only_one {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A B : Region}
    (wa : Ready gs out j.val A) (wb : Ready gs out j.val B) :
    (pool gs out (j.val+1) (A∪B)).card≤(pool gs out j.val A).card+(pool gs out j.val B).card+1 := by
  classical
  let merged := pool gs out j.val A ∪ pool gs out j.val B
  have sub : pool gs out (j.val+1) (A∪B)⊆insert (13+j.val) merged := by
    intro k mem
    obtain ⟨paid,valid,op,non,inside⟩ := Finset.mem_filter.mp mem
    by_cases root : k=13+j.val
    · exact root ▸ Finset.mem_insert_self _ _
    have old : k<13+j.val := by omega
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union.mpr
    have eq := old_raw gs out j old
    change ((prefixSets gs out (j.val+1)).getD k ∅).Nonempty at non
    change (prefixSets gs out (j.val+1)).getD k ∅⊆A∪B at inside
    rw [eq] at non inside
    rcases wa.2 k with inc|awayA
    · exact Or.inl (Finset.mem_filter.mpr ⟨paid,old,op,non,inc⟩)
    rcases wb.2 k with inc|awayB
    · exact Or.inr (Finset.mem_filter.mpr ⟨paid,old,op,non,inc⟩)
    obtain ⟨x,hx⟩ := non
    exact False.elim ((Finset.mem_union.mp (inside hx)).elim (Finset.disjoint_left.mp awayA hx) (Finset.disjoint_left.mp awayB hx))
  exact (Finset.card_le_card sub).trans ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) 1))
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse Plane920.Forest

structure Fork (gs : List Gate) (out : V→Nat) (j : Fin gs.length) (A B : Region) : Prop where
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  disjoint : Disjoint A B
  readyA : Ready gs out j.val A
  readyB : Ready gs out j.val B
  parent : Ready gs out (j.val+1) (A∪B)
  budget : (pool gs out j.val A).card+(pool gs out j.val B).card+(if isDualAnd gs[j.val].op then 1 else 0)≤
    (pool gs out (j.val+1) (A∪B)).card
  labels : ∃a b : Nat, gs[j.val].inputs=[a,b] ∧
    (∀w : V, (line w∩A).Nonempty → (line w∩B).Nonempty →
      Bill (isDualAnd gs[j.val].op) (Internal gs out j.val A) (Internal gs out j.val B)
        (globalWire gs out a) (globalWire gs out b) (line w∩A) (line w∩B)) ∧
    (∀T : Region, Charge (Internal gs out (j.val+1) (A∪B)) T →
      NativeRule (isDualAnd gs[j.val].op) (Internal gs out j.val A) (Internal gs out j.val B)
        (globalWire gs out a) (globalWire gs out b) (globalWire gs out (13+j.val)) A B T)

theorem make_fork {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (j : Fin gs.length) (hide : 13+j.val∉terminals out) :
    ∃A B : Region, Fork gs out j A B ∧ added gs out j⊆A∪B := by
  obtain ⟨a,b,A,B,ids,ha,hb,dis,sa,sb,ra,rb,rc,bills,native⟩ := physical_rules basis arity h conn cap j hide
  obtain ⟨i,k,eq,na,_,_⟩ := Bypass.connected_split arity h conn cap j hide
  rw [ids,List.cons.injEq,List.cons.injEq] at eq
  obtain ⟨rfl,rfl,_⟩ := eq
  refine ⟨A,B,⟨ha,hb,dis,ra,rb,rc,parent_pool hide ids sa sb na dis,a,b,ids,bills,native⟩,?_⟩
  simpa only [added,ite_eq_right hide,ids,gather,Finset.union_empty,prefixSets,region] using Finset.union_subset_union sa sb

theorem base_size {gs : List Gate} {out : V→Nat} {U : Region} (ready : Ready gs out 0 U) : U.card≤1 := by
  have uni : Uniform id start := by
    intro s mem;obtain ⟨v,rfl⟩ := List.mem_ofFn.mp mem
    intro a ha b hb;simpa using (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm
  have eq : prefixSets gs out 0=start := by simp [prefixSets,supportTail]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact ready.1 id (eq ▸ uni) a ha b hb

theorem root_ready {gs : List Gate} {out : V→Nat} (conn : Connected gs out) : Ready gs out gs.length Finset.univ := by
  refine ⟨?_,fun _=>Or.inl (Finset.subset_univ _)⟩
  intro f good x _ y _
  have uni : Uniform f (start++supportTail (terminals out) start gs) := by simpa [prefixSets] using good
  apply Finset.card_le_one.mp (conn f uni).le
  · exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩

theorem meet_eq {xs : List SetV} {s U C : Region} (uc : Intrinsic U xs ∧ Closed U xs) (cc : Intrinsic C xs ∧ Closed C xs)
    (inside : s⊆C) (touch : ¬Disjoint s U) : U=C := by
  obtain ⟨p,raw,pu⟩ := Finset.not_disjoint_iff.mp touch
  have pc : p∈C := inside raw
  exact Finset.Subset.antisymm (intersecting_ready uc.1 cc.2 pu pc) (intersecting_ready cc.1 uc.2 pc pu)
  
theorem tree_induction {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (Goal : Nat→Region→Prop)
    (leaf : ∀ U : Region, U.Nonempty → U.card≤1 → Ready gs out 0 U → Goal 0 U)
    (idle : ∀ (j : Fin gs.length) (U : Region), Ready gs out (j.val+1) U →
      (∀F,Internal gs out (j.val+1) U F → Internal gs out j.val U F) →
      (pool gs out j.val U).card=(pool gs out (j.val+1) U).card → Goal j.val U → Goal (j.val+1) U)
    (merge : ∀ (j : Fin gs.length) (A B : Region), Fork gs out j A B →
      Goal j.val A → Goal j.val B → Goal (j.val+1) (A∪B)) :
    Goal gs.length Finset.univ := by
  have main (n : Nat) (len : n≤gs.length) (U : Region) (non : U.Nonempty) (r : Ready gs out n U) : Goal n U := by
    induction n generalizing U with
    | zero => exact leaf U non (base_size r) r
    | succ k ih =>
      let j : Fin gs.length := ⟨k,len⟩
      by_cases away : Disjoint (added gs out j) U
      · have prior : Ready gs out j.val U := by
          have rs := r
          change Ready gs out (j.val+1) U at rs
          unfold Ready at rs ⊢
          rw [stage] at rs
          exact before_idle rs.1 rs.2 away
        exact idle j U r (fun _=>unchanged_sources away) (congrArg Finset.card (pool_idle j away)) (ih (by omega) U non prior)
      · have hide : 13+j.val∉terminals out := by
          intro named
          simp [added,named] at away
        obtain ⟨A,B,fork,inside⟩ := make_fork basis arity h conn cap j hide
        have eq : U=A∪B := meet_eq (xs:=prefixSets gs out (j.val+1)) (s:=added gs out j) r fork.parent inside away
        rw [eq]
        exact merge j A B fork (ih (by omega) A fork.nonemptyA fork.readyA) (ih (by omega) B fork.nonemptyB fork.readyB)
  exact main gs.length le_rfl _ Finset.univ_nonempty (root_ready conn)
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse Plane920.Forest

noncomputable def native (gs : List Gate) (out : V→Nat) (n : Nat) (U : Region) : Finset V := by
  classical
  exact Finset.univ.filter (fun w=>2≤(line w∩U).card ∧ (line w∩U).card≤3 ∧ Charge (Internal gs out n U) (line w∩U))

def Owes (E : Finset V) (U : Region) (w : V) := 2≤(line w∩U).card → w∈E
def Cross (A B : Region) (w : V) := (line w∩A).Nonempty ∧ (line w∩B).Nonempty

structure Transition (tag : Bool) (A B : Region) (E EA EB : Finset V) : Prop where
  kept : ∀w∈E,Owes EA A w ∧ Owes EB B w
  unique : ∀w∈E, ∀v∈E, Cross A B w → Cross A B v → w=v
  drivers : ∃p q : V,
    (∀w∈E,Cross A B w → tag=true ∧ line w∩A=line p∩A ∧ line w∩B=line q∩B) ∧
    (∀w,Cross A B w → (Owes EA A w ∧ Owes EB B w) ∨ (tag=true ∧
      ((line w∩A=line p∩A ∧ Owes EA A w) ∨ (line w∩B=line q∩B ∧ Owes EB B w))))

theorem owing {gs : List Gate} {out : V→Nat} {n : Nat} {U : Region} {w : V} (small : (line w∩U).card≤3)
    (yes : Charge (Internal gs out n U) (line w∩U)) : Owes (native gs out n U) U w := by
  classical
  exact fun big=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,big,small,yes⟩

theorem native_member {gs : List Gate} {out : V→Nat} {n : Nat} {U : Region} {w : V} (mem : w∈native gs out n U) :
    2≤(line w∩U).card ∧ (line w∩U).card≤3 ∧ Charge (Internal gs out n U) (line w∩U) := by
  classical
  exact (Finset.mem_filter.mp mem).2

theorem small_cross {A B : Region} (dis : Disjoint A B) {w : V} (cross : Cross A B w) :
    (line w∩A).card≤3 ∧ (line w∩B).card≤3 := by
  have dis' : Disjoint (line w∩A) (line w∩B) := dis.mono Finset.inter_subset_right Finset.inter_subset_right
  have bound : (line w∩A).card+(line w∩B).card≤(line w).card := by
    rw [←Finset.card_union_of_disjoint dis'];exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  rw [line_size] at bound
  have a := Finset.card_pos.mpr cross.1
  have b := Finset.card_pos.mpr cross.2
  omega

theorem carry {tag : Bool} {P Q : Signal→Prop} {f g H : Signal} {A B T : Region} (dis : Disjoint A B)
    (r : NativeRule tag P Q f g H A B T) : ((T∩A).Nonempty → Charge P (T∩A)) ∧ ((T∩B).Nonempty → Charge Q (T∩B)) := by
  rcases r with (⟨sub,p⟩|⟨sub,q⟩)|yes
  · exact ⟨fun _=>by simpa only [Finset.inter_eq_left.mpr sub] using p,fun c=>False.elim (missed dis c sub)⟩
  · exact ⟨fun c=>False.elim (missed dis.symm c sub),fun _=>by simpa only [Finset.inter_eq_left.mpr sub] using q⟩
  · exact ⟨fun _=>yes.2.2.2.2.1,fun _=>yes.2.2.2.2.2⟩

theorem profile {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A B : Region} (fork : Fork gs out j A B)
    (E : Finset V) (eligible : E⊆native gs out (j.val+1) (A∪B)) :
    Transition (isDualAnd gs[j.val].op) A B E (native gs out j.val A) (native gs out j.val B) := by
  obtain ⟨a,b,_,bills,natives⟩ := fork.labels
  obtain ⟨p,designA⟩ := LastMerge.designated (globalWire gs out a) A
  obtain ⟨q,designB⟩ := LastMerge.designated (globalWire gs out b) B
  let T := fun w=>line w∩(A∪B)
  have xa (w) : T w∩A=line w∩A := by ext x;simp [T]
  have yb (w) : T w∩B=line w∩B := by ext x;simp [T]
  have inherited (w) (hw : w∈E) := natives (T w) (native_member (eligible hw)).2.2
  have forced (w) (hw : w∈E) (cw : Cross A B w) := split_required fork.disjoint
    ((xa w).symm ▸ cw.1) ((yb w).symm ▸ cw.2) (inherited w hw)
  constructor
  · intro w hw
    have paid := carry fork.disjoint (inherited w hw)
    rw [xa,yb] at paid
    have both := (native_member (eligible hw)).2.1
    have ca : (line w∩A).card≤(T w).card :=
      Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_left)
    have cb : (line w∩B).card≤(T w).card :=
      Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_right)
    exact ⟨fun big=>owing (ca.trans both) (paid.1 (Finset.card_pos.mp (by omega))) big,
      fun big=>owing (cb.trans both) (paid.2 (Finset.card_pos.mp (by omega))) big⟩
  · intro w hw v hv cw cv
    have eq := minima_eq (forced w hw cw).2.1 (forced v hv cv).2.1
    by_contra ne
    have sub : T w⊆line w∩line v := Finset.subset_inter Finset.inter_subset_left (eq ▸ Finset.inter_subset_left)
    have bound := (Finset.card_le_card sub).trans (OrSupport.line_pair w v ne)
    have atLeast := (native_member (eligible hw)).1
    change 2≤(T w).card at atLeast
    omega
  · refine ⟨p,q,?_,?_⟩
    · intro w hw cw
      obtain ⟨tag,_,one,two,_,_⟩ := forced w hw cw
      rw [xa] at one;rw [yb] at two
      exact ⟨tag,designA _ one,designB _ two⟩
    · intro w cw
      have prices := bills w cw.1 cw.2
      have small := small_cross fork.disjoint cw
      rcases prices with ⟨one,two⟩|⟨tag,⟨fixed,one⟩|⟨fixed,two⟩⟩
      · exact Or.inl ⟨owing small.1 one,owing small.2 two⟩
      · exact Or.inr ⟨tag,Or.inl ⟨designA _ fixed,owing small.1 one⟩⟩
      · exact Or.inr ⟨tag,Or.inr ⟨designB _ fixed,owing small.2 two⟩⟩
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Parse Plane920.Forest

def labelCost (U : Region) (E : Finset V) := ∑w∈E, ((line w∩U).card-1)

theorem initial_pool (gs : List Gate) (out : V→Nat) (U : Region) : pool gs out 0 U=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i mem
  obtain ⟨paid,old,_,_,_⟩ := Finset.mem_filter.mp mem
  have lo := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp paid).1).1
  omega

theorem native_cost {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {U : Region}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (ready : Ready gs out j.val U) :
    labelCost U (native gs out j.val U)≤(pool gs out j.val U).card :=
  sum_cost basis arity h conn cap ready _ (fun _ hw=>(native_member hw).2.1) (fun _ hw=>(native_member hw).2.2)

theorem table_sound {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (Test : Region→Finset V→Nat→Prop)
    (leaf : ∀U : Region, U.Nonempty → U.card≤1 → Test U ∅ 0)
    (merge : ∀(A B : Region) (E EA EB : Finset V) (a b k : Nat) (tag : Bool),
      A.Nonempty → B.Nonempty → Disjoint A B → Transition tag A B E EA EB →
      labelCost A EA≤a → labelCost B EB≤b → a≤A.card-1 → b≤B.card-1 →
      a+b+(if tag then 1 else 0)≤k → k≤(A∪B).card-1 → Test A EA a → Test B EB b → Test (A∪B) E k) :
    Test Finset.univ ∅ (pool gs out gs.length Finset.univ).card := by
  classical
  let Goal := fun (n : Nat) (U : Region)=> (pool gs out n U).card≤U.card-1 ∧
    ∀E⊆native gs out n U, Test U E (pool gs out n U).card
  have root : Goal gs.length Finset.univ := by
    apply tree_induction basis arity h conn cap Goal
    · intro U non size _
      have zero := initial_pool gs out U
      constructor
      · rw [zero];simp
      intro E allowed
      have none : E=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have big := (native_member (allowed hw)).1
        have sm := Finset.card_le_card (Finset.inter_subset_right (s₁:=line w) (s₂:=U))
        omega
      rw [zero,none,Finset.card_empty]
      exact leaf U non size
    · intro j U _ old count prev
      constructor
      · rw [←count];exact prev.1
      intro E elig
      rw [←count]
      apply prev.2 E
      intro w mem
      obtain ⟨a,b,F,source,min⟩ := native_member (elig mem)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,b,F,old _ source,min⟩
    · intro j A B fork IA IB
      have bounds := only_one fork.readyA fork.readyB
      have a := Finset.card_pos.mpr fork.nonemptyA
      have b := Finset.card_pos.mpr fork.nonemptyB
      have ca := IA.1
      have cb := IB.1
      have upper : (pool gs out (j.val+1) (A∪B)).card≤(A∪B).card-1 := by
        rw [Finset.card_union_of_disjoint fork.disjoint]
        omega
      refine ⟨upper,?_⟩
      intro E elig
      exact merge A B E _ _ _ _ _ _ fork.nonemptyA fork.nonemptyB fork.disjoint (profile fork E elig)
        (native_cost basis arity h conn cap fork.readyA) (native_cost basis arity h conn cap fork.readyB)
        ca cb fork.budget upper (IA.2 _ (Finset.Subset.refl _)) (IB.2 _ (Finset.Subset.refl _))
  exact root.2 ∅ (Finset.empty_subset _)
end Plane920.Restriction

namespace Plane920.Restriction
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Forest
noncomputable def hiddenDualAnd (gs : List Gate) (out : V→Nat) : Finset Nat := by
  classical
  exact (paid (terminals out) 13 gs.length).filter (Conjunction gs)

theorem actual_pool {gs : List Gate} {out : V→Nat} (arity : ∀g∈gs,g.inputs.length≤2)
    (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25) :
    pool gs out gs.length Finset.univ=hiddenDualAnd gs out := by
  classical
  ext i
  constructor
  · intro mem
    obtain ⟨paid,_,op,_,_⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨paid,op⟩
  · intro mem
    obtain ⟨paid,op⟩ := Finset.mem_filter.mp mem
    obtain ⟨j,idx,gate⟩ := op
    have nz : 13+j.val∉terminals out := idx ▸ (Finset.mem_sdiff.mp paid).2
    obtain ⟨a,b,ids,na,_,_⟩ := Bypass.connected_split arity h conn cap j nz
    let pre := gs.take j.val
    let post := gs.drop (j.val+1)
    have eq : pre++gs[j.val]::post=gs := by simp [pre,post]
    have ix : start.length+pre.length=13+j.val := by simp [start,pre]
    have atWire := after_prefix (terminals out) start pre gs[j.val] post
    rw [eq,ix,ite_eq_right nz,ids] at atWire
    have s : ((prefixSets gs out gs.length).getD i ∅).Nonempty := by
      rw [←idx]
      simp only [prefixSets,List.take_length,atWire,gather,Finset.union_empty]
      exact na.mono Finset.subset_union_left
    exact Finset.mem_filter.mpr ⟨paid,(Finset.mem_Ico.mp (Finset.mem_sdiff.mp paid).1).2,⟨j,idx,gate⟩,s,Finset.subset_univ _⟩

theorem finite_lower {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (Test : Region→Finset V→Nat→Prop)
    (leaf : ∀U : Region,U.Nonempty → U.card≤1 → Test U ∅ 0)
    (merge : ∀(A B : Region) (E EA EB : Finset V) (a b k : Nat) (tag : Bool),
      A.Nonempty → B.Nonempty → Disjoint A B → Transition tag A B E EA EB →
      labelCost A EA≤a → labelCost B EB≤b → a≤A.card-1 → b≤B.card-1 →
      a+b+(if tag then 1 else 0)≤k → k≤(A∪B).card-1 → Test A EA a → Test B EB b → Test (A∪B) E k)
    (K : Nat) (reject : ∀k,Test Finset.univ ∅ k → K≤k) : K≤(hiddenDualAnd gs out).card := by
  rw [←actual_pool arity h conn cap]
  exact reject _ (table_sound basis arity h conn cap Test leaf merge)
end Plane920.Restriction

namespace Plane920.RootCost
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Restriction

def rowCost (tag : Bool) (A B : Region) (p q w : V) : Nat :=
  if (line w∩A).Nonempty ∧ (line w∩B).Nonempty then
    let x := (line w∩A).card-1
    let y := (line w∩B).card-1
    if tag then min (if line w∩A=line p∩A then x else x+y) (if line w∩B=line q∩B then y else x+y)
    else x+y
  else 0

def total (tag : Bool) (A B : Region) (p q : V) := (∑w : V,rowCost tag A B p q w)+(if tag then 1 else 0)

def TooCostly (A B : Region) := ∀ (tag : Bool) (p q : V), 13≤total tag A B p q
def partCost (U : Region) (E : Finset V) (w : V) := if w∈E then (line w∩U).card-1 else 0

theorem label_sum (U : Region) (E : Finset V) : (∑w : V,partCost U E w)=labelCost U E := by
  classical
  simp [partCost,labelCost]

theorem price {E : Finset V} {U : Region} {w : V} (due : Owes E U w) :
    (line w∩U).card-1≤partCost U E w := by
  by_cases big : 2≤(line w∩U).card
  · simp [partCost,due big]
  · unfold partCost;split <;> omega

theorem cost_le {tag : Bool} {A B : Region} {E EA EB : Finset V} (step : Transition tag A B E EA EB) :
    ∃p q : V, total tag A B p q≤labelCost A EA+labelCost B EB+(if tag then 1 else 0) := by
  obtain ⟨p,q,_,all⟩ := step.drivers
  refine ⟨p,q,Nat.add_le_add_right ?_ _⟩
  rw [←label_sum,←label_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  unfold rowCost
  split
  · rename_i cross
    let x := (line w∩A).card-1
    let y := (line w∩B).card-1
    rcases all w cross with ⟨wa,wb⟩|⟨yes,ob⟩
    · have bound := Nat.add_le_add (price wa) (price wb)
      cases tag <;> simp only [ite_true,ite_false,Bool.false_eq_true]
      · exact bound
      · apply le_trans (Nat.min_le_left _ _)
        split <;> omega
    · subst tag
      simp only [ite_true]
      rcases ob with ⟨id,due⟩|⟨id,due⟩
      · rw [ite_eq_left id]
        exact (Nat.min_le_left _ _).trans ((price due).trans (Nat.le_add_right _ _))
      · rw [ite_eq_left id]
        exact (Nat.min_le_right _ _).trans ((price due).trans (Nat.le_add_left _ _))
  · exact Nat.zero_le _

theorem too_many {price left right a b fee parent n : Nat} (c : price≤left+right+fee)
    (la : left≤a) (rb : right≤b) (sum : a+b+fee≤parent) (pc : parent≤n-13)
    (cap : n≤25) (high : 13≤price) : False := by omega

theorem impossible_tag {A B : Region} (tag : Bool) {p q : V} (bad : TooCostly A B) (low : total tag A B p q≤12) : False := Nat.not_succ_le_self 12 ((bad tag p q).trans low)

theorem affordable {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A B : Region}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (fork : Fork gs out j A B) : ¬TooCostly A B := by
  have step := profile fork ∅ (Finset.empty_subset _)
  obtain ⟨p,q,cost⟩ := cost_le step
  have a := native_cost basis arity h conn cap fork.readyA
  have b := native_cost basis arity h conn cap fork.readyB
  have used := fork.budget
  have sub : pool gs out (j.val+1) (A∪B)⊆paid (terminals out) 13 gs.length := by
    classical
    exact Finset.filter_subset _ _
  have limit := Finset.card_le_card sub
  rw [hidden_count h] at limit
  intro too
  apply impossible_tag (p:=p) (q:=q) (isDualAnd (gs.get j).op) too
  have maxSize : gs.length-13≤12 := by omega
  exact cost.trans ((Nat.add_le_add_right (Nat.add_le_add a b) _).trans (used.trans (limit.trans maxSize)))
end Plane920.RootCost

namespace Plane920.RootCost
open Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.LastMerge

theorem row_map (d : Collineation) (t : Bool) (A B : Region) (p q w : V) :
    rowCost t (A.map d.pts.toEmbedding) (B.map d.pts.toEmbedding) (d.lns p) (d.lns q) (d.lns w)=rowCost t A B p q w := by
  unfold rowCost
  simp only [←d.incidence,←Finset.map_inter,Finset.map_nonempty,Finset.card_map,Finset.map_inj]

theorem carry_orbit {A B : Region} (h : TooCostly A B) (d : Collineation) :
    TooCostly (A.map d.pts.toEmbedding) (B.map d.pts.toEmbedding) := by
  intro t p q
  obtain ⟨p,rfl⟩ := d.lns.surjective p
  obtain ⟨q,rfl⟩ := d.lns.surjective q
  unfold total
  rw [←Equiv.sum_comp d.lns (rowCost t _ _ (d.lns p) (d.lns q))]
  simpa only [total,row_map] using h t p q

theorem opposite_row (t : Bool) (A B : Region) (p q w : V) : rowCost t B A q p w=rowCost t A B p q w := by
  unfold rowCost
  simp only [and_comm (a:=(line w ∩ B).Nonempty) (b:=(line w ∩ A).Nonempty)]
  by_cases left : line w∩B=line q∩B <;> by_cases right : line w∩A=line p∩A <;> cases t <;> simp [left,right,Nat.add_comm,min_comm]

theorem carry_swap {A B : Region} (h : TooCostly A B) : TooCostly B A := by
  intro t p q
  unfold total
  simpa only [total,opposite_row (A:=A) (B:=B)] using h t q p
end Plane920.RootCost

namespace Plane920.RootCost
open Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.LastMerge
def part7 : Region := {0,1,2}
def part11 : Region := {0,1,3}
def part15 : Region := {0,1,2,3}
def part29 : Region := {0,2,3,4}
def part31 : Region := {0,1,2,3,4}
def part63 : Region := {0,1,2,3,4,5}
def part79 : Region := {0,1,2,3,6}
def part95 : Region := {0,1,2,3,4,6}
def part177 : Region := {0,4,5,7}
def part179 : Region := {0,1,4,5,7}
def part183 : Region := {0,1,2,4,5,7}
def part207 : Region := {0,1,2,3,6,7}
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check7 : TooCostly part7 (Finset.univ \ part7) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check11 : TooCostly part11 (Finset.univ \ part11) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check15 : TooCostly part15 (Finset.univ \ part15) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check29 : TooCostly part29 (Finset.univ \ part29) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check31 : TooCostly part31 (Finset.univ \ part31) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check63 : TooCostly part63 (Finset.univ \ part63) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check79 : TooCostly part79 (Finset.univ \ part79) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check95 : TooCostly part95 (Finset.univ \ part95) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check177 : TooCostly part177 (Finset.univ \ part177) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check179 : TooCostly part179 (Finset.univ \ part179) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check183 : TooCostly part183 (Finset.univ \ part183) := by
  unfold TooCostly
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 2000000 in
theorem check207 : TooCostly part207 (Finset.univ \ part207) := by
  unfold TooCostly
  decide +kernel
end Plane920.RootCost

namespace Plane920.RootCost
open Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.LastMerge

def bits : Nat → (Nat→Bool) → Nat
  | 0, _ => 0
  | n+1, f => Nat.bit (f 0) (bits n (fun i=>f (i+1)))

theorem bits_get (n : Nat) (f : Nat→Bool) (i : Nat) (small : i<n) : (bits n f).testBit i=f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => exact Nat.testBit_bit_zero _ _
    | succ i => rw [bits,Nat.testBit_bit_succ]; exact ih _ _ (by omega)

theorem bits_lt (n : Nat) (f : Nat→Bool) : bits n f<2^n := by
  induction n generalizing f with
  | zero => simp [bits]
  | succ n ih =>
    have lim := ih (fun i=>f (i+1))
    rw [bits,Nat.pow_succ]
    cases f 0 <;> simp [Nat.bit] <;> omega

def decode (n : Nat) : Region := Finset.univ.filter (fun v=>n.testBit v.val)
theorem mem_decode (n : Nat) (v : V) : v∈decode n ↔ n.testBit v.val=true :=
  ⟨fun h=>(Finset.mem_filter.mp h).2,fun h=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩

def encode (U : Region) := bits 13 (fun n=>decide (Fin.ofNat 13 n∈U))
theorem decode_encode (U : Region) : decode (encode U)=U := by
  ext v
  simp only [mem_decode,encode,bits_get _ _ _ v.isLt,decide_eq_true_eq]
  have eq : Fin.ofNat 13 v.val=v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
  rw [eq]

def shift (d : Collineation) (n : Nat) := bits 13 (fun i=> n.testBit (d.pts.symm (Fin.ofNat 13 i)).val)
theorem decode_shift (d : Collineation) (n : Nat) : decode (shift d n)=(decode n).map d.pts.toEmbedding := by
  ext v
  simp only [Finset.mem_map_equiv,mem_decode,shift,bits_get _ _ _ v.isLt]
  have eq : Fin.ofNat 13 v.val=v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
  rw [eq]
theorem shifted_card (d : Collineation) (n : Nat) : (decode (shift d n)).card=(decode n).card := by rw [decode_shift,Finset.card_map]

def backwards (d : Collineation) : Collineation where
  pts := d.pts.symm
  lns := d.lns.symm
  incidence := by
    intro w
    rw [←d.lns.apply_symm_apply w,←d.incidence,Finset.map_map]
    ext x;simp

theorem preimage_cost (d : Collineation) {A : Region}
    (h : TooCostly (A.map d.pts.toEmbedding) (Finset.univ\A.map d.pts.toEmbedding)) :
    TooCostly A (Finset.univ\A) := by
  have back := carry_orbit h (backwards d)
  have eqA : (A.map d.pts.toEmbedding).map (backwards d).pts.toEmbedding=A := by ext x;simp [backwards]
  have eqB : (Finset.univ\A.map d.pts.toEmbedding).map (backwards d).pts.toEmbedding=Finset.univ\A := by ext x;simp [backwards]
  rwa [eqA,eqB] at back
end Plane920.RootCost

namespace Plane920.RootCost
open Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.LastMerge
def p0 : V≃V where
  toFun := ![12,0,1,2,3,4,5,6,7,8,9,10,11]
  invFun := ![1,2,3,4,5,6,7,8,9,10,11,12,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l0 : V≃V where
  toFun := ![12,0,1,2,3,4,5,6,7,8,9,10,11]
  invFun := ![1,2,3,4,5,6,7,8,9,10,11,12,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c0 : Collineation where
  pts := p0
  lns := l0
  incidence := by decide +kernel
def p1 : V≃V where
  toFun := ![5,6,2,1,7,4,12,0,3,8,9,10,11]
  invFun := ![7,3,2,8,5,0,1,4,9,10,11,12,6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l1 : V≃V where
  toFun := ![5,6,1,11,4,3,12,0,7,8,9,10,2]
  invFun := ![7,2,12,5,4,0,1,8,9,10,11,3,6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c1 : Collineation where
  pts := p1
  lns := l1
  incidence := by decide +kernel
def p2 : V≃V where
  toFun := ![4,0,9,5,3,12,2,6,8,7,1,10,11]
  invFun := ![1,10,6,4,0,3,7,9,8,2,11,12,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l2 : V≃V where
  toFun := ![4,0,9,2,3,12,6,5,7,11,1,10,8]
  invFun := ![1,10,3,4,0,7,6,8,12,2,11,9,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c2 : Collineation where
  pts := p2
  lns := l2
  incidence := by decide +kernel
def p3 : V≃V where
  toFun := ![3,0,2,1,12,4,7,6,5,9,8,10,11]
  invFun := ![1,3,2,0,5,8,7,6,10,9,11,12,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l3 : V≃V where
  toFun := ![0,12,1,11,3,4,6,5,9,8,7,10,2]
  invFun := ![0,2,12,4,5,7,6,10,9,8,11,3,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c3 : Collineation where
  pts := p3
  lns := l3
  incidence := by decide +kernel
def p4 : V≃V where
  toFun := ![0,5,2,4,3,1,6,9,8,7,11,10,12]
  invFun := ![0,5,2,4,3,1,6,9,8,7,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l4 : V≃V where
  toFun := ![4,2,1,3,0,5,6,8,7,11,10,9,12]
  invFun := ![4,2,1,3,0,5,6,8,7,11,10,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c4 : Collineation where
  pts := p4
  lns := l4
  incidence := by decide +kernel
def p5 : V≃V where
  toFun := ![0,12,6,2,4,7,1,5,11,8,3,9,10]
  invFun := ![0,6,3,10,4,7,2,5,9,11,12,8,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l5 : V≃V where
  toFun := ![12,3,6,1,4,11,5,2,8,7,0,9,10]
  invFun := ![10,3,7,1,4,6,2,9,8,11,12,5,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c5 : Collineation where
  pts := p5
  lns := l5
  incidence := by decide +kernel
def p6 : V≃V where
  toFun := ![0,1,6,3,5,4,2,7,10,9,8,12,11]
  invFun := ![0,1,6,3,5,4,2,7,10,9,8,12,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l6 : V≃V where
  toFun := ![0,5,3,2,4,1,6,7,9,8,12,11,10]
  invFun := ![0,5,3,2,4,1,6,7,9,8,12,11,10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c6 : Collineation where
  pts := p6
  lns := l6
  incidence := by decide +kernel
def p7 : V≃V where
  toFun := ![0,2,5,12,3,9,6,1,7,8,11,10,4]
  invFun := ![0,7,1,4,12,2,6,8,9,5,11,10,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l7 : V≃V where
  toFun := ![12,2,9,3,0,6,5,11,7,8,10,1,4]
  invFun := ![4,11,1,3,12,6,5,8,9,2,10,7,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c7 : Collineation where
  pts := p7
  lns := l7
  incidence := by decide +kernel
def p8 : V≃V where
  toFun := ![0,12,1,2,7,4,6,5,3,8,11,10,9]
  invFun := ![0,2,3,8,5,7,6,4,9,12,11,10,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l8 : V≃V where
  toFun := ![12,11,1,6,4,3,5,2,7,8,10,9,0]
  invFun := ![12,2,7,5,4,6,3,8,9,11,10,1,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c8 : Collineation where
  pts := p8
  lns := l8
  incidence := by decide +kernel
def p9 : V≃V where
  toFun := ![4,1,3,2,0,5,8,7,6,10,9,11,12]
  invFun := ![4,1,3,2,0,5,8,7,6,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l9 : V≃V where
  toFun := ![1,0,2,12,4,5,7,6,10,9,8,11,3]
  invFun := ![1,0,2,12,4,5,7,6,10,9,8,11,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c9 : Collineation where
  pts := p9
  lns := l9
  incidence := by decide +kernel
def p10 : V≃V where
  toFun := ![2,0,1,12,3,11,6,5,10,8,9,7,4]
  invFun := ![1,2,0,4,12,7,6,11,9,10,8,5,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l10 : V≃V where
  toFun := ![12,0,11,3,2,10,5,9,7,8,6,4,1]
  invFun := ![1,12,4,3,11,6,10,8,9,7,5,2,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c10 : Collineation where
  pts := p10
  lns := l10
  incidence := by decide +kernel
def p11 : V≃V where
  toFun := ![0,1,2,9,10,6,5,11,8,3,4,7,12]
  invFun := ![0,1,2,9,10,6,5,11,8,3,4,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l11 : V≃V where
  toFun := ![0,1,6,9,10,5,2,8,7,3,4,11,12]
  invFun := ![0,1,6,9,10,5,2,8,7,3,4,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c11 : Collineation where
  pts := p11
  lns := l11
  incidence := by decide +kernel
def p12 : V≃V where
  toFun := ![1,3,2,0,5,8,7,6,10,9,11,12,4]
  invFun := ![3,0,2,1,12,4,7,6,5,9,8,10,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def l12 : V≃V where
  toFun := ![0,2,12,4,5,7,6,10,9,8,11,3,1]
  invFun := ![0,12,1,11,3,4,6,5,9,8,7,10,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def c12 : Collineation where
  pts := p12
  lns := l12
  incidence := by decide +kernel
def syms : Fin 13→Collineation := ![c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12]
end Plane920.RootCost

namespace Plane920.RootCost
open Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.LastMerge
def Listed (m : Nat) := m∈([7,11,15,29,31,63,79,95,177,179,183,207] : List Nat)
instance (n : Nat) : Decidable (Listed n) := by unfold Listed;infer_instance
def descent (n : Nat) : Bool := decide (Listed n ∨ (decode n).card<3 ∨ 6<(decode n).card ∨ ∃i : Fin 13,shift (syms i) n<n)
end Plane920.RootCost

namespace Plane920.RootCost
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Restriction Plane920.Bypass
theorem full_after_last {gs : List Gate} {out : V→Nat} (arity : ∀g∈gs,g.inputs.length≤2) (conn : Connected gs out)
    (j : Fin gs.length) (last : Last out j) : Ready gs out (j.val+1) Finset.univ := by
  refine ⟨?_,fun _=>Or.inl (Finset.subset_univ _)⟩
  intro f good
  let pre := gs.take (j.val+1)
  let post := gs.drop (j.val+1)
  let xs := prefixSets gs out (j.val+1)
  have split : pre++post=gs := List.take_append_drop (j.val+1) gs
  have len : xs.length=13+(j.val+1) := by simp only [xs,prefixSets,List.length_append,tail_len,List.length_take,Nat.min_eq_left j.isLt,show start.length=13 from by simp [start]]
  obtain ⟨k,final,cost⟩ := components post (fun g mem=>arity g (List.mem_of_mem_drop mem)) (terminals out) xs f good
  have all : Uniform k (start++supportTail (terminals out) start gs) := by
    conv in supportTail _ _ gs => rw [←split,tail_append]
    simpa only [←List.append_assoc,xs,prefixSets,pre] using final
  have none : paid (terminals out) xs.length post.length=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i mem
    obtain ⟨range,nz⟩ := Finset.mem_sdiff.mp mem
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp range
    rw [len] at lo hi
    have ends : 13+(j.val+1)+post.length=13+gs.length := by simp [post]
    exact nz (last.2 i (by omega) (by omega))
  rw [none,Finset.card_empty,conn k all] at cost
  have one : (colors f).card≤1 := by omega
  intro x _ y _
  apply Finset.card_le_one.mp one
  · exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  · exact Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩

theorem actual_root {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (j : Fin gs.length) (last : Last out j) :
    ∃A B : Region, Fork gs out j A B ∧ A∪B=Finset.univ ∧ ¬TooCostly A B := by
  obtain ⟨A,B,fork,_⟩ := make_fork basis arity h conn cap j last.1
  have root := full_after_last arity conn j last
  obtain ⟨x,xa⟩ := fork.nonemptyA
  have inside : (Finset.univ : Region)⊆A∪B := intersecting_ready (xs:=prefixSets gs out (j.val+1))
    (A:=Finset.univ) (B:=A∪B) (p:=x) root.1 fork.parent.2 (Finset.mem_univ _) (Finset.mem_union_left B xa)
  exact ⟨A,B,fork,Finset.Subset.antisymm (Finset.subset_univ _) inside,affordable basis arity h conn cap fork⟩
end Plane920.RootCost

namespace Plane920.RootCost
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Restriction Plane920.Bypass Plane920.LastMerge
theorem listed_cost {m : Nat} (used : Listed m) : TooCostly (decode m) (Finset.univ \ decode m) := by
  simp only [Listed,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have name : decode 7=part7 := by decide +kernel
    rw [name];exact check7
  · have name : decode 11=part11 := by decide +kernel
    rw [name];exact check11
  · have name : decode 15=part15 := by decide +kernel
    rw [name];exact check15
  · have name : decode 29=part29 := by decide +kernel
    rw [name];exact check29
  · have name : decode 31=part31 := by decide +kernel
    rw [name];exact check31
  · have name : decode 63=part63 := by decide +kernel
    rw [name];exact check63
  · have name : decode 79=part79 := by decide +kernel
    rw [name];exact check79
  · have name : decode 95=part95 := by decide +kernel
    rw [name];exact check95
  · have name : decode 177=part177 := by decide +kernel
    rw [name];exact check177
  · have name : decode 179=part179 := by decide +kernel
    rw [name];exact check179
  · have name : decode 183=part183 := by decide +kernel
    rw [name];exact check183
  · have name : decode 207=part207 := by decide +kernel
    rw [name];exact check207
theorem from_descent (cover : ∀m : Fin 8192,descent m.val=true) (A : Region) (small : 3≤A.card) (large : A.card≤6) :
    TooCostly A (Finset.univ \ A) := by
  have go (m : Nat) (bound : m<8192) (lo : 3≤(decode m).card) (hi : (decode m).card≤6) : TooCostly (decode m) (Finset.univ \ decode m) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      have casesM := of_decide_eq_true (show decide (Listed m ∨ (decode m).card<3 ∨ 6<(decode m).card ∨ ∃i : Fin 13,shift (syms i) m<m)=true from cover ⟨m,bound⟩)
      rcases casesM with base|bad|bad|⟨i,down⟩
      · exact listed_cost base
      · omega
      · omega
      · have equal := shifted_card (syms i) m
        have next := ih (shift (syms i) m) down (down.trans bound) (equal.symm ▸ lo) (equal.symm ▸ hi)
        rw [decode_shift] at next
        exact preimage_cost _ next
  have same := decode_encode A
  simpa only [same] using go (encode A) (bits_lt 13 _) (same.symm ▸ small) (same.symm ▸ large)
end Plane920.RootCost

namespace Plane920.RootCost
open Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.LastMerge
def words : Array Nat := #[
  0xf04090404040404e3030303e303e3eeef0f0905ea04e7eeef08efeeefeeeeeee,
  0xe040604040404040604060406040604ef0502020a040202ef050202eb05e2eee,
  0xe0109010f080f0f0101010101010101ec05020207050202e1010101e101e1eee,
  0xeee0e050e0506050e030303030303030e050202070502020f05020207050202e,
  0xe010101010101010101010101010101e101010101010101e1010101e101e1eee,
  0xeee0e040e0404040e030303030303030e080202070402020303020203030202e,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e080eee0e030e0303030eee0e020e0702020e030202030302020,
  0xe010101010101010101010101010101e101010101010101e1010101e101e1eee,
  0xeee0e040e0404040e040404040404040e040202040402020404020204040202e,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0402020e050202070502020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0402020e030202030302020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0302020,
  0xe010101010101010101010101010101e101010101010101e1010101e101e1eee,
  0xeee0e050e0506050e030303030303030e020202020202020202020202020202e,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e050eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e060eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e050eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xe010101010101010101010101010101e101010101010101e1010101e101e1eee,
  0xeee0e040e0404040e030303030303030e020202020202020202020202020202e,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0,
  0xe010101010101010101010101010101e101010101010101e1010101e101e1eee,
  0xeee0e040e0404040e030303030303030e020202020202020202020202020202e,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e050eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e050eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0,
  0xeee0e010e0101010e010101010101010e010101010101010101010101010101e,
  0xeeeeeee0eee0e040eee0e030e0303030eee0e020e0202020e020202020202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e030eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0,
  0xeeeeeee0eee0e010eee0e010e0101010eee0e010e0101010e010101010101010,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e020eeeeeee0eee0e020eee0e020e0202020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0,
  0xeeeeeeeeeeeeeee0eeeeeee0eee0e010eeeeeee0eee0e010eee0e010e0101010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e020,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eeeeeeeeeeeeeee0eeeeeee0eee0e010,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee]
def witnessCode (n : Nat) := ((words[n/64]?.getD 0) >>> (4*(n%64))) &&& 15
def checked (n : Nat) : Bool :=
  let g := witnessCode n
  if g=14 then decide ((decode n).card<3 ∨ 6<(decode n).card)
  else if g=15 then decide (Listed n)
  else decide (shift (syms (Fin.ofNat 13 g)) n<n)
theorem verifies {n : Nat} (h : checked n=true) : descent n=true := by
  simp only [checked] at h
  unfold descent
  apply decide_eq_true
  split at h
  · rcases of_decide_eq_true h with lo|hi
    · exact Or.inr (Or.inl lo)
    · exact Or.inr (Or.inr (Or.inl hi))
  · split at h
    · exact Or.inl (of_decide_eq_true h)
    · exact Or.inr (Or.inr (Or.inr ⟨_,of_decide_eq_true h⟩))
end Plane920.RootCost

namespace Plane920.RootCost
open Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.LastMerge
def chunk (k : Nat) := ∀i : Fin 256, checked (k*256+i.val)=true
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk0 : chunk 0 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk1 : chunk 1 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk2 : chunk 2 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk3 : chunk 3 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk4 : chunk 4 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk5 : chunk 5 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk6 : chunk 6 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk7 : chunk 7 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk8 : chunk 8 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk9 : chunk 9 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk10 : chunk 10 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk11 : chunk 11 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk12 : chunk 12 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk13 : chunk 13 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk14 : chunk 14 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk15 : chunk 15 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk16 : chunk 16 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk17 : chunk 17 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk18 : chunk 18 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk19 : chunk 19 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk20 : chunk 20 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk21 : chunk 21 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk22 : chunk 22 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk23 : chunk 23 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk24 : chunk 24 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk25 : chunk 25 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk26 : chunk 26 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk27 : chunk 27 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk28 : chunk 28 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk29 : chunk 29 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk30 : chunk 30 := by
  unfold chunk
  decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 3000000 in
theorem chunk31 : chunk 31 := by
  unfold chunk
  decide +kernel
theorem all_chunks (k : Fin 32) : chunk k.val := by
  fin_cases k
  · exact chunk0
  · exact chunk1
  · exact chunk2
  · exact chunk3
  · exact chunk4
  · exact chunk5
  · exact chunk6
  · exact chunk7
  · exact chunk8
  · exact chunk9
  · exact chunk10
  · exact chunk11
  · exact chunk12
  · exact chunk13
  · exact chunk14
  · exact chunk15
  · exact chunk16
  · exact chunk17
  · exact chunk18
  · exact chunk19
  · exact chunk20
  · exact chunk21
  · exact chunk22
  · exact chunk23
  · exact chunk24
  · exact chunk25
  · exact chunk26
  · exact chunk27
  · exact chunk28
  · exact chunk29
  · exact chunk30
  · exact chunk31
theorem all_masks (m : Fin 8192) : checked m.val=true := by
  let hi : Fin 32 := ⟨m.val/256,by have := m.isLt;omega⟩
  let lo : Fin 256 := ⟨m.val%256,Nat.mod_lt _ (by decide)⟩
  have yes := all_chunks hi lo
  change checked ((m.val/256)*256+m.val%256)=true at yes
  have eq : m.val/256*256+m.val%256=m.val := by omega
  rwa [eq] at yes
end Plane920.RootCost

namespace Plane920.RootCost
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Restriction Plane920.Bypass

theorem costly_large (A : Region) (lo : 3≤A.card) (hi : A.card≤6) : TooCostly A (Finset.univ\A) :=
  from_descent (fun i=>verifies (all_masks i)) A lo hi

theorem complement_of_partition {A B : Region} (sep : Disjoint A B) (full : A∪B=Finset.univ) : B=Finset.univ\A := by
  ext p
  have any : p∈A∪B := full ▸ Finset.mem_univ p
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
  exact ⟨fun pb pa=>Finset.disjoint_left.mp sep pa pb,fun np=>(Finset.mem_union.mp any).resolve_left np⟩

theorem small_side {A B : Region} (dis : Disjoint A B) (un : A∪B=Finset.univ) (ok : ¬TooCostly A B) :
    A.card≤2 ∨ B.card≤2 := by
  have num := Finset.card_union_of_disjoint dis
  rw [un,show (Finset.univ : Region).card=13 from by decide] at num
  by_contra! large
  apply ok
  by_cases a : A.card≤6
  · rw [complement_of_partition dis un]
    exact costly_large A (by omega) a
  · apply carry_swap
    have rev : B∪A=Finset.univ := (Finset.union_comm B A).trans un
    rw [complement_of_partition dis.symm rev]
    exact costly_large B (by omega) (by omega)

theorem actual_last_small {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25)
    (j : Fin gs.length) (last : Last out j) :
    ∃A B : Region,Fork gs out j A B ∧ A∪B=Finset.univ ∧ (A.card≤2 ∨ B.card≤2) := by
  obtain ⟨A,B,fork,un,ok⟩ := actual_root basis arity h conn cap j last
  exact ⟨A,B,fork,un,small_side fork.disjoint un ok⟩

theorem only_two_types {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25) :
    ∃ (j : Fin gs.length) (A B : Region), Last out j ∧ (gs.get j).op=.or ∧ Fork gs out j A B ∧ A∪B=Finset.univ ∧
      (A.card=1 ∨ A.card=2 ∨ B.card=1 ∨ B.card=2) := by
  have floor := Forest.twenty_five basis arity h
  obtain ⟨j,last⟩ := last_exists h (by omega)
  obtain ⟨A,B,fork,un,small⟩ := actual_last_small basis arity h conn cap j last
  have a := Finset.card_pos.mpr fork.nonemptyA
  have b := Finset.card_pos.mpr fork.nonemptyB
  exact ⟨j,A,B,last,(connected_last_and basis arity h conn cap j last).1,fork,un,by omega⟩
end Plane920.RootCost

namespace Plane920.RootCost
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Restriction Plane920.LastMerge

def Needs (K : Nat) (A B : Region) := ∀(t : Bool) (p q : V), K≤total t A B p q
theorem needs_map {K : Nat} {A B : Region} (d : Collineation) (yes : Needs K A B) :
    Needs K (A.map d.pts.toEmbedding) (B.map d.pts.toEmbedding) := by
  intro t p q
  obtain ⟨p,rfl⟩ := d.lns.surjective p
  obtain ⟨q,rfl⟩ := d.lns.surjective q
  unfold total
  rw [←Equiv.sum_comp d.lns (rowCost t _ _ (d.lns p) (d.lns q))]
  simpa only [total,row_map] using yes t p q

theorem needs_preimage {K : Nat} {A : Region} (d : Collineation)
    (yes : Needs K (A.map d.pts.toEmbedding) (Finset.univ\A.map d.pts.toEmbedding)) : Needs K A (Finset.univ\A) := by
  have back := needs_map (backwards d) yes
  have eqA : (A.map d.pts.toEmbedding).map (backwards d).pts.toEmbedding=A := by ext x;simp [backwards]
  have eqB : (Finset.univ\A.map d.pts.toEmbedding).map (backwards d).pts.toEmbedding=Finset.univ\A := by ext x;simp [backwards]
  rwa [eqA,eqB] at back

theorem pair_rep : Needs 8 ({0,1} : Region) (Finset.univ\({0,1} : Region)) := by
  unfold Needs
  decide +kernel

theorem pair_descends : ∀x y : V,x≠y → ({x,y} : Region)={0,1} ∨
    ∃i : Fin 13,shift (syms i) (encode {x,y})<encode {x,y} := by decide +kernel

theorem same_code (d : Collineation) (A : Region) : encode (A.map d.pts.toEmbedding)=shift d (encode A) := by
  unfold encode shift
  congr 1
  funext i
  rw [bits_get _ _ _ (d.pts.symm (Fin.ofNat 13 i)).isLt]
  have eq : Fin.ofNat 13 (d.pts.symm (Fin.ofNat 13 i)).val=d.pts.symm (Fin.ofNat 13 i) :=
    Fin.ext (Nat.mod_eq_of_lt (d.pts.symm _).isLt)
  rw [eq]
  simp

theorem pair_floor (A : Region) (two : A.card=2) : Needs 8 A (Finset.univ\A) := by
  suffices ∀k : Nat,∀U : Region,encode U=k → U.card=2 → Needs 8 U (Finset.univ\U) from this (encode A) A rfl two
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro U code num
    obtain ⟨x,y,ne,rfl⟩ := Finset.card_eq_two.mp num
    rcases pair_descends x y ne with eq|⟨i,down⟩
    · rw [eq];exact pair_rep
    · let X : Region := {x,y}
      let d := syms i
      apply needs_preimage d
      apply ih (encode (X.map d.pts.toEmbedding)) ?_ _ rfl (by simpa only [Finset.card_map] using num)
      rw [same_code,←code]
      exact down

theorem needs_flip {K : Nat} {A B : Region} (yes : Needs K A B) : Needs K B A := by
  intro t p q
  unfold total
  simpa only [total,opposite_row (A:=A) (B:=B)] using yes t q p

theorem paid_at_root {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A B : Region} {K : Nat}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (fork : Fork gs out j A B) (yes : Needs K A B) :
    K≤(hiddenDualAnd gs out).card := by
  have step := profile fork ∅ (Finset.empty_subset _)
  obtain ⟨p,q,cost⟩ := cost_le step
  have a := native_cost basis arity h conn cap fork.readyA
  have b := native_cost basis arity h conn cap fork.readyB
  have sub : pool gs out (j.val+1) (A∪B)⊆hiddenDualAnd gs out := by
    classical
    intro k mem
    obtain ⟨paid,_,op,_,_⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨paid,op⟩
  exact (yes (isDualAnd (gs.get j).op) p q).trans (cost.trans
    ((Nat.add_le_add_right (Nat.add_le_add a b) _).trans (fork.budget.trans (Finset.card_le_card sub))))
end Plane920.RootCost

namespace Plane920.RootCost
open PEqualNP.CircuitLowerBounds Plane920.Pencil Plane920.OrSupport Plane920.Terminal Plane920.Component Plane920.Restriction Plane920.Bypass

theorem pair_uses_eight {gs : List Gate} {out : V→Nat} {j : Fin gs.length} {A B : Region}
    (basis : ∀g∈gs,g.op=.and ∨ g.op=.or) (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out)
    (conn : Connected gs out) (cap : gs.length≤25) (fork : Fork gs out j A B) (un : A∪B=Finset.univ)
    (pair : A.card=2 ∨ B.card=2) : 8≤(hiddenDualAnd gs out).card := by
  apply paid_at_root basis arity h conn cap fork
  rcases pair with a|b
  · rw [complement_of_partition fork.disjoint un]
    exact pair_floor A a
  · apply needs_flip
    rw [complement_of_partition fork.disjoint.symm ((Finset.union_comm B A).trans un)]
    exact pair_floor B b

theorem last_partition {gs : List Gate} {out : V→Nat} (basis : ∀g∈gs,g.op=.and ∨ g.op=.or)
    (arity : ∀g∈gs,g.inputs.length≤2) (h : Correct gs out) (conn : Connected gs out) (cap : gs.length≤25) :
    ∃(j : Fin gs.length) (A B : Region), Last out j ∧ (gs.get j).op=.or ∧ Fork gs out j A B ∧ A∪B=Finset.univ ∧
      (A.card=1 ∨ B.card=1 ∨ ((A.card=2 ∨ B.card=2) ∧ 8≤(hiddenDualAnd gs out).card)) := by
  obtain ⟨j,A,B,last,op,fork,un,small⟩ := only_two_types basis arity h conn cap
  refine ⟨j,A,B,last,op,fork,un,?_⟩
  rcases small with a|a|b|b
  · exact Or.inl a
  · exact Or.inr (Or.inr ⟨Or.inl a,pair_uses_eight basis arity h conn cap fork un (Or.inl a)⟩)
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr ⟨Or.inr b,pair_uses_eight basis arity h conn cap fork un (Or.inr b)⟩)

theorem remaining_count :
    ((((Finset.univ : Region).powersetCard 1)∪(Finset.univ : Region).powersetCard 2).card)=91 := by decide +kernel
end Plane920.RootCost
