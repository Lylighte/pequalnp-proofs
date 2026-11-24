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
