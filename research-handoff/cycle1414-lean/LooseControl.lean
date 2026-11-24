import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1414_aux
open PEqualNP.CircuitLowerBounds

abbrev Input := Fin 7 → Bool
def atMask (m : Fin 128) : Input := fun i => m.val.testBit i.val
theorem listed (x : Input) : ∃ m : Fin 128, atMask m = x := by
  let z := BitVec.ofBoolListLE (List.ofFn x)
  have h : z.toNat < 128 := by simpa [z] using z.isLt
  refine ⟨⟨z.toNat,h⟩,funext (fun i => ?_)⟩
  change z.getLsbD i.val = x i
  rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  exact List.getElem_ofFn _

def eliminable (C : Circuit) (p : Fin 7) (b : Bool) (j : Fin 10) :=
  (∀ y z : Input, y p = b → z p = b →
    (C.wires (List.ofFn y)).getD (7+j.val) false = (C.wires (List.ofFn z)).getD (7+j.val) false) ∨
  ∃ w < 7+j.val, ∀ u : Input, u p = b →
    (C.wires (List.ofFn u)).getD (7+j.val) false = (C.wires (List.ofFn u)).getD w false

def Tight (C : Circuit) := ∃ (p : Fin 7) (b : Bool) (S : Finset (Fin 10)),
  (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, eliminable C p b j

def allow (words : Array Nat) (p : Fin 7) (b : Bool) : Finset (Fin 10) :=
  Finset.univ.filter (fun j => words[2*p.val+b.toNat]!.testBit j.val)

def val (columns : Array Nat) (w : Nat) (m : Fin 128) := columns[w]!.testBit m.val
def sample (ws : Array Nat) (p : Fin 7) (b : Bool) (j : Fin 10) (k : Nat) : Fin 128 :=
  ⟨(ws[(2*p.val+b.toNat)*10+j.val]! >>> (7*k)) % 128,Nat.mod_lt _ (by decide)⟩

abbrev Check (columns ws : Array Nat) (p : Fin 7) (b : Bool) (j : Fin 10) : Prop :=
  let row := sample ws p b j
  let gate := val columns (7+j.val)
  atMask (row 0) p = b ∧ atMask (row 1) p = b ∧ gate (row 0) ≠ gate (row 1) ∧
    ∀ w : Fin (7+j.val), atMask (row (2+w.val)) p = b ∧ gate (row (2+w.val)) ≠ val columns w.val (row (2+w.val))
def Rows (C : Circuit) (cols : Array Nat) :=
  ∀ m : Fin 128, C.wires (List.ofFn (atMask m)) = List.ofFn (fun w : Fin 17 => val cols w.val m)

theorem wire {C : Circuit} {cols : Array Nat} (rows : Rows C cols) (m : Fin 128) (w : Nat) (hw : w < 17) :
    (C.wires (List.ofFn (atMask m))).getD w false = val cols w m := by
  rw [rows]
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hw)]
  exact List.getElem_ofFn _

theorem reject {C : Circuit} {cols ws good : Array Nat} (rows : Rows C cols)
    (checks : ∀ p b j, j ∉ allow good p b → Check cols ws p b j)
    (small : ∀ p b, (allow good p b).card < (if b = true then 4 else 3)) : ¬ Tight C := by
  rintro ⟨p,b,S,card,all⟩
  have sub : S ⊆ allow good p b := by
    intro j hj
    by_contra excluded
    let row := sample ws p b j
    have q := checks p b j excluded
    obtain ⟨x,y,diff,older⟩ := q
    have le : 7+j.val < 17 := by omega
    rcases all j hj with constant | ⟨w,wh,copy⟩
    · have eq := constant (atMask (row 0)) (atMask (row 1)) x y
      exact diff (by simpa only [wire rows _ _ le] using eq)
    · let i : Fin (7+j.val) := ⟨w,wh⟩
      obtain ⟨on,mismatch⟩ := older i
      have eq := copy (atMask (row (2+w))) on
      exact mismatch (by simpa only [wire rows _ _ le,wire rows _ _ (lt_trans wh le)] using eq)
  exact (Nat.not_lt_of_ge (card.trans (Finset.card_le_card sub))) (small p b)

def candidate : Circuit := ⟨[⟨.not,[0]⟩,⟨.not,[1]⟩,⟨.not,[2]⟩,⟨.not,[3]⟩,⟨.not,[4]⟩,⟨.not,[5]⟩,⟨.not,[6]⟩,⟨.and,[7,8]⟩,⟨.and,[9,10]⟩,⟨.and,[11,12]⟩],16⟩
def cols : Array Nat := #[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0x55555555555555555555555555555555,0x33333333333333333333333333333333,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xff00ff00ff00ff00ff00ff00ff00ff,0xffff0000ffff0000ffff0000ffff,0xffffffff00000000ffffffff,0xffffffffffffffff,0x11111111111111111111111111111111,0xf000f000f000f000f000f000f000f,0xffff000000000000ffff]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 40000000 in
theorem dataOK : Rows candidate cols := by unfold Rows; decide +kernel
theorem basisOK : ∀ g ∈ candidate.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
theorem sizeOK : candidate.size = 10 := rfl
theorem mismatch : ¬ (candidate.eval (List.ofFn (atMask 0)) = true ↔ ∃ i : Fin 7, atMask 0 i = true ∧ atMask 0 (i+1) = true) := by decide +kernel
def good : Array Nat := #[129,129,130,130,260,260,264,264,528,528,544,544,64,64]
def ws : Array Nat := #[0x0,0x10000000000000002,0x820000000000000004,0x80840000000000000008,0x8080880000000000000010,0x808080900000000000000020,0x80808080a00000000000000040,0x0,0x20810204100820000000000000004,0x2022041008080880000000000000010,0x0,0x810204081020c083,0xc08102040810214085,0xa0c08102040810224089,0x90a0c08102040810244091,0x8890a0c081020408102840a1,0x848890a0c081020408103040c1,0x0,0x10a14285120c08102040810214085,0x28122450890a0c08102040810244091,0x1,0x0,0x1008000000000000004,0x82008000000000000008,0x8084008000000000000010,0x808088008000000000000020,0x80808090008000000000000040,0x0,0x10810204101008000000000000004,0x2012041008084008000000000000010,0x204081020608103,0x0,0x818204081020c08106,0xc081820408102140810a,0xa0c0818204081022408112,0x90a0c0818204081024408122,0x8890a0c0818204081028408142,0x0,0x20c18306140818204081020c08106,0x302244910a0c0818204081022408112,0x1,0x8000000000000002,0x0,0x100808000000000000008,0x8200808000000000000010,0x808400808000000000000020,0x80808800808000000000000040,0x204081020410000000000000001,0x0,0x4012041008200808000000000000010,0x408102050810205,0x28408102060810206,0x0,0x818284081020c081020c,0xc081828408102140810214,0xa0c081828408102240810224,0x90a0c081828408102440810244,0xa14285081430408102050810205,0x0,0x205285120c081828408102140810214,0x1,0x8000000000000002,0x808000000000000004,0x0,0x10080808000000000000010,0x820080808000000000000020,0x80840080808000000000000040,0x204081020410000000000000001,0x0,0x2012041010080808000000000000010,0x810204881020409,0x4881020508102040a,0x284881020608102040c,0x0,0x818284881020c081020418,0xc08182848810214081020428,0xa0c08182848810224081020448,0x1224488122450810204881020409,0x0,0x409306140818284881020c081020418,0x1,0x8000000000000002,0x808000000000000004,0x80808000000000000008,0x0,0x1008080808000000000000020,0x82008080808000000000000040,0x204081020410000000000000001,0x10810204100808000000000000004,0x0,0x1020448102040811,0x89020488102040812,0x4889020508102040814,0x284889020608102040818,0x0,0x818284889020c08102040830,0xc0818284889021408102040850,0x2244811224491020448102040811,0x112850814304889020508102040814,0x0,0x1,0x8000000000000002,0x808000000000000004,0x80808000000000000008,0x8080808000000000000010,0x0,0x100808080808000000000000040,0x204081020410000000000000001,0x10810204100808000000000000004,0x0,0x2042810204081021,0x10a044810204081022,0x890a048810204081024,0x48890a050810204081028,0x2848890a060810204081030,0x0,0x8182848890a0c0810204081060,0x42810a1428512042810204081021,0x21488122450890a048810204081024,0x0,0x1,0x8000000000000002,0x808000000000000004,0x80808000000000000008,0x8080808000000000000010,0x808080808000000000000020,0x0,0x204081020410000000000000001,0x10810204100808000000000000004,0x2012041008080808000000000000010,0x4181020408102041,0x20c281020408102042,0x10a0c481020408102044,0x890a0c881020408102048,0x48890a0d081020408102050,0x2848890a0e081020408102060,0x0,0x81060c1830614181020408102041,0x418112244910a0c481020408102044,0x22418143048890a0d081020408102050]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 40000000 in
theorem noTight : ¬ Tight candidate := by
  apply reject (ws := ws) (good := good) dataOK <;> decide +kernel
end PEqualNP.Outside.L_meta_1414_aux
