import CnfBridge
import DimacsIndex

open Std.Sat PetersenCnfBridge PetersenDimacs

namespace PetersenExport

def bare (g : Gate) (s : Side) (v : Vertex) : Variable := .inl ⟨g,s,.inl v⟩
def link (g : Gate) (s : Side) (h : Fin g.val) : Variable := .inl ⟨g,s,.inr h⟩
def outSelect (g : Gate) : Variable := .inr (.inl g)
def used (v : Vertex) (g : Gate) : Variable := .inr (.inr (.inl (v,g)))
def rwVar (r : Row) (w : RowWire) : Variable := .inr (.inr (.inr (r,w)))
def productV (r : Row) (g : Gate) (s : Side) (h : Fin g.val) : Variable :=
  rwVar r (.inl ⟨g,.inl (s,.inl h)⟩)
def sideV (r : Row) (g : Gate) (s : Side) : Variable :=
  rwVar r (.inl ⟨g,.inl (s,.inr 0)⟩)
def gateV (r : Row) (g : Gate) : Variable := rwVar r (.inl ⟨g,.inr 0⟩)
def outProduct (r : Row) (g : Gate) : Variable := rwVar r (.inr (.inl g))
def result (r : Row) : Variable := rwVar r (.inr (.inr 0))

def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def independent (m : Nat) := edges.all (fun (a,b) => !(m.testBit a && m.testBit b))
def successors (m : Nat) := ((List.range 10).filter (fun v => !m.testBit v)).map (fun v => m ||| (1 <<< v))
def zeros := (List.range 1024).filter fun m => independent m && !(successors m).any independent
def positives := (zeros.flatMap successors).eraseDups
def points := (zeros.map (fun m => (m,false)) ++ positives.map (fun m => (m,true))).toArray

def capBlocks : List (CNF Variable) := (List.finRange 10).flatMap fun v =>
  let gs := List.finRange 6
  let flags := gs.map fun g => orBlock [bare g 0 v, bare g 1 v] (used v g)
  let triples := gs.flatMap fun a => (gs.filter (· < a)).flatMap fun b =>
    (gs.filter (· < b)).map fun c => pack [[(used v a,false),(used v b,false),(used v c,false)]]
  flags ++ triples

def rowBlocks (r : Row) (m : Nat) (label : Bool) : List (CNF Variable) :=
  let gs := List.finRange 6
  let vs := (List.finRange 10).filter (fun v => m.testBit v.val)
  let gates := gs.flatMap fun g =>
    let hs := List.finRange g.val
    let sides := (List.finRange 2).flatMap fun s =>
      (hs.map fun h => andBlock (link g s h) (gateV r ⟨h.val,by omega⟩) (productV r g s h)) ++
        [orBlock (vs.map (bare g s) ++ hs.map (productV r g s)) (sideV r g s)]
    sides ++ [andBlock (sideV r g 0) (sideV r g 1) (gateV r g)]
  gates ++ (gs.map fun g => andBlock (outSelect g) (gateV r g) (outProduct r g)) ++
    [orBlock (gs.map (outProduct r)) (result r), pack [[(result r,label)]]]

def symbolicFormula : CNF Variable := ⟨(capBlocks ++ (List.finRange 115).flatMap
  (fun r => let p := points[r.val]?.getD (0,false); rowBlocks r p.1 p.2)).toArray.flatMap CNF.clauses⟩

def exportFile (filename : String) : IO Unit := do
  if zeros.length != 15 || positives.length != 100 then throw (IO.userError "unexpected Petersen boundary")
  let f := symbolicFormula.relabel closedId
  if f.clauses.size != 26380 then throw (IO.userError "unexpected clause count")
  let file ← IO.FS.Handle.mk filename .write
  file.putStrLn "p cnf 6541 26380"
  for c in f.clauses do
    let literals := c.literals.map (fun (n,pol) => (if pol then "" else "-") ++ toString n)
    file.putStrLn (String.intercalate " " (literals ++ ["0"]))

end PetersenExport

def main (args : List String) : IO Unit := do
  match args with
  | [filename] => PetersenExport.exportFile filename
  | _ => throw (IO.userError "pass exactly one output path")
