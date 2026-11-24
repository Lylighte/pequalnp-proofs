import BatchUnmix
namespace PetersenSecondCube.Batch
open PetersenFootprintCenters PetersenBoundary
open PetersenMixedStar (V)
def posRow : Fin 60 → M := ![139,387,523,771,54,278,550,774,77,108,525,556,58,120,154,216,85,209,277,401,101,105,553,549,114,106,202,210,197,212,404,389,394,393,777,778,562,788,564,786,178,232,170,240,650,897,649,898,581,616,585,612,325,464,340,449,306,308,804,802]
def negRow : Fin 15 → M := ![50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
def pc : V → Nat := ![42045352848590095,648682830955565311,457397253507977200,1783472391782149,243205308037460016,1083695496673901136,71787115237843712,45316388852252675,1148594581681209514,869178218240806092]
def nc : V → Nat := ![17698,12817,18570,5172,713,6157,110,880,25472,31744]
def fromV : Fin 15 → V := ![0,1,2,3,4,0,1,2,3,4,5,7,9,6,8]
def toV : Fin 15 → V := ![1,2,3,4,0,5,6,7,8,9,7,9,6,8,5]
def incident : V → Fin 3 → Fin 15 := ![![0,4,5],![0,1,6],![1,2,7],![2,3,8],![3,4,9],![5,10,14],![6,12,13],![7,10,11],![8,13,14],![9,11,12]]
def adjacent : V → Fin 3 → V := ![![1,4,5],![0,2,6],![1,3,7],![2,4,8],![3,0,9],![0,7,8],![1,9,8],![2,5,9],![3,6,5],![4,7,6]]
def index (e : Fin 15) (j : Fin 4) : Fin 60 := ⟨4*e.val+j.val,by have h := e.isLt; have k := j.isLt; omega⟩
theorem rows_ok : ∀ e j, RowEdge (posRow (index e j)) (fromV e) (toV e) := by decide +kernel
theorem n_ok : ∀ i, negRow i∈negativeMasks := by decide +kernel
theorem p_bits : ∀ (v : V) (j : Fin 60), (pc v).testBit j.val = (posRow j).val.testBit v.val := by decide +kernel
theorem n_bits : ∀ (v : V) (j : Fin 15), (nc v).testBit j.val = (negRow j).val.testBit v.val := by decide +kernel
theorem adjacent_inj : ∀ (v : V) (i j : Fin 3), adjacent v i=adjacent v j → i=j := by decide +kernel
theorem incident_pairs : ∀ v i, (fromV (incident v i)=v ∧ toV (incident v i)=adjacent v i) ∨
    (toV (incident v i)=v ∧ fromV (incident v i)=adjacent v i) := by decide +kernel
end PetersenSecondCube.Batch
