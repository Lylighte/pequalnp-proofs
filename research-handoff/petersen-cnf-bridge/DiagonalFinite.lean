import DiagonalCertificate

namespace PetersenDiagonalNumeric.Checked
open PetersenFootprintCenters
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def words : Array Nat := #[99170406906587127626106689931708459697820703394773719551523127996463163912720,1159947078301502752379287920639215077733207317529859065163556409178075664,1159924745618102545055081158604862058176946273647848982113892726868029968,270066025113905099720980503675613313081918990833921789248172560,1256572284271858733308900807284961000288936518334602523350210105490551312,340771299010673335975814641716257873562220804041282515410895632,325103653117008330038438256926321683544913875711823799345230352,17183238682406629590304860860314997286339856,932184709881424151191078236055785484817055798249118588407125226919309840,183291370741808598988069673559708770650137135777471971007148560,210609317476275976922897633984697410642415627175297921162686992,793652717211041838166544,294170095795654367922256086058472598354822679772670587361571344,12810950549839491273188402665604696197059344,16992340274563983112508511238986325069672976,38209,1146138530617918216224569866319475845527126404543411264545614808705151504,106158344610243093763680321061994903297337356661288335462904336,262031334903739757340140700754214088160633638562461322461590032,14378971696611175713063474479745910881427984,289349281661754935289024822496022013446311393512760456208462352,5841967675298671541519586321863194152289040,7235764250206835488011076631157140442067472,42256,260424396867338016815420834647933903568953196517456240467522064,14117634838815894972933804231440752559796752,14204747124747655219131803315067368512696848,41488,15598543699655819165161092004762486491329040,21264,12816,0,814846287570659216972476962637696871166716573493988663044857983696646672,106158344592284161644158185999332891241454988581972313702937104,210609317475479173078226157551817113015158247964791625946771984,10197581971886683873789408979424784671601168,43424799967582940277810251908066396837007448230343184,5841967675298671541438420647903689968730896,7235764250206835487714452986414504704225808,34064,183291370723824821340712913150137496993871443580149536046199312,9936245114091403133669183464088664175292944,10023357400023163380093856138910616358236688,29200,10023357400023163380315807363552714467324432,21264,12816,0,106158344586671995356807518795419695179027307605680178773111312,5754855389366911294404562696734450050413072,7235764250206835487401891354795559323972112,0,5841967675298671541051186596235810186474000,17168,12816,0,236413472138891394822672,12816,12816,0,12816,0,0,0]
def fourWord (t : M) := (words[t.val/16]! >>> (16*(t.val%16))) % 65536
def masks : Fin 15 → M := ![45,90,149,184,226,267,294,337,452,534,588,609,643,816,904]

def w0 : PortTree := (.split 0 (.split 2 (.split 3 (.split 5 (.split 1 (.split 6 (.miss 8) (.split 8 (.split 4 (.split 9 (.miss 49) (.split 7 (.mode 576) (.tri 2625))) (.split 9 (.split 7 (.miss 55) (.mode 208)) (.tri 2576))) (.tri 3441))) (.split 4 (.split 6 (.split 7 (.split 8 (.miss 30) (.split 9 (.miss 50) (.mode 770))) (.tri 3152)) (.tri 3088)) (.tri 3120))) (.tri 2848)) (.tri 2626)) (.tri 2929)) (.tri 2689))
theorem e0 : portCheck (masks 0) w0 0 1023 = true := by decide +kernel

def w1 : PortTree := (.split 1 (.split 3 (.split 4 (.split 6 (.split 0 (.split 5 (.miss 7) (.split 8 (.split 2 (.split 7 (.miss 17) (.split 9 (.mode 160) (.tri 2624))) (.split 7 (.split 9 (.miss 55) (.mode 548)) (.tri 1040))) (.tri 2160))) (.split 2 (.split 5 (.split 7 (.miss 15) (.split 8 (.miss 28) (.split 9 (.mode 385) (.tri 2881)))) (.tri 1296)) (.tri 1329))) (.tri 1313)) (.tri 1888)) (.tri 2626)) (.tri 3392))
theorem e1 : portCheck (masks 1) w1 0 1023 = true := by decide +kernel

def w2 : PortTree := (.split 0 (.split 2 (.split 4 (.split 7 (.split 1 (.split 6 (.miss 20) (.split 9 (.split 3 (.split 8 (.miss 35) (.split 5 (.mode 320) (.tri 1808))) (.split 8 (.split 5 (.miss 28) (.mode 104)) (.tri 1857))) (.tri 3489))) (.split 3 (.split 5 (.split 6 (.split 8 (.miss 29) (.split 9 (.miss 51) (.mode 770))) (.tri 2320)) (.tri 2336)) (.tri 2336))) (.tri 2132)) (.tri 1840)) (.tri 2929)) (.tri 2689))
theorem e2 : portCheck (masks 2) w2 0 1023 = true := by decide +kernel

def w3 : PortTree := (.split 3 (.split 4 (.split 5 (.split 7 (.split 0 (.split 1 (.miss 12) (.split 2 (.split 6 (.split 8 (.miss 30) (.split 9 (.miss 51) (.mode 770))) (.split 8 (.split 9 (.mode 66) (.tri 2576)) (.tri 1808))) (.tri 1808))) (.split 1 (.split 2 (.miss 1) (.split 6 (.miss 8) (.split 8 (.split 9 (.mode 69) (.tri 3185)) (.tri 2417)))) (.tri 2064))) (.tri 2132)) (.tri 2848)) (.tri 1840)) (.tri 2626))
theorem e3 : portCheck (masks 3) w3 0 1023 = true := by decide +kernel

def w4 : PortTree := (.split 1 (.split 5 (.split 6 (.split 7 (.split 0 (.split 4 (.miss 19) (.split 9 (.split 2 (.split 3 (.miss 4) (.split 8 (.mode 24) (.tri 2080))) (.split 3 (.split 8 (.miss 35) (.mode 276)) (.tri 528))) (.tri 2976))) (.split 2 (.split 3 (.miss 9) (.split 4 (.split 8 (.split 9 (.miss 49) (.mode 521)) (.tri 1825)) (.tri 528))) (.tri 1329))) (.tri 2148)) (.tri 801)) (.tri 2848)) (.tri 3392))
theorem e4 : portCheck (masks 4) w4 0 1023 = true := by decide +kernel

def w5 : PortTree := (.split 0 (.split 1 (.split 3 (.split 8 (.split 2 (.split 7 (.miss 34) (.split 5 (.split 4 (.split 9 (.miss 49) (.split 6 (.mode 640) (.tri 2625))) (.split 9 (.split 6 (.miss 51) (.mode 208)) (.tri 2624))) (.tri 2880))) (.split 4 (.split 6 (.split 7 (.split 5 (.miss 15) (.split 9 (.miss 52) (.mode 548))) (.tri 2881)) (.tri 2897)) (.tri 2912))) (.tri 3463)) (.tri 2626)) (.tri 3136)) (.tri 2641))
theorem e5 : portCheck (masks 5) w5 0 1023 = true := by decide +kernel

def w6 : PortTree := (.split 1 (.split 2 (.split 5 (.split 8 (.split 0 (.split 4 (.miss 25) (.split 3 (.split 6 (.split 9 (.miss 51) (.split 7 (.mode 528) (.tri 2624))) (.split 9 (.split 7 (.miss 55) (.mode 208)) (.tri 2576))) (.tri 2592))) (.split 4 (.split 3 (.miss 2) (.split 6 (.split 7 (.split 9 (.miss 49) (.mode 521)) (.tri 2657)) (.tri 2609))) (.tri 2576))) (.tri 3463)) (.tri 2848)) (.tri 2865)) (.tri 3136))
theorem e6 : portCheck (masks 6) w6 0 1023 = true := by decide +kernel

def w7 : PortTree := (.split 0 (.split 4 (.split 6 (.split 8 (.split 1 (.split 2 (.miss 26) (.split 3 (.split 5 (.split 7 (.miss 15) (.split 9 (.mode 132) (.tri 2625))) (.split 7 (.split 9 (.miss 55) (.mode 548)) (.tri 1040))) (.tri 1057))) (.split 2 (.split 3 (.miss 4) (.split 5 (.split 7 (.miss 17) (.split 9 (.mode 138) (.tri 2880))) (.tri 1072))) (.tri 1040))) (.tri 3463)) (.tri 1313)) (.tri 1584)) (.tri 2641))
theorem e7 : portCheck (masks 7) w7 0 1023 = true := by decide +kernel

def w8 : PortTree := (.split 2 (.split 6 (.split 7 (.split 8 (.split 0 (.split 1 (.miss 33) (.split 3 (.split 4 (.miss 5) (.split 5 (.miss 6) (.split 9 (.mode 50) (.tri 2592)))) (.tri 1312))) (.split 1 (.split 5 (.split 3 (.split 4 (.miss 2) (.split 9 (.mode 17) (.tri 2832))) (.split 4 (.split 9 (.miss 49) (.mode 521)) (.tri 528))) (.tri 528)) (.tri 1040))) (.tri 3463)) (.tri 1620)) (.tri 801)) (.tri 2865))
theorem e8 : portCheck (masks 8) w8 0 1023 = true := by decide +kernel

def w9 : PortTree := (.split 1 (.split 2 (.split 4 (.split 9 (.split 0 (.split 5 (.miss 45) (.split 7 (.split 3 (.split 8 (.miss 35) (.split 6 (.mode 288) (.tri 1808))) (.split 8 (.split 6 (.miss 30) (.mode 104)) (.tri 1856))) (.tri 2112))) (.split 3 (.split 5 (.split 6 (.split 7 (.miss 15) (.split 8 (.miss 28) (.mode 385))) (.tri 2081)) (.tri 2064)) (.tri 2081))) (.tri 3514)) (.tri 1888)) (.tri 1841)) (.tri 2368))
theorem e9 : portCheck (masks 9) w9 0 1023 = true := by decide +kernel

def w10 : PortTree := (.split 2 (.split 3 (.split 6 (.split 9 (.split 0 (.split 1 (.miss 42) (.split 4 (.miss 5) (.split 5 (.miss 6) (.split 7 (.split 8 (.mode 50) (.tri 2112)) (.tri 1344))))) (.split 1 (.split 4 (.split 5 (.split 7 (.miss 15) (.split 8 (.miss 28) (.mode 385))) (.split 7 (.split 8 (.mode 33) (.tri 1808)) (.tri 1040))) (.tri 1552)) (.tri 1040))) (.tri 3514)) (.tri 1569)) (.tri 1346)) (.tri 1841))
theorem e10 : portCheck (masks 10) w10 0 1023 = true := by decide +kernel

def w11 : PortTree := (.split 0 (.split 5 (.split 6 (.split 9 (.split 1 (.split 2 (.miss 46) (.split 7 (.split 3 (.split 4 (.miss 2) (.split 8 (.miss 35) (.mode 276))) (.split 4 (.split 8 (.mode 12) (.tri 2081)) (.tri 528))) (.tri 1601))) (.split 2 (.split 3 (.miss 4) (.split 4 (.split 7 (.miss 17) (.split 8 (.mode 138) (.tri 1824))) (.tri 800))) (.tri 1040))) (.tri 3514)) (.tri 1569)) (.tri 800)) (.tri 2129))
theorem e11 : portCheck (masks 11) w11 0 1023 = true := by decide +kernel

def w12 : PortTree := (.split 0 (.split 1 (.split 7 (.split 9 (.split 2 (.split 3 (.miss 43) (.split 4 (.split 5 (.split 8 (.miss 28) (.split 6 (.mode 264) (.tri 1825))) (.split 8 (.split 6 (.miss 30) (.mode 104)) (.tri 1824))) (.tri 1824))) (.split 3 (.split 4 (.miss 14) (.split 5 (.split 6 (.split 8 (.miss 32) (.mode 276)) (.tri 1824)) (.tri 1824))) (.tri 1825))) (.tri 3514)) (.tri 2148)) (.tri 2368)) (.tri 2129))
theorem e12 : portCheck (masks 12) w12 0 1023 = true := by decide +kernel

def w13 : PortTree := (.split 4 (.split 5 (.split 8 (.split 9 (.split 0 (.split 1 (.miss 59) (.split 6 (.split 2 (.split 3 (.miss 4) (.split 7 (.miss 17) (.mode 138))) (.split 3 (.split 7 (.mode 6) (.tri 1296)) (.tri 528))) (.tri 528))) (.split 1 (.split 2 (.miss 1) (.split 3 (.split 6 (.miss 8) (.split 7 (.mode 69) (.tri 1057))) (.tri 1057))) (.tri 1296))) (.tri 3258)) (.tri 2439)) (.tri 800)) (.tri 1584))
theorem e13 : portCheck (masks 13) w13 0 1023 = true := by decide +kernel

def w14 : PortTree := (.split 3 (.split 7 (.split 8 (.split 9 (.split 0 (.split 1 (.miss 12) (.split 2 (.split 4 (.miss 25) (.split 5 (.miss 45) (.split 6 (.mode 50) (.tri 528)))) (.tri 784))) (.split 4 (.split 5 (.split 1 (.split 2 (.miss 1) (.split 6 (.miss 8) (.mode 69))) (.split 2 (.split 6 (.mode 3) (.tri 528)) (.tri 784))) (.tri 528)) (.tri 784))) (.tri 3258)) (.tri 2439)) (.tri 1620)) (.tri 1346))
theorem e14 : portCheck (masks 14) w14 0 1023 = true := by decide +kernel

def trees : Fin 15 → PortTree := ![w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14]
theorem exceptional (i : Fin 15) : portCheck (masks i) (trees i) 0 1023 = true := by
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6
  · exact e7
  · exact e8
  · exact e9
  · exact e10
  · exact e11
  · exact e12
  · exact e13
  · exact e14

def tested (t : M) := decide (4 < population t) ||
  ((List.finRange 15).any (fun i => masks i == t) || clique t 4 (fourWord t))
def label (q : Fin 32) (i : Fin 32) : M := ⟨q.val*32+i.val,by omega⟩
def lane (q : Fin 32) := (List.finRange 32).all (fun i => tested (label q i))

theorem l0 : lane 0 = true := by decide +kernel
theorem l1 : lane 1 = true := by decide +kernel
theorem l2 : lane 2 = true := by decide +kernel
theorem l3 : lane 3 = true := by decide +kernel
theorem l4 : lane 4 = true := by decide +kernel
theorem l5 : lane 5 = true := by decide +kernel
theorem l6 : lane 6 = true := by decide +kernel
theorem l7 : lane 7 = true := by decide +kernel
theorem l8 : lane 8 = true := by decide +kernel
theorem l9 : lane 9 = true := by decide +kernel
theorem l10 : lane 10 = true := by decide +kernel
theorem l11 : lane 11 = true := by decide +kernel
theorem l12 : lane 12 = true := by decide +kernel
theorem l13 : lane 13 = true := by decide +kernel
theorem l14 : lane 14 = true := by decide +kernel
theorem l15 : lane 15 = true := by decide +kernel
theorem l16 : lane 16 = true := by decide +kernel
theorem l17 : lane 17 = true := by decide +kernel
theorem l18 : lane 18 = true := by decide +kernel
theorem l19 : lane 19 = true := by decide +kernel
theorem l20 : lane 20 = true := by decide +kernel
theorem l21 : lane 21 = true := by decide +kernel
theorem l22 : lane 22 = true := by decide +kernel
theorem l23 : lane 23 = true := by decide +kernel
theorem l24 : lane 24 = true := by decide +kernel
theorem l25 : lane 25 = true := by decide +kernel
theorem l26 : lane 26 = true := by decide +kernel
theorem l27 : lane 27 = true := by decide +kernel
theorem l28 : lane 28 = true := by decide +kernel
theorem l29 : lane 29 = true := by decide +kernel
theorem l30 : lane 30 = true := by decide +kernel
theorem l31 : lane 31 = true := by decide +kernel

theorem all_lanes (q : Fin 32) : lane q = true := by
  fin_cases q
  · exact l0
  · exact l1
  · exact l2
  · exact l3
  · exact l4
  · exact l5
  · exact l6
  · exact l7
  · exact l8
  · exact l9
  · exact l10
  · exact l11
  · exact l12
  · exact l13
  · exact l14
  · exact l15
  · exact l16
  · exact l17
  · exact l18
  · exact l19
  · exact l20
  · exact l21
  · exact l22
  · exact l23
  · exact l24
  · exact l25
  · exact l26
  · exact l27
  · exact l28
  · exact l29
  · exact l30
  · exact l31

theorem all_tested (t : M) : tested t = true := by
  let q : Fin 32 := ⟨t.val/32,by have := t.isLt; omega⟩
  let i : Fin 32 := ⟨t.val%32,Nat.mod_lt _ (by decide)⟩
  have eq : label q i = t := Fin.ext (by change (t.val/32)*32+t.val%32 = t.val; omega)
  exact eq ▸ List.all_eq_true.mp (all_lanes q) i (List.mem_finRange i)

theorem impossible (m : Model) : False := by
  have valid := all_tested m.t
  rcases Bool.or_eq_true_iff.mp valid with many | rest
  · exact (Nat.not_lt_of_le m.size) (of_decide_eq_true many)
  · rcases Bool.or_eq_true_iff.mp rest with e | four
    · obtain ⟨i,_,eq⟩ := List.any_eq_true.mp e
      exact exception_impossible m (trees i) (eq_of_beq eq ▸ exceptional i)
    · exact four_impossible m _ four

end PetersenDiagonalNumeric.Checked
#print axioms PetersenDiagonalNumeric.Checked.impossible
