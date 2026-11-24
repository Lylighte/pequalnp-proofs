import OrbitRows
namespace PetersenSecondCube.Envelope.Atlas.ShardA
set_option maxHeartbeats 40000000
set_option maxRecDepth 24000
run_cmd Lean.logInfo m!"ATLAS_BEGIN {← IO.monoMsNow}"
namespace T0
def s : Group := ⟨122,1152886180648321023,4621⟩
local notation "V" => refutesLoose s
theorem n13 : V ⟨0,1792,0,1925⟩ := localProof s _ "XXXSXXTXSNXXSXXTXSNLXXXSNXXTXNUJXVKXXXXUSXXSNXXNLXVKXXXSUXVJXXXSXNXVKTI" (by decide +kernel)
theorem n14 : V ⟨128,1920,0,1925⟩ := localProof s _ "XXXXTNXVKXXTXXTUXVJXXNXLXXNXVKXXUXVJXXXNXVKTIXXXTXNXVKXXVXNXLXUJXXXVKXUXNXLXTIS" (by decide +kernel)
theorem n12 : V ⟨0,1920,0,1925⟩ := split_loose s _ false 7 n13 n14
theorem n15 : V ⟨4,1924,0,1925⟩ := localProof s _ "XXXXSUXVKXXXTUXVJXXXSTXVIXXSXTXVHXXXTXSXVKXXVXSXLXTIXXVXTXLXSHN" (by decide +kernel)
theorem n11 : V ⟨0,1924,0,1925⟩ := split_loose s _ false 2 n12 n15
theorem n18 : V ⟨1,1921,0,1924⟩ := localProof s _ "XXXTXXTSXXTXSNXXXTNXXTXSXNUJXVKXXXXUSXXSNXVKXXXSUXVJXXXSXNXVKTIXXXXTNXVKXXTXXNUXVJXXNXXNXVKXXUXVJXXXNXVKTIXXXIXKVXUXTXNSH" (by decide +kernel)
theorem n19 : V ⟨5,1925,0,1924⟩ := localProof s _ "XXXXTUXVKXXXTUXVJXXXSTXVIXXSXTXVHXXXIXHXKVXTXSN" (by decide +kernel)
theorem n17 : V ⟨1,1925,0,1924⟩ := split_loose s _ false 2 n18 n19
theorem n20 : V ⟨1,1925,1,1925⟩ := localProof s _ "XXXUXNXVKXXVXSXTIXXVXTXSHXXXKXJUXVXNC" (by decide +kernel)
theorem n16 : V ⟨1,1925,0,1925⟩ := split_loose s _ true 0 n17 n20
theorem n10 : V ⟨0,1925,0,1925⟩ := split_loose s _ false 0 n11 n16
theorem n21 : V ⟨0,1925,64,1989⟩ := localProof s _ "WXXWIXHWAWCNWUWTWSWVK" (by decide +kernel)
theorem n9 : V ⟨0,1925,0,1989⟩ := split_loose s _ true 6 n10 n21
theorem n22 : V ⟨0,1925,32,2021⟩ := localProof s _ "WXXWSWTIWVKWXXNKXXNXKIWVWTWSHWWXWVWTIWSHXKXJWNCWXWSWNXJWVKWXWNKXXNXKIWVWTWSHWWXWVWTIWSHXKXJWNCXWKWJWCLAWWKR" (by decide +kernel)
theorem n8 : V ⟨0,1925,0,2021⟩ := split_loose s _ true 5 n9 n22
theorem n23 : V ⟨0,1925,16,2037⟩ := localProof s _ "WWXXSWNWLJXWNIXXNHXXSCXWSWNWLAWUWRWQWVK" (by decide +kernel)
theorem n7 : V ⟨0,1925,0,2037⟩ := split_loose s _ true 4 n8 n23
theorem n24 : V ⟨0,1925,8,2045⟩ := localProof s _ "WXXWIXHWCWAWJUWTWSWNWRWQWPWVK" (by decide +kernel)
theorem n6 : V ⟨0,1925,0,2045⟩ := split_loose s _ true 3 n7 n24
theorem n25 : V ⟨0,1925,2,2047⟩ := localProof s _ "WXXTXXSIXXTHXXWTSWLCXWTWSWLAWNWRWQWPWOWVK" (by decide +kernel)
theorem n5 : V ⟨0,1925,0,2047⟩ := split_loose s _ true 1 n6 n25
theorem n27 : V ⟨64,1989,0,1983⟩ := localProof s _ "WXXWTXSWLWNCWJWIWHWKVWWWVWSHWKWJWCQWWKPWWKOWXWXTSXLWVWNCWKWJWIWHWQWPWOM" (by decide +kernel)
theorem n28 : V ⟨64,1989,64,2047⟩ := localProof s _ "XXXNWTWSWVKXXSWVWTWNWLWUJXWVWUWSWNWLWTIXXNXWUJXWNIWVWTWLWSHXXWVKXXWKSJXWVIXWVHWUWTWLWNCXXXCWIWHWKVWUWTWSWNWLAWQWPWOWM" (by decide +kernel)
theorem n26 : V ⟨64,1989,0,2047⟩ := split_loose s _ true 6 n27 n28
theorem n4 : V ⟨0,1989,0,2047⟩ := split_loose s _ false 6 n5 n26
theorem n31 : V ⟨32,1957,0,2015⟩ := localProof s _ "WXXWUJWKSXVWWVWTIWWVWSHXXVWUWNCXXVWWSWVKXXVJWWVWTIWWVWSHXXVCXWVLWUWNAWWWSWVKWHWARWWKWHWCWRPWWWSWVKWHWAWRWPOWWKWHWRWPWOM" (by decide +kernel)
theorem n32 : V ⟨96,2021,0,2015⟩ := localProof s _ "WWVWOWMWR" (by decide +kernel)
theorem n30 : V ⟨32,2021,0,2015⟩ := split_loose s _ false 6 n31 n32
theorem n33 : V ⟨32,2021,32,2047⟩ := localProof s _ "XXWVWTIXWVWSHXWTWSWLAXUXNXJXCWRWPWOWMWG" (by decide +kernel)
theorem n29 : V ⟨32,2021,0,2047⟩ := split_loose s _ true 5 n30 n33
theorem n3 : V ⟨0,2021,0,2047⟩ := split_loose s _ false 5 n4 n29
theorem n35 : V ⟨16,2037,0,2031⟩ := localProof s _ "WXXHXXHCWWUWTWSWNWLAWJWRWKVWWWVWSHWKWJWCWRQWWWWUWTIWNCWKWJWRWQOWWKMWWVWQWOWMWRGWWVWOWMWQF" (by decide +kernel)
theorem n36 : V ⟨16,2037,16,2047⟩ := localProof s _ "XXXNXXSWNWLJWUWVKXXWNWVKWTIXXXNWVKXIWSHXXXXSWVKWUJXIXHWNCXXWVKXIXCWUWTWSWNWLAWRWQWOWMWGWF" (by decide +kernel)
theorem n34 : V ⟨16,2037,0,2047⟩ := split_loose s _ true 4 n35 n36
theorem n2 : V ⟨0,2037,0,2047⟩ := split_loose s _ false 4 n3 n34
theorem n38 : V ⟨8,2045,0,2039⟩ := localProof s _ "WXXWTXSWNWLWUJWIWHWCWRWKVWWWVWSHWKWJWCWRQWWWVWNWLWKWUJWIWHWCWRWQPWWKMWWVWQWPWMWRGWWVWPWMWQFWWVWQWMWPE" (by decide +kernel)
theorem n39 : V ⟨8,2045,8,2047⟩ := localProof s _ "XXWTWNWVKXXWTWNWLWVKWUJXWVWSWNWLWTIXXWNKXWNJXWNIWVWTWLWSHXXSWVWUWTWLWNCXXWIWCWKVWUWTWSWNWLAWRWQWPWMWGWFWE" (by decide +kernel)
theorem n37 : V ⟨8,2045,0,2047⟩ := split_loose s _ true 3 n38 n39
theorem n1 : V ⟨0,2045,0,2047⟩ := split_loose s _ false 3 n2 n37
theorem n41 : V ⟨2,2047,0,2045⟩ := localProof s _ "WXXIXXIHXXIWTWSWNWLAWCWKVWWXWVWSWUJWTIWKWCRWWWVWSHWKWJWCWRQWWKPWWKOWWVWQWPWOWRGWWVWRWPWOWQFWWVWQWOWPEWWVWQWPWOD" (by decide +kernel)
theorem n42 : V ⟨2,2047,2,2047⟩ := localProof s _ "XXXUWVKXJXXWUWVKXJWTIXXXTWVKXJXIWSHXWVWUWTWLWNCXXWVKXJXIWTWSWNWLAWRWQWPWOWGWFWEWD" (by decide +kernel)
theorem n40 : V ⟨2,2047,0,2047⟩ := split_loose s _ true 1 n41 n42
theorem n0 : V ⟨0,2047,0,2047⟩ := split_loose s _ false 1 n1 n40
run_cmd Lean.logInfo m!"TREE_0 {← IO.monoMsNow}"
def rs : List Entry := [⟨3,392,20⟩,⟨3,393,20⟩,⟨3,397,20⟩,⟨3,410,20⟩,⟨3,905,20⟩,⟨5,336,15⟩,⟨5,337,15⟩,⟨5,338,15⟩,⟨5,339,15⟩,⟨5,340,15⟩,⟨5,342,15⟩,⟨5,345,15⟩,⟨5,347,15⟩,⟨5,372,15⟩,⟨5,374,15⟩,⟨5,464,15⟩,⟨5,465,15⟩,⟨5,466,15⟩,⟨5,467,15⟩,⟨5,473,15⟩,⟨11,176,101⟩,⟨11,178,101⟩,⟨11,385,20⟩,⟨11,386,20⟩,⟨11,387,20⟩,⟨11,389,20⟩,⟨11,390,20⟩,⟨11,391,20⟩,⟨11,392,20⟩,⟨11,393,20⟩,⟨11,394,20⟩,⟨11,397,20⟩,⟨11,400,20⟩,⟨11,401,20⟩,⟨11,402,20⟩,⟨11,403,20⟩,⟨11,404,20⟩,⟨11,405,20⟩,⟨11,406,20⟩,⟨11,407,20⟩,⟨11,410,20⟩,⟨11,643,21⟩,⟨11,645,21⟩,⟨11,647,21⟩,⟨11,648,21⟩,⟨11,649,21⟩,⟨11,653,21⟩,⟨11,663,21⟩,⟨11,897,20⟩,⟨11,899,20⟩,⟨11,904,20⟩,⟨42,89,0⟩,⟨42,90,0⟩,⟨42,91,0⟩,⟨42,112,0⟩,⟨42,113,0⟩,⟨42,114,0⟩,⟨42,116,0⟩,⟨42,117,0⟩,⟨42,118,0⟩,⟨42,121,0⟩,⟨42,125,0⟩,⟨42,151,10⟩,⟨42,189,10⟩,⟨42,210,0⟩,⟨42,373,0⟩,⟨42,564,4⟩,⟨43,69,12⟩,⟨43,77,12⟩,⟨43,101,12⟩,⟨43,114,0⟩,⟨45,77,46⟩,⟨45,588,37⟩,⟨47,77,46⟩,⟨50,106,0⟩,⟨50,107,0⟩,⟨50,202,0⟩,⟨54,154,11⟩,⟨54,278,2⟩,⟨54,279,2⟩,⟨54,306,98⟩,⟨54,308,5⟩,⟨54,309,5⟩,⟨54,325,44⟩,⟨54,774,2⟩]
theorem settled : ∀ r∈rs, excludes r := members s n0 rs (by decide +kernel)
run_cmd Lean.logInfo m!"MEMBERS_0 {← IO.monoMsNow}"
end T0
namespace T1
def s : Group := ⟨31,1143905509259083775,16931⟩
local notation "V" => refutesLoose s
theorem n52 : V ⟨0,2016,0,2032⟩ := localProof s _ "XXXXQSXTXXXQSXTHXVKXXXSXVKXXVXSIXXVXSHXXXSXQXVKXHRGXXXRXVKXXVXRHXXVXRGXXXSXRXVKXJXGQFWXXQWTWSWRWVKWXWVKXWVGWUWRWQFP" (by decide +kernel)
theorem n53 : V ⟨0,2016,8,2040⟩ := localProof s _ "WXWUWTXJWSWRWQWVKWXWSWRKXWUGWVWQFWWKWFP" (by decide +kernel)
theorem n51 : V ⟨0,2016,0,2040⟩ := split_loose s _ true 3 n52 n53
theorem n54 : V ⟨0,2016,4,2044⟩ := localProof s _ "WXWTWSWRWQWVKWXWSWRKXWSWRGWVWQFWWKWFPWWKWGO" (by decide +kernel)
theorem n50 : V ⟨0,2016,0,2044⟩ := split_loose s _ true 2 n51 n54
theorem n55 : V ⟨0,2016,2,2046⟩ := localProof s _ "WXXWTQXJWSWRWVKWXWVKXWVHXWVWSGWUWRWQFWXXQWUWTWSWRWJWGWVKWIWHWFPWWKWFOWWKWFN" (by decide +kernel)
theorem n49 : V ⟨0,2016,0,2046⟩ := split_loose s _ true 1 n50 n55
theorem n56 : V ⟨0,2016,1,2047⟩ := localProof s _ "WXXWTRWSWQWVKWXWVKXJXIWSWQWRGWXWSWRWVKWXWVKXJXIWSWRGWQFWWKWFPWWKWGOWWKWGNWWKWFM" (by decide +kernel)
theorem n48 : V ⟨0,2016,0,2047⟩ := split_loose s _ true 0 n49 n56
theorem n58 : V ⟨16,2032,0,2031⟩ := localProof s _ "XWWRWVKWWVWQWUJWWVWTIWWVWSHWWVWRGWXWIWHWGWKVWQFWWKWGOWWKWGNWWWRWVKWJWIWHWFWOWNMWWKWHWGWML" (by decide +kernel)
theorem n59 : V ⟨16,2032,16,2047⟩ := localProof s _ "XXXQWTWSWRWVKXXWUWRWVKWTIXWVWTWRWSHXWVWSWQWRGXXWIWHWGWKVWUWRWQFWOWNWMWL" (by decide +kernel)
theorem n57 : V ⟨16,2032,0,2047⟩ := split_loose s _ true 4 n58 n59
theorem n47 : V ⟨0,2032,0,2047⟩ := split_loose s _ false 4 n48 n57
theorem n61 : V ⟨8,2040,0,2039⟩ := localProof s _ "XWWQWVKWWVWUJWWVWSWTIWWVWSHWWVWRGWWVWQFWWKWIWHWFPWWKWIWGNWWKWFMWWKWGWPWNWMLWWVWQWMWLWPE" (by decide +kernel)
theorem n62 : V ⟨8,2040,8,2047⟩ := localProof s _ "XXWSWRWQWVKXWVWUWSWTIXWVWTWRWSHXWVWSWQWRGXWVWUWRWQFWPWNWMWLWE" (by decide +kernel)
theorem n60 : V ⟨8,2040,0,2047⟩ := split_loose s _ true 3 n61 n62
theorem n46 : V ⟨0,2040,0,2047⟩ := split_loose s _ false 3 n47 n60
theorem n64 : V ⟨4,2044,0,2043⟩ := localProof s _ "XWWQWVKWWVWTIWWVWRWSHWWVWRGWWVWQFWWKWFPWWKWHWGOWWKWHWFMWWKWHWGWPWOWMLWWVWQWMWLWPEWWVWRWLWOD" (by decide +kernel)
theorem n65 : V ⟨4,2044,4,2047⟩ := localProof s _ "XXWSWRWQWVKXWVWTWRWSHXWVWSWQWRGXWVWUWRWQFWPWOWMWLWEWD" (by decide +kernel)
theorem n63 : V ⟨4,2044,0,2047⟩ := split_loose s _ true 2 n64 n65
theorem n45 : V ⟨0,2044,0,2047⟩ := split_loose s _ false 2 n46 n63
theorem n69 : V ⟨2,2034,0,2045⟩ := localProof s _ "XWWSWVKWWVWTIWWVWSHWWVWQWRGWXWIWHWGWKVWQFWWWSWVKWIWHWGWFPWWKWGWPOWWKWGWPNWWKWGWPLWXXFWJWIWHWGWOWNWKVWWVWNWKWJWIWHWGLWTWSWQWPE" (by decide +kernel)
theorem n70 : V ⟨10,2042,0,2045⟩ := localProof s _ "WWVWQWPWLWO" (by decide +kernel)
theorem n68 : V ⟨2,2042,0,2045⟩ := split_loose s _ false 3 n69 n70
theorem n71 : V ⟨6,2046,0,2045⟩ := localProof s _ "WWVWQWPWLWN" (by decide +kernel)
theorem n67 : V ⟨2,2046,0,2045⟩ := split_loose s _ false 2 n68 n71
theorem n72 : V ⟨2,2046,2,2047⟩ := localProof s _ "XXXIWSWRWVKXXXQWRWVKWSHXWVWSWQWRGXXWHWGWKVWUWRWQFWPWOWNWLWEWDWC" (by decide +kernel)
theorem n66 : V ⟨2,2046,0,2047⟩ := split_loose s _ true 1 n67 n72
theorem n44 : V ⟨0,2046,0,2047⟩ := split_loose s _ false 1 n45 n66
theorem n77 : V ⟨1,2033,0,2046⟩ := localProof s _ "XWWSWVKWXWKVWTWUJWWVWTIWWVWSHWXWIWHWKVWSWRGWWVWRWQFWWKWFPWWWRWVKWJWHWGWFWPOWWWSWVKWJWIWGWFWPWONWWKWFWOWNMWWVWQWOWNWMWPE" (by decide +kernel)
theorem n78 : V ⟨9,2041,0,2046⟩ := localProof s _ "WWVWRWNWO" (by decide +kernel)
theorem n76 : V ⟨1,2041,0,2046⟩ := split_loose s _ false 3 n77 n78
theorem n79 : V ⟨5,2045,0,2046⟩ := localProof s _ "WWVWRWOWN" (by decide +kernel)
theorem n75 : V ⟨1,2045,0,2046⟩ := split_loose s _ false 2 n76 n79
theorem n80 : V ⟨3,2047,0,2046⟩ := localProof s _ "WWVWQWPWOWNWM" (by decide +kernel)
theorem n74 : V ⟨1,2047,0,2046⟩ := split_loose s _ false 1 n75 n80
theorem n81 : V ⟨1,2047,1,2047⟩ := localProof s _ "XXXWTRWQWVKXXWRWQWVKWSHXXWVKXJXIWSWQWRGXWVWUWRWQFWPWOWNWMWEWDWCWB" (by decide +kernel)
theorem n73 : V ⟨1,2047,0,2047⟩ := split_loose s _ true 0 n74 n81
theorem n43 : V ⟨0,2047,0,2047⟩ := split_loose s _ false 0 n44 n73
run_cmd Lean.logInfo m!"TREE_1 {← IO.monoMsNow}"
def rs : List Entry := [⟨3,28,0⟩,⟨3,29,0⟩,⟨3,60,0⟩,⟨3,61,0⟩,⟨3,62,0⟩,⟨3,124,0⟩,⟨3,125,0⟩,⟨3,157,0⟩,⟨3,189,0⟩,⟨3,221,0⟩,⟨7,25,0⟩,⟨7,26,16⟩,⟨7,27,0⟩,⟨7,29,0⟩,⟨7,56,16⟩,⟨7,58,16⟩,⟨11,21,0⟩,⟨11,23,0⟩,⟨11,29,0⟩,⟨11,52,12⟩,⟨11,53,0⟩,⟨11,54,12⟩,⟨11,60,0⟩,⟨11,61,0⟩,⟨11,62,0⟩,⟨11,116,0⟩,⟨11,117,0⟩,⟨11,124,0⟩,⟨11,125,0⟩,⟨11,148,0⟩,⟨11,149,0⟩,⟨11,150,0⟩,⟨11,151,0⟩,⟨11,157,0⟩,⟨11,166,13⟩,⟨11,173,13⟩,⟨11,180,0⟩,⟨11,182,0⟩,⟨11,189,0⟩,⟨11,212,0⟩,⟨11,213,0⟩,⟨11,214,0⟩,⟨11,221,0⟩,⟨11,277,0⟩,⟨11,279,0⟩,⟨11,305,34⟩,⟨11,308,12⟩,⟨11,309,0⟩,⟨11,310,12⟩,⟨15,23,0⟩,⟨15,27,0⟩,⟨15,84,0⟩,⟨15,85,0⟩,⟨42,277,16⟩,⟨42,279,16⟩,⟨43,54,48⟩,⟨47,54,48⟩,⟨47,58,52⟩,⟨54,77,40⟩]
theorem settled : ∀ r∈rs, excludes r := members s n43 rs (by decide +kernel)
run_cmd Lean.logInfo m!"MEMBERS_1 {← IO.monoMsNow}"
end T1
namespace T2
def s : Group := ⟨15,691293332780875775,21554⟩
local notation "V" => refutesLoose s
theorem n94 : V ⟨0,1792,0,2032⟩ := localProof s _ "XXXRXXTQXXRXXTQPXXSXXTQXXSXXTQPJXUXVKXXXSXUXVKXXXXRXPKQXVXUJXXXRXQXVKXXXQXVKXUJTI" (by decide +kernel)
theorem n95 : V ⟨128,1920,0,2032⟩ := localProof s _ "XXXUXTXVKXXVXTXUJXXXURXXPXUJXXXQKXXQJXPXRTXVIXXXRXQXVKXXVXQXUJXXRXVXUXTIS" (by decide +kernel)
theorem n93 : V ⟨0,1920,0,2032⟩ := split_loose s _ false 7 n94 n95
theorem n97 : V ⟨64,1984,0,1968⟩ := localProof s _ "XXXUXXUXTSXXTXSQXXUXQPXVKXXXQXPTXXTUXVJXXXQSXVXXVXUJXXUXVXSXQXPTIXXQXPXXXTQXVKXXXQUXVJXXXUXQXPTXVIXXVXXVIXQXPSH" (by decide +kernel)
theorem n98 : V ⟨64,1984,64,2032⟩ := localProof s _ "XXXUXSXQXVKXXVXTXQXUJXXVXUXSXPXTIXXVXXVXUIXTXPXSH" (by decide +kernel)
theorem n96 : V ⟨64,1984,0,2032⟩ := split_loose s _ true 6 n97 n98
theorem n92 : V ⟨0,1984,0,2032⟩ := split_loose s _ false 6 n93 n96
theorem n100 : V ⟨32,2016,0,2000⟩ := localProof s _ "XXXXTSXUXVKXXXXKTSXVXUJXXXSXRXPTXVXUIXXXTRXVXXVXUIXXVXUXRXPSHXXSXXXTSXPXUKXXPXUJXXTXSIXXXUSHXXSXURXVG" (by decide +kernel)
theorem n101 : V ⟨32,2016,32,2032⟩ := localProof s _ "XXXUXTXSXRXVKXXXTXVKXUJXXRXVXUXSXPXTIXXUXVXTXRXPXSHXXXUXTKXXTJXXTIXXUXTHXVXSXPXRG" (by decide +kernel)
theorem n99 : V ⟨32,2016,0,2032⟩ := split_loose s _ true 5 n100 n101
theorem n91 : V ⟨0,2016,0,2032⟩ := split_loose s _ false 5 n92 n99
theorem n106 : V ⟨16,1808,0,2016⟩ := localProof s _ "XXXTXSXXUXSRXXTXSXRQXVKXXRXQXXSXXSRXXTXRQXVKXXXSXQXVKUJXXQXXXRQXUXVKXXXRQXVXUJXXXSXVKXXXSXVKXUJXRXQTI" (by decide +kernel)
theorem n107 : V ⟨144,1936,0,2016⟩ := localProof s _ "XXXUXXTXRQXVKXXXTQXXQUXVJXXXQRXXUJXXJXRXQTXVIXXXVKXXVXUJXXVXUXTIXRXQS" (by decide +kernel)
theorem n105 : V ⟨16,1936,0,2016⟩ := split_loose s _ false 7 n106 n107
theorem n108 : V ⟨80,2000,0,2016⟩ := localProof s _ "XXXTXSXXTXSQXVKXXXTQXXTUXVJXXXSQXXUXVKXXVXUJXXUXVXSXQTIXXQXXXTQXVKXXXQUXVJXXXUXQTXVIXXVXTXQSHXXXUXVKXXVXUJXXVXUIXXVXQHXTXSR" (by decide +kernel)
theorem n104 : V ⟨16,2000,0,2016⟩ := split_loose s _ false 6 n105 n108
theorem n110 : V ⟨48,2032,0,1984⟩ := localProof s _ "XXTXXXSTXUXVKXXXRSXVXUJXXXSTXVXUIXXTXRXXUXVKXXVXUJXXVXUIXXVXUXRSHXXSXXSXUKXXUJXXTXSIXXXTSHXXUXSRXVG" (by decide +kernel)
theorem n111 : V ⟨48,2032,32,2016⟩ := localProof s _ "XXXUXVKXXVJXXVIXXUXVHXXUXVGXTXSXR" (by decide +kernel)
theorem n109 : V ⟨48,2032,0,2016⟩ := split_loose s _ true 5 n110 n111
theorem n103 : V ⟨16,2032,0,2016⟩ := split_loose s _ false 5 n104 n109
theorem n112 : V ⟨16,2032,16,2032⟩ := localProof s _ "XXXUXRXQXVKXXXUXQXVKXTIXXXQKXVXRXSHXXXTQXVXSXRGXXSXVXUXQF" (by decide +kernel)
theorem n102 : V ⟨16,2032,0,2032⟩ := split_loose s _ true 4 n103 n112
theorem n90 : V ⟨0,2032,0,2032⟩ := split_loose s _ false 4 n91 n102
theorem n113 : V ⟨0,2032,8,2040⟩ := localProof s _ "WXXWSHWUWTWRWVKWXKXWUWTIXWTWSHWVWQWPWRGWXKXHXGWUWRWPWQFWXWTWSWRWQWVKWXWTKXJWSWQWRGWXWTKXGWSWRWQFWWKWGWFPE" (by decide +kernel)
theorem n89 : V ⟨0,2032,0,2040⟩ := split_loose s _ true 3 n90 n113
theorem n114 : V ⟨0,2032,4,2044⟩ := localProof s _ "WWXWUWTWRWQWPWVKWSHWXWTHXIWVWSWQWPWRGWXWRWSHXWSWRGWVWUWQFWXWQWVKXWVWQGXWVWQFWTWSWRWPEWWKWGWFO" (by decide +kernel)
theorem n88 : V ⟨0,2032,0,2044⟩ := split_loose s _ true 2 n89 n114
theorem n118 : V ⟨0,2016,2,2034⟩ := localProof s _ "WXXIXJWUWTWSWRWVKWXWTWQWPKXWTWQWPHWVWSWRGWXWTWVKXWVWSHWXWTKXJXIXHWVWSGWUWRWPWQF" (by decide +kernel)
theorem n119 : V ⟨16,2032,2,2034⟩ := localProof s _ "WXWTWSWRWQWVKWXWTWQKXWTWQHWVWSWRGXXWVKXGWUWTWSWRWQFWWKWHWFP" (by decide +kernel)
theorem n117 : V ⟨0,2032,2,2034⟩ := split_loose s _ false 4 n118 n119
theorem n120 : V ⟨0,2032,10,2042⟩ := localProof s _ "WWKWGWF" (by decide +kernel)
theorem n116 : V ⟨0,2032,2,2042⟩ := split_loose s _ true 3 n117 n120
theorem n121 : V ⟨0,2032,6,2046⟩ := localProof s _ "WWIWHWFWE" (by decide +kernel)
theorem n115 : V ⟨0,2032,2,2046⟩ := split_loose s _ true 2 n116 n121
theorem n87 : V ⟨0,2032,0,2046⟩ := split_loose s _ true 1 n88 n115
theorem n125 : V ⟨0,2032,1,2033⟩ := localProof s _ "WXXXIRWUWSWQWVKWXWUWVKXWVXIWSHWQWPWRGWXWRWPKXWRWSHWXKXJXIWRGWVWUWQFWXWUWRWQWVKWXKXJXIWSWQWRGWXWRKXWRWSHXWSWRGWVWUWQFWWKWHWGPE" (by decide +kernel)
theorem n126 : V ⟨0,2032,9,2041⟩ := localProof s _ "WWKWGWF" (by decide +kernel)
theorem n124 : V ⟨0,2032,1,2041⟩ := split_loose s _ true 3 n125 n126
theorem n127 : V ⟨0,2032,5,2045⟩ := localProof s _ "WWKWG" (by decide +kernel)
theorem n123 : V ⟨0,2032,1,2045⟩ := split_loose s _ true 2 n124 n127
theorem n128 : V ⟨0,2032,3,2047⟩ := localProof s _ "WWKWGWF" (by decide +kernel)
theorem n122 : V ⟨0,2032,1,2047⟩ := split_loose s _ true 1 n123 n128
theorem n86 : V ⟨0,2032,0,2047⟩ := split_loose s _ true 0 n87 n122
theorem n130 : V ⟨8,2040,0,2039⟩ := localProof s _ "WWXURXVWWVWSWTIWWWTRXVWWVWTIWSHWWVWRGWXXHWIWGWKVWUWRWQFWXWTWPWKVWSWRWQEWWKWJWIWGNWWWRWVKWJWIWHWEWNMWWKWIWHWGWNWML" (by decide +kernel)
theorem n131 : V ⟨8,2040,8,2047⟩ := localProof s _ "XXXQWUWSWPWTIXXXQWUWPWTIWSHXXWTIXXJHWVWQWPWRGXXSWUWRWPWQFXWTWSWRWQWPEWNWMWL" (by decide +kernel)
theorem n129 : V ⟨8,2040,0,2047⟩ := split_loose s _ true 3 n130 n131
theorem n85 : V ⟨0,2040,0,2047⟩ := split_loose s _ false 3 n86 n129
theorem n133 : V ⟨4,2044,0,2043⟩ := localProof s _ "XWWRWVKWWVWUJWWSWPWTIWWRWPWSHWWVWRGWWVWRWQFWWSWRWPEWWWSWPWTIWKWJWHWGWFOWWKWHWFWEMWWKWHWGWOWMLWWVWRWQWMWLWOD" (by decide +kernel)
theorem n134 : V ⟨4,2044,4,2047⟩ := localProof s _ "XXXTWSWRWQWVKXXWSWRWQWPWVKWTIXXQWVWTWRWPWSHXXTWVWSWQWPWRGXXTWVWUWRWPWQFXXXIWHWGWFWKVWTWSWRWQWPEWOWMWLWD" (by decide +kernel)
theorem n132 : V ⟨4,2044,0,2047⟩ := split_loose s _ true 2 n133 n134
theorem n84 : V ⟨0,2044,0,2047⟩ := split_loose s _ false 2 n85 n132
theorem n138 : V ⟨2,2034,0,2045⟩ := localProof s _ "XWWSWVKWWVWUJWWVWSWTIWWVWSHWWVWQWRGWXXTWIWHWGWKVWUWQFWXXWTFWJWIWHWGWPWKVWSWQEWWKWGWFOWWKWJWIWONWWWVWUWSXPWQFWNWKWJWIWHWGWOL" (by decide +kernel)
theorem n139 : V ⟨10,2042,0,2045⟩ := localProof s _ "WWVWRWQWLWO" (by decide +kernel)
theorem n137 : V ⟨2,2042,0,2045⟩ := split_loose s _ false 3 n138 n139
theorem n140 : V ⟨6,2046,0,2045⟩ := localProof s _ "WWTWSWQWPWOWLWN" (by decide +kernel)
theorem n136 : V ⟨2,2046,0,2045⟩ := split_loose s _ false 2 n137 n140
theorem n141 : V ⟨2,2046,2,2047⟩ := localProof s _ "XXXQWRWVKXXXQWRWPWVKWTIXXXQWVKWTWRWPWSHXXTWVWSWQWPWRGXXWVKXWVWSHXWVWSGWUWRWPWQFXXXFWGWKVWTWSWRWQWPEWOWNWLWDWC" (by decide +kernel)
theorem n135 : V ⟨2,2046,0,2047⟩ := split_loose s _ true 1 n136 n141
theorem n83 : V ⟨0,2046,0,2047⟩ := split_loose s _ false 1 n84 n135
theorem n147 : V ⟨1,2033,0,2044⟩ := localProof s _ "XWWSWVKWWVWUJWXWKVWUWSWTIWWVWSHWWWSQXVWWVWUJWXWKVWUWSWTIWWVWSHWRGWWVWRWQFWXXXIGWJWHWFWPWKVWTWSWREWWKWGWFOWWWVWSHWGWFWEWON" (by decide +kernel)
theorem n148 : V ⟨1,2033,2,2046⟩ := localProof s _ "WWKWJWHWFWOWN" (by decide +kernel)
theorem n146 : V ⟨1,2033,0,2046⟩ := split_loose s _ true 1 n147 n148
theorem n149 : V ⟨9,2041,0,2046⟩ := localProof s _ "WWVWRWQWNWMWO" (by decide +kernel)
theorem n145 : V ⟨1,2041,0,2046⟩ := split_loose s _ false 3 n146 n149
theorem n150 : V ⟨5,2045,0,2046⟩ := localProof s _ "WWVWRWOWN" (by decide +kernel)
theorem n144 : V ⟨1,2045,0,2046⟩ := split_loose s _ false 2 n145 n150
theorem n151 : V ⟨3,2047,0,2046⟩ := localProof s _ "WWVWRWQWOWNWM" (by decide +kernel)
theorem n143 : V ⟨1,2047,0,2046⟩ := split_loose s _ false 1 n144 n151
theorem n152 : V ⟨1,2047,1,2047⟩ := localProof s _ "XXJXXJIXXIWVWTXRWPWSHXXIXSWQWPWRGXWVWUWRWPWQFXXUWTWSWRWQWPEWOWNWMWDWCWB" (by decide +kernel)
theorem n142 : V ⟨1,2047,0,2047⟩ := split_loose s _ true 0 n143 n152
theorem n82 : V ⟨0,2047,0,2047⟩ := split_loose s _ false 0 n83 n142
run_cmd Lean.logInfo m!"TREE_2 {← IO.monoMsNow}"
def rs : List Entry := [⟨3,12,0⟩,⟨3,13,0⟩,⟨3,14,0⟩,⟨3,44,0⟩,⟨3,45,0⟩,⟨3,46,0⟩,⟨3,56,12⟩,⟨3,57,12⟩,⟨3,58,12⟩,⟨3,108,0⟩,⟨3,109,0⟩,⟨3,110,0⟩,⟨3,141,0⟩,⟨3,152,12⟩,⟨3,153,12⟩,⟨3,154,12⟩,⟨3,184,12⟩,⟨3,185,12⟩,⟨3,186,12⟩,⟨3,205,0⟩,⟨3,216,12⟩,⟨3,217,12⟩,⟨3,218,12⟩,⟨3,248,12⟩,⟨3,249,12⟩,⟨3,250,12⟩,⟨3,269,0⟩,⟨3,314,12⟩,⟨5,25,4⟩,⟨5,27,4⟩,⟨5,60,4⟩,⟨5,62,4⟩,⟨5,89,4⟩,⟨5,91,4⟩,⟨5,124,4⟩,⟨5,126,4⟩,⟨5,281,4⟩,⟨5,283,4⟩,⟨5,409,4⟩,⟨5,411,4⟩,⟨7,11,0⟩,⟨7,13,36⟩,⟨11,13,0⟩,⟨11,44,0⟩,⟨11,45,0⟩,⟨11,46,0⟩,⟨11,56,12⟩,⟨11,57,12⟩,⟨11,58,12⟩,⟨11,108,0⟩,⟨11,109,0⟩,⟨11,110,0⟩,⟨11,135,0⟩,⟨11,141,0⟩,⟨11,147,12⟩,⟨11,152,12⟩,⟨11,153,12⟩,⟨11,154,12⟩,⟨11,184,12⟩,⟨11,185,12⟩,⟨11,186,12⟩,⟨11,205,0⟩,⟨11,216,12⟩,⟨11,217,12⟩,⟨11,218,12⟩,⟨11,263,0⟩,⟨11,269,0⟩,⟨11,314,12⟩]
theorem settled : ∀ r∈rs, excludes r := members s n82 rs (by decide +kernel)
run_cmd Lean.logInfo m!"MEMBERS_2 {← IO.monoMsNow}"
end T2
namespace T3
def s : Group := ⟨47,1125899767793057791,7224⟩
local notation "V" => refutesLoose s
theorem n166 : V ⟨0,1792,0,2000⟩ := localProof s _ "XXXXUXSPXRXXXSPXRXXSXPUJXXXUSXXSRXXUXRPXXPXRXXSXPUJXXRXPTIXVK" (by decide +kernel)
theorem n167 : V ⟨128,1920,0,2000⟩ := localProof s _ "XXXRXVKXXXPUXVJXXXRXVKXXXPUXVJXXXRXVKTIXXXUXVKXXPXVXTXUJXXXVKXUXPXTIS" (by decide +kernel)
theorem n165 : V ⟨0,1920,0,2000⟩ := split_loose s _ false 7 n166 n167
theorem n168 : V ⟨64,1984,0,2000⟩ := localProof s _ "XXXXUPXVKXXXPXXSXPUKXVJXXXXSPXVKXXXXUPKXVJXXVXPTIXXXPSXVHXXXUXVKXHR" (by decide +kernel)
theorem n164 : V ⟨0,1984,0,2000⟩ := split_loose s _ false 6 n165 n168
theorem n169 : V ⟨16,2000,0,2000⟩ := localProof s _ "XXXRXVKXXXRUXVJXXXRXVKXXXRUXVJXXVXRTIXXVXRHXXVXRGXXXUXRXVKXXRXVXTXUJXXXJXKVXUXSXTIXXVXRXSHXXVXSXRGP" (by decide +kernel)
theorem n163 : V ⟨0,2000,0,2000⟩ := split_loose s _ false 4 n164 n169
theorem n170 : V ⟨0,2000,32,2032⟩ := localProof s _ "WXXWIPWSWRWVKWXWPWVKXJWRGWXWSWRXGWVKXJWPE" (by decide +kernel)
theorem n162 : V ⟨0,2000,0,2032⟩ := split_loose s _ true 5 n163 n170
theorem n171 : V ⟨0,2000,8,2040⟩ := localProof s _ "WXXWUSWRWPWVKWXWSKWXWSKXJGWVWRWPEWWKWEQ" (by decide +kernel)
theorem n161 : V ⟨0,2000,0,2040⟩ := split_loose s _ true 3 n162 n171
theorem n172 : V ⟨0,2000,4,2044⟩ := localProof s _ "WWXHXGWUXJWSWRWVKWXWVKXWVGWTWSWRWPEWWKWEQWWKWEO" (by decide +kernel)
theorem n160 : V ⟨0,2000,0,2044⟩ := split_loose s _ true 2 n161 n172
theorem n173 : V ⟨0,2000,2,2046⟩ := localProof s _ "WXWSWRWPWVKWXWSKXJWVWRWPEWWKWEQWWKWGOWWKWEN" (by decide +kernel)
theorem n159 : V ⟨0,2000,0,2046⟩ := split_loose s _ true 1 n160 n173
theorem n174 : V ⟨0,2000,1,2047⟩ := localProof s _ "WXWUWSWRWPWVKWXKXJXIWVWSWPWRGWXWUKWXWSKXJGWVWRWPEWWKWGWEQWWKWGOWWKWENWWKWGM" (by decide +kernel)
theorem n158 : V ⟨0,2000,0,2047⟩ := split_loose s _ true 0 n159 n174
theorem n176 : V ⟨32,2032,0,2015⟩ := localProof s _ "XWWRWVKWWVWUJWXWKVWUWPIWWVWSHWWVWRGWXWTVWRWPEWWKWGOWWWRWVKWJWIWGWONWWKWHWEWOWNMWWKWHWGWOWNWML" (by decide +kernel)
theorem n177 : V ⟨32,2032,32,2047⟩ := localProof s _ "XXXWIPWSWRWVKXWVWRWPWSHXWVWPXJWRGXWTWRXJXGWPEWOWNWMWL" (by decide +kernel)
theorem n175 : V ⟨32,2032,0,2047⟩ := split_loose s _ true 5 n176 n177
theorem n157 : V ⟨0,2032,0,2047⟩ := split_loose s _ false 5 n158 n175
theorem n179 : V ⟨8,2040,0,2039⟩ := localProof s _ "WWXRWKPXVWXWKVWUWSIWXWJWKVWRWSHWWVWRGWWVWPEWWKWGWEQWWKWEWQNWWWRWVKWIWHWEWQWNMWWWPWVKWJWIWGWQWNWMLWWVWPWNWMWLWQF" (by decide +kernel)
theorem n180 : V ⟨8,2040,8,2047⟩ := localProof s _ "XXXWPWVKXJWTIXXXWPWVKXJWTIWSHXXXWSWVKXJWTIXHWRGXWTWSWRWPEWQWNWMWLWF" (by decide +kernel)
theorem n178 : V ⟨8,2040,0,2047⟩ := split_loose s _ true 3 n179 n180
theorem n156 : V ⟨0,2040,0,2047⟩ := split_loose s _ false 3 n157 n178
theorem n182 : V ⟨4,2044,0,2043⟩ := localProof s _ "XWWRWVKWWVWUJWWSWPWTIWWRWPWSHWWVWRGWWSWRWPEWWKWGWEQWWWVWPEWKWJWHWGWQOWWKWHWEWQMWWKWGWQLWWVWPWOWMWQFWWVWPWQWMWLWOD" (by decide +kernel)
theorem n183 : V ⟨4,2044,4,2047⟩ := localProof s _ "XXXPWSWRWVKXWVWRWPWSHXWVWSWPWRGXXWHWGWKVWTWSWRWPEWQWOWMWLWFWD" (by decide +kernel)
theorem n181 : V ⟨4,2044,0,2047⟩ := split_loose s _ true 2 n182 n183
theorem n155 : V ⟨0,2044,0,2047⟩ := split_loose s _ false 2 n156 n181
theorem n185 : V ⟨2,2046,0,2045⟩ := localProof s _ "XWWPWVKWWVWUJWXWKVWUWSIWWVWSHWWVWRGWWVWPEWWKWGWEQWWKWGWQOWWKWGWEWQWONWWKWGWQWOLWWVWPWOWNWQFWWVWRWQWLWODWWVWPWQWOWNC" (by decide +kernel)
theorem n186 : V ⟨2,2046,2,2047⟩ := localProof s _ "XXWRWPWVKXXWRWPWVKWSHXWVWSWPWRGXWVWSWRWPEWQWOWNWLWFWDWC" (by decide +kernel)
theorem n184 : V ⟨2,2046,0,2047⟩ := split_loose s _ true 1 n185 n186
theorem n154 : V ⟨0,2046,0,2047⟩ := split_loose s _ false 1 n155 n184
theorem n190 : V ⟨1,2041,0,2046⟩ := localProof s _ "XWWRWVKWWVWUJWXWJWKVWUWSIWWVWSHWWVWRGWWVWRWPEWWWVWSHWKWJWGWEQWWKWGWQOWWKWEWONWWKWJWHWOMWWVWRWPWOWNWMWQFWWVWRWQWMWOD" (by decide +kernel)
theorem n191 : V ⟨5,2045,0,2046⟩ := localProof s _ "WWSWRWPWQWOWN" (by decide +kernel)
theorem n189 : V ⟨1,2045,0,2046⟩ := split_loose s _ false 2 n190 n191
theorem n192 : V ⟨3,2047,0,2046⟩ := localProof s _ "WWVWRWQWOWM" (by decide +kernel)
theorem n188 : V ⟨1,2047,0,2046⟩ := split_loose s _ false 1 n189 n192
theorem n193 : V ⟨1,2047,1,2047⟩ := localProof s _ "XXXJWRWPWVKXXWRWVKWUWSWPWTIXWVWTWRWPWSHXWVWSWPWRGXWVWTWSWRWPEWQWOWNWMWFWDWCWB" (by decide +kernel)
theorem n187 : V ⟨1,2047,0,2047⟩ := split_loose s _ true 0 n188 n193
theorem n153 : V ⟨0,2047,0,2047⟩ := split_loose s _ false 0 n154 n187
run_cmd Lean.logInfo m!"TREE_3 {← IO.monoMsNow}"
def rs : List Entry := [⟨5,296,44⟩,⟨5,298,44⟩,⟨5,312,44⟩,⟨5,314,44⟩,⟨5,440,44⟩,⟨5,808,44⟩,⟨5,810,44⟩,⟨5,824,44⟩,⟨7,41,0⟩,⟨7,42,0⟩,⟨7,43,0⟩,⟨11,261,36⟩,⟨11,293,10⟩,⟨11,298,10⟩,⟨42,45,0⟩,⟨42,53,25⟩,⟨42,61,0⟩,⟨42,77,0⟩,⟨42,109,0⟩,⟨42,263,0⟩,⟨42,519,0⟩,⟨42,525,0⟩,⟨42,533,25⟩,⟨42,535,0⟩,⟨42,557,0⟩,⟨42,565,25⟩,⟨42,589,0⟩,⟨42,621,0⟩,⟨42,775,0⟩,⟨42,789,25⟩,⟨42,791,0⟩,⟨43,45,0⟩,⟨43,46,0⟩]
theorem settled : ∀ r∈rs, excludes r := members s n153 rs (by decide +kernel)
run_cmd Lean.logInfo m!"MEMBERS_3 {← IO.monoMsNow}"
end T3
namespace T4
def s : Group := ⟨203,691293332780875775,822⟩
local notation "V" => refutesLoose s
theorem n205 : V ⟨0,1840,0,1844⟩ := localProof s _ "XXXXPQXXNXXPXNTIXVKXXXVKXXTXVXPIXXXPXVKXJQFXXXXNTXVKXXXQXNXKVXXXNXVKTIXXVXXNXVKXXNXXNXVKXXXNXVKUJXXTXVIXXNQFXXXQXVKXXVXQFPE" (by decide +kernel)
theorem n206 : V ⟨4,1844,0,1844⟩ := localProof s _ "XXXQXVKXXVXPIXXXPXKVXXXPXVKXJQFXXXQVXXXQXVKXIXFPEXXXPXVKXXXPXVKXQFXXVXQXPEN" (by decide +kernel)
theorem n204 : V ⟨0,1844,0,1844⟩ := split_loose s _ false 2 n205 n206
theorem n207 : V ⟨0,1844,128,1972⟩ := localProof s _ "WWXKEXWVWTWQWPWNC" (by decide +kernel)
theorem n203 : V ⟨0,1844,0,1972⟩ := split_loose s _ true 7 n204 n207
theorem n208 : V ⟨0,1844,64,2036⟩ := localProof s _ "WXXXQNWTWPWSWVK" (by decide +kernel)
theorem n202 : V ⟨0,1844,0,2036⟩ := split_loose s _ true 6 n203 n208
theorem n209 : V ⟨0,1844,8,2044⟩ := localProof s _ "WXXQWTWPWNWVKWXWTWPKXXQWTWPEWVWNCWWFWESWWKR" (by decide +kernel)
theorem n201 : V ⟨0,1844,0,2044⟩ := split_loose s _ true 3 n202 n209
theorem n210 : V ⟨0,1844,2,2046⟩ := localProof s _ "WXXXWUJWIWFWCWEPWTWQWNWSWRWOWVK" (by decide +kernel)
theorem n200 : V ⟨0,1844,0,2046⟩ := split_loose s _ true 1 n201 n210
theorem n211 : V ⟨0,1844,1,2047⟩ := localProof s _ "WXXWTNWQWPWSWRWOWMWVK" (by decide +kernel)
theorem n199 : V ⟨0,1844,0,2047⟩ := split_loose s _ true 0 n200 n211
theorem n213 : V ⟨128,1972,0,1919⟩ := localProof s _ "WXWKNXVWWPWNWTIWWPWQFWWNWPEWWPWNCWWKWFWEWCRWWWPWNCWKWJWFWROWWWNWVKWJWFWEWRWOMWWWNWPEWKWJWIWCWRWOWML" (by decide +kernel)
theorem n214 : V ⟨128,1972,128,2047⟩ := localProof s _ "XXWNWQFXWQWNCXTXPXIXEWRWOWMWL" (by decide +kernel)
theorem n212 : V ⟨128,1972,0,2047⟩ := split_loose s _ true 7 n213 n214
theorem n198 : V ⟨0,1972,0,2047⟩ := split_loose s _ false 7 n199 n212
theorem n215 : V ⟨64,2036,0,2047⟩ := localProof s _ "WXXXFCWIWEWKVWWWWUWQFWKWNCWIWESWWWTWPEWKWJWFWSOWWKMWWKLWWVWOWMWLWSHXXXWINWTWPWVKXWUWPWNWQFXWTWQWNXFWPEXWTWQWPXFXEWNCWSWOWMWLWHR" (by decide +kernel)
theorem n197 : V ⟨0,2036,0,2047⟩ := split_loose s _ false 6 n198 n215
theorem n217 : V ⟨8,2044,0,2039⟩ := localProof s _ "XWWNWVKWWVWTIXXVWWVWTIWQFWWVWPEWWVWNCWWWVWNCWESWWKWEWCWSRWWKWEWSWRMWWKWIWCWSWRWMLWWQWPWRWMWLWSHWWVWSWMWLWRG" (by decide +kernel)
theorem n218 : V ⟨8,2044,8,2047⟩ := localProof s _ "XXXQWPWNWTIXXWPWTIWQFXWTWQWNWPEXWTWQWPWNCWSWRWMWLWHWG" (by decide +kernel)
theorem n216 : V ⟨8,2044,0,2047⟩ := split_loose s _ true 3 n217 n218
theorem n196 : V ⟨0,2044,0,2047⟩ := split_loose s _ false 3 n197 n216
theorem n220 : V ⟨2,2046,0,2045⟩ := localProof s _ "WXXXWQWNWUJWPEWIWFWCWKVWWWWVWQFWNCWESWWVWSRWWWWVWPEWNCWKWJWFWSWROWWVWRWKWIWSWOLWWVWOWLWSHWWVWSWOWLWRGWWVWSWRWLWOD" (by decide +kernel)
theorem n221 : V ⟨2,2046,2,2047⟩ := localProof s _ "XXXWUJWQWNWVKXXWQWPWNWVKWTIXWVWUWPWNWQFXXXWVKWIWFWJUWTWQWNWPEXWVWQWPWNCWSWRWOWLWHWGWD" (by decide +kernel)
theorem n219 : V ⟨2,2046,0,2047⟩ := split_loose s _ true 1 n220 n221
theorem n195 : V ⟨0,2046,0,2047⟩ := split_loose s _ false 1 n196 n219
theorem n223 : V ⟨1,2047,0,2046⟩ := localProof s _ "WXXWICWFWEWKVWWWWVWQFWNCWESWWKRWWWWVWPEWNCWKWJWFWSWROWWKMWWVWOWMWSHWWVWQWNWSWOWRGWWVWSWRWMWODWWVWSWRWOWMB" (by decide +kernel)
theorem n224 : V ⟨1,2047,1,2047⟩ := localProof s _ "XXXWINWQWPWVKXWVWPWNWQFXWVWQWNWPEXWUWTWQWPWNCWSWRWOWMWHWGWDWB" (by decide +kernel)
theorem n222 : V ⟨1,2047,0,2047⟩ := split_loose s _ true 0 n223 n224
theorem n194 : V ⟨0,2047,0,2047⟩ := split_loose s _ false 0 n195 n222
run_cmd Lean.logInfo m!"TREE_4 {← IO.monoMsNow}"
def rs : List Entry := [⟨5,776,94⟩,⟨11,193,0⟩,⟨11,194,0⟩,⟨11,196,0⟩,⟨11,197,0⟩,⟨11,198,0⟩,⟨11,200,0⟩,⟨11,201,0⟩,⟨11,202,0⟩,⟨11,208,0⟩,⟨11,209,0⟩,⟨11,210,0⟩]
theorem settled : ∀ r∈rs, excludes r := members s n194 rs (by decide +kernel)
run_cmd Lean.logInfo m!"MEMBERS_4 {← IO.monoMsNow}"
end T4
def entries := T0.rs++T1.rs++T2.rs++T3.rs++T4.rs
theorem all_entries : ∀ r∈entries, excludes r := (combine _ _ (combine _ _ (combine _ _ (combine _ _ T0.settled T1.settled) T2.settled) T3.settled) T4.settled)
theorem count : entries.length=257 := by decide +kernel
theorem unique : (entries.map (fun r => (r.a,r.b))).Nodup := by decide +kernel
run_cmd Lean.logInfo m!"ATLAS_END {← IO.monoMsNow}"
end PetersenSecondCube.Envelope.Atlas.ShardA
#print axioms PetersenSecondCube.Envelope.Atlas.ShardA.all_entries
