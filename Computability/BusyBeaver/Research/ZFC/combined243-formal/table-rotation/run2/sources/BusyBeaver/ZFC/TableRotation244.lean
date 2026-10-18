import BusyBeaver.Core

/-!
Exact loop-rotation244 table from submission d91a27b462, in canonical numbering.
Old26 is removed from Routing245; old12/read0, old12/read1 and old17/read1
are changed. The original machine/calculus attribution and routing245 lineage
are retained; this module supplies literal data and finite facts only.
No source-program equivalence, runtime or blank-halting theorem is asserted.
-/
namespace SetTheory.BusyBeaver.ZFC

abbrev RawActionRotation244 := Bool × Move × Nat

def rawTableRotation244 : Array (RawActionRotation244 × RawActionRotation244) := #[
  ((true, .right, 99), (true, .right, 0)), -- 0; old95
  ((false, .left, 1), (true, .left, 2)), -- 1; old2
  ((false, .left, 3), (true, .left, 2)), -- 2; old4
  ((false, .left, 5), (true, .left, 2)), -- 3; old6
  ((true, .right, 6), (false, .left, 4)), -- 4; old7
  ((false, .left, 9), (true, .left, 2)), -- 5; old9
  ((false, .right, 6), (false, .right, 10)), -- 6; old10
  ((false, .right, 11), (true, .right, 12)), -- 7; old11
  ((false, .right, 14), (true, .right, 13)), -- 8; old12
  ((false, .left, 15), (true, .left, 2)), -- 9; old13
  ((false, .left, 16), (false, .right, 10)), -- 10; old14
  ((false, .right, 17), (true, .right, 18)), -- 11; old15
  ((false, .right, 19), (true, .right, 20)), -- 12; old16
  ((false, .right, 21), (false, .left, 16)), -- 13; old17
  ((false, .left, 22), (false, .right, 23)), -- 14; old18
  ((false, .left, 24), (true, .left, 2)), -- 15; old19
  ((true, .left, 1), (false, .left, 1)), -- 16; old20
  ((false, .right, 25), (false, .right, 33)), -- 17; old21
  ((false, .right, 27), (false, .left, 28)), -- 18; old22
  ((false, .right, 29), (true, .right, 30)), -- 19; old23
  ((false, .right, 31), (true, .right, 32)), -- 20; old24
  ((false, .right, 25), (false, .right, 62)), -- 21; old25
  ((false, .left, 27), (true, .right, 34)), -- 22; old27
  ((false, .right, 35), (true, .right, 23)), -- 23; old28
  ((false, .left, 36), (true, .left, 2)), -- 24; old29
  ((false, .left, 37), (false, .right, 0)), -- 25; old30
  ((false, .right, 38), (true, .right, 26)), -- 26; old31
  ((false, .right, 39), (true, .right, 40)), -- 27; old32
  ((false, .right, 41), (false, .left, 42)), -- 28; old33
  ((false, .right, 43), (true, .right, 44)), -- 29; old34
  ((false, .right, 45), (true, .right, 46)), -- 30; old35
  ((false, .right, 47), (true, .right, 48)), -- 31; old36
  ((false, .right, 21), (true, .right, 49)), -- 32; old37
  ((false, .right, 50), (true, .right, 33)), -- 33; old38
  ((false, .right, 51), (false, .right, 62)), -- 34; old39
  ((false, .right, 33), (true, .right, 35)), -- 35; old40
  ((false, .left, 52), (true, .left, 2)), -- 36; old41
  ((true, .right, 37), (true, .left, 1)), -- 37; old42
  ((false, .right, 53), (true, .right, 38)), -- 38; old44
  ((false, .right, 17), (true, .right, 54)), -- 39; old45
  ((false, .right, 34), (true, .right, 55)), -- 40; old46
  ((false, .left, 22), (false, .right, 38)), -- 41; old47
  ((false, .left, 4), (true, .left, 56)), -- 42; old48
  ((false, .right, 25), (false, .right, 26)), -- 43; old49
  ((false, .right, 34), (false, .left, 16)), -- 44; old50
  ((false, .right, 58), (true, .right, 59)), -- 45; old51
  ((false, .right, 60), (true, .right, 61)), -- 46; old52
  ((false, .right, 25), (false, .right, 57)), -- 47; old53
  ((false, .right, 63), (true, .right, 64)), -- 48; old54
  ((false, .right, 65), (false, .left, 16)), -- 49; old55
  ((false, .right, 26), (true, .right, 50)), -- 50; old56
  ((false, .left, 37), (false, .right, 66)), -- 51; old57
  ((false, .left, 77), (true, .left, 2)), -- 52; old58
  ((false, .right, 16), (true, .right, 53)), -- 53; old60
  ((false, .right, 69), (false, .left, 28)), -- 54; old61
  ((false, .right, 70), (true, .right, 71)), -- 55; old62
  ((false, .left, 42), (true, .left, 56)), -- 56; old63
  ((false, .right, 23), (true, .right, 57)), -- 57; old64
  ((false, .left, 22), (false, .right, 53)), -- 58; old65
  ((false, .right, 63), (false, .left, 16)), -- 59; old66
  ((false, .right, 72), (true, .right, 73)), -- 60; old67
  ((false, .right, 64), (true, .right, 74)), -- 61; old68
  ((false, .right, 57), (true, .right, 62)), -- 62; old69
  ((false, .right, 51), (false, .right, 26)), -- 63; old70
  ((false, .left, 29), (true, .left, 75)), -- 64; old71
  ((false, .right, 51), (false, .right, 57)), -- 65; old72
  ((false, .right, 76), (true, .right, 66)), -- 66; old73
  ((false, .right, 122), (true, .right, 12)), -- 67; old74
  ((true, .right, 243), (true, .left, 56)), -- 68; old75
  ((false, .right, 78), (true, .right, 79)), -- 69; old76
  ((false, .right, 80), (true, .right, 244)), -- 70; old77
  ((false, .left, 81), (true, .right, 32)), -- 71; old78
  ((false, .right, 43), (true, .right, 82)), -- 72; old79
  ((false, .right, 21), (true, .right, 83)), -- 73; old80
  ((false, .right, 58), (true, .left, 84)), -- 74; old81
  ((false, .right, 85), (true, .right, 86)), -- 75; old82
  ((true, .right, 0), (true, .right, 66)), -- 76; old83
  ((false, .right, 77), (true, .right, 87)), -- 77; old84
  ((false, .right, 88), (true, .right, 89)), -- 78; old86
  ((false, .right, 204), (true, .right, 238)), -- 79; old87
  ((false, .right, 92), (true, .right, 93)), -- 80; old88
  ((false, .right, 94), (true, .right, 95)), -- 81; old89
  ((false, .right, 85), (true, .right, 64)), -- 82; old90
  ((false, .right, 96), (false, .left, 44)), -- 83; old91
  ((false, .left, 97), (true, .left, 20)), -- 84; old92
  ((false, .right, 51), (false, .right, 35)), -- 85; old93
  ((false, .right, 98), (false, .left, 44)), -- 86; old94
  ((false, .right, 100), (true, .right, 101)), -- 87; old96
  ((false, .right, 19), (true, .right, 67)), -- 88; old98
  ((false, .right, 95), (true, .right, 104)), -- 89; old99
  ((false, .right, 143), (true, .right, 174)), -- 90; old100
  ((false, .right, 184), (true, .right, 197)), -- 91; old101
  ((false, .right, 21), (true, .right, 109)), -- 92; old102
  ((false, .right, 47), (true, .right, 110)), -- 93; old103
  ((false, .right, 111), (true, .right, 112)), -- 94; old104
  ((false, .right, 113), (true, .right, 114)), -- 95; old105
  ((false, .right, 85), (true, .right, 112)), -- 96; old106
  ((false, .right, 111), (true, .right, 115)), -- 97; old107
  ((false, .right, 116), (true, .right, 117)), -- 98; old108
  ((false, .right, 68), (false, .right, 0)), -- 99; old109
  ((false, .right, 28), (true, .right, 118)), -- 100; old110
  ((false, .right, 119), (true, .right, 120)), -- 101; old111
  ((true, .left, 121), (true, .left, 102)), -- 102; old112
  ((false, .right, 19), (true, .right, 122)), -- 103; old113
  ((false, .right, 63), (true, .right, 63)), -- 104; old114
  ((false, .right, 127), (true, .right, 219)), -- 105; old115
  ((false, .right, 173), (true, .right, 124)), -- 106; old116
  ((false, .right, 173), (true, .right, 201)), -- 107; old117
  ((false, .right, 221), (true, .right, 149)), -- 108; old118
  ((false, .right, 131), (true, .right, 132)), -- 109; old119
  ((false, .right, 133), (false, .left, 54)), -- 110; old120
  ((false, .right, 134), (true, .right, 135)), -- 111; old121
  ((false, .right, 21), (true, .right, 59)), -- 112; old122
  ((false, .right, 74), (true, .right, 61)), -- 113; old123
  ((false, .right, 60), (true, .right, 136)), -- 114; old124
  ((false, .right, 21), (true, .right, 137)), -- 115; old125
  ((false, .right, 21), (false, .left, 42)), -- 116; old126
  ((false, .right, 64), (true, .right, 44)), -- 117; old127
  ((false, .right, 138), (true, .right, 8)), -- 118; old128
  ((false, .right, 111), (true, .right, 139)), -- 119; old129
  ((false, .right, 97), (true, .right, 140)), -- 120; old130
  ((false, .left, 42), (false, .left, 102)), -- 121; old131
  ((false, .right, 141), (true, .right, 115)), -- 122; old132
  ((false, .right, 71), (true, .right, 142)), -- 123; old133
  ((false, .right, 203), (true, .right, 237)), -- 124; old134
  ((false, .right, 230), (true, .right, 205)), -- 125; old135
  ((false, .right, 177), (true, .right, 205)), -- 126; old136
  ((false, .right, 149), (true, .right, 150)), -- 127; old137
  ((false, .right, 172), (true, .right, 107)), -- 128; old138
  ((false, .right, 78), (true, .right, 225)), -- 129; old139
  ((false, .right, 129), (true, .right, 212)), -- 130; old140
  ((false, .right, 47), (false, .left, 10)), -- 131; old141
  ((false, .right, 32), (true, .right, 65)), -- 132; old142
  ((false, .left, 156), (false, .left, 1)), -- 133; old143
  ((false, .right, 41), (true, .right, 75)), -- 134; old144
  ((false, .right, 64), (true, .right, 157)), -- 135; old145
  ((false, .right, 64), (true, .right, 158)), -- 136; old146
  ((false, .right, 159), (false, .left, 16)), -- 137; old147
  ((false, .right, 14), (true, .right, 157)), -- 138; old148
  ((false, .right, 21), (true, .right, 160)), -- 139; old149
  ((false, .right, 161), (true, .right, 162)), -- 140; old150
  ((false, .right, 163), (true, .left, 20)), -- 141; old151
  ((false, .right, 164), (true, .right, 165)), -- 142; old152
  ((false, .right, 166), (true, .left, 147)), -- 143; old153
  ((false, .right, 78), (true, .right, 232)), -- 144; old154
  ((false, .right, 144), (true, .right, 207)), -- 145; old155
  ((false, .right, 223), (true, .right, 226)), -- 146; old156
  ((false, .right, 165), (true, .right, 197)), -- 147; old157
  ((false, .right, 211), (true, .right, 180)), -- 148; old158
  ((false, .left, 147), (true, .right, 177)), -- 149; old159
  ((false, .right, 178), (true, .right, 179)), -- 150; old160
  ((false, .right, 169), (true, .right, 181)), -- 151; old161
  ((false, .right, 236), (true, .right, 106)), -- 152; old162
  ((false, .right, 215), (true, .right, 183)), -- 153; old163
  ((false, .right, 224), (true, .right, 108)), -- 154; old164
  ((false, .right, 12), (true, .right, 125)), -- 155; old165
  ((false, .right, 31), (true, .right, 72)), -- 156; old166
  ((false, .right, 41), (true, .left, 84)), -- 157; old167
  ((false, .right, 190), (false, .left, 16)), -- 158; old168
  ((false, .right, 51), (false, .right, 50)), -- 159; old169
  ((false, .right, 191), (false, .left, 16)), -- 160; old170
  ((false, .right, 17), (true, .right, 192)), -- 161; old171
  ((false, .right, 193), (true, .right, 194)), -- 162; old172
  ((false, .right, 25), (false, .right, 50)), -- 163; old173
  ((false, .right, 195), (true, .right, 81)), -- 164; old174
  ((false, .right, 103), (true, .right, 95)), -- 165; old175
  ((false, .right, 103), (true, .right, 196)), -- 166; old176
  ((false, .right, 155), (true, .right, 175)), -- 167; old177
  ((false, .right, 12), (true, .right, 196)), -- 168; old178
  ((false, .right, 95), (true, .right, 95)), -- 169; old179
  ((false, .right, 95), (true, .right, 199)), -- 170; old180
  ((false, .right, 168), (true, .right, 231)), -- 171; old181
  ((false, .right, 177), (true, .right, 202)), -- 172; old182
  ((false, .right, 89), (true, .left, 203)), -- 173; old183
  ((false, .right, 171), (true, .right, 152)), -- 174; old184
  ((false, .right, 182), (true, .right, 202)), -- 175; old185
  ((false, .right, 222), (true, .right, 197)), -- 176; old186
  ((false, .right, 88), (true, .right, 208)), -- 177; old187
  ((false, .right, 209), (true, .right, 210)), -- 178; old188
  ((false, .right, 148), (true, .right, 234)), -- 179; old189
  ((false, .right, 95), (true, .right, 89)), -- 180; old190
  ((false, .right, 176), (true, .right, 196)), -- 181; old191
  ((false, .right, 211), (true, .right, 210)), -- 182; old192
  ((false, .right, 180), (true, .right, 203)), -- 183; old193
  ((false, .right, 149), (true, .right, 214)), -- 184; old194
  ((false, .right, 104), (true, .right, 146)), -- 185; old195
  ((false, .right, 185), (true, .right, 130)), -- 186; old196
  ((false, .right, 186), (true, .right, 105)), -- 187; old197
  ((false, .right, 196), (true, .right, 126)), -- 188; old198
  ((false, .right, 187), (true, .right, 217)), -- 189; old199
  ((false, .right, 104), (true, .right, 104)), -- 190; old200
  ((false, .right, 51), (false, .right, 33)), -- 191; old201
  ((false, .right, 7), (false, .left, 28)), -- 192; old202
  ((false, .right, 165), (true, .right, 29)), -- 193; old203
  ((false, .right, 80), (true, .right, 103)), -- 194; old204
  ((false, .right, 196), (true, .right, 19)), -- 195; old205
  ((false, .right, 19), (true, .right, 220)), -- 196; old206
  ((false, .right, 203), (true, .right, 221)), -- 197; old207
  ((false, .right, 189), (true, .right, 180)), -- 198; old208
  ((false, .right, 211), (true, .right, 222)), -- 199; old209
  ((false, .right, 104), (true, .right, 167)), -- 200; old210
  ((false, .right, 200), (true, .right, 180)), -- 201; old211
  ((false, .right, 226), (true, .right, 168)), -- 202; old212
  ((false, .right, 227), (true, .right, 228)), -- 203; old213
  ((false, .right, 123), (true, .right, 90)), -- 204; old214
  ((false, .right, 173), (true, .right, 223)), -- 205; old215
  ((false, .right, 170), (true, .right, 128)), -- 206; old216
  ((false, .right, 223), (true, .right, 225)), -- 207; old217
  ((false, .left, 78), (true, .right, 63)), -- 208; old218
  ((false, .right, 196), (true, .right, 168)), -- 209; old219
  ((false, .right, 233), (true, .right, 208)), -- 210; old220
  ((false, .right, 196), (true, .right, 233)), -- 211; old221
  ((false, .right, 206), (true, .right, 145)), -- 212; old222
  ((false, .right, 170), (true, .right, 198)), -- 213; old223
  ((false, .right, 234), (true, .right, 234)), -- 214; old224
  ((false, .right, 235), (true, .right, 143)), -- 215; old225
  ((false, .right, 213), (true, .right, 154)), -- 216; old226
  ((false, .right, 183), (true, .right, 218)), -- 217; old227
  ((false, .right, 151), (true, .right, 91)), -- 218; old228
  ((false, .right, 151), (true, .right, 182)), -- 219; old229
  ((false, .right, 239), (true, .right, 139)), -- 220; old230
  ((false, .right, 227), (true, .right, 173)), -- 221; old231
  ((false, .right, 104), (true, .right, 210)), -- 222; old232
  ((false, .right, 78), (true, .right, 63)), -- 223; old233
  ((false, .right, 180), (true, .right, 153)), -- 224; old234
  ((false, .right, 221), (true, .right, 12)), -- 225; old235
  ((false, .right, 169), (true, .right, 103)), -- 226; old236
  ((false, .right, 208), (true, .right, 95)), -- 227; old237
  ((false, .right, 95), (true, .right, 227)), -- 228; old238
  ((false, .right, 169), (true, .right, 216)), -- 229; old239
  ((false, .right, 166), (true, .right, 89)), -- 230; old240
  ((false, .right, 229), (true, .right, 188)), -- 231; old241
  ((false, .right, 230), (true, .right, 226)), -- 232; old242
  ((false, .left, 142), (true, .left, 235)), -- 233; old243
  ((false, .right, 168), (true, .left, 178)), -- 234; old244
  ((false, .right, 12), (true, .right, 234)), -- 235; old245
  ((false, .right, 196), (true, .right, 223)), -- 236; old246
  ((false, .right, 203), (true, .right, 239)), -- 237; old248
  ((false, .right, 240), (true, .right, 241)), -- 238; old249
  ((false, .right, 17), (true, .left, 156)), -- 239; old250
  ((false, .right, 241), (true, .right, 242)), -- 240; old251
  ((false, .right, 80), (true, .right, 133)), -- 241; old252
  ((false, .right, 117), (true, .right, 141)), -- 242; old253
  ((true, .left, 243), (true, .left, 121)) -- 243; old255
]

theorem rawTableRotation244_size : rawTableRotation244.size = 244 := by decide +kernel

theorem rawTableRotation244_transition_count :
    (rawTableRotation244.toList.flatMap (fun r => [r.1, r.2])).length = 488 := by
  decide +kernel

def rawActionRotation244 (q : Fin 244) (b : Bool) : RawActionRotation244 :=
  let row := rawTableRotation244.getD q.val
    ((false, .right, 244), (false, .right, 244))
  if b then row.2 else row.1

def actionRotation244 (q : Fin 244) (b : Bool) : Action 244 :=
  let raw := rawActionRotation244 q b
  { write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 244 then some ⟨raw.2.2, h⟩ else none }

def machineRotation244 : Machine 244 where
  transition := actionRotation244

/-- Absent old labels have only a total fallback value. -/
def oldStateRotation244 : Nat → Fin 244
  | 95 => 0
  | 2 => 1
  | 4 => 2
  | 6 => 3
  | 7 => 4
  | 9 => 5
  | 10 => 6
  | 11 => 7
  | 12 => 8
  | 13 => 9
  | 14 => 10
  | 15 => 11
  | 16 => 12
  | 17 => 13
  | 18 => 14
  | 19 => 15
  | 20 => 16
  | 21 => 17
  | 22 => 18
  | 23 => 19
  | 24 => 20
  | 25 => 21
  | 27 => 22
  | 28 => 23
  | 29 => 24
  | 30 => 25
  | 31 => 26
  | 32 => 27
  | 33 => 28
  | 34 => 29
  | 35 => 30
  | 36 => 31
  | 37 => 32
  | 38 => 33
  | 39 => 34
  | 40 => 35
  | 41 => 36
  | 42 => 37
  | 44 => 38
  | 45 => 39
  | 46 => 40
  | 47 => 41
  | 48 => 42
  | 49 => 43
  | 50 => 44
  | 51 => 45
  | 52 => 46
  | 53 => 47
  | 54 => 48
  | 55 => 49
  | 56 => 50
  | 57 => 51
  | 58 => 52
  | 60 => 53
  | 61 => 54
  | 62 => 55
  | 63 => 56
  | 64 => 57
  | 65 => 58
  | 66 => 59
  | 67 => 60
  | 68 => 61
  | 69 => 62
  | 70 => 63
  | 71 => 64
  | 72 => 65
  | 73 => 66
  | 74 => 67
  | 75 => 68
  | 76 => 69
  | 77 => 70
  | 78 => 71
  | 79 => 72
  | 80 => 73
  | 81 => 74
  | 82 => 75
  | 83 => 76
  | 84 => 77
  | 86 => 78
  | 87 => 79
  | 88 => 80
  | 89 => 81
  | 90 => 82
  | 91 => 83
  | 92 => 84
  | 93 => 85
  | 94 => 86
  | 96 => 87
  | 98 => 88
  | 99 => 89
  | 100 => 90
  | 101 => 91
  | 102 => 92
  | 103 => 93
  | 104 => 94
  | 105 => 95
  | 106 => 96
  | 107 => 97
  | 108 => 98
  | 109 => 99
  | 110 => 100
  | 111 => 101
  | 112 => 102
  | 113 => 103
  | 114 => 104
  | 115 => 105
  | 116 => 106
  | 117 => 107
  | 118 => 108
  | 119 => 109
  | 120 => 110
  | 121 => 111
  | 122 => 112
  | 123 => 113
  | 124 => 114
  | 125 => 115
  | 126 => 116
  | 127 => 117
  | 128 => 118
  | 129 => 119
  | 130 => 120
  | 131 => 121
  | 132 => 122
  | 133 => 123
  | 134 => 124
  | 135 => 125
  | 136 => 126
  | 137 => 127
  | 138 => 128
  | 139 => 129
  | 140 => 130
  | 141 => 131
  | 142 => 132
  | 143 => 133
  | 144 => 134
  | 145 => 135
  | 146 => 136
  | 147 => 137
  | 148 => 138
  | 149 => 139
  | 150 => 140
  | 151 => 141
  | 152 => 142
  | 153 => 143
  | 154 => 144
  | 155 => 145
  | 156 => 146
  | 157 => 147
  | 158 => 148
  | 159 => 149
  | 160 => 150
  | 161 => 151
  | 162 => 152
  | 163 => 153
  | 164 => 154
  | 165 => 155
  | 166 => 156
  | 167 => 157
  | 168 => 158
  | 169 => 159
  | 170 => 160
  | 171 => 161
  | 172 => 162
  | 173 => 163
  | 174 => 164
  | 175 => 165
  | 176 => 166
  | 177 => 167
  | 178 => 168
  | 179 => 169
  | 180 => 170
  | 181 => 171
  | 182 => 172
  | 183 => 173
  | 184 => 174
  | 185 => 175
  | 186 => 176
  | 187 => 177
  | 188 => 178
  | 189 => 179
  | 190 => 180
  | 191 => 181
  | 192 => 182
  | 193 => 183
  | 194 => 184
  | 195 => 185
  | 196 => 186
  | 197 => 187
  | 198 => 188
  | 199 => 189
  | 200 => 190
  | 201 => 191
  | 202 => 192
  | 203 => 193
  | 204 => 194
  | 205 => 195
  | 206 => 196
  | 207 => 197
  | 208 => 198
  | 209 => 199
  | 210 => 200
  | 211 => 201
  | 212 => 202
  | 213 => 203
  | 214 => 204
  | 215 => 205
  | 216 => 206
  | 217 => 207
  | 218 => 208
  | 219 => 209
  | 220 => 210
  | 221 => 211
  | 222 => 212
  | 223 => 213
  | 224 => 214
  | 225 => 215
  | 226 => 216
  | 227 => 217
  | 228 => 218
  | 229 => 219
  | 230 => 220
  | 231 => 221
  | 232 => 222
  | 233 => 223
  | 234 => 224
  | 235 => 225
  | 236 => 226
  | 237 => 227
  | 238 => 228
  | 239 => 229
  | 240 => 230
  | 241 => 231
  | 242 => 232
  | 243 => 233
  | 244 => 234
  | 245 => 235
  | 246 => 236
  | 248 => 237
  | 249 => 238
  | 250 => 239
  | 251 => 240
  | 252 => 241
  | 253 => 242
  | 255 => 243
  | _ => 0

def oldLabelsRotation244 : Array Nat := #[95, 2, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 89, 90, 91, 92, 93, 94, 96, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 248, 249, 250, 251, 252, 253, 255]

def oldLabelRotation244 (q : Fin 244) : Nat := oldLabelsRotation244.getD q.val 95

theorem oldStateRotation244_oldLabel : ∀ q : Fin 244,
    oldStateRotation244 (oldLabelRotation244 q) = q := by decide +kernel

theorem machineRotation244_start : oldStateRotation244 95 = 0 := by decide +kernel

theorem machineRotation244_dispatch : oldStateRotation244 96 = 87 := by decide +kernel

theorem machineRotation244_halt_iff : ∀ (q : Fin 244) (b : Bool),
    (machineRotation244.transition q b).next = none ↔
      q = oldStateRotation244 77 ∧ b = true := by decide +kernel

theorem machineRotation244_halt_action :
    machineRotation244.transition (oldStateRotation244 77) true =
      ⟨true, .right, none⟩ := by decide +kernel

end SetTheory.BusyBeaver.ZFC
