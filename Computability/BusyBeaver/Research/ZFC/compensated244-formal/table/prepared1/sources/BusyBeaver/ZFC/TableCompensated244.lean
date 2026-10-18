import BusyBeaver.ZFC.TableRouting245
import Lean.Elab.Tactic.Omega

/-!
Exact compensated244 canonical table and its embedding into the retained245
state labels. The finite table deletes old122 and changes exactly four rows.
The original245 table remains the checked reference. This module states only
literal table, renumbering, and common-transition facts; no runtime theorem.
Core configurations carry arbitrary finite-support List Int tapes.
-/
namespace SetTheory.BusyBeaver.ZFC

abbrev RawActionCompensated244 := Bool × Move × Nat

def rawTableCompensated244 : Array (RawActionCompensated244 × RawActionCompensated244) := #[
  ((true, .right, 100), (true, .right, 0)), -- 0; old95
  ((false, .left, 1), (true, .left, 2)), -- 1; old2
  ((false, .left, 3), (true, .left, 2)), -- 2; old4
  ((false, .left, 5), (true, .left, 2)), -- 3; old6
  ((true, .right, 6), (false, .left, 4)), -- 4; old7
  ((false, .left, 9), (true, .left, 2)), -- 5; old9
  ((false, .right, 6), (false, .right, 10)), -- 6; old10
  ((false, .right, 11), (true, .right, 12)), -- 7; old11
  ((false, .right, 13), (true, .right, 14)), -- 8; old12
  ((false, .left, 15), (true, .left, 2)), -- 9; old13
  ((false, .left, 16), (false, .right, 10)), -- 10; old14
  ((false, .right, 17), (true, .right, 18)), -- 11; old15
  ((false, .right, 19), (true, .right, 20)), -- 12; old16
  ((false, .right, 21), (true, .right, 22)), -- 13; old17
  ((false, .left, 23), (false, .right, 24)), -- 14; old18
  ((false, .left, 25), (true, .left, 2)), -- 15; old19
  ((true, .left, 1), (false, .left, 1)), -- 16; old20
  ((false, .right, 26), (false, .right, 34)), -- 17; old21
  ((false, .right, 28), (false, .left, 29)), -- 18; old22
  ((false, .right, 30), (true, .right, 31)), -- 19; old23
  ((false, .right, 32), (true, .right, 33)), -- 20; old24
  ((false, .right, 26), (false, .right, 63)), -- 21; old25
  ((false, .right, 14), (false, .left, 16)), -- 22; old26
  ((false, .left, 28), (true, .right, 35)), -- 23; old27
  ((false, .right, 36), (true, .right, 24)), -- 24; old28
  ((false, .left, 37), (true, .left, 2)), -- 25; old29
  ((false, .left, 38), (false, .right, 0)), -- 26; old30
  ((false, .right, 39), (true, .right, 27)), -- 27; old31
  ((false, .right, 40), (true, .right, 41)), -- 28; old32
  ((false, .right, 42), (false, .left, 43)), -- 29; old33
  ((false, .right, 44), (true, .right, 45)), -- 30; old34
  ((false, .right, 46), (true, .right, 47)), -- 31; old35
  ((false, .right, 48), (true, .right, 49)), -- 32; old36
  ((false, .right, 21), (true, .right, 50)), -- 33; old37
  ((false, .right, 51), (true, .right, 34)), -- 34; old38
  ((false, .right, 52), (false, .right, 63)), -- 35; old39
  ((false, .right, 34), (true, .right, 36)), -- 36; old40
  ((false, .left, 53), (true, .left, 2)), -- 37; old41
  ((true, .right, 38), (true, .left, 1)), -- 38; old42
  ((false, .right, 54), (true, .right, 39)), -- 39; old44
  ((false, .right, 17), (true, .right, 55)), -- 40; old45
  ((false, .right, 35), (true, .right, 56)), -- 41; old46
  ((false, .left, 23), (false, .right, 39)), -- 42; old47
  ((false, .left, 4), (true, .left, 57)), -- 43; old48
  ((false, .right, 26), (false, .right, 27)), -- 44; old49
  ((false, .right, 35), (false, .left, 16)), -- 45; old50
  ((false, .right, 59), (true, .right, 60)), -- 46; old51
  ((false, .right, 61), (true, .right, 62)), -- 47; old52
  ((false, .right, 26), (false, .right, 58)), -- 48; old53
  ((false, .right, 64), (true, .right, 65)), -- 49; old54
  ((false, .right, 66), (false, .left, 16)), -- 50; old55
  ((false, .right, 27), (true, .right, 51)), -- 51; old56
  ((false, .left, 38), (false, .right, 67)), -- 52; old57
  ((false, .left, 78), (true, .left, 2)), -- 53; old58
  ((false, .right, 16), (true, .right, 54)), -- 54; old60
  ((false, .right, 70), (false, .left, 29)), -- 55; old61
  ((false, .right, 71), (true, .right, 72)), -- 56; old62
  ((false, .left, 43), (true, .left, 57)), -- 57; old63
  ((false, .right, 24), (true, .right, 58)), -- 58; old64
  ((false, .left, 23), (false, .right, 54)), -- 59; old65
  ((false, .right, 64), (false, .left, 16)), -- 60; old66
  ((false, .right, 73), (true, .right, 74)), -- 61; old67
  ((false, .right, 65), (true, .right, 75)), -- 62; old68
  ((false, .right, 58), (true, .right, 63)), -- 63; old69
  ((false, .right, 52), (false, .right, 27)), -- 64; old70
  ((false, .left, 30), (true, .left, 76)), -- 65; old71
  ((false, .right, 52), (false, .right, 58)), -- 66; old72
  ((false, .right, 77), (true, .right, 67)), -- 67; old73
  ((false, .right, 122), (true, .right, 12)), -- 68; old74
  ((true, .right, 243), (true, .left, 57)), -- 69; old75
  ((false, .right, 79), (true, .right, 80)), -- 70; old76
  ((false, .right, 81), (true, .right, 244)), -- 71; old77
  ((false, .left, 82), (true, .right, 33)), -- 72; old78
  ((false, .right, 44), (true, .right, 83)), -- 73; old79
  ((false, .right, 21), (true, .right, 84)), -- 74; old80
  ((false, .right, 59), (true, .left, 85)), -- 75; old81
  ((false, .right, 86), (true, .right, 87)), -- 76; old82
  ((true, .right, 0), (true, .right, 67)), -- 77; old83
  ((false, .right, 78), (true, .right, 88)), -- 78; old84
  ((false, .right, 89), (true, .right, 90)), -- 79; old86
  ((false, .right, 204), (true, .right, 238)), -- 80; old87
  ((false, .right, 93), (true, .right, 94)), -- 81; old88
  ((false, .right, 95), (true, .right, 96)), -- 82; old89
  ((false, .right, 86), (true, .right, 65)), -- 83; old90
  ((false, .right, 97), (false, .left, 45)), -- 84; old91
  ((false, .left, 98), (true, .right, 60)), -- 85; old92
  ((false, .right, 52), (false, .right, 36)), -- 86; old93
  ((false, .right, 99), (false, .left, 45)), -- 87; old94
  ((false, .right, 101), (true, .right, 102)), -- 88; old96
  ((false, .right, 19), (true, .right, 68)), -- 89; old98
  ((false, .right, 96), (true, .right, 105)), -- 90; old99
  ((false, .right, 143), (true, .right, 174)), -- 91; old100
  ((false, .right, 184), (true, .right, 197)), -- 92; old101
  ((false, .right, 21), (true, .right, 110)), -- 93; old102
  ((false, .right, 48), (true, .right, 111)), -- 94; old103
  ((false, .right, 112), (true, .right, 85)), -- 95; old104
  ((false, .right, 113), (true, .right, 114)), -- 96; old105
  ((false, .right, 86), (true, .right, 85)), -- 97; old106
  ((false, .right, 112), (true, .right, 115)), -- 98; old107
  ((false, .right, 116), (true, .right, 117)), -- 99; old108
  ((false, .right, 69), (false, .right, 0)), -- 100; old109
  ((false, .right, 29), (true, .right, 118)), -- 101; old110
  ((false, .right, 119), (true, .right, 120)), -- 102; old111
  ((true, .left, 121), (true, .left, 103)), -- 103; old112
  ((false, .right, 19), (true, .right, 122)), -- 104; old113
  ((false, .right, 64), (true, .right, 64)), -- 105; old114
  ((false, .right, 127), (true, .right, 219)), -- 106; old115
  ((false, .right, 173), (true, .right, 124)), -- 107; old116
  ((false, .right, 173), (true, .right, 201)), -- 108; old117
  ((false, .right, 221), (true, .right, 149)), -- 109; old118
  ((false, .right, 131), (true, .right, 132)), -- 110; old119
  ((false, .right, 133), (false, .left, 55)), -- 111; old120
  ((false, .right, 134), (true, .right, 135)), -- 112; old121
  ((false, .right, 75), (true, .right, 62)), -- 113; old123
  ((false, .right, 61), (true, .right, 136)), -- 114; old124
  ((false, .right, 21), (true, .right, 137)), -- 115; old125
  ((false, .right, 21), (false, .left, 43)), -- 116; old126
  ((false, .right, 65), (true, .right, 45)), -- 117; old127
  ((false, .right, 138), (true, .right, 8)), -- 118; old128
  ((false, .right, 112), (true, .right, 139)), -- 119; old129
  ((false, .right, 98), (true, .right, 140)), -- 120; old130
  ((false, .left, 43), (false, .left, 103)), -- 121; old131
  ((false, .right, 141), (true, .right, 115)), -- 122; old132
  ((false, .right, 72), (true, .right, 142)), -- 123; old133
  ((false, .right, 203), (true, .right, 237)), -- 124; old134
  ((false, .right, 230), (true, .right, 205)), -- 125; old135
  ((false, .right, 177), (true, .right, 205)), -- 126; old136
  ((false, .right, 149), (true, .right, 150)), -- 127; old137
  ((false, .right, 172), (true, .right, 108)), -- 128; old138
  ((false, .right, 79), (true, .right, 225)), -- 129; old139
  ((false, .right, 129), (true, .right, 212)), -- 130; old140
  ((false, .right, 48), (false, .left, 10)), -- 131; old141
  ((false, .right, 33), (true, .right, 66)), -- 132; old142
  ((false, .left, 156), (false, .left, 1)), -- 133; old143
  ((false, .right, 42), (true, .right, 76)), -- 134; old144
  ((false, .right, 65), (true, .right, 157)), -- 135; old145
  ((false, .right, 65), (true, .right, 158)), -- 136; old146
  ((false, .right, 159), (false, .left, 16)), -- 137; old147
  ((false, .right, 14), (true, .right, 157)), -- 138; old148
  ((false, .right, 21), (true, .right, 160)), -- 139; old149
  ((false, .right, 161), (true, .right, 162)), -- 140; old150
  ((false, .right, 163), (true, .left, 20)), -- 141; old151
  ((false, .right, 164), (true, .right, 165)), -- 142; old152
  ((false, .right, 166), (true, .left, 147)), -- 143; old153
  ((false, .right, 79), (true, .right, 232)), -- 144; old154
  ((false, .right, 144), (true, .right, 207)), -- 145; old155
  ((false, .right, 223), (true, .right, 226)), -- 146; old156
  ((false, .right, 165), (true, .right, 197)), -- 147; old157
  ((false, .right, 211), (true, .right, 180)), -- 148; old158
  ((false, .left, 147), (true, .right, 177)), -- 149; old159
  ((false, .right, 178), (true, .right, 179)), -- 150; old160
  ((false, .right, 169), (true, .right, 181)), -- 151; old161
  ((false, .right, 236), (true, .right, 107)), -- 152; old162
  ((false, .right, 215), (true, .right, 183)), -- 153; old163
  ((false, .right, 224), (true, .right, 109)), -- 154; old164
  ((false, .right, 12), (true, .right, 125)), -- 155; old165
  ((false, .right, 32), (true, .right, 73)), -- 156; old166
  ((false, .right, 42), (true, .left, 141)), -- 157; old167
  ((false, .right, 190), (false, .left, 16)), -- 158; old168
  ((false, .right, 52), (false, .right, 51)), -- 159; old169
  ((false, .right, 191), (false, .left, 16)), -- 160; old170
  ((false, .right, 17), (true, .right, 192)), -- 161; old171
  ((false, .right, 193), (true, .right, 194)), -- 162; old172
  ((false, .right, 26), (false, .right, 51)), -- 163; old173
  ((false, .right, 195), (true, .right, 82)), -- 164; old174
  ((false, .right, 104), (true, .right, 96)), -- 165; old175
  ((false, .right, 104), (true, .right, 196)), -- 166; old176
  ((false, .right, 155), (true, .right, 175)), -- 167; old177
  ((false, .right, 12), (true, .right, 196)), -- 168; old178
  ((false, .right, 96), (true, .right, 96)), -- 169; old179
  ((false, .right, 96), (true, .right, 199)), -- 170; old180
  ((false, .right, 168), (true, .right, 231)), -- 171; old181
  ((false, .right, 177), (true, .right, 202)), -- 172; old182
  ((false, .right, 90), (true, .left, 203)), -- 173; old183
  ((false, .right, 171), (true, .right, 152)), -- 174; old184
  ((false, .right, 182), (true, .right, 202)), -- 175; old185
  ((false, .right, 222), (true, .right, 197)), -- 176; old186
  ((false, .right, 89), (true, .right, 208)), -- 177; old187
  ((false, .right, 209), (true, .right, 210)), -- 178; old188
  ((false, .right, 148), (true, .right, 234)), -- 179; old189
  ((false, .right, 96), (true, .right, 90)), -- 180; old190
  ((false, .right, 176), (true, .right, 196)), -- 181; old191
  ((false, .right, 211), (true, .right, 210)), -- 182; old192
  ((false, .right, 180), (true, .right, 203)), -- 183; old193
  ((false, .right, 149), (true, .right, 214)), -- 184; old194
  ((false, .right, 105), (true, .right, 146)), -- 185; old195
  ((false, .right, 185), (true, .right, 130)), -- 186; old196
  ((false, .right, 186), (true, .right, 106)), -- 187; old197
  ((false, .right, 196), (true, .right, 126)), -- 188; old198
  ((false, .right, 187), (true, .right, 217)), -- 189; old199
  ((false, .right, 105), (true, .right, 105)), -- 190; old200
  ((false, .right, 52), (false, .right, 34)), -- 191; old201
  ((false, .right, 7), (false, .left, 29)), -- 192; old202
  ((false, .right, 165), (true, .right, 30)), -- 193; old203
  ((false, .right, 81), (true, .right, 104)), -- 194; old204
  ((false, .right, 196), (true, .right, 19)), -- 195; old205
  ((false, .right, 19), (true, .right, 220)), -- 196; old206
  ((false, .right, 203), (true, .right, 221)), -- 197; old207
  ((false, .right, 189), (true, .right, 180)), -- 198; old208
  ((false, .right, 211), (true, .right, 222)), -- 199; old209
  ((false, .right, 105), (true, .right, 167)), -- 200; old210
  ((false, .right, 200), (true, .right, 180)), -- 201; old211
  ((false, .right, 226), (true, .right, 168)), -- 202; old212
  ((false, .right, 227), (true, .right, 228)), -- 203; old213
  ((false, .right, 123), (true, .right, 91)), -- 204; old214
  ((false, .right, 173), (true, .right, 223)), -- 205; old215
  ((false, .right, 170), (true, .right, 128)), -- 206; old216
  ((false, .right, 223), (true, .right, 225)), -- 207; old217
  ((false, .left, 79), (true, .right, 64)), -- 208; old218
  ((false, .right, 196), (true, .right, 168)), -- 209; old219
  ((false, .right, 233), (true, .right, 208)), -- 210; old220
  ((false, .right, 196), (true, .right, 233)), -- 211; old221
  ((false, .right, 206), (true, .right, 145)), -- 212; old222
  ((false, .right, 170), (true, .right, 198)), -- 213; old223
  ((false, .right, 234), (true, .right, 234)), -- 214; old224
  ((false, .right, 235), (true, .right, 143)), -- 215; old225
  ((false, .right, 213), (true, .right, 154)), -- 216; old226
  ((false, .right, 183), (true, .right, 218)), -- 217; old227
  ((false, .right, 151), (true, .right, 92)), -- 218; old228
  ((false, .right, 151), (true, .right, 182)), -- 219; old229
  ((false, .right, 239), (true, .right, 139)), -- 220; old230
  ((false, .right, 227), (true, .right, 173)), -- 221; old231
  ((false, .right, 105), (true, .right, 210)), -- 222; old232
  ((false, .right, 79), (true, .right, 64)), -- 223; old233
  ((false, .right, 180), (true, .right, 153)), -- 224; old234
  ((false, .right, 221), (true, .right, 12)), -- 225; old235
  ((false, .right, 169), (true, .right, 104)), -- 226; old236
  ((false, .right, 208), (true, .right, 96)), -- 227; old237
  ((false, .right, 96), (true, .right, 227)), -- 228; old238
  ((false, .right, 169), (true, .right, 216)), -- 229; old239
  ((false, .right, 166), (true, .right, 90)), -- 230; old240
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
  ((false, .right, 81), (true, .right, 133)), -- 241; old252
  ((false, .right, 117), (true, .right, 141)), -- 242; old253
  ((true, .left, 243), (true, .left, 121)) -- 243; old255
]

theorem rawTableCompensated244_size : rawTableCompensated244.size = 244 := by decide +kernel

theorem rawTableCompensated244_transition_count :
    (rawTableCompensated244.toList.flatMap (fun r => [r.1, r.2])).length = 488 := by
  decide +kernel

def rawActionCompensated244 (q : Fin 244) (b : Bool) : RawActionCompensated244 :=
  let row := rawTableCompensated244.getD q.val
    ((false, .right, 244), (false, .right, 244))
  if b then row.2 else row.1

def actionCompensated244 (q : Fin 244) (b : Bool) : Action 244 :=
  let raw := rawActionCompensated244 q b
  { write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 244 then some ⟨raw.2.2, h⟩ else none }

def machineCompensated244 : Machine 244 where
  transition := actionCompensated244

/-- Original labels; absent labels have only a total fallback value. -/
def oldStateCompensated244 : Nat → Fin 244
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
  | 26 => 22
  | 27 => 23
  | 28 => 24
  | 29 => 25
  | 30 => 26
  | 31 => 27
  | 32 => 28
  | 33 => 29
  | 34 => 30
  | 35 => 31
  | 36 => 32
  | 37 => 33
  | 38 => 34
  | 39 => 35
  | 40 => 36
  | 41 => 37
  | 42 => 38
  | 44 => 39
  | 45 => 40
  | 46 => 41
  | 47 => 42
  | 48 => 43
  | 49 => 44
  | 50 => 45
  | 51 => 46
  | 52 => 47
  | 53 => 48
  | 54 => 49
  | 55 => 50
  | 56 => 51
  | 57 => 52
  | 58 => 53
  | 60 => 54
  | 61 => 55
  | 62 => 56
  | 63 => 57
  | 64 => 58
  | 65 => 59
  | 66 => 60
  | 67 => 61
  | 68 => 62
  | 69 => 63
  | 70 => 64
  | 71 => 65
  | 72 => 66
  | 73 => 67
  | 74 => 68
  | 75 => 69
  | 76 => 70
  | 77 => 71
  | 78 => 72
  | 79 => 73
  | 80 => 74
  | 81 => 75
  | 82 => 76
  | 83 => 77
  | 84 => 78
  | 86 => 79
  | 87 => 80
  | 88 => 81
  | 89 => 82
  | 90 => 83
  | 91 => 84
  | 92 => 85
  | 93 => 86
  | 94 => 87
  | 96 => 88
  | 98 => 89
  | 99 => 90
  | 100 => 91
  | 101 => 92
  | 102 => 93
  | 103 => 94
  | 104 => 95
  | 105 => 96
  | 106 => 97
  | 107 => 98
  | 108 => 99
  | 109 => 100
  | 110 => 101
  | 111 => 102
  | 112 => 103
  | 113 => 104
  | 114 => 105
  | 115 => 106
  | 116 => 107
  | 117 => 108
  | 118 => 109
  | 119 => 110
  | 120 => 111
  | 121 => 112
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

/-- The sole deleted old state is canonical113 in Routing245. -/
def embedState244 (q : Fin 244) : Fin 245 :=
  if h : q.val < 113 then ⟨q.val, by omega⟩ else ⟨q.val + 1, by omega⟩

def embedAction244 (a : Action 244) : Action 245 :=
  ⟨a.write, a.move, a.next.map embedState244⟩

def embedConfig244 (c : Config 244) : Config 245 :=
  ⟨c.state.map embedState244, c.head, c.tape⟩

theorem embedState244_ne_deleted : ∀ q,
    embedState244 q ≠ oldStateRouting245 122 := by decide +kernel

theorem embedState244_zero : embedState244 0 = 0 := by decide +kernel

theorem embedConfig244_initial : embedConfig244 (initial 244) = initial 245 := by
  rfl

/-- Four entry rows use the separately proved positive blocks. -/
def exceptionalRow244 (q : Fin 244) (b : Bool) : Prop :=
  b = true ∧ (q = oldStateCompensated244 104 ∨ q = oldStateCompensated244 106 ∨
    q = oldStateCompensated244 167 ∨ q = oldStateCompensated244 81)

instance (q : Fin 244) (b : Bool) : Decidable (exceptionalRow244 q b) :=
  inferInstanceAs (Decidable (b = true ∧ (q = oldStateCompensated244 104 ∨
    q = oldStateCompensated244 106 ∨ q = oldStateCompensated244 167 ∨
    q = oldStateCompensated244 81)))

/-- All482 ordinary retained rows agree, including final write/move on halt. -/
theorem compensated244_common_action : ∀ (q : Fin 244) (b : Bool),
    q ≠ oldStateCompensated244 92 → ¬ exceptionalRow244 q b →
      embedAction244 (machineCompensated244.transition q b) =
        machineRouting245.transition (embedState244 q) b := by decide +kernel

theorem compensated244_common_next : ∀ (q : Fin 244) (b : Bool),
    q ≠ oldStateCompensated244 92 → ¬ exceptionalRow244 q b →
      (machineCompensated244.transition q b).next ≠
        some (oldStateCompensated244 92) := by decide +kernel

theorem foldRowRouting245_old20_true :
    machineRouting245.transition (oldStateRouting245 20) true =
      ⟨false, .left, some (oldStateRouting245 2)⟩ := by decide +kernel

theorem foldRowRouting245_old24_true :
    machineRouting245.transition (oldStateRouting245 24) true =
      ⟨true, .right, some (oldStateRouting245 37)⟩ := by decide +kernel

theorem foldRowRouting245_old37_true :
    machineRouting245.transition (oldStateRouting245 37) true =
      ⟨true, .right, some (oldStateRouting245 55)⟩ := by decide +kernel

theorem foldRowRouting245_old55_true :
    machineRouting245.transition (oldStateRouting245 55) true =
      ⟨false, .left, some (oldStateRouting245 20)⟩ := by decide +kernel

theorem foldRowRouting245_old66_true :
    machineRouting245.transition (oldStateRouting245 66) true =
      ⟨false, .left, some (oldStateRouting245 20)⟩ := by decide +kernel

theorem foldRowRouting245_old81_true :
    machineRouting245.transition (oldStateRouting245 81) true =
      ⟨true, .left, some (oldStateRouting245 92)⟩ := by decide +kernel

theorem foldRowRouting245_old92_false :
    machineRouting245.transition (oldStateRouting245 92) false =
      ⟨false, .left, some (oldStateRouting245 107)⟩ := by decide +kernel

theorem foldRowRouting245_old92_true :
    machineRouting245.transition (oldStateRouting245 92) true =
      ⟨true, .left, some (oldStateRouting245 24)⟩ := by decide +kernel

theorem foldRowRouting245_old104_true :
    machineRouting245.transition (oldStateRouting245 104) true =
      ⟨true, .right, some (oldStateRouting245 122)⟩ := by decide +kernel

theorem foldRowRouting245_old106_true :
    machineRouting245.transition (oldStateRouting245 106) true =
      ⟨true, .right, some (oldStateRouting245 122)⟩ := by decide +kernel

theorem foldRowRouting245_old107_true :
    machineRouting245.transition (oldStateRouting245 107) true =
      ⟨true, .right, some (oldStateRouting245 125)⟩ := by decide +kernel

theorem foldRowRouting245_old122_false :
    machineRouting245.transition (oldStateRouting245 122) false =
      ⟨false, .right, some (oldStateRouting245 25)⟩ := by decide +kernel

theorem foldRowRouting245_old122_true :
    machineRouting245.transition (oldStateRouting245 122) true =
      ⟨true, .right, some (oldStateRouting245 66)⟩ := by decide +kernel

theorem foldRowRouting245_old125_false :
    machineRouting245.transition (oldStateRouting245 125) false =
      ⟨false, .right, some (oldStateRouting245 25)⟩ := by decide +kernel

theorem foldRowRouting245_old151_true :
    machineRouting245.transition (oldStateRouting245 151) true =
      ⟨true, .left, some (oldStateRouting245 24)⟩ := by decide +kernel

theorem foldRowRouting245_old167_true :
    machineRouting245.transition (oldStateRouting245 167) true =
      ⟨true, .left, some (oldStateRouting245 92)⟩ := by decide +kernel

theorem foldRowCompensated244_old20_true :
    machineCompensated244.transition (oldStateCompensated244 20) true =
      ⟨false, .left, some (oldStateCompensated244 2)⟩ := by decide +kernel

theorem foldRowCompensated244_old24_true :
    machineCompensated244.transition (oldStateCompensated244 24) true =
      ⟨true, .right, some (oldStateCompensated244 37)⟩ := by decide +kernel

theorem foldRowCompensated244_old37_true :
    machineCompensated244.transition (oldStateCompensated244 37) true =
      ⟨true, .right, some (oldStateCompensated244 55)⟩ := by decide +kernel

theorem foldRowCompensated244_old55_true :
    machineCompensated244.transition (oldStateCompensated244 55) true =
      ⟨false, .left, some (oldStateCompensated244 20)⟩ := by decide +kernel

theorem foldRowCompensated244_old66_true :
    machineCompensated244.transition (oldStateCompensated244 66) true =
      ⟨false, .left, some (oldStateCompensated244 20)⟩ := by decide +kernel

theorem foldRowCompensated244_old81_true :
    machineCompensated244.transition (oldStateCompensated244 81) true =
      ⟨true, .left, some (oldStateCompensated244 92)⟩ := by decide +kernel

theorem foldRowCompensated244_old92_false :
    machineCompensated244.transition (oldStateCompensated244 92) false =
      ⟨false, .left, some (oldStateCompensated244 107)⟩ := by decide +kernel

theorem foldRowCompensated244_old92_true :
    machineCompensated244.transition (oldStateCompensated244 92) true =
      ⟨true, .right, some (oldStateCompensated244 66)⟩ := by decide +kernel

theorem foldRowCompensated244_old104_true :
    machineCompensated244.transition (oldStateCompensated244 104) true =
      ⟨true, .right, some (oldStateCompensated244 92)⟩ := by decide +kernel

theorem foldRowCompensated244_old106_true :
    machineCompensated244.transition (oldStateCompensated244 106) true =
      ⟨true, .right, some (oldStateCompensated244 92)⟩ := by decide +kernel

theorem foldRowCompensated244_old107_true :
    machineCompensated244.transition (oldStateCompensated244 107) true =
      ⟨true, .right, some (oldStateCompensated244 125)⟩ := by decide +kernel

theorem foldRowCompensated244_old125_false :
    machineCompensated244.transition (oldStateCompensated244 125) false =
      ⟨false, .right, some (oldStateCompensated244 25)⟩ := by decide +kernel

theorem foldRowCompensated244_old151_true :
    machineCompensated244.transition (oldStateCompensated244 151) true =
      ⟨true, .left, some (oldStateCompensated244 24)⟩ := by decide +kernel

theorem foldRowCompensated244_old167_true :
    machineCompensated244.transition (oldStateCompensated244 167) true =
      ⟨true, .left, some (oldStateCompensated244 151)⟩ := by decide +kernel

theorem embedState244_old2 :
    embedState244 (oldStateCompensated244 2) = oldStateRouting245 2 := by decide +kernel

theorem embedState244_old20 :
    embedState244 (oldStateCompensated244 20) = oldStateRouting245 20 := by decide +kernel

theorem embedState244_old24 :
    embedState244 (oldStateCompensated244 24) = oldStateRouting245 24 := by decide +kernel

theorem embedState244_old25 :
    embedState244 (oldStateCompensated244 25) = oldStateRouting245 25 := by decide +kernel

theorem embedState244_old37 :
    embedState244 (oldStateCompensated244 37) = oldStateRouting245 37 := by decide +kernel

theorem embedState244_old55 :
    embedState244 (oldStateCompensated244 55) = oldStateRouting245 55 := by decide +kernel

theorem embedState244_old66 :
    embedState244 (oldStateCompensated244 66) = oldStateRouting245 66 := by decide +kernel

theorem embedState244_old81 :
    embedState244 (oldStateCompensated244 81) = oldStateRouting245 81 := by decide +kernel

theorem embedState244_old92 :
    embedState244 (oldStateCompensated244 92) = oldStateRouting245 92 := by decide +kernel

theorem embedState244_old95 :
    embedState244 (oldStateCompensated244 95) = oldStateRouting245 95 := by decide +kernel

theorem embedState244_old104 :
    embedState244 (oldStateCompensated244 104) = oldStateRouting245 104 := by decide +kernel

theorem embedState244_old106 :
    embedState244 (oldStateCompensated244 106) = oldStateRouting245 106 := by decide +kernel

theorem embedState244_old107 :
    embedState244 (oldStateCompensated244 107) = oldStateRouting245 107 := by decide +kernel

theorem embedState244_old125 :
    embedState244 (oldStateCompensated244 125) = oldStateRouting245 125 := by decide +kernel

theorem embedState244_old151 :
    embedState244 (oldStateCompensated244 151) = oldStateRouting245 151 := by decide +kernel

theorem embedState244_old167 :
    embedState244 (oldStateCompensated244 167) = oldStateRouting245 167 := by decide +kernel

end SetTheory.BusyBeaver.ZFC
