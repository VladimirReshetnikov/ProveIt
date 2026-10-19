import BusyBeaver.Core

/-!
Exact canonical 240-state table from e5c2b3337e, with the second source-loop
rotation and the old72/90 fold. The inherited old15/27, old17/39 and old122
folds are already present in these literal data. Original Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt attribution is retained.
This module supplies literal data and finite facts only. Runtime, bootstrap,
source calibration and a blank-halting endpoint require separate proofs.
-/
namespace SetTheory.BusyBeaver.ZFC

abbrev RawActionRotation240 := Bool × Move × Nat

def rawTableRotation240 : Array (RawActionRotation240 × RawActionRotation240) := #[
  ((true, .right, 96), (true, .right, 0)), -- 0; old95
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
  ((false, .left, 26), (true, .right, 18)), -- 11; old15
  ((false, .right, 19), (true, .right, 20)), -- 12; old16
  ((false, .left, 93), (true, .left, 31)), -- 13; old17
  ((false, .left, 11), (false, .right, 22)), -- 14; old18
  ((false, .left, 23), (true, .left, 2)), -- 15; old19
  ((true, .left, 1), (false, .left, 1)), -- 16; old20
  ((false, .right, 24), (false, .right, 32)), -- 17; old21
  ((false, .right, 26), (false, .left, 27)), -- 18; old22
  ((false, .right, 28), (true, .right, 29)), -- 19; old23
  ((false, .right, 30), (true, .right, 31)), -- 20; old24
  ((false, .right, 24), (false, .right, 60)), -- 21; old25
  ((false, .right, 33), (true, .right, 22)), -- 22; old28
  ((false, .left, 34), (true, .left, 2)), -- 23; old29
  ((false, .left, 35), (false, .right, 0)), -- 24; old30
  ((false, .right, 36), (true, .right, 25)), -- 25; old31
  ((false, .right, 37), (true, .right, 38)), -- 26; old32
  ((false, .right, 39), (false, .left, 40)), -- 27; old33
  ((false, .right, 41), (true, .right, 42)), -- 28; old34
  ((false, .right, 43), (true, .right, 44)), -- 29; old35
  ((false, .right, 45), (true, .right, 46)), -- 30; old36
  ((false, .right, 21), (true, .right, 47)), -- 31; old37
  ((false, .right, 48), (true, .right, 32)), -- 32; old38
  ((false, .right, 32), (true, .right, 33)), -- 33; old40
  ((false, .left, 50), (true, .left, 2)), -- 34; old41
  ((true, .right, 35), (true, .left, 1)), -- 35; old42
  ((false, .right, 51), (true, .right, 36)), -- 36; old44
  ((false, .right, 17), (true, .right, 52)), -- 37; old45
  ((false, .right, 13), (true, .right, 53)), -- 38; old46
  ((false, .left, 11), (false, .right, 36)), -- 39; old47
  ((false, .left, 4), (true, .left, 54)), -- 40; old48
  ((false, .right, 24), (false, .right, 25)), -- 41; old49
  ((false, .right, 13), (false, .left, 16)), -- 42; old50
  ((false, .right, 56), (true, .right, 57)), -- 43; old51
  ((false, .right, 58), (true, .right, 59)), -- 44; old52
  ((false, .right, 24), (false, .right, 55)), -- 45; old53
  ((false, .right, 61), (true, .right, 62)), -- 46; old54
  ((false, .right, 63), (false, .left, 16)), -- 47; old55
  ((false, .right, 25), (true, .right, 48)), -- 48; old56
  ((false, .left, 35), (false, .right, 64)), -- 49; old57
  ((false, .left, 75), (true, .left, 2)), -- 50; old58
  ((false, .right, 16), (true, .right, 51)), -- 51; old60
  ((false, .right, 67), (false, .left, 27)), -- 52; old61
  ((false, .right, 68), (true, .right, 69)), -- 53; old62
  ((false, .left, 40), (true, .left, 54)), -- 54; old63
  ((false, .right, 22), (true, .right, 55)), -- 55; old64
  ((false, .left, 11), (false, .right, 51)), -- 56; old65
  ((false, .right, 61), (false, .left, 16)), -- 57; old66
  ((false, .right, 70), (true, .right, 71)), -- 58; old67
  ((false, .right, 62), (true, .right, 72)), -- 59; old68
  ((false, .right, 55), (true, .right, 60)), -- 60; old69
  ((false, .right, 49), (false, .right, 25)), -- 61; old70
  ((false, .left, 28), (true, .left, 73)), -- 62; old71
  ((false, .left, 130), (true, .left, 30)), -- 63; old72
  ((false, .right, 74), (true, .right, 64)), -- 64; old73
  ((false, .right, 118), (true, .right, 12)), -- 65; old74
  ((true, .right, 239), (true, .left, 54)), -- 66; old75
  ((false, .right, 76), (true, .right, 77)), -- 67; old76
  ((false, .right, 78), (true, .right, 240)), -- 68; old77
  ((false, .left, 79), (true, .right, 31)), -- 69; old78
  ((false, .right, 41), (true, .right, 63)), -- 70; old79
  ((false, .right, 21), (true, .right, 80)), -- 71; old80
  ((false, .right, 56), (true, .left, 81)), -- 72; old81
  ((false, .right, 82), (true, .right, 83)), -- 73; old82
  ((true, .right, 0), (true, .right, 64)), -- 74; old83
  ((false, .right, 75), (true, .right, 84)), -- 75; old84
  ((false, .right, 85), (true, .right, 86)), -- 76; old86
  ((false, .right, 200), (true, .right, 234)), -- 77; old87
  ((false, .right, 89), (true, .right, 90)), -- 78; old88
  ((false, .right, 91), (true, .right, 92)), -- 79; old89
  ((false, .right, 93), (false, .left, 42)), -- 80; old91
  ((false, .left, 94), (true, .right, 57)), -- 81; old92
  ((false, .right, 49), (false, .right, 33)), -- 82; old93
  ((false, .right, 95), (false, .left, 42)), -- 83; old94
  ((false, .right, 97), (true, .right, 98)), -- 84; old96
  ((false, .right, 19), (true, .right, 65)), -- 85; old98
  ((false, .right, 92), (true, .right, 101)), -- 86; old99
  ((false, .right, 139), (true, .right, 170)), -- 87; old100
  ((false, .right, 180), (true, .right, 193)), -- 88; old101
  ((false, .right, 21), (true, .right, 106)), -- 89; old102
  ((false, .right, 45), (true, .right, 107)), -- 90; old103
  ((false, .right, 108), (true, .right, 81)), -- 91; old104
  ((false, .right, 109), (true, .right, 110)), -- 92; old105
  ((false, .right, 82), (true, .right, 81)), -- 93; old106
  ((false, .right, 108), (true, .right, 111)), -- 94; old107
  ((false, .right, 112), (true, .right, 113)), -- 95; old108
  ((false, .right, 66), (false, .right, 0)), -- 96; old109
  ((false, .right, 27), (true, .right, 114)), -- 97; old110
  ((false, .right, 115), (true, .right, 116)), -- 98; old111
  ((true, .left, 117), (true, .left, 99)), -- 99; old112
  ((false, .right, 19), (true, .right, 118)), -- 100; old113
  ((false, .right, 61), (true, .right, 61)), -- 101; old114
  ((false, .right, 123), (true, .right, 215)), -- 102; old115
  ((false, .right, 169), (true, .right, 120)), -- 103; old116
  ((false, .right, 169), (true, .right, 197)), -- 104; old117
  ((false, .right, 217), (true, .right, 145)), -- 105; old118
  ((false, .right, 127), (true, .right, 128)), -- 106; old119
  ((false, .right, 129), (false, .left, 52)), -- 107; old120
  ((false, .right, 130), (true, .right, 131)), -- 108; old121
  ((false, .right, 72), (true, .right, 59)), -- 109; old123
  ((false, .right, 58), (true, .right, 132)), -- 110; old124
  ((false, .right, 21), (true, .right, 133)), -- 111; old125
  ((false, .right, 21), (false, .left, 40)), -- 112; old126
  ((false, .right, 62), (true, .right, 42)), -- 113; old127
  ((false, .right, 134), (true, .right, 8)), -- 114; old128
  ((false, .right, 108), (true, .right, 135)), -- 115; old129
  ((false, .right, 94), (true, .right, 136)), -- 116; old130
  ((false, .left, 40), (false, .left, 99)), -- 117; old131
  ((false, .right, 137), (true, .right, 111)), -- 118; old132
  ((false, .right, 69), (true, .right, 138)), -- 119; old133
  ((false, .right, 199), (true, .right, 233)), -- 120; old134
  ((false, .right, 226), (true, .right, 201)), -- 121; old135
  ((false, .right, 173), (true, .right, 201)), -- 122; old136
  ((false, .right, 145), (true, .right, 146)), -- 123; old137
  ((false, .right, 168), (true, .right, 104)), -- 124; old138
  ((false, .right, 76), (true, .right, 221)), -- 125; old139
  ((false, .right, 125), (true, .right, 208)), -- 126; old140
  ((false, .right, 45), (false, .left, 10)), -- 127; old141
  ((false, .right, 63), (true, .right, 13)), -- 128; old142
  ((false, .left, 152), (false, .left, 1)), -- 129; old143
  ((false, .right, 39), (true, .right, 73)), -- 130; old144
  ((false, .right, 62), (true, .right, 153)), -- 131; old145
  ((false, .right, 62), (true, .right, 154)), -- 132; old146
  ((false, .right, 155), (false, .left, 16)), -- 133; old147
  ((false, .right, 14), (true, .right, 153)), -- 134; old148
  ((false, .right, 21), (true, .right, 156)), -- 135; old149
  ((false, .right, 157), (true, .right, 158)), -- 136; old150
  ((false, .right, 159), (true, .left, 20)), -- 137; old151
  ((false, .right, 160), (true, .right, 161)), -- 138; old152
  ((false, .right, 162), (true, .left, 143)), -- 139; old153
  ((false, .right, 76), (true, .right, 228)), -- 140; old154
  ((false, .right, 140), (true, .right, 203)), -- 141; old155
  ((false, .right, 219), (true, .right, 222)), -- 142; old156
  ((false, .right, 161), (true, .right, 193)), -- 143; old157
  ((false, .right, 207), (true, .right, 176)), -- 144; old158
  ((false, .left, 143), (true, .right, 173)), -- 145; old159
  ((false, .right, 174), (true, .right, 175)), -- 146; old160
  ((false, .right, 165), (true, .right, 177)), -- 147; old161
  ((false, .right, 232), (true, .right, 103)), -- 148; old162
  ((false, .right, 211), (true, .right, 179)), -- 149; old163
  ((false, .right, 220), (true, .right, 105)), -- 150; old164
  ((false, .right, 12), (true, .right, 121)), -- 151; old165
  ((false, .right, 30), (true, .right, 70)), -- 152; old166
  ((false, .right, 39), (true, .left, 137)), -- 153; old167
  ((false, .right, 186), (false, .left, 16)), -- 154; old168
  ((false, .right, 49), (false, .right, 48)), -- 155; old169
  ((false, .right, 187), (false, .left, 16)), -- 156; old170
  ((false, .right, 17), (true, .right, 188)), -- 157; old171
  ((false, .right, 189), (true, .right, 190)), -- 158; old172
  ((false, .right, 24), (false, .right, 48)), -- 159; old173
  ((false, .right, 191), (true, .right, 79)), -- 160; old174
  ((false, .right, 100), (true, .right, 92)), -- 161; old175
  ((false, .right, 100), (true, .right, 192)), -- 162; old176
  ((false, .right, 151), (true, .right, 171)), -- 163; old177
  ((false, .right, 12), (true, .right, 192)), -- 164; old178
  ((false, .right, 92), (true, .right, 92)), -- 165; old179
  ((false, .right, 92), (true, .right, 195)), -- 166; old180
  ((false, .right, 164), (true, .right, 227)), -- 167; old181
  ((false, .right, 173), (true, .right, 198)), -- 168; old182
  ((false, .right, 86), (true, .left, 199)), -- 169; old183
  ((false, .right, 167), (true, .right, 148)), -- 170; old184
  ((false, .right, 178), (true, .right, 198)), -- 171; old185
  ((false, .right, 218), (true, .right, 193)), -- 172; old186
  ((false, .right, 85), (true, .right, 204)), -- 173; old187
  ((false, .right, 205), (true, .right, 206)), -- 174; old188
  ((false, .right, 144), (true, .right, 230)), -- 175; old189
  ((false, .right, 92), (true, .right, 86)), -- 176; old190
  ((false, .right, 172), (true, .right, 192)), -- 177; old191
  ((false, .right, 207), (true, .right, 206)), -- 178; old192
  ((false, .right, 176), (true, .right, 199)), -- 179; old193
  ((false, .right, 145), (true, .right, 210)), -- 180; old194
  ((false, .right, 101), (true, .right, 142)), -- 181; old195
  ((false, .right, 181), (true, .right, 126)), -- 182; old196
  ((false, .right, 182), (true, .right, 102)), -- 183; old197
  ((false, .right, 192), (true, .right, 122)), -- 184; old198
  ((false, .right, 183), (true, .right, 213)), -- 185; old199
  ((false, .right, 101), (true, .right, 101)), -- 186; old200
  ((false, .right, 49), (false, .right, 32)), -- 187; old201
  ((false, .right, 7), (false, .left, 27)), -- 188; old202
  ((false, .right, 161), (true, .right, 28)), -- 189; old203
  ((false, .right, 78), (true, .right, 100)), -- 190; old204
  ((false, .right, 192), (true, .right, 19)), -- 191; old205
  ((false, .right, 19), (true, .right, 216)), -- 192; old206
  ((false, .right, 199), (true, .right, 217)), -- 193; old207
  ((false, .right, 185), (true, .right, 176)), -- 194; old208
  ((false, .right, 207), (true, .right, 218)), -- 195; old209
  ((false, .right, 101), (true, .right, 163)), -- 196; old210
  ((false, .right, 196), (true, .right, 176)), -- 197; old211
  ((false, .right, 222), (true, .right, 164)), -- 198; old212
  ((false, .right, 223), (true, .right, 224)), -- 199; old213
  ((false, .right, 119), (true, .right, 87)), -- 200; old214
  ((false, .right, 169), (true, .right, 219)), -- 201; old215
  ((false, .right, 166), (true, .right, 124)), -- 202; old216
  ((false, .right, 219), (true, .right, 221)), -- 203; old217
  ((false, .left, 76), (true, .right, 61)), -- 204; old218
  ((false, .right, 192), (true, .right, 164)), -- 205; old219
  ((false, .right, 229), (true, .right, 204)), -- 206; old220
  ((false, .right, 192), (true, .right, 229)), -- 207; old221
  ((false, .right, 202), (true, .right, 141)), -- 208; old222
  ((false, .right, 166), (true, .right, 194)), -- 209; old223
  ((false, .right, 230), (true, .right, 230)), -- 210; old224
  ((false, .right, 231), (true, .right, 139)), -- 211; old225
  ((false, .right, 209), (true, .right, 150)), -- 212; old226
  ((false, .right, 179), (true, .right, 214)), -- 213; old227
  ((false, .right, 147), (true, .right, 88)), -- 214; old228
  ((false, .right, 147), (true, .right, 178)), -- 215; old229
  ((false, .right, 235), (true, .right, 135)), -- 216; old230
  ((false, .right, 223), (true, .right, 169)), -- 217; old231
  ((false, .right, 101), (true, .right, 206)), -- 218; old232
  ((false, .right, 76), (true, .right, 61)), -- 219; old233
  ((false, .right, 176), (true, .right, 149)), -- 220; old234
  ((false, .right, 217), (true, .right, 12)), -- 221; old235
  ((false, .right, 165), (true, .right, 100)), -- 222; old236
  ((false, .right, 204), (true, .right, 92)), -- 223; old237
  ((false, .right, 92), (true, .right, 223)), -- 224; old238
  ((false, .right, 165), (true, .right, 212)), -- 225; old239
  ((false, .right, 162), (true, .right, 86)), -- 226; old240
  ((false, .right, 225), (true, .right, 184)), -- 227; old241
  ((false, .right, 226), (true, .right, 222)), -- 228; old242
  ((false, .left, 138), (true, .left, 231)), -- 229; old243
  ((false, .right, 164), (true, .left, 174)), -- 230; old244
  ((false, .right, 12), (true, .right, 230)), -- 231; old245
  ((false, .right, 192), (true, .right, 219)), -- 232; old246
  ((false, .right, 199), (true, .right, 235)), -- 233; old248
  ((false, .right, 236), (true, .right, 237)), -- 234; old249
  ((false, .right, 17), (true, .left, 152)), -- 235; old250
  ((false, .right, 237), (true, .right, 238)), -- 236; old251
  ((false, .right, 78), (true, .right, 129)), -- 237; old252
  ((false, .right, 113), (true, .right, 137)), -- 238; old253
  ((true, .left, 239), (true, .left, 117)) -- 239; old255
]

theorem rawTableRotation240_size : rawTableRotation240.size = 240 := by decide +kernel

theorem rawTableRotation240_transition_count :
    (rawTableRotation240.toList.flatMap (fun r => [r.1, r.2])).length = 480 := by
  decide +kernel

def rawActionRotation240 (q : Fin 240) (b : Bool) : RawActionRotation240 :=
  let row := rawTableRotation240.getD q.val
    ((false, .right, 240), (false, .right, 240))
  if b then row.2 else row.1

def actionRotation240 (q : Fin 240) (b : Bool) : Action 240 :=
  let raw := rawActionRotation240 q b
  { write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 240 then some ⟨raw.2.2, h⟩ else none }

def machineRotation240 : Machine 240 where
  transition := actionRotation240

/-- Absent old labels have only a total fallback value. -/
def oldStateRotation240 : Nat → Fin 240
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
  | 28 => 22
  | 29 => 23
  | 30 => 24
  | 31 => 25
  | 32 => 26
  | 33 => 27
  | 34 => 28
  | 35 => 29
  | 36 => 30
  | 37 => 31
  | 38 => 32
  | 40 => 33
  | 41 => 34
  | 42 => 35
  | 44 => 36
  | 45 => 37
  | 46 => 38
  | 47 => 39
  | 48 => 40
  | 49 => 41
  | 50 => 42
  | 51 => 43
  | 52 => 44
  | 53 => 45
  | 54 => 46
  | 55 => 47
  | 56 => 48
  | 57 => 49
  | 58 => 50
  | 60 => 51
  | 61 => 52
  | 62 => 53
  | 63 => 54
  | 64 => 55
  | 65 => 56
  | 66 => 57
  | 67 => 58
  | 68 => 59
  | 69 => 60
  | 70 => 61
  | 71 => 62
  | 72 => 63
  | 73 => 64
  | 74 => 65
  | 75 => 66
  | 76 => 67
  | 77 => 68
  | 78 => 69
  | 79 => 70
  | 80 => 71
  | 81 => 72
  | 82 => 73
  | 83 => 74
  | 84 => 75
  | 86 => 76
  | 87 => 77
  | 88 => 78
  | 89 => 79
  | 91 => 80
  | 92 => 81
  | 93 => 82
  | 94 => 83
  | 96 => 84
  | 98 => 85
  | 99 => 86
  | 100 => 87
  | 101 => 88
  | 102 => 89
  | 103 => 90
  | 104 => 91
  | 105 => 92
  | 106 => 93
  | 107 => 94
  | 108 => 95
  | 109 => 96
  | 110 => 97
  | 111 => 98
  | 112 => 99
  | 113 => 100
  | 114 => 101
  | 115 => 102
  | 116 => 103
  | 117 => 104
  | 118 => 105
  | 119 => 106
  | 120 => 107
  | 121 => 108
  | 123 => 109
  | 124 => 110
  | 125 => 111
  | 126 => 112
  | 127 => 113
  | 128 => 114
  | 129 => 115
  | 130 => 116
  | 131 => 117
  | 132 => 118
  | 133 => 119
  | 134 => 120
  | 135 => 121
  | 136 => 122
  | 137 => 123
  | 138 => 124
  | 139 => 125
  | 140 => 126
  | 141 => 127
  | 142 => 128
  | 143 => 129
  | 144 => 130
  | 145 => 131
  | 146 => 132
  | 147 => 133
  | 148 => 134
  | 149 => 135
  | 150 => 136
  | 151 => 137
  | 152 => 138
  | 153 => 139
  | 154 => 140
  | 155 => 141
  | 156 => 142
  | 157 => 143
  | 158 => 144
  | 159 => 145
  | 160 => 146
  | 161 => 147
  | 162 => 148
  | 163 => 149
  | 164 => 150
  | 165 => 151
  | 166 => 152
  | 167 => 153
  | 168 => 154
  | 169 => 155
  | 170 => 156
  | 171 => 157
  | 172 => 158
  | 173 => 159
  | 174 => 160
  | 175 => 161
  | 176 => 162
  | 177 => 163
  | 178 => 164
  | 179 => 165
  | 180 => 166
  | 181 => 167
  | 182 => 168
  | 183 => 169
  | 184 => 170
  | 185 => 171
  | 186 => 172
  | 187 => 173
  | 188 => 174
  | 189 => 175
  | 190 => 176
  | 191 => 177
  | 192 => 178
  | 193 => 179
  | 194 => 180
  | 195 => 181
  | 196 => 182
  | 197 => 183
  | 198 => 184
  | 199 => 185
  | 200 => 186
  | 201 => 187
  | 202 => 188
  | 203 => 189
  | 204 => 190
  | 205 => 191
  | 206 => 192
  | 207 => 193
  | 208 => 194
  | 209 => 195
  | 210 => 196
  | 211 => 197
  | 212 => 198
  | 213 => 199
  | 214 => 200
  | 215 => 201
  | 216 => 202
  | 217 => 203
  | 218 => 204
  | 219 => 205
  | 220 => 206
  | 221 => 207
  | 222 => 208
  | 223 => 209
  | 224 => 210
  | 225 => 211
  | 226 => 212
  | 227 => 213
  | 228 => 214
  | 229 => 215
  | 230 => 216
  | 231 => 217
  | 232 => 218
  | 233 => 219
  | 234 => 220
  | 235 => 221
  | 236 => 222
  | 237 => 223
  | 238 => 224
  | 239 => 225
  | 240 => 226
  | 241 => 227
  | 242 => 228
  | 243 => 229
  | 244 => 230
  | 245 => 231
  | 246 => 232
  | 248 => 233
  | 249 => 234
  | 250 => 235
  | 251 => 236
  | 252 => 237
  | 253 => 238
  | 255 => 239
  | _ => 0

def oldLabelsRotation240 : Array Nat := #[95, 2, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 86, 87, 88, 89, 91, 92, 93, 94, 96, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 248, 249, 250, 251, 252, 253, 255]

def oldLabelRotation240 (q : Fin 240) : Nat := oldLabelsRotation240.getD q.val 95

theorem oldStateRotation240_oldLabel : ∀ q : Fin 240,
    oldStateRotation240 (oldLabelRotation240 q) = q := by decide +kernel

theorem machineRotation240_start : oldStateRotation240 95 = 0 := by decide +kernel

theorem machineRotation240_dispatch : oldStateRotation240 96 = 84 := by decide +kernel

theorem machineRotation240_halt_iff : ∀ (q : Fin 240) (b : Bool),
    (machineRotation240.transition q b).next = none ↔
      q = oldStateRotation240 77 ∧ b = true := by decide +kernel

theorem machineRotation240_halt_action :
    machineRotation240.transition (oldStateRotation240 77) true =
      ⟨true, .right, none⟩ := by decide +kernel

end SetTheory.BusyBeaver.ZFC
