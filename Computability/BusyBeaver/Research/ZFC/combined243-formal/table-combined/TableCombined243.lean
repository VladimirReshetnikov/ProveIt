import BusyBeaver.ZFC.TableRotation244
import Lean.Elab.Tactic.Omega

/-!
Exact combined243 canonical table and its embedding into Rotation244.
The compensated fold removes old122 and changes four rows of Rotation244;
the loop rotation removing old26 is already present on both sides.
This module states literal table, renumbering and common-transition facts.
Core configurations carry arbitrary finite-support List Int tapes.
-/
namespace SetTheory.BusyBeaver.ZFC

abbrev RawActionCombined243 := Bool × Move × Nat

def rawTableCombined243 : Array (RawActionCombined243 × RawActionCombined243) := #[
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
  ((false, .right, 121), (true, .right, 12)), -- 67; old74
  ((true, .right, 242), (true, .left, 56)), -- 68; old75
  ((false, .right, 78), (true, .right, 79)), -- 69; old76
  ((false, .right, 80), (true, .right, 243)), -- 70; old77
  ((false, .left, 81), (true, .right, 32)), -- 71; old78
  ((false, .right, 43), (true, .right, 82)), -- 72; old79
  ((false, .right, 21), (true, .right, 83)), -- 73; old80
  ((false, .right, 58), (true, .left, 84)), -- 74; old81
  ((false, .right, 85), (true, .right, 86)), -- 75; old82
  ((true, .right, 0), (true, .right, 66)), -- 76; old83
  ((false, .right, 77), (true, .right, 87)), -- 77; old84
  ((false, .right, 88), (true, .right, 89)), -- 78; old86
  ((false, .right, 203), (true, .right, 237)), -- 79; old87
  ((false, .right, 92), (true, .right, 93)), -- 80; old88
  ((false, .right, 94), (true, .right, 95)), -- 81; old89
  ((false, .right, 85), (true, .right, 64)), -- 82; old90
  ((false, .right, 96), (false, .left, 44)), -- 83; old91
  ((false, .left, 97), (true, .right, 59)), -- 84; old92
  ((false, .right, 51), (false, .right, 35)), -- 85; old93
  ((false, .right, 98), (false, .left, 44)), -- 86; old94
  ((false, .right, 100), (true, .right, 101)), -- 87; old96
  ((false, .right, 19), (true, .right, 67)), -- 88; old98
  ((false, .right, 95), (true, .right, 104)), -- 89; old99
  ((false, .right, 142), (true, .right, 173)), -- 90; old100
  ((false, .right, 183), (true, .right, 196)), -- 91; old101
  ((false, .right, 21), (true, .right, 109)), -- 92; old102
  ((false, .right, 47), (true, .right, 110)), -- 93; old103
  ((false, .right, 111), (true, .right, 84)), -- 94; old104
  ((false, .right, 112), (true, .right, 113)), -- 95; old105
  ((false, .right, 85), (true, .right, 84)), -- 96; old106
  ((false, .right, 111), (true, .right, 114)), -- 97; old107
  ((false, .right, 115), (true, .right, 116)), -- 98; old108
  ((false, .right, 68), (false, .right, 0)), -- 99; old109
  ((false, .right, 28), (true, .right, 117)), -- 100; old110
  ((false, .right, 118), (true, .right, 119)), -- 101; old111
  ((true, .left, 120), (true, .left, 102)), -- 102; old112
  ((false, .right, 19), (true, .right, 121)), -- 103; old113
  ((false, .right, 63), (true, .right, 63)), -- 104; old114
  ((false, .right, 126), (true, .right, 218)), -- 105; old115
  ((false, .right, 172), (true, .right, 123)), -- 106; old116
  ((false, .right, 172), (true, .right, 200)), -- 107; old117
  ((false, .right, 220), (true, .right, 148)), -- 108; old118
  ((false, .right, 130), (true, .right, 131)), -- 109; old119
  ((false, .right, 132), (false, .left, 54)), -- 110; old120
  ((false, .right, 133), (true, .right, 134)), -- 111; old121
  ((false, .right, 74), (true, .right, 61)), -- 112; old123
  ((false, .right, 60), (true, .right, 135)), -- 113; old124
  ((false, .right, 21), (true, .right, 136)), -- 114; old125
  ((false, .right, 21), (false, .left, 42)), -- 115; old126
  ((false, .right, 64), (true, .right, 44)), -- 116; old127
  ((false, .right, 137), (true, .right, 8)), -- 117; old128
  ((false, .right, 111), (true, .right, 138)), -- 118; old129
  ((false, .right, 97), (true, .right, 139)), -- 119; old130
  ((false, .left, 42), (false, .left, 102)), -- 120; old131
  ((false, .right, 140), (true, .right, 114)), -- 121; old132
  ((false, .right, 71), (true, .right, 141)), -- 122; old133
  ((false, .right, 202), (true, .right, 236)), -- 123; old134
  ((false, .right, 229), (true, .right, 204)), -- 124; old135
  ((false, .right, 176), (true, .right, 204)), -- 125; old136
  ((false, .right, 148), (true, .right, 149)), -- 126; old137
  ((false, .right, 171), (true, .right, 107)), -- 127; old138
  ((false, .right, 78), (true, .right, 224)), -- 128; old139
  ((false, .right, 128), (true, .right, 211)), -- 129; old140
  ((false, .right, 47), (false, .left, 10)), -- 130; old141
  ((false, .right, 32), (true, .right, 65)), -- 131; old142
  ((false, .left, 155), (false, .left, 1)), -- 132; old143
  ((false, .right, 41), (true, .right, 75)), -- 133; old144
  ((false, .right, 64), (true, .right, 156)), -- 134; old145
  ((false, .right, 64), (true, .right, 157)), -- 135; old146
  ((false, .right, 158), (false, .left, 16)), -- 136; old147
  ((false, .right, 14), (true, .right, 156)), -- 137; old148
  ((false, .right, 21), (true, .right, 159)), -- 138; old149
  ((false, .right, 160), (true, .right, 161)), -- 139; old150
  ((false, .right, 162), (true, .left, 20)), -- 140; old151
  ((false, .right, 163), (true, .right, 164)), -- 141; old152
  ((false, .right, 165), (true, .left, 146)), -- 142; old153
  ((false, .right, 78), (true, .right, 231)), -- 143; old154
  ((false, .right, 143), (true, .right, 206)), -- 144; old155
  ((false, .right, 222), (true, .right, 225)), -- 145; old156
  ((false, .right, 164), (true, .right, 196)), -- 146; old157
  ((false, .right, 210), (true, .right, 179)), -- 147; old158
  ((false, .left, 146), (true, .right, 176)), -- 148; old159
  ((false, .right, 177), (true, .right, 178)), -- 149; old160
  ((false, .right, 168), (true, .right, 180)), -- 150; old161
  ((false, .right, 235), (true, .right, 106)), -- 151; old162
  ((false, .right, 214), (true, .right, 182)), -- 152; old163
  ((false, .right, 223), (true, .right, 108)), -- 153; old164
  ((false, .right, 12), (true, .right, 124)), -- 154; old165
  ((false, .right, 31), (true, .right, 72)), -- 155; old166
  ((false, .right, 41), (true, .left, 140)), -- 156; old167
  ((false, .right, 189), (false, .left, 16)), -- 157; old168
  ((false, .right, 51), (false, .right, 50)), -- 158; old169
  ((false, .right, 190), (false, .left, 16)), -- 159; old170
  ((false, .right, 17), (true, .right, 191)), -- 160; old171
  ((false, .right, 192), (true, .right, 193)), -- 161; old172
  ((false, .right, 25), (false, .right, 50)), -- 162; old173
  ((false, .right, 194), (true, .right, 81)), -- 163; old174
  ((false, .right, 103), (true, .right, 95)), -- 164; old175
  ((false, .right, 103), (true, .right, 195)), -- 165; old176
  ((false, .right, 154), (true, .right, 174)), -- 166; old177
  ((false, .right, 12), (true, .right, 195)), -- 167; old178
  ((false, .right, 95), (true, .right, 95)), -- 168; old179
  ((false, .right, 95), (true, .right, 198)), -- 169; old180
  ((false, .right, 167), (true, .right, 230)), -- 170; old181
  ((false, .right, 176), (true, .right, 201)), -- 171; old182
  ((false, .right, 89), (true, .left, 202)), -- 172; old183
  ((false, .right, 170), (true, .right, 151)), -- 173; old184
  ((false, .right, 181), (true, .right, 201)), -- 174; old185
  ((false, .right, 221), (true, .right, 196)), -- 175; old186
  ((false, .right, 88), (true, .right, 207)), -- 176; old187
  ((false, .right, 208), (true, .right, 209)), -- 177; old188
  ((false, .right, 147), (true, .right, 233)), -- 178; old189
  ((false, .right, 95), (true, .right, 89)), -- 179; old190
  ((false, .right, 175), (true, .right, 195)), -- 180; old191
  ((false, .right, 210), (true, .right, 209)), -- 181; old192
  ((false, .right, 179), (true, .right, 202)), -- 182; old193
  ((false, .right, 148), (true, .right, 213)), -- 183; old194
  ((false, .right, 104), (true, .right, 145)), -- 184; old195
  ((false, .right, 184), (true, .right, 129)), -- 185; old196
  ((false, .right, 185), (true, .right, 105)), -- 186; old197
  ((false, .right, 195), (true, .right, 125)), -- 187; old198
  ((false, .right, 186), (true, .right, 216)), -- 188; old199
  ((false, .right, 104), (true, .right, 104)), -- 189; old200
  ((false, .right, 51), (false, .right, 33)), -- 190; old201
  ((false, .right, 7), (false, .left, 28)), -- 191; old202
  ((false, .right, 164), (true, .right, 29)), -- 192; old203
  ((false, .right, 80), (true, .right, 103)), -- 193; old204
  ((false, .right, 195), (true, .right, 19)), -- 194; old205
  ((false, .right, 19), (true, .right, 219)), -- 195; old206
  ((false, .right, 202), (true, .right, 220)), -- 196; old207
  ((false, .right, 188), (true, .right, 179)), -- 197; old208
  ((false, .right, 210), (true, .right, 221)), -- 198; old209
  ((false, .right, 104), (true, .right, 166)), -- 199; old210
  ((false, .right, 199), (true, .right, 179)), -- 200; old211
  ((false, .right, 225), (true, .right, 167)), -- 201; old212
  ((false, .right, 226), (true, .right, 227)), -- 202; old213
  ((false, .right, 122), (true, .right, 90)), -- 203; old214
  ((false, .right, 172), (true, .right, 222)), -- 204; old215
  ((false, .right, 169), (true, .right, 127)), -- 205; old216
  ((false, .right, 222), (true, .right, 224)), -- 206; old217
  ((false, .left, 78), (true, .right, 63)), -- 207; old218
  ((false, .right, 195), (true, .right, 167)), -- 208; old219
  ((false, .right, 232), (true, .right, 207)), -- 209; old220
  ((false, .right, 195), (true, .right, 232)), -- 210; old221
  ((false, .right, 205), (true, .right, 144)), -- 211; old222
  ((false, .right, 169), (true, .right, 197)), -- 212; old223
  ((false, .right, 233), (true, .right, 233)), -- 213; old224
  ((false, .right, 234), (true, .right, 142)), -- 214; old225
  ((false, .right, 212), (true, .right, 153)), -- 215; old226
  ((false, .right, 182), (true, .right, 217)), -- 216; old227
  ((false, .right, 150), (true, .right, 91)), -- 217; old228
  ((false, .right, 150), (true, .right, 181)), -- 218; old229
  ((false, .right, 238), (true, .right, 138)), -- 219; old230
  ((false, .right, 226), (true, .right, 172)), -- 220; old231
  ((false, .right, 104), (true, .right, 209)), -- 221; old232
  ((false, .right, 78), (true, .right, 63)), -- 222; old233
  ((false, .right, 179), (true, .right, 152)), -- 223; old234
  ((false, .right, 220), (true, .right, 12)), -- 224; old235
  ((false, .right, 168), (true, .right, 103)), -- 225; old236
  ((false, .right, 207), (true, .right, 95)), -- 226; old237
  ((false, .right, 95), (true, .right, 226)), -- 227; old238
  ((false, .right, 168), (true, .right, 215)), -- 228; old239
  ((false, .right, 165), (true, .right, 89)), -- 229; old240
  ((false, .right, 228), (true, .right, 187)), -- 230; old241
  ((false, .right, 229), (true, .right, 225)), -- 231; old242
  ((false, .left, 141), (true, .left, 234)), -- 232; old243
  ((false, .right, 167), (true, .left, 177)), -- 233; old244
  ((false, .right, 12), (true, .right, 233)), -- 234; old245
  ((false, .right, 195), (true, .right, 222)), -- 235; old246
  ((false, .right, 202), (true, .right, 238)), -- 236; old248
  ((false, .right, 239), (true, .right, 240)), -- 237; old249
  ((false, .right, 17), (true, .left, 155)), -- 238; old250
  ((false, .right, 240), (true, .right, 241)), -- 239; old251
  ((false, .right, 80), (true, .right, 132)), -- 240; old252
  ((false, .right, 116), (true, .right, 140)), -- 241; old253
  ((true, .left, 242), (true, .left, 120)) -- 242; old255
]

theorem rawTableCombined243_size : rawTableCombined243.size = 243 := by decide +kernel

theorem rawTableCombined243_transition_count :
    (rawTableCombined243.toList.flatMap (fun r => [r.1, r.2])).length = 486 := by
  decide +kernel

def rawActionCombined243 (q : Fin 243) (b : Bool) : RawActionCombined243 :=
  let row := rawTableCombined243.getD q.val
    ((false, .right, 243), (false, .right, 243))
  if b then row.2 else row.1

def actionCombined243 (q : Fin 243) (b : Bool) : Action 243 :=
  let raw := rawActionCombined243 q b
  { write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 243 then some ⟨raw.2.2, h⟩ else none }

def machineCombined243 : Machine 243 where
  transition := actionCombined243

/-- Original labels; absent labels have only a total fallback value. -/
def oldStateCombined243 : Nat → Fin 243
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
  | 123 => 112
  | 124 => 113
  | 125 => 114
  | 126 => 115
  | 127 => 116
  | 128 => 117
  | 129 => 118
  | 130 => 119
  | 131 => 120
  | 132 => 121
  | 133 => 122
  | 134 => 123
  | 135 => 124
  | 136 => 125
  | 137 => 126
  | 138 => 127
  | 139 => 128
  | 140 => 129
  | 141 => 130
  | 142 => 131
  | 143 => 132
  | 144 => 133
  | 145 => 134
  | 146 => 135
  | 147 => 136
  | 148 => 137
  | 149 => 138
  | 150 => 139
  | 151 => 140
  | 152 => 141
  | 153 => 142
  | 154 => 143
  | 155 => 144
  | 156 => 145
  | 157 => 146
  | 158 => 147
  | 159 => 148
  | 160 => 149
  | 161 => 150
  | 162 => 151
  | 163 => 152
  | 164 => 153
  | 165 => 154
  | 166 => 155
  | 167 => 156
  | 168 => 157
  | 169 => 158
  | 170 => 159
  | 171 => 160
  | 172 => 161
  | 173 => 162
  | 174 => 163
  | 175 => 164
  | 176 => 165
  | 177 => 166
  | 178 => 167
  | 179 => 168
  | 180 => 169
  | 181 => 170
  | 182 => 171
  | 183 => 172
  | 184 => 173
  | 185 => 174
  | 186 => 175
  | 187 => 176
  | 188 => 177
  | 189 => 178
  | 190 => 179
  | 191 => 180
  | 192 => 181
  | 193 => 182
  | 194 => 183
  | 195 => 184
  | 196 => 185
  | 197 => 186
  | 198 => 187
  | 199 => 188
  | 200 => 189
  | 201 => 190
  | 202 => 191
  | 203 => 192
  | 204 => 193
  | 205 => 194
  | 206 => 195
  | 207 => 196
  | 208 => 197
  | 209 => 198
  | 210 => 199
  | 211 => 200
  | 212 => 201
  | 213 => 202
  | 214 => 203
  | 215 => 204
  | 216 => 205
  | 217 => 206
  | 218 => 207
  | 219 => 208
  | 220 => 209
  | 221 => 210
  | 222 => 211
  | 223 => 212
  | 224 => 213
  | 225 => 214
  | 226 => 215
  | 227 => 216
  | 228 => 217
  | 229 => 218
  | 230 => 219
  | 231 => 220
  | 232 => 221
  | 233 => 222
  | 234 => 223
  | 235 => 224
  | 236 => 225
  | 237 => 226
  | 238 => 227
  | 239 => 228
  | 240 => 229
  | 241 => 230
  | 242 => 231
  | 243 => 232
  | 244 => 233
  | 245 => 234
  | 246 => 235
  | 248 => 236
  | 249 => 237
  | 250 => 238
  | 251 => 239
  | 252 => 240
  | 253 => 241
  | 255 => 242
  | _ => 0

/-- The sole deleted old state is canonical112 in Rotation244. -/
def embedState243 (q : Fin 243) : Fin 244 :=
  if h : q.val < 112 then ⟨q.val, by omega⟩ else ⟨q.val + 1, by omega⟩

def embedAction243 (a : Action 243) : Action 244 :=
  ⟨a.write, a.move, a.next.map embedState243⟩

def embedConfig243 (c : Config 243) : Config 244 :=
  ⟨c.state.map embedState243, c.head, c.tape⟩

theorem embedState243_ne_deleted : ∀ q,
    embedState243 q ≠ oldStateRotation244 122 := by decide +kernel

theorem embedState243_zero : embedState243 0 = 0 := by decide +kernel

theorem embedConfig243_initial : embedConfig243 (initial 243) = initial 244 := by
  rfl

/-- Four entry rows use the separately proved positive blocks. -/
def exceptionalRow243 (q : Fin 243) (b : Bool) : Prop :=
  b = true ∧ (q = oldStateCombined243 104 ∨ q = oldStateCombined243 106 ∨
    q = oldStateCombined243 167 ∨ q = oldStateCombined243 81)

instance (q : Fin 243) (b : Bool) : Decidable (exceptionalRow243 q b) :=
  inferInstanceAs (Decidable (b = true ∧ (q = oldStateCombined243 104 ∨
    q = oldStateCombined243 106 ∨ q = oldStateCombined243 167 ∨
    q = oldStateCombined243 81)))

/-- All480 ordinary retained rows agree, including final write/move on halt. -/
theorem combined243_common_action : ∀ (q : Fin 243) (b : Bool),
    q ≠ oldStateCombined243 92 → ¬ exceptionalRow243 q b →
      embedAction243 (machineCombined243.transition q b) =
        machineRotation244.transition (embedState243 q) b := by decide +kernel

theorem combined243_common_next : ∀ (q : Fin 243) (b : Bool),
    q ≠ oldStateCombined243 92 → ¬ exceptionalRow243 q b →
      (machineCombined243.transition q b).next ≠
        some (oldStateCombined243 92) := by decide +kernel

theorem foldRowRotation244_old20_true :
    machineRotation244.transition (oldStateRotation244 20) true =
      ⟨false, .left, some (oldStateRotation244 2)⟩ := by decide +kernel

theorem foldRowRotation244_old24_true :
    machineRotation244.transition (oldStateRotation244 24) true =
      ⟨true, .right, some (oldStateRotation244 37)⟩ := by decide +kernel

theorem foldRowRotation244_old37_true :
    machineRotation244.transition (oldStateRotation244 37) true =
      ⟨true, .right, some (oldStateRotation244 55)⟩ := by decide +kernel

theorem foldRowRotation244_old55_true :
    machineRotation244.transition (oldStateRotation244 55) true =
      ⟨false, .left, some (oldStateRotation244 20)⟩ := by decide +kernel

theorem foldRowRotation244_old66_true :
    machineRotation244.transition (oldStateRotation244 66) true =
      ⟨false, .left, some (oldStateRotation244 20)⟩ := by decide +kernel

theorem foldRowRotation244_old81_true :
    machineRotation244.transition (oldStateRotation244 81) true =
      ⟨true, .left, some (oldStateRotation244 92)⟩ := by decide +kernel

theorem foldRowRotation244_old92_false :
    machineRotation244.transition (oldStateRotation244 92) false =
      ⟨false, .left, some (oldStateRotation244 107)⟩ := by decide +kernel

theorem foldRowRotation244_old92_true :
    machineRotation244.transition (oldStateRotation244 92) true =
      ⟨true, .left, some (oldStateRotation244 24)⟩ := by decide +kernel

theorem foldRowRotation244_old104_true :
    machineRotation244.transition (oldStateRotation244 104) true =
      ⟨true, .right, some (oldStateRotation244 122)⟩ := by decide +kernel

theorem foldRowRotation244_old106_true :
    machineRotation244.transition (oldStateRotation244 106) true =
      ⟨true, .right, some (oldStateRotation244 122)⟩ := by decide +kernel

theorem foldRowRotation244_old107_true :
    machineRotation244.transition (oldStateRotation244 107) true =
      ⟨true, .right, some (oldStateRotation244 125)⟩ := by decide +kernel

theorem foldRowRotation244_old122_false :
    machineRotation244.transition (oldStateRotation244 122) false =
      ⟨false, .right, some (oldStateRotation244 25)⟩ := by decide +kernel

theorem foldRowRotation244_old122_true :
    machineRotation244.transition (oldStateRotation244 122) true =
      ⟨true, .right, some (oldStateRotation244 66)⟩ := by decide +kernel

theorem foldRowRotation244_old125_false :
    machineRotation244.transition (oldStateRotation244 125) false =
      ⟨false, .right, some (oldStateRotation244 25)⟩ := by decide +kernel

theorem foldRowRotation244_old151_true :
    machineRotation244.transition (oldStateRotation244 151) true =
      ⟨true, .left, some (oldStateRotation244 24)⟩ := by decide +kernel

theorem foldRowRotation244_old167_true :
    machineRotation244.transition (oldStateRotation244 167) true =
      ⟨true, .left, some (oldStateRotation244 92)⟩ := by decide +kernel

theorem foldRowCombined243_old20_true :
    machineCombined243.transition (oldStateCombined243 20) true =
      ⟨false, .left, some (oldStateCombined243 2)⟩ := by decide +kernel

theorem foldRowCombined243_old24_true :
    machineCombined243.transition (oldStateCombined243 24) true =
      ⟨true, .right, some (oldStateCombined243 37)⟩ := by decide +kernel

theorem foldRowCombined243_old37_true :
    machineCombined243.transition (oldStateCombined243 37) true =
      ⟨true, .right, some (oldStateCombined243 55)⟩ := by decide +kernel

theorem foldRowCombined243_old55_true :
    machineCombined243.transition (oldStateCombined243 55) true =
      ⟨false, .left, some (oldStateCombined243 20)⟩ := by decide +kernel

theorem foldRowCombined243_old66_true :
    machineCombined243.transition (oldStateCombined243 66) true =
      ⟨false, .left, some (oldStateCombined243 20)⟩ := by decide +kernel

theorem foldRowCombined243_old81_true :
    machineCombined243.transition (oldStateCombined243 81) true =
      ⟨true, .left, some (oldStateCombined243 92)⟩ := by decide +kernel

theorem foldRowCombined243_old92_false :
    machineCombined243.transition (oldStateCombined243 92) false =
      ⟨false, .left, some (oldStateCombined243 107)⟩ := by decide +kernel

theorem foldRowCombined243_old92_true :
    machineCombined243.transition (oldStateCombined243 92) true =
      ⟨true, .right, some (oldStateCombined243 66)⟩ := by decide +kernel

theorem foldRowCombined243_old104_true :
    machineCombined243.transition (oldStateCombined243 104) true =
      ⟨true, .right, some (oldStateCombined243 92)⟩ := by decide +kernel

theorem foldRowCombined243_old106_true :
    machineCombined243.transition (oldStateCombined243 106) true =
      ⟨true, .right, some (oldStateCombined243 92)⟩ := by decide +kernel

theorem foldRowCombined243_old107_true :
    machineCombined243.transition (oldStateCombined243 107) true =
      ⟨true, .right, some (oldStateCombined243 125)⟩ := by decide +kernel

theorem foldRowCombined243_old125_false :
    machineCombined243.transition (oldStateCombined243 125) false =
      ⟨false, .right, some (oldStateCombined243 25)⟩ := by decide +kernel

theorem foldRowCombined243_old151_true :
    machineCombined243.transition (oldStateCombined243 151) true =
      ⟨true, .left, some (oldStateCombined243 24)⟩ := by decide +kernel

theorem foldRowCombined243_old167_true :
    machineCombined243.transition (oldStateCombined243 167) true =
      ⟨true, .left, some (oldStateCombined243 151)⟩ := by decide +kernel

theorem embedState243_old2 :
    embedState243 (oldStateCombined243 2) = oldStateRotation244 2 := by decide +kernel

theorem embedState243_old20 :
    embedState243 (oldStateCombined243 20) = oldStateRotation244 20 := by decide +kernel

theorem embedState243_old24 :
    embedState243 (oldStateCombined243 24) = oldStateRotation244 24 := by decide +kernel

theorem embedState243_old25 :
    embedState243 (oldStateCombined243 25) = oldStateRotation244 25 := by decide +kernel

theorem embedState243_old37 :
    embedState243 (oldStateCombined243 37) = oldStateRotation244 37 := by decide +kernel

theorem embedState243_old55 :
    embedState243 (oldStateCombined243 55) = oldStateRotation244 55 := by decide +kernel

theorem embedState243_old66 :
    embedState243 (oldStateCombined243 66) = oldStateRotation244 66 := by decide +kernel

theorem embedState243_old81 :
    embedState243 (oldStateCombined243 81) = oldStateRotation244 81 := by decide +kernel

theorem embedState243_old92 :
    embedState243 (oldStateCombined243 92) = oldStateRotation244 92 := by decide +kernel

theorem embedState243_old95 :
    embedState243 (oldStateCombined243 95) = oldStateRotation244 95 := by decide +kernel

theorem embedState243_old104 :
    embedState243 (oldStateCombined243 104) = oldStateRotation244 104 := by decide +kernel

theorem embedState243_old106 :
    embedState243 (oldStateCombined243 106) = oldStateRotation244 106 := by decide +kernel

theorem embedState243_old107 :
    embedState243 (oldStateCombined243 107) = oldStateRotation244 107 := by decide +kernel

theorem embedState243_old125 :
    embedState243 (oldStateCombined243 125) = oldStateRotation244 125 := by decide +kernel

theorem embedState243_old151 :
    embedState243 (oldStateCombined243 151) = oldStateRotation244 151 := by decide +kernel

theorem embedState243_old167 :
    embedState243 (oldStateCombined243 167) = oldStateRotation244 167 := by decide +kernel

end SetTheory.BusyBeaver.ZFC
