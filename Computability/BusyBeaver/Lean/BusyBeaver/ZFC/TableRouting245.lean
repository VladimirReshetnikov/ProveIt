import BusyBeaver.Core

/-!
Exact245-state routing/reassociation table in canonical numbering.
Canonical source SHA-256:
17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13.
Old-label source SHA-256:
f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267.
There are490 literal actions. Start old95 is canonical0; dispatcher old96
is canonical88. The numerical halt245 is interpreted as Core none, retaining
its final write and head movement. Old74,177,208 are repurposed grammar labels.

Mira-Cult designed the original machine and compact calculus; Jeff Ketchersid
supplied its verification; Andrew James Wade supplied the compiler framework.
Earlier permutation252 and contextual-fold246 developments retain their
attribution. Submission8286787dd0 contributes joint source-grammar/routing
optimization and scanner shortening. Adapted from checked TablePrefix246.
This source imports exact literal data and finite graph facts only. No runtime,
blank bootstrap, nonhalting, consistency, or source-program equivalence is
established here.
-/

namespace SetTheory.BusyBeaver.ZFC

abbrev RawActionRouting245 := Bool × Move × Nat

/-- Literal read-zero/read-one actions, indexed by canonical working state. -/
def rawTableRouting245 : Array (RawActionRouting245 × RawActionRouting245) := #[
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
  ((false, .right, 123), (true, .right, 12)), -- 68; old74
  ((true, .right, 244), (true, .left, 57)), -- 69; old75
  ((false, .right, 79), (true, .right, 80)), -- 70; old76
  ((false, .right, 81), (true, .right, 245)), -- 71; old77
  ((false, .left, 82), (true, .right, 33)), -- 72; old78
  ((false, .right, 44), (true, .right, 83)), -- 73; old79
  ((false, .right, 21), (true, .right, 84)), -- 74; old80
  ((false, .right, 59), (true, .left, 85)), -- 75; old81
  ((false, .right, 86), (true, .right, 87)), -- 76; old82
  ((true, .right, 0), (true, .right, 67)), -- 77; old83
  ((false, .right, 78), (true, .right, 88)), -- 78; old84
  ((false, .right, 89), (true, .right, 90)), -- 79; old86
  ((false, .right, 205), (true, .right, 239)), -- 80; old87
  ((false, .right, 93), (true, .right, 94)), -- 81; old88
  ((false, .right, 95), (true, .right, 96)), -- 82; old89
  ((false, .right, 86), (true, .right, 65)), -- 83; old90
  ((false, .right, 97), (false, .left, 45)), -- 84; old91
  ((false, .left, 98), (true, .left, 20)), -- 85; old92
  ((false, .right, 52), (false, .right, 36)), -- 86; old93
  ((false, .right, 99), (false, .left, 45)), -- 87; old94
  ((false, .right, 101), (true, .right, 102)), -- 88; old96
  ((false, .right, 19), (true, .right, 68)), -- 89; old98
  ((false, .right, 96), (true, .right, 105)), -- 90; old99
  ((false, .right, 144), (true, .right, 175)), -- 91; old100
  ((false, .right, 185), (true, .right, 198)), -- 92; old101
  ((false, .right, 21), (true, .right, 110)), -- 93; old102
  ((false, .right, 48), (true, .right, 111)), -- 94; old103
  ((false, .right, 112), (true, .right, 113)), -- 95; old104
  ((false, .right, 114), (true, .right, 115)), -- 96; old105
  ((false, .right, 86), (true, .right, 113)), -- 97; old106
  ((false, .right, 112), (true, .right, 116)), -- 98; old107
  ((false, .right, 117), (true, .right, 118)), -- 99; old108
  ((false, .right, 69), (false, .right, 0)), -- 100; old109
  ((false, .right, 29), (true, .right, 119)), -- 101; old110
  ((false, .right, 120), (true, .right, 121)), -- 102; old111
  ((true, .left, 122), (true, .left, 103)), -- 103; old112
  ((false, .right, 19), (true, .right, 123)), -- 104; old113
  ((false, .right, 64), (true, .right, 64)), -- 105; old114
  ((false, .right, 128), (true, .right, 220)), -- 106; old115
  ((false, .right, 174), (true, .right, 125)), -- 107; old116
  ((false, .right, 174), (true, .right, 202)), -- 108; old117
  ((false, .right, 222), (true, .right, 150)), -- 109; old118
  ((false, .right, 132), (true, .right, 133)), -- 110; old119
  ((false, .right, 134), (false, .left, 55)), -- 111; old120
  ((false, .right, 135), (true, .right, 136)), -- 112; old121
  ((false, .right, 21), (true, .right, 60)), -- 113; old122
  ((false, .right, 75), (true, .right, 62)), -- 114; old123
  ((false, .right, 61), (true, .right, 137)), -- 115; old124
  ((false, .right, 21), (true, .right, 138)), -- 116; old125
  ((false, .right, 21), (false, .left, 43)), -- 117; old126
  ((false, .right, 65), (true, .right, 45)), -- 118; old127
  ((false, .right, 139), (true, .right, 8)), -- 119; old128
  ((false, .right, 112), (true, .right, 140)), -- 120; old129
  ((false, .right, 98), (true, .right, 141)), -- 121; old130
  ((false, .left, 43), (false, .left, 103)), -- 122; old131
  ((false, .right, 142), (true, .right, 116)), -- 123; old132
  ((false, .right, 72), (true, .right, 143)), -- 124; old133
  ((false, .right, 204), (true, .right, 238)), -- 125; old134
  ((false, .right, 231), (true, .right, 206)), -- 126; old135
  ((false, .right, 178), (true, .right, 206)), -- 127; old136
  ((false, .right, 150), (true, .right, 151)), -- 128; old137
  ((false, .right, 173), (true, .right, 108)), -- 129; old138
  ((false, .right, 79), (true, .right, 226)), -- 130; old139
  ((false, .right, 130), (true, .right, 213)), -- 131; old140
  ((false, .right, 48), (false, .left, 10)), -- 132; old141
  ((false, .right, 33), (true, .right, 66)), -- 133; old142
  ((false, .left, 157), (false, .left, 1)), -- 134; old143
  ((false, .right, 42), (true, .right, 76)), -- 135; old144
  ((false, .right, 65), (true, .right, 158)), -- 136; old145
  ((false, .right, 65), (true, .right, 159)), -- 137; old146
  ((false, .right, 160), (false, .left, 16)), -- 138; old147
  ((false, .right, 14), (true, .right, 158)), -- 139; old148
  ((false, .right, 21), (true, .right, 161)), -- 140; old149
  ((false, .right, 162), (true, .right, 163)), -- 141; old150
  ((false, .right, 164), (true, .left, 20)), -- 142; old151
  ((false, .right, 165), (true, .right, 166)), -- 143; old152
  ((false, .right, 167), (true, .left, 148)), -- 144; old153
  ((false, .right, 79), (true, .right, 233)), -- 145; old154
  ((false, .right, 145), (true, .right, 208)), -- 146; old155
  ((false, .right, 224), (true, .right, 227)), -- 147; old156
  ((false, .right, 166), (true, .right, 198)), -- 148; old157
  ((false, .right, 212), (true, .right, 181)), -- 149; old158
  ((false, .left, 148), (true, .right, 178)), -- 150; old159
  ((false, .right, 179), (true, .right, 180)), -- 151; old160
  ((false, .right, 170), (true, .right, 182)), -- 152; old161
  ((false, .right, 237), (true, .right, 107)), -- 153; old162
  ((false, .right, 216), (true, .right, 184)), -- 154; old163
  ((false, .right, 225), (true, .right, 109)), -- 155; old164
  ((false, .right, 12), (true, .right, 126)), -- 156; old165
  ((false, .right, 32), (true, .right, 73)), -- 157; old166
  ((false, .right, 42), (true, .left, 85)), -- 158; old167
  ((false, .right, 191), (false, .left, 16)), -- 159; old168
  ((false, .right, 52), (false, .right, 51)), -- 160; old169
  ((false, .right, 192), (false, .left, 16)), -- 161; old170
  ((false, .right, 17), (true, .right, 193)), -- 162; old171
  ((false, .right, 194), (true, .right, 195)), -- 163; old172
  ((false, .right, 26), (false, .right, 51)), -- 164; old173
  ((false, .right, 196), (true, .right, 82)), -- 165; old174
  ((false, .right, 104), (true, .right, 96)), -- 166; old175
  ((false, .right, 104), (true, .right, 197)), -- 167; old176
  ((false, .right, 156), (true, .right, 176)), -- 168; old177
  ((false, .right, 12), (true, .right, 197)), -- 169; old178
  ((false, .right, 96), (true, .right, 96)), -- 170; old179
  ((false, .right, 96), (true, .right, 200)), -- 171; old180
  ((false, .right, 169), (true, .right, 232)), -- 172; old181
  ((false, .right, 178), (true, .right, 203)), -- 173; old182
  ((false, .right, 90), (true, .left, 204)), -- 174; old183
  ((false, .right, 172), (true, .right, 153)), -- 175; old184
  ((false, .right, 183), (true, .right, 203)), -- 176; old185
  ((false, .right, 223), (true, .right, 198)), -- 177; old186
  ((false, .right, 89), (true, .right, 209)), -- 178; old187
  ((false, .right, 210), (true, .right, 211)), -- 179; old188
  ((false, .right, 149), (true, .right, 235)), -- 180; old189
  ((false, .right, 96), (true, .right, 90)), -- 181; old190
  ((false, .right, 177), (true, .right, 197)), -- 182; old191
  ((false, .right, 212), (true, .right, 211)), -- 183; old192
  ((false, .right, 181), (true, .right, 204)), -- 184; old193
  ((false, .right, 150), (true, .right, 215)), -- 185; old194
  ((false, .right, 105), (true, .right, 147)), -- 186; old195
  ((false, .right, 186), (true, .right, 131)), -- 187; old196
  ((false, .right, 187), (true, .right, 106)), -- 188; old197
  ((false, .right, 197), (true, .right, 127)), -- 189; old198
  ((false, .right, 188), (true, .right, 218)), -- 190; old199
  ((false, .right, 105), (true, .right, 105)), -- 191; old200
  ((false, .right, 52), (false, .right, 34)), -- 192; old201
  ((false, .right, 7), (false, .left, 29)), -- 193; old202
  ((false, .right, 166), (true, .right, 30)), -- 194; old203
  ((false, .right, 81), (true, .right, 104)), -- 195; old204
  ((false, .right, 197), (true, .right, 19)), -- 196; old205
  ((false, .right, 19), (true, .right, 221)), -- 197; old206
  ((false, .right, 204), (true, .right, 222)), -- 198; old207
  ((false, .right, 190), (true, .right, 181)), -- 199; old208
  ((false, .right, 212), (true, .right, 223)), -- 200; old209
  ((false, .right, 105), (true, .right, 168)), -- 201; old210
  ((false, .right, 201), (true, .right, 181)), -- 202; old211
  ((false, .right, 227), (true, .right, 169)), -- 203; old212
  ((false, .right, 228), (true, .right, 229)), -- 204; old213
  ((false, .right, 124), (true, .right, 91)), -- 205; old214
  ((false, .right, 174), (true, .right, 224)), -- 206; old215
  ((false, .right, 171), (true, .right, 129)), -- 207; old216
  ((false, .right, 224), (true, .right, 226)), -- 208; old217
  ((false, .left, 79), (true, .right, 64)), -- 209; old218
  ((false, .right, 197), (true, .right, 169)), -- 210; old219
  ((false, .right, 234), (true, .right, 209)), -- 211; old220
  ((false, .right, 197), (true, .right, 234)), -- 212; old221
  ((false, .right, 207), (true, .right, 146)), -- 213; old222
  ((false, .right, 171), (true, .right, 199)), -- 214; old223
  ((false, .right, 235), (true, .right, 235)), -- 215; old224
  ((false, .right, 236), (true, .right, 144)), -- 216; old225
  ((false, .right, 214), (true, .right, 155)), -- 217; old226
  ((false, .right, 184), (true, .right, 219)), -- 218; old227
  ((false, .right, 152), (true, .right, 92)), -- 219; old228
  ((false, .right, 152), (true, .right, 183)), -- 220; old229
  ((false, .right, 240), (true, .right, 140)), -- 221; old230
  ((false, .right, 228), (true, .right, 174)), -- 222; old231
  ((false, .right, 105), (true, .right, 211)), -- 223; old232
  ((false, .right, 79), (true, .right, 64)), -- 224; old233
  ((false, .right, 181), (true, .right, 154)), -- 225; old234
  ((false, .right, 222), (true, .right, 12)), -- 226; old235
  ((false, .right, 170), (true, .right, 104)), -- 227; old236
  ((false, .right, 209), (true, .right, 96)), -- 228; old237
  ((false, .right, 96), (true, .right, 228)), -- 229; old238
  ((false, .right, 170), (true, .right, 217)), -- 230; old239
  ((false, .right, 167), (true, .right, 90)), -- 231; old240
  ((false, .right, 230), (true, .right, 189)), -- 232; old241
  ((false, .right, 231), (true, .right, 227)), -- 233; old242
  ((false, .left, 143), (true, .left, 236)), -- 234; old243
  ((false, .right, 169), (true, .left, 179)), -- 235; old244
  ((false, .right, 12), (true, .right, 235)), -- 236; old245
  ((false, .right, 197), (true, .right, 224)), -- 237; old246
  ((false, .right, 204), (true, .right, 240)), -- 238; old248
  ((false, .right, 241), (true, .right, 242)), -- 239; old249
  ((false, .right, 17), (true, .left, 157)), -- 240; old250
  ((false, .right, 242), (true, .right, 243)), -- 241; old251
  ((false, .right, 81), (true, .right, 134)), -- 242; old252
  ((false, .right, 118), (true, .right, 142)), -- 243; old253
  ((true, .left, 244), (true, .left, 122)) -- 244; old255
]

theorem rawTableRouting245_size : rawTableRouting245.size = 245 := by decide +kernel

theorem rawTableRouting245_transition_count :
    (rawTableRouting245.toList.flatMap (fun row => [row.1, row.2])).length = 490 := by decide +kernel

theorem rawTableRouting245_targets_bounded :
    rawTableRouting245.toList.all (fun row =>
      decide (row.1.2.2 ≤ 245 ∧ row.2.2.2 ≤ 245)) = true := by decide +kernel

theorem rawTableRouting245_halt_edge_count :
    ((rawTableRouting245.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 245)).length = 1 := by decide +kernel

/-- The fallback cannot be reached by Fin 245 indices, by the size theorem. -/
def rawActionRouting245 (state : Fin 245) (bit : Bool) : RawActionRouting245 :=
  let row := rawTableRouting245.getD state.val
    ((false, .right, 245), (false, .right, 245))
  if bit then row.2 else row.1

def actionRouting245 (state : Fin 245) (bit : Bool) : Action 245 :=
  let raw := rawActionRouting245 state bit
  { write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 245 then some ⟨raw.2.2, h⟩ else none }

def machineRouting245 : Machine 245 where
  transition := actionRouting245

def typedMachineRouting245 : TypedMachine (Fin 245) where
  transition state bit :=
    let a := actionRouting245 state bit
    { write := a.write, move := a.move, next := a.next }

theorem rawActionRouting245_target_bounded : ∀ (q : Fin 245) (b : Bool),
    (rawActionRouting245 q b).2.2 ≤ 245 := by decide +kernel

/-- All 245 old working labels, in canonical order. -/
def oldLabelsRouting245 : Array Nat := #[
  95, 2, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
  24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44,
  45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65,
  66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 86,
  87, 88, 89, 90, 91, 92, 93, 94, 96, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,
  109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128,
  129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148,
  149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168,
  169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188,
  189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208,
  209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228,
  229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 248, 249,
  250, 251, 252, 253, 255
]

theorem oldLabelsRouting245_size : oldLabelsRouting245.size = 245 := by decide +kernel

/-- The original label of a canonical working state. -/
def oldLabelRouting245 (q : Fin 245) : Nat := oldLabelsRouting245.getD q.val 95

/-- Exact inverse on old working labels. Absent and terminal labels map to 0;
    this total fallback has no claim to represent an absent operational state. -/
def oldStateRouting245 : Nat → Fin 245
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
  | 122 => 113
  | 123 => 114
  | 124 => 115
  | 125 => 116
  | 126 => 117
  | 127 => 118
  | 128 => 119
  | 129 => 120
  | 130 => 121
  | 131 => 122
  | 132 => 123
  | 133 => 124
  | 134 => 125
  | 135 => 126
  | 136 => 127
  | 137 => 128
  | 138 => 129
  | 139 => 130
  | 140 => 131
  | 141 => 132
  | 142 => 133
  | 143 => 134
  | 144 => 135
  | 145 => 136
  | 146 => 137
  | 147 => 138
  | 148 => 139
  | 149 => 140
  | 150 => 141
  | 151 => 142
  | 152 => 143
  | 153 => 144
  | 154 => 145
  | 155 => 146
  | 156 => 147
  | 157 => 148
  | 158 => 149
  | 159 => 150
  | 160 => 151
  | 161 => 152
  | 162 => 153
  | 163 => 154
  | 164 => 155
  | 165 => 156
  | 166 => 157
  | 167 => 158
  | 168 => 159
  | 169 => 160
  | 170 => 161
  | 171 => 162
  | 172 => 163
  | 173 => 164
  | 174 => 165
  | 175 => 166
  | 176 => 167
  | 177 => 168
  | 178 => 169
  | 179 => 170
  | 180 => 171
  | 181 => 172
  | 182 => 173
  | 183 => 174
  | 184 => 175
  | 185 => 176
  | 186 => 177
  | 187 => 178
  | 188 => 179
  | 189 => 180
  | 190 => 181
  | 191 => 182
  | 192 => 183
  | 193 => 184
  | 194 => 185
  | 195 => 186
  | 196 => 187
  | 197 => 188
  | 198 => 189
  | 199 => 190
  | 200 => 191
  | 201 => 192
  | 202 => 193
  | 203 => 194
  | 204 => 195
  | 205 => 196
  | 206 => 197
  | 207 => 198
  | 208 => 199
  | 209 => 200
  | 210 => 201
  | 211 => 202
  | 212 => 203
  | 213 => 204
  | 214 => 205
  | 215 => 206
  | 216 => 207
  | 217 => 208
  | 218 => 209
  | 219 => 210
  | 220 => 211
  | 221 => 212
  | 222 => 213
  | 223 => 214
  | 224 => 215
  | 225 => 216
  | 226 => 217
  | 227 => 218
  | 228 => 219
  | 229 => 220
  | 230 => 221
  | 231 => 222
  | 232 => 223
  | 233 => 224
  | 234 => 225
  | 235 => 226
  | 236 => 227
  | 237 => 228
  | 238 => 229
  | 239 => 230
  | 240 => 231
  | 241 => 232
  | 242 => 233
  | 243 => 234
  | 244 => 235
  | 245 => 236
  | 246 => 237
  | 248 => 238
  | 249 => 239
  | 250 => 240
  | 251 => 241
  | 252 => 242
  | 253 => 243
  | 255 => 244
  | _ => 0

theorem oldStateRouting245_oldLabel : ∀ q : Fin 245,
    oldStateRouting245 (oldLabelRouting245 q) = q := by decide +kernel

theorem oldLabelRouting245_injective {q r : Fin 245}
    (h : oldLabelRouting245 q = oldLabelRouting245 r) : q = r := by
  calc
    q = oldStateRouting245 (oldLabelRouting245 q) := (oldStateRouting245_oldLabel q).symm
    _ = oldStateRouting245 (oldLabelRouting245 r) := congrArg oldStateRouting245 h
    _ = r := oldStateRouting245_oldLabel r

def startRouting245 : Fin 245 := 0
def dispatchRouting245 : Fin 245 := oldStateRouting245 96

theorem startRouting245_old95 : startRouting245 = oldStateRouting245 95 := by decide +kernel
theorem dispatchRouting245_eq : dispatchRouting245 = 88 := by decide +kernel

theorem machineRouting245_initial_action :
    machineRouting245.transition startRouting245 false =
      ⟨true, .right, some (oldStateRouting245 109)⟩ := by decide +kernel

/-- The single terminal action is old77/read-one, with its final write/move. -/
theorem machineRouting245_halt_action :
    machineRouting245.transition (oldStateRouting245 77) true =
      ⟨true, .right, none⟩ := by decide +kernel

theorem machineRouting245_halt_iff : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = none ↔
      q = oldStateRouting245 77 ∧ b = true := by decide +kernel

/-- The initial read-zero successor has exactly one incoming action. -/
theorem machineRouting245_into_old109_iff : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 109) ↔
      q = oldStateRouting245 95 ∧ b = false := by decide +kernel

/-- The folded pulse state is entered from old75 or its own read-zero loop. -/
theorem machineRouting245_into_old255_iff : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 255) ↔
      (q = oldStateRouting245 75 ∨ q = oldStateRouting245 255) ∧ b = false := by decide +kernel

theorem oldStateRouting245_95 : oldStateRouting245 95 = 0 := by decide +kernel
theorem oldStateRouting245_83_ne_95 : oldStateRouting245 83 ≠ oldStateRouting245 95 := by decide +kernel
theorem oldStateRouting245_83_ne_255 : oldStateRouting245 83 ≠ oldStateRouting245 255 := by decide +kernel

theorem rowRouting245_old75_false :
    machineRouting245.transition (oldStateRouting245 75) false =
      ⟨true, .right, some (oldStateRouting245 255)⟩ := by decide +kernel

theorem rowRouting245_old75_true :
    machineRouting245.transition (oldStateRouting245 75) true =
      ⟨true, .left, some (oldStateRouting245 63)⟩ := by decide +kernel

theorem rowRouting245_old255_false :
    machineRouting245.transition (oldStateRouting245 255) false =
      ⟨true, .left, some (oldStateRouting245 255)⟩ := by decide +kernel

theorem rowRouting245_old255_true :
    machineRouting245.transition (oldStateRouting245 255) true =
      ⟨true, .left, some (oldStateRouting245 131)⟩ := by decide +kernel

theorem rowRouting245_old60_false :
    machineRouting245.transition (oldStateRouting245 60) false =
      ⟨false, .right, some (oldStateRouting245 20)⟩ := by decide +kernel

theorem rowRouting245_old60_true :
    machineRouting245.transition (oldStateRouting245 60) true =
      ⟨true, .right, some (oldStateRouting245 60)⟩ := by decide +kernel

theorem rowRouting245_old112_false :
    machineRouting245.transition (oldStateRouting245 112) false =
      ⟨true, .left, some (oldStateRouting245 131)⟩ := by decide +kernel

theorem rowRouting245_old131_true :
    machineRouting245.transition (oldStateRouting245 131) true =
      ⟨false, .left, some (oldStateRouting245 112)⟩ := by decide +kernel

theorem rowRouting245_old73_false :
    machineRouting245.transition (oldStateRouting245 73) false =
      ⟨false, .right, some (oldStateRouting245 83)⟩ := by decide +kernel

theorem rowRouting245_old73_true :
    machineRouting245.transition (oldStateRouting245 73) true =
      ⟨true, .right, some (oldStateRouting245 73)⟩ := by decide +kernel

theorem rowRouting245_old83_false :
    machineRouting245.transition (oldStateRouting245 83) false =
      ⟨true, .right, some (oldStateRouting245 95)⟩ := by decide +kernel

theorem rowRouting245_old83_true :
    machineRouting245.transition (oldStateRouting245 83) true =
      ⟨true, .right, some (oldStateRouting245 73)⟩ := by decide +kernel

theorem rowRouting245_old95_false :
    machineRouting245.transition (oldStateRouting245 95) false =
      ⟨true, .right, some (oldStateRouting245 109)⟩ := by decide +kernel

theorem rowRouting245_old95_true :
    machineRouting245.transition (oldStateRouting245 95) true =
      ⟨true, .right, some (oldStateRouting245 95)⟩ := by decide +kernel

theorem rowRouting245_old109_false :
    machineRouting245.transition (oldStateRouting245 109) false =
      ⟨false, .right, some (oldStateRouting245 75)⟩ := by decide +kernel

theorem rowRouting245_old109_true :
    machineRouting245.transition (oldStateRouting245 109) true =
      ⟨false, .right, some (oldStateRouting245 95)⟩ := by decide +kernel

theorem rowRouting245_old112_true :
    machineRouting245.transition (oldStateRouting245 112) true =
      ⟨true, .left, some (oldStateRouting245 112)⟩ := by decide +kernel

theorem rowRouting245_old131_false :
    machineRouting245.transition (oldStateRouting245 131) false =
      ⟨false, .left, some (oldStateRouting245 48)⟩ := by decide +kernel

theorem rowRouting245_old48_false :
    machineRouting245.transition (oldStateRouting245 48) false =
      ⟨false, .left, some (oldStateRouting245 7)⟩ := by decide +kernel

theorem rowRouting245_old48_true :
    machineRouting245.transition (oldStateRouting245 48) true =
      ⟨true, .left, some (oldStateRouting245 63)⟩ := by decide +kernel

theorem rowRouting245_old63_false :
    machineRouting245.transition (oldStateRouting245 63) false =
      ⟨false, .left, some (oldStateRouting245 48)⟩ := by decide +kernel

theorem rowRouting245_old63_true :
    machineRouting245.transition (oldStateRouting245 63) true =
      ⟨true, .left, some (oldStateRouting245 63)⟩ := by decide +kernel

theorem rowRouting245_old20_false :
    machineRouting245.transition (oldStateRouting245 20) false =
      ⟨true, .left, some (oldStateRouting245 2)⟩ := by decide +kernel

theorem rowRouting245_old20_true :
    machineRouting245.transition (oldStateRouting245 20) true =
      ⟨false, .left, some (oldStateRouting245 2)⟩ := by decide +kernel

theorem rowRouting245_old2_false :
    machineRouting245.transition (oldStateRouting245 2) false =
      ⟨false, .left, some (oldStateRouting245 2)⟩ := by decide +kernel

theorem rowRouting245_old2_true :
    machineRouting245.transition (oldStateRouting245 2) true =
      ⟨true, .left, some (oldStateRouting245 4)⟩ := by decide +kernel

theorem rowRouting245_old4_false :
    machineRouting245.transition (oldStateRouting245 4) false =
      ⟨false, .left, some (oldStateRouting245 6)⟩ := by decide +kernel

theorem rowRouting245_old4_true :
    machineRouting245.transition (oldStateRouting245 4) true =
      ⟨true, .left, some (oldStateRouting245 4)⟩ := by decide +kernel

theorem rowRouting245_old6_true :
    machineRouting245.transition (oldStateRouting245 6) true =
      ⟨true, .left, some (oldStateRouting245 4)⟩ := by decide +kernel

theorem rowRouting245_old44_false :
    machineRouting245.transition (oldStateRouting245 44) false =
      ⟨false, .right, some (oldStateRouting245 60)⟩ := by decide +kernel

theorem rowRouting245_old44_true :
    machineRouting245.transition (oldStateRouting245 44) true =
      ⟨true, .right, some (oldStateRouting245 44)⟩ := by decide +kernel

theorem rowRouting245_old31_false :
    machineRouting245.transition (oldStateRouting245 31) false =
      ⟨false, .right, some (oldStateRouting245 44)⟩ := by decide +kernel

theorem rowRouting245_old31_true :
    machineRouting245.transition (oldStateRouting245 31) true =
      ⟨true, .right, some (oldStateRouting245 31)⟩ := by decide +kernel

theorem rowRouting245_old56_false :
    machineRouting245.transition (oldStateRouting245 56) false =
      ⟨false, .right, some (oldStateRouting245 31)⟩ := by decide +kernel

theorem rowRouting245_old56_true :
    machineRouting245.transition (oldStateRouting245 56) true =
      ⟨true, .right, some (oldStateRouting245 56)⟩ := by decide +kernel

theorem rowRouting245_old38_false :
    machineRouting245.transition (oldStateRouting245 38) false =
      ⟨false, .right, some (oldStateRouting245 56)⟩ := by decide +kernel

theorem rowRouting245_old38_true :
    machineRouting245.transition (oldStateRouting245 38) true =
      ⟨true, .right, some (oldStateRouting245 38)⟩ := by decide +kernel

theorem rowRouting245_old40_false :
    machineRouting245.transition (oldStateRouting245 40) false =
      ⟨false, .right, some (oldStateRouting245 38)⟩ := by decide +kernel

theorem rowRouting245_old40_true :
    machineRouting245.transition (oldStateRouting245 40) true =
      ⟨true, .right, some (oldStateRouting245 40)⟩ := by decide +kernel

theorem rowRouting245_old28_false :
    machineRouting245.transition (oldStateRouting245 28) false =
      ⟨false, .right, some (oldStateRouting245 40)⟩ := by decide +kernel

theorem rowRouting245_old28_true :
    machineRouting245.transition (oldStateRouting245 28) true =
      ⟨true, .right, some (oldStateRouting245 28)⟩ := by decide +kernel

theorem rowRouting245_old64_false :
    machineRouting245.transition (oldStateRouting245 64) false =
      ⟨false, .right, some (oldStateRouting245 28)⟩ := by decide +kernel

theorem rowRouting245_old64_true :
    machineRouting245.transition (oldStateRouting245 64) true =
      ⟨true, .right, some (oldStateRouting245 64)⟩ := by decide +kernel

theorem rowRouting245_old69_false :
    machineRouting245.transition (oldStateRouting245 69) false =
      ⟨false, .right, some (oldStateRouting245 64)⟩ := by decide +kernel

theorem rowRouting245_old69_true :
    machineRouting245.transition (oldStateRouting245 69) true =
      ⟨true, .right, some (oldStateRouting245 69)⟩ := by decide +kernel

theorem rowRouting245_old6_false :
    machineRouting245.transition (oldStateRouting245 6) false =
      ⟨false, .left, some (oldStateRouting245 9)⟩ := by decide +kernel

end SetTheory.BusyBeaver.ZFC
