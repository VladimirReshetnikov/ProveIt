import BusyBeaver.Core

/-!
Experimental literal 252-state research candidate in the Lean machine model.

Generated from Computability/BusyBeaver/Research/ZFC/raw-candidate-252.tm.
Source SHA-256:
58f8aab7fcc21a7e3a88e6250bf05b7a97eaafd340f75ea8117b6d8f989f3142.

The named source is AX-raw_equality_free_C_G_shared_dual_base3.tm,
SHA-256 06feea82f1ea6cbd7a93458d00e76c4afb14ab18e1cade3bb4afe1740dc48cab.
It is an edited public Wade-backend research candidate, not the Mira-Cult
254-state benchmark. See raw_candidate_252.md and raw-candidate-252-audit.json
under Computability/BusyBeaver/Research/ZFC for provenance and limitations.

The sole missing named row, 1.inc/read1, was filled with write1, right, halt
before canonical numbering. It is row 13/read1 here. Under undefined-row
halting this preserves halting and the final tape, adding one final head move.
Working states are Fin 252; numerical terminal 252 maps to `none`, retaining
the final write and move of BusyBeaver.Core. There are two terminal edges.

Only finite table facts are represented below. No whole-compiler simulation,
proof-search correctness, consistency calibration, or ZFC endpoint is proved.
In particular, the numerical size is not a verified improvement on the
254-state ZFC-consistency machine.
-/

namespace SetTheory.BusyBeaver.ZFC

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Write bit, head move, numerical successor (252 is terminal). -/
abbrev RawAction252 := Bool × Move × Nat

/-- Read-zero/read-one actions in numerical working-state order. -/
def rawTable252 : Array (RawAction252 × RawAction252) := #[
  ((true, .right, 1), (false, .left, 2)), -- 0
  ((false, .right, 2), (false, .right, 1)), -- 1
  ((true, .left, 3), (false, .right, 4)), -- 2
  ((false, .left, 4), (false, .left, 61)), -- 3
  ((true, .left, 0), (false, .left, 1)), -- 4
  ((true, .right, 6), (true, .left, 10)), -- 5
  ((false, .right, 6), (false, .right, 7)), -- 6
  ((true, .right, 8), (true, .right, 7)), -- 7
  ((false, .right, 9), (false, .right, 7)), -- 8
  ((false, .left, 5), (true, .right, 9)), -- 9
  ((false, .left, 26), (true, .right, 11)), -- 10
  ((true, .right, 12), (false, .right, 11)), -- 11
  ((false, .left, 17), (true, .right, 9)), -- 12
  ((true, .right, 14), (true, .right, 252)), -- 13
  ((false, .right, 14), (true, .right, 15)), -- 14
  ((false, .right, 16), (true, .right, 15)), -- 15
  ((true, .left, 23), (true, .right, 15)), -- 16
  ((true, .right, 18), (false, .left, 23)), -- 17
  ((false, .right, 18), (true, .right, 19)), -- 18
  ((false, .right, 20), (true, .right, 19)), -- 19
  ((false, .left, 21), (true, .right, 19)), -- 20
  ((true, .left, 22), (false, .left, 23)), -- 21
  ((false, .right, 21), (true, .left, 22)), -- 22
  ((false, .left, 24), (true, .left, 23)), -- 23
  ((false, .left, 25), (true, .left, 23)), -- 24
  ((false, .left, 25), (false, .left, 55)), -- 25
  ((false, .left, 27), (true, .left, 26)), -- 26
  ((false, .left, 28), (true, .left, 26)), -- 27
  ((false, .left, 28), (false, .left, 56)), -- 28
  ((false, .right, 17), (true, .right, 45)), -- 29
  ((false, .right, 17), (true, .right, 46)), -- 30
  ((false, .right, 17), (true, .right, 5)), -- 31
  ((false, .right, 17), (true, .right, 13)), -- 32
  ((false, .right, 17), (true, .right, 29)), -- 33
  ((false, .right, 17), (true, .right, 30)), -- 34
  ((false, .right, 17), (true, .right, 33)), -- 35
  ((false, .right, 17), (true, .right, 34)), -- 36
  ((false, .right, 17), (true, .right, 41)), -- 37
  ((false, .right, 17), (true, .right, 42)), -- 38
  ((false, .right, 17), (true, .right, 35)), -- 39
  ((false, .right, 17), (true, .right, 36)), -- 40
  ((false, .right, 17), (true, .right, 39)), -- 41
  ((false, .right, 17), (true, .right, 40)), -- 42
  ((false, .right, 17), (true, .right, 31)), -- 43
  ((false, .right, 17), (true, .right, 32)), -- 44
  ((false, .right, 17), (true, .right, 43)), -- 45
  ((false, .right, 17), (true, .right, 44)), -- 46
  ((false, .left, 48), (true, .left, 57)), -- 47
  ((false, .left, 49), (true, .left, 57)), -- 48
  ((false, .left, 50), (true, .left, 57)), -- 49
  ((false, .left, 51), (true, .left, 57)), -- 50
  ((false, .left, 52), (true, .left, 57)), -- 51
  ((false, .left, 53), (true, .left, 57)), -- 52
  ((false, .right, 54), (true, .left, 57)), -- 53
  ((false, .right, 54), (true, .right, 173)), -- 54
  ((true, .left, 57), (false, .left, 55)), -- 55
  ((false, .left, 55), (false, .left, 56)), -- 56
  ((false, .left, 47), (true, .left, 57)), -- 57
  ((false, .left, 58), (false, .left, 57)), -- 58
  ((false, .left, 59), (false, .left, 58)), -- 59
  ((false, .left, 60), (false, .left, 59)), -- 60
  ((false, .left, 61), (false, .left, 60)), -- 61
  ((false, .right, 131), (true, .right, 63)), -- 62
  ((false, .right, 210), (true, .right, 74)), -- 63
  ((false, .right, 140), (true, .right, 65)), -- 64
  ((false, .right, 127), (true, .right, 66)), -- 65
  ((false, .right, 142), (true, .right, 67)), -- 66
  ((false, .right, 131), (true, .right, 68)), -- 67
  ((false, .right, 132), (true, .right, 69)), -- 68
  ((false, .right, 127), (true, .right, 70)), -- 69
  ((false, .right, 214), (true, .right, 71)), -- 70
  ((false, .right, 214), (true, .right, 72)), -- 71
  ((false, .right, 155), (true, .right, 73)), -- 72
  ((false, .right, 132), (true, .right, 75)), -- 73
  ((false, .right, 202), (true, .right, 85)), -- 74
  ((false, .right, 114), (true, .right, 76)), -- 75
  ((false, .right, 138), (true, .right, 77)), -- 76
  ((false, .right, 216), (true, .right, 78)), -- 77
  ((false, .right, 214), (true, .right, 79)), -- 78
  ((false, .right, 137), (true, .right, 80)), -- 79
  ((false, .right, 130), (true, .right, 81)), -- 80
  ((false, .right, 143), (true, .right, 82)), -- 81
  ((false, .right, 114), (true, .right, 83)), -- 82
  ((false, .right, 129), (true, .right, 84)), -- 83
  ((false, .right, 139), (true, .right, 86)), -- 84
  ((false, .right, 205), (true, .right, 96)), -- 85
  ((false, .right, 148), (true, .right, 87)), -- 86
  ((false, .right, 130), (true, .right, 88)), -- 87
  ((false, .right, 133), (true, .right, 89)), -- 88
  ((false, .right, 134), (true, .right, 90)), -- 89
  ((false, .right, 123), (true, .right, 91)), -- 90
  ((false, .right, 145), (true, .right, 92)), -- 91
  ((false, .right, 141), (true, .right, 93)), -- 92
  ((false, .right, 143), (true, .right, 94)), -- 93
  ((false, .right, 142), (true, .right, 95)), -- 94
  ((false, .right, 212), (true, .right, 97)), -- 95
  ((false, .right, 192), (true, .right, 107)), -- 96
  ((false, .right, 123), (true, .right, 98)), -- 97
  ((false, .right, 129), (true, .right, 99)), -- 98
  ((false, .right, 116), (true, .right, 100)), -- 99
  ((false, .right, 134), (true, .right, 101)), -- 100
  ((false, .right, 144), (true, .right, 102)), -- 101
  ((false, .right, 142), (true, .right, 103)), -- 102
  ((false, .right, 142), (true, .right, 104)), -- 103
  ((false, .right, 155), (true, .right, 105)), -- 104
  ((false, .right, 134), (true, .right, 106)), -- 105
  ((false, .right, 146), (true, .right, 108)), -- 106
  ((false, .right, 241), (true, .right, 110)), -- 107
  ((false, .right, 136), (true, .right, 109)), -- 108
  ((false, .right, 144), (true, .right, 117)), -- 109
  ((false, .right, 153), (true, .right, 111)), -- 110
  ((false, .right, 195), (true, .right, 112)), -- 111
  ((false, .right, 146), (true, .right, 113)), -- 112
  ((false, .right, 115), (true, .right, 64)), -- 113
  ((false, .right, 214), (true, .right, 115)), -- 114
  ((false, .right, 153), (true, .right, 155)), -- 115
  ((false, .right, 155), (true, .right, 139)), -- 116
  ((false, .right, 212), (true, .right, 118)), -- 117
  ((false, .right, 212), (true, .right, 119)), -- 118
  ((false, .right, 225), (true, .right, 120)), -- 119
  ((false, .right, 165), (true, .right, 121)), -- 120
  ((false, .right, 244), (true, .right, 122)), -- 121
  ((false, .right, 230), (true, .right, 165)), -- 122
  ((false, .right, 142), (true, .right, 124)), -- 123
  ((false, .right, 202), (true, .right, 125)), -- 124
  ((false, .right, 143), (true, .right, 126)), -- 125
  ((false, .right, 144), (true, .right, 202)), -- 126
  ((false, .right, 153), (true, .right, 128)), -- 127
  ((false, .right, 137), (true, .right, 202)), -- 128
  ((false, .right, 138), (true, .right, 215)), -- 129
  ((false, .right, 141), (true, .right, 200)), -- 130
  ((false, .right, 147), (true, .right, 214)), -- 131
  ((false, .right, 146), (true, .right, 214)), -- 132
  ((false, .right, 215), (true, .right, 142)), -- 133
  ((false, .right, 155), (true, .right, 135)), -- 134
  ((false, .right, 202), (true, .right, 215)), -- 135
  ((false, .right, 216), (true, .right, 142)), -- 136
  ((false, .right, 153), (true, .right, 147)), -- 137
  ((false, .right, 200), (true, .right, 147)), -- 138
  ((false, .right, 148), (true, .right, 202)), -- 139
  ((false, .right, 202), (true, .right, 153)), -- 140
  ((false, .right, 215), (true, .right, 202)), -- 141
  ((false, .right, 153), (true, .right, 214)), -- 142
  ((false, .right, 155), (true, .right, 215)), -- 143
  ((false, .right, 212), (true, .right, 216)), -- 144
  ((false, .right, 202), (true, .right, 200)), -- 145
  ((false, .right, 200), (true, .right, 202)), -- 146
  ((false, .right, 200), (true, .right, 155)), -- 147
  ((false, .right, 202), (true, .right, 155)), -- 148
  ((false, .right, 37), (true, .right, 189)), -- 149
  ((false, .right, 45), (true, .right, 189)), -- 150
  ((false, .right, 41), (true, .right, 152)), -- 151
  ((false, .right, 191), (false, .left, 58)), -- 152
  ((false, .right, 194), (true, .right, 154)), -- 153
  ((false, .right, 196), (true, .right, 151)), -- 154
  ((false, .right, 205), (true, .right, 156)), -- 155
  ((false, .right, 233), (true, .right, 240)), -- 156
  ((false, .right, 158), (true, .right, 162)), -- 157
  ((false, .right, 39), (true, .right, 159)), -- 158
  ((false, .right, 160), (true, .right, 161)), -- 159
  ((false, .right, 35), (false, .left, 58)), -- 160
  ((false, .right, 240), (true, .right, 36)), -- 161
  ((false, .right, 35), (true, .right, 163)), -- 162
  ((false, .right, 232), (false, .left, 56)), -- 163
  ((false, .right, 157), (true, .right, 200)), -- 164
  ((false, .right, 157), (true, .right, 247)), -- 165
  ((false, .right, 157), (true, .right, 252)), -- 166
  ((false, .right, 168), (true, .right, 169)), -- 167
  ((false, .right, 37), (false, .left, 56)), -- 168
  ((false, .right, 227), (true, .right, 170)), -- 169
  ((false, .right, 236), (true, .right, 32)), -- 170
  ((false, .right, 172), (true, .right, 244)), -- 171
  ((false, .right, 39), (false, .left, 56)), -- 172
  ((false, .right, 167), (true, .right, 174)), -- 173
  ((false, .right, 208), (true, .right, 175)), -- 174
  ((false, .right, 209), (true, .right, 176)), -- 175
  ((false, .right, 177), (true, .right, 185)), -- 176
  ((false, .right, 29), (true, .right, 178)), -- 177
  ((false, .right, 179), (false, .left, 56)), -- 178
  ((false, .right, 180), (true, .right, 155)), -- 179
  ((false, .right, 29), (true, .right, 181)), -- 180
  ((false, .right, 182), (false, .left, 56)), -- 181
  ((false, .right, 183), (true, .right, 187)), -- 182
  ((false, .right, 29), (true, .right, 184)), -- 183
  ((false, .right, 62), (false, .left, 56)), -- 184
  ((false, .right, 195), (true, .right, 186)), -- 185
  ((false, .right, 249), (true, .right, 164)), -- 186
  ((false, .right, 40), (true, .right, 188)), -- 187
  ((false, .right, 166), (true, .right, 204)), -- 188
  ((false, .right, 190), (false, .left, 58)), -- 189
  ((false, .right, 42), (true, .right, 171)), -- 190
  ((false, .right, 193), (true, .right, 44)), -- 191
  ((false, .right, 149), (true, .right, 242)), -- 192
  ((false, .right, 44), (true, .right, 44)), -- 193
  ((false, .right, 150), (true, .right, 245)), -- 194
  ((false, .right, 200), (true, .right, 153)), -- 195
  ((false, .right, 248), (true, .right, 197)), -- 196
  ((false, .right, 39), (true, .right, 198)), -- 197
  ((false, .right, 199), (false, .left, 59)), -- 198
  ((false, .right, 42), (true, .right, 241)), -- 199
  ((false, .right, 205), (true, .right, 201)), -- 200
  ((false, .right, 231), (true, .right, 238)), -- 201
  ((false, .right, 205), (true, .right, 203)), -- 202
  ((false, .right, 226), (true, .right, 234)), -- 203
  ((false, .right, 194), (true, .right, 240)), -- 204
  ((false, .right, 249), (true, .right, 206)), -- 205
  ((false, .right, 250), (true, .right, 207)), -- 206
  ((false, .right, 196), (true, .right, 245)), -- 207
  ((false, .right, 192), (true, .right, 234)), -- 208
  ((false, .right, 192), (true, .right, 238)), -- 209
  ((false, .right, 192), (true, .right, 240)), -- 210
  ((false, .right, 205), (true, .right, 44)), -- 211
  ((false, .right, 251), (true, .right, 213)), -- 212
  ((false, .right, 153), (true, .right, 251)), -- 213
  ((false, .right, 153), (true, .right, 193)), -- 214
  ((false, .right, 153), (true, .right, 44)), -- 215
  ((false, .right, 251), (true, .right, 217)), -- 216
  ((false, .right, 214), (true, .right, 251)), -- 217
  ((false, .right, 40), (false, .left, 58)), -- 218
  ((false, .right, 44), (false, .left, 58)), -- 219
  ((false, .right, 221), (false, .left, 58)), -- 220
  ((false, .right, 40), (true, .right, 42)), -- 221
  ((false, .right, 223), (false, .left, 58)), -- 222
  ((false, .right, 40), (true, .right, 44)), -- 223
  ((false, .right, 36), (false, .left, 58)), -- 224
  ((false, .right, 29), (true, .right, 220)), -- 225
  ((false, .right, 29), (true, .right, 222)), -- 226
  ((false, .right, 31), (true, .right, 228)), -- 227
  ((false, .right, 229), (false, .left, 58)), -- 228
  ((false, .right, 38), (true, .right, 40)), -- 229
  ((false, .right, 33), (true, .right, 224)), -- 230
  ((false, .right, 33), (true, .right, 222)), -- 231
  ((false, .right, 35), (false, .left, 57)), -- 232
  ((false, .right, 35), (true, .right, 222)), -- 233
  ((false, .right, 39), (true, .right, 235)), -- 234
  ((false, .right, 30), (false, .left, 58)), -- 235
  ((false, .right, 39), (true, .right, 237)), -- 236
  ((false, .right, 32), (false, .left, 58)), -- 237
  ((false, .right, 39), (true, .right, 239)), -- 238
  ((false, .right, 34), (false, .left, 58)), -- 239
  ((false, .right, 39), (true, .right, 224)), -- 240
  ((false, .right, 39), (true, .right, 219)), -- 241
  ((false, .right, 41), (true, .right, 243)), -- 242
  ((false, .right, 38), (false, .left, 58)), -- 243
  ((false, .right, 41), (true, .right, 218)), -- 244
  ((false, .right, 41), (true, .right, 246)), -- 245
  ((false, .right, 46), (false, .left, 58)), -- 246
  ((false, .right, 43), (false, .left, 57)), -- 247
  ((false, .right, 43), (true, .right, 220)), -- 248
  ((false, .right, 43), (true, .right, 218)), -- 249
  ((false, .right, 45), (true, .right, 219)), -- 250
  ((false, .right, 211), (true, .right, 153)) -- 251
]

/-- Finite size check by kernel reduction. -/
theorem rawTable252_size : rawTable252.size = 252 := by decide

/-- The literal binary table contains exactly 504 transition actions. -/
theorem rawTable252_transition_count :
    (rawTable252.toList.flatMap (fun row => [row.1, row.2])).length = 504 := by decide

/-- Every successor is a working state or the designated terminal. -/
theorem rawTable252_targets_bounded :
    rawTable252.toList.all (fun row =>
      decide (row.1.2.2 ≤ 252 ∧ row.2.2.2 ≤ 252)) = true := by decide

/-- Exactly two actions enter the source terminal label. -/
theorem rawTable252_halt_edge_count :
    ((rawTable252.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 252)).length = 2 := by decide

/-- The fallback is unreachable at Fin 252 indices, by rawTable252_size. -/
def rawAction252 (state : Fin 252) (bit : Bool) : RawAction252 :=
  let row := rawTable252.getD state.val
    ((false, .right, 252), (false, .right, 252))
  if bit then row.2 else row.1

/-- Interpret the numerical halt label with the separate terminal convention. -/
def action252 (state : Fin 252) (bit : Bool) : Action 252 :=
  let raw := rawAction252 state bit
  { write := raw.1
    move := raw.2.1
    next := if h : raw.2.2 < 252 then some ⟨raw.2.2, h⟩ else none }

/-- The frozen experimental table, without a proof-search calibration. -/
def machine252 : Machine 252 where
  transition := action252

/-- The same literal table at the typed-state interface. -/
def typedMachine252 : TypedMachine (Fin 252) where
  transition state bit :=
    let action := action252 state bit
    { write := action.write, move := action.move, next := action.next }

/-- Sanity check of the initial blank-tape action. -/
theorem machine252_initial_action :
    machine252.transition ⟨0, by decide⟩ false =
      { write := true, move := .right, next := some ⟨1, by decide⟩ } := by decide

/-- The formerly undefined read-one row preserves its read bit and halts. -/
theorem machine252_totalized_action :
    machine252.transition ⟨13, by decide⟩ true =
      { write := true, move := .right, next := none } := by decide

#print axioms rawTable252_size
#print axioms rawTable252_transition_count
#print axioms rawTable252_targets_bounded
#print axioms rawTable252_halt_edge_count
#print axioms machine252_initial_action
#print axioms machine252_totalized_action

end SetTheory.BusyBeaver.ZFC
