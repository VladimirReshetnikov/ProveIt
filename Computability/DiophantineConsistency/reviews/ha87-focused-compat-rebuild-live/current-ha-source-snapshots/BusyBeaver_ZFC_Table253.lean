import BusyBeaver.Core

/-!
Literal attributed 253-state reduction of the Mira-Cult benchmark.

The source is mira-emmy's public busy-beaver PR 20, pinned head
0d544f2a2e3c18f12278441a74b7879f31cbe856, ZF/m253/machine/zfc_253.tm.
Its byte-identical retained copy is
SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/
04-machine-machines-zfc_253.tm. Source SHA-256:
84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95.

Mira-Cult designed the original 254-state machine; Jeff supplied the original
verification. The existing 253-state reduction and its separate PR proof are
attributed to mira-emmy. This imports literal data, not the Coq development.
The finite facts below do not establish the register-machine simulation,
the 330-step register prefix, or an internal ZFC/PA consistency endpoint.
Operational states are Fin 253; source halt label 253 is none, retaining the
last write and head move under BusyBeaver.Core's convention.
-/

namespace SetTheory.BusyBeaver.ZFC

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev RawAction253 := Bool × Move × Nat

def rawTable253 : Array (RawAction253 × RawAction253) := #[
  ((true, .right, 1), (true, .right, 2)), -- 0
  ((false, .left, 3), (true, .right, 4)), -- 1
  ((false, .right, 5), (true, .right, 2)), -- 2
  ((true, .left, 6), (true, .left, 3)), -- 3
  ((false, .right, 1), (true, .right, 4)), -- 4
  ((false, .right, 7), (true, .right, 5)), -- 5
  ((false, .left, 8), (false, .left, 3)), -- 6
  ((false, .right, 9), (true, .right, 7)), -- 7
  ((false, .left, 10), (true, .left, 8)), -- 8
  ((false, .right, 11), (true, .right, 9)), -- 9
  ((false, .left, 12), (true, .left, 8)), -- 10
  ((false, .right, 13), (true, .right, 11)), -- 11
  ((true, .right, 14), (false, .left, 12)), -- 12
  ((false, .right, 15), (true, .right, 13)), -- 13
  ((false, .right, 14), (false, .right, 16)), -- 14
  ((false, .right, 17), (true, .right, 15)), -- 15
  ((false, .left, 18), (false, .right, 16)), -- 16
  ((false, .right, 19), (true, .right, 17)), -- 17
  ((true, .left, 20), (false, .left, 20)), -- 18
  ((true, .left, 21), (false, .left, 20)), -- 19
  ((false, .left, 20), (true, .left, 22)), -- 20
  ((false, .left, 23), (true, .left, 21)), -- 21
  ((false, .left, 24), (true, .left, 22)), -- 22
  ((false, .left, 10), (true, .left, 21)), -- 23
  ((false, .left, 25), (true, .left, 22)), -- 24
  ((false, .left, 26), (true, .left, 22)), -- 25
  ((false, .left, 27), (true, .left, 22)), -- 26
  ((false, .left, 28), (true, .left, 22)), -- 27
  ((false, .left, 29), (true, .left, 22)), -- 28
  ((false, .left, 30), (true, .left, 22)), -- 29
  ((false, .left, 31), (true, .left, 22)), -- 30
  ((false, .left, 32), (true, .left, 22)), -- 31
  ((false, .right, 32), (true, .right, 33)), -- 32
  ((false, .right, 34), (true, .right, 35)), -- 33
  ((false, .right, 36), (true, .right, 37)), -- 34
  ((false, .right, 38), (true, .right, 39)), -- 35
  ((false, .right, 40), (false, .left, 10)), -- 36
  ((false, .right, 41), (true, .right, 42)), -- 37
  ((false, .right, 43), (true, .right, 44)), -- 38
  ((false, .right, 45), (true, .right, 46)), -- 39
  ((false, .left, 47), (false, .right, 7)), -- 40
  ((false, .right, 48), (true, .right, 49)), -- 41
  ((false, .right, 50), (true, .right, 48)), -- 42
  ((false, .right, 51), (true, .right, 52)), -- 43
  ((false, .right, 53), (true, .right, 54)), -- 44
  ((false, .right, 43), (true, .right, 55)), -- 45
  ((false, .right, 56), (true, .right, 57)), -- 46
  ((false, .left, 58), (true, .right, 59)), -- 47
  ((false, .left, 47), (false, .right, 5)), -- 48
  ((false, .right, 40), (true, .left, 60)), -- 49
  ((false, .right, 53), (true, .right, 61)), -- 50
  ((false, .right, 40), (true, .right, 62)), -- 51
  ((false, .right, 63), (true, .right, 49)), -- 52
  ((false, .right, 64), (false, .right, 9)), -- 53
  ((false, .right, 65), (false, .left, 18)), -- 54
  ((false, .right, 53), (true, .right, 66)), -- 55
  ((false, .right, 67), (true, .right, 68)), -- 56
  ((false, .right, 69), (true, .right, 70)), -- 57
  ((false, .right, 71), (true, .right, 72)), -- 58
  ((false, .right, 73), (false, .right, 9)), -- 59
  ((false, .left, 45), (true, .left, 74)), -- 60
  ((false, .right, 48), (false, .left, 18)), -- 61
  ((false, .right, 75), (true, .right, 76)), -- 62
  ((false, .left, 77), (true, .left, 62)), -- 63
  ((false, .left, 78), (false, .right, 79)), -- 64
  ((false, .right, 73), (false, .right, 13)), -- 65
  ((false, .right, 80), (false, .left, 18)), -- 66
  ((false, .right, 64), (false, .right, 13)), -- 67
  ((false, .right, 81), (false, .left, 36)), -- 68
  ((false, .right, 82), (true, .right, 77)), -- 69
  ((false, .right, 83), (true, .right, 84)), -- 70
  ((false, .right, 67), (true, .right, 85)), -- 71
  ((false, .right, 59), (true, .right, 86)), -- 72
  ((false, .left, 78), (false, .right, 87)), -- 73
  ((false, .right, 88), (true, .right, 89)), -- 74
  ((false, .right, 73), (false, .right, 11)), -- 75
  ((false, .right, 90), (false, .left, 91)), -- 76
  ((false, .right, 92), (true, .right, 91)), -- 77
  ((true, .right, 78), (true, .left, 20)), -- 78
  ((false, .right, 93), (true, .right, 79)), -- 79
  ((false, .right, 73), (false, .right, 15)), -- 80
  ((false, .right, 94), (true, .right, 95)), -- 81
  ((false, .right, 84), (true, .right, 96)), -- 82
  ((false, .right, 97), (true, .right, 98)), -- 83
  ((false, .right, 99), (true, .right, 100)), -- 84
  ((false, .right, 101), (false, .left, 36)), -- 85
  ((false, .right, 102), (true, .right, 103)), -- 86
  ((false, .right, 104), (true, .right, 87)), -- 87
  ((false, .right, 105), (true, .right, 106)), -- 88
  ((false, .right, 53), (true, .right, 107)), -- 89
  ((false, .right, 108), (true, .right, 109)), -- 90
  ((false, .right, 59), (false, .left, 18)), -- 91
  ((false, .right, 64), (false, .right, 0)), -- 92
  ((false, .right, 110), (true, .right, 79)), -- 93
  ((false, .right, 67), (true, .right, 111)), -- 94
  ((false, .right, 99), (true, .right, 74)), -- 95
  ((false, .right, 112), (true, .right, 113)), -- 96
  ((false, .right, 53), (true, .right, 114)), -- 97
  ((false, .right, 105), (true, .right, 115)), -- 98
  ((false, .right, 77), (true, .right, 116)), -- 99
  ((false, .right, 117), (true, .right, 55)), -- 100
  ((false, .right, 118), (true, .right, 119)), -- 101
  ((false, .right, 83), (true, .right, 253)), -- 102
  ((false, .left, 120), (true, .right, 89)), -- 103
  ((true, .right, 121), (true, .right, 87)), -- 104
  ((false, .right, 64), (false, .right, 122)), -- 105
  ((false, .right, 123), (true, .right, 63)), -- 106
  ((false, .right, 124), (false, .left, 18)), -- 107
  ((false, .right, 53), (false, .left, 10)), -- 108
  ((false, .right, 63), (true, .right, 91)), -- 109
  ((false, .left, 19), (true, .right, 4)), -- 110
  ((false, .right, 58), (false, .left, 36)), -- 111
  ((false, .right, 125), (true, .right, 126)), -- 112
  ((false, .right, 127), (true, .right, 128)), -- 113
  ((false, .right, 129), (true, .right, 130)), -- 114
  ((false, .right, 131), (false, .left, 85)), -- 115
  ((false, .right, 132), (true, .right, 133)), -- 116
  ((false, .right, 134), (true, .left, 74)), -- 117
  ((false, .right, 135), (true, .right, 136)), -- 118
  ((false, .right, 137), (true, .right, 138)), -- 119
  ((false, .right, 139), (true, .right, 96)), -- 120
  ((true, .right, 140), (true, .right, 121)), -- 121
  ((false, .right, 2), (true, .right, 122)), -- 122
  ((false, .right, 73), (false, .right, 2)), -- 123
  ((false, .right, 73), (false, .right, 122)), -- 124
  ((false, .right, 141), (true, .left, 60)), -- 125
  ((false, .right, 63), (true, .right, 125)), -- 126
  ((false, .right, 142), (true, .right, 143)), -- 127
  ((false, .right, 63), (true, .right, 144)), -- 128
  ((false, .right, 105), (false, .left, 16)), -- 129
  ((false, .right, 89), (true, .right, 124)), -- 130
  ((false, .left, 145), (false, .left, 20)), -- 131
  ((false, .right, 141), (true, .right, 146)), -- 132
  ((false, .right, 127), (true, .right, 126)), -- 133
  ((false, .right, 64), (false, .right, 15)), -- 134
  ((false, .right, 84), (true, .right, 95)), -- 135
  ((false, .right, 96), (true, .right, 147)), -- 136
  ((false, .right, 148), (true, .right, 149)), -- 137
  ((false, .right, 150), (true, .right, 151)), -- 138
  ((false, .right, 43), (true, .right, 152)), -- 139
  ((false, .left, 8), (false, .right, 121)), -- 140
  ((false, .left, 47), (false, .right, 17)), -- 141
  ((false, .right, 92), (true, .right, 153)), -- 142
  ((false, .right, 53), (true, .right, 154)), -- 143
  ((false, .right, 155), (false, .left, 18)), -- 144
  ((false, .right, 88), (true, .right, 142)), -- 145
  ((false, .right, 123), (false, .left, 18)), -- 146
  ((false, .right, 123), (true, .right, 123)), -- 147
  ((false, .right, 156), (true, .right, 157)), -- 148
  ((false, .right, 158), (true, .right, 159)), -- 149
  ((false, .right, 160), (true, .right, 161)), -- 150
  ((false, .right, 162), (true, .right, 163)), -- 151
  ((false, .right, 53), (true, .right, 146)), -- 152
  ((false, .right, 75), (true, .right, 63)), -- 153
  ((false, .right, 164), (false, .left, 91)), -- 154
  ((false, .right, 147), (true, .right, 147)), -- 155
  ((false, .right, 103), (true, .right, 165)), -- 156
  ((false, .right, 166), (true, .right, 167)), -- 157
  ((false, .right, 168), (true, .right, 169)), -- 158
  ((false, .right, 170), (true, .right, 171)), -- 159
  ((false, .right, 172), (true, .right, 173)), -- 160
  ((false, .right, 174), (true, .right, 175)), -- 161
  ((false, .right, 174), (true, .right, 176)), -- 162
  ((false, .right, 177), (true, .right, 178)), -- 163
  ((false, .right, 75), (true, .right, 152)), -- 164
  ((false, .right, 179), (true, .right, 82)), -- 165
  ((false, .right, 180), (true, .left, 181)), -- 166
  ((false, .right, 182), (true, .right, 183)), -- 167
  ((false, .right, 184), (true, .right, 185)), -- 168
  ((false, .right, 184), (true, .right, 186)), -- 169
  ((false, .right, 187), (true, .right, 188)), -- 170
  ((false, .right, 189), (true, .right, 190)), -- 171
  ((false, .left, 181), (true, .right, 191)), -- 172
  ((false, .right, 192), (true, .right, 193)), -- 173
  ((false, .right, 194), (true, .right, 195)), -- 174
  ((false, .right, 196), (true, .right, 197)), -- 175
  ((false, .right, 198), (true, .right, 199)), -- 176
  ((false, .right, 200), (true, .right, 201)), -- 177
  ((false, .right, 202), (true, .right, 203)), -- 178
  ((false, .right, 204), (true, .right, 120)), -- 179
  ((false, .right, 84), (true, .right, 205)), -- 180
  ((false, .right, 82), (true, .right, 206)), -- 181
  ((false, .right, 99), (true, .right, 207)), -- 182
  ((false, .right, 96), (true, .right, 96)), -- 183
  ((false, .right, 96), (true, .right, 208)), -- 184
  ((false, .right, 209), (true, .right, 210)), -- 185
  ((false, .right, 191), (true, .right, 211)), -- 186
  ((false, .right, 136), (true, .left, 212)), -- 187
  ((false, .right, 213), (true, .right, 214)), -- 188
  ((false, .right, 196), (true, .right, 211)), -- 189
  ((false, .right, 215), (true, .right, 216)), -- 190
  ((false, .right, 135), (true, .right, 217)), -- 191
  ((false, .right, 218), (true, .right, 219)), -- 192
  ((false, .right, 220), (true, .right, 221)), -- 193
  ((false, .right, 96), (true, .right, 136)), -- 194
  ((false, .right, 219), (true, .right, 222)), -- 195
  ((false, .right, 220), (true, .right, 219)), -- 196
  ((false, .right, 194), (true, .right, 212)), -- 197
  ((false, .right, 172), (true, .right, 223)), -- 198
  ((false, .right, 206), (true, .right, 194)), -- 199
  ((false, .right, 194), (true, .right, 224)), -- 200
  ((false, .right, 225), (true, .right, 172)), -- 201
  ((false, .right, 226), (true, .right, 214)), -- 202
  ((false, .right, 227), (true, .right, 228)), -- 203
  ((false, .right, 205), (true, .right, 99)), -- 204
  ((false, .right, 99), (true, .right, 229)), -- 205
  ((false, .right, 212), (true, .right, 230)), -- 206
  ((false, .right, 74), (true, .right, 205)), -- 207
  ((false, .right, 220), (true, .right, 231)), -- 208
  ((false, .right, 147), (true, .right, 232)), -- 209
  ((false, .right, 233), (true, .right, 234)), -- 210
  ((false, .right, 235), (true, .right, 182)), -- 211
  ((false, .right, 236), (true, .right, 237)), -- 212
  ((false, .right, 238), (true, .right, 239)), -- 213
  ((false, .right, 187), (true, .right, 232)), -- 214
  ((false, .right, 240), (true, .right, 241)), -- 215
  ((false, .right, 232), (true, .right, 234)), -- 216
  ((false, .left, 167), (true, .right, 123)), -- 217
  ((false, .right, 205), (true, .right, 182)), -- 218
  ((false, .right, 242), (true, .right, 217)), -- 219
  ((false, .right, 205), (true, .right, 242)), -- 220
  ((false, .right, 194), (true, .right, 243)), -- 221
  ((false, .right, 206), (true, .right, 205)), -- 222
  ((false, .right, 243), (true, .right, 243)), -- 223
  ((false, .right, 244), (true, .right, 166)), -- 224
  ((false, .right, 197), (true, .right, 230)), -- 225
  ((false, .right, 205), (true, .right, 191)), -- 226
  ((false, .right, 245), (true, .right, 246)), -- 227
  ((false, .right, 247), (true, .right, 248)), -- 228
  ((false, .right, 249), (true, .right, 44)), -- 229
  ((false, .right, 236), (true, .right, 187)), -- 230
  ((false, .right, 147), (true, .right, 219)), -- 231
  ((false, .right, 118), (true, .right, 123)), -- 232
  ((false, .right, 235), (true, .right, 118)), -- 233
  ((false, .right, 230), (true, .right, 95)), -- 234
  ((false, .right, 183), (true, .right, 84)), -- 235
  ((false, .right, 217), (true, .right, 96)), -- 236
  ((false, .right, 96), (true, .right, 236)), -- 237
  ((false, .right, 147), (true, .right, 95)), -- 238
  ((false, .right, 180), (true, .right, 136)), -- 239
  ((false, .right, 194), (true, .right, 118)), -- 240
  ((false, .right, 239), (true, .right, 235)), -- 241
  ((false, .left, 165), (true, .left, 244)), -- 242
  ((false, .right, 182), (true, .left, 192)), -- 243
  ((false, .right, 95), (true, .right, 243)), -- 244
  ((false, .right, 205), (true, .right, 232)), -- 245
  ((false, .right, 187), (true, .right, 212)), -- 246
  ((false, .right, 212), (true, .right, 249)), -- 247
  ((false, .right, 250), (true, .right, 251)), -- 248
  ((false, .right, 67), (true, .left, 145)), -- 249
  ((false, .right, 251), (true, .right, 252)), -- 250
  ((false, .right, 83), (true, .right, 131)), -- 251
  ((false, .right, 109), (true, .right, 117)) -- 252
]

/-- Finite size check, proved by kernel reduction. -/
theorem rawTable253_size : rawTable253.size = 253 := by decide

/-- Every numerical successor is a working state or the designated terminal. -/
theorem rawTable253_targets_bounded :
    rawTable253.toList.all (fun row =>
      decide (row.1.2.2 ≤ 253 ∧ row.2.2.2 ≤ 253)) = true := by decide

/-- There is exactly one transition into the source terminal label. -/
theorem rawTable253_halt_edge_count :
    ((rawTable253.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 253)).length = 1 := by decide

/-- The fallback is unreachable for Fin 253 indices, by rawTable253_size. -/
def rawAction253 (state : Fin 253) (bit : Bool) : RawAction253 :=
  let row := rawTable253.getD state.val
    ((false, .right, 253), (false, .right, 253))
  if bit then row.2 else row.1

/-- Map the numerical halt label to the existing separate terminal convention. -/
def action253 (state : Fin 253) (bit : Bool) : Action 253 :=
  let raw := rawAction253 state bit
  { write := raw.1
    move := raw.2.1
    next := if h : raw.2.2 < 253 then some ⟨raw.2.2, h⟩ else none }

/-- The literal benchmark uses 253 operational states and two tape symbols. -/
def machine253 : Machine 253 where
  transition := action253

/-- The same table at the typed-state interface used by StateReduction.lean. -/
def typedMachine253 : TypedMachine (Fin 253) where
  transition state bit :=
    let action := action253 state bit
    { write := action.write, move := action.move, next := action.next }

/-- A direct sanity check of the first blank-tape transition. -/
theorem machine253_initial_action :
    machine253.transition ⟨0, by decide⟩ false =
      { write := true, move := .right, next := some ⟨1, by decide⟩ } := by decide

#print axioms rawTable253_size
#print axioms rawTable253_targets_bounded
#print axioms rawTable253_halt_edge_count
#print axioms machine253_initial_action


namespace Boot253

/-- A first bounded actual-machine checkpoint; no prepared tape is supplied. -/
def shortCheckpoint : Config 253 :=
  { state := some ⟨32, by decide⟩, head := -12,
    tape := [9, 8, 7, 6, 10, 2, 15, 14, 1, -3, 18, 12, -4, -5] }

/-- Kernel computation checks all 1024 actual transitions from the blank tape. -/
theorem first1024 : machine253.run 1024 = shortCheckpoint := by decide

#print axioms first1024


end Boot253

end SetTheory.BusyBeaver.ZFC
