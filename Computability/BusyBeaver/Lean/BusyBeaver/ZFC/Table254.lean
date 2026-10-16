import BusyBeaver.Core

/-!
Literal Mira-Cult 254-state benchmark in the repository's Lean machine model.

Generated from lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm,
upstream jeff87654/busy-beaver commit
297ab8df7e5de329605c3875b4934643b371a5e3.
Source SHA-256:
d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb.

Mira-Cult designed the machine; Jeff supplied the separate upstream Coq
verification. This generated Lean representation imports only BusyBeaver.Core
and proves finite table facts. It does not import the Coq development or prove
any ZFC consistency endpoint, whole-machine simulation, or new state bound.
Operational states are Fin 254. Source terminal label 254 becomes `none`;
the final write/move still occur, exactly as in BusyBeaver.Core.
-/

namespace SetTheory.BusyBeaver.ZFC

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Write bit, head move, numerical successor (254 is terminal). -/
abbrev RawAction254 := Bool × Move × Nat

/-- Each pair stores the read-zero and read-one actions, in numerical state order. -/
def rawTable254 : Array (RawAction254 × RawAction254) := #[
  ((true, .left, 1), (false, .left, 2)), -- 0
  ((false, .left, 3), (true, .left, 1)), -- 1
  ((false, .left, 2), (true, .left, 4)), -- 2
  ((false, .left, 5), (true, .left, 1)), -- 3
  ((false, .left, 6), (true, .left, 4)), -- 4
  ((false, .left, 7), (true, .left, 8)), -- 5
  ((false, .left, 9), (true, .left, 4)), -- 6
  ((true, .right, 10), (false, .left, 7)), -- 7
  ((true, .left, 11), (true, .right, 12)), -- 8
  ((false, .left, 13), (true, .left, 4)), -- 9
  ((false, .right, 10), (false, .right, 14)), -- 10
  ((false, .right, 15), (true, .right, 16)), -- 11
  ((false, .right, 17), (true, .right, 18)), -- 12
  ((false, .left, 19), (true, .left, 4)), -- 13
  ((false, .left, 20), (false, .right, 14)), -- 14
  ((false, .right, 21), (true, .right, 22)), -- 15
  ((false, .right, 23), (true, .right, 24)), -- 16
  ((false, .right, 25), (true, .right, 26)), -- 17
  ((false, .left, 27), (false, .right, 28)), -- 18
  ((false, .left, 29), (true, .left, 4)), -- 19
  ((true, .left, 2), (false, .left, 2)), -- 20
  ((false, .right, 30), (false, .right, 31)), -- 21
  ((false, .right, 32), (false, .left, 33)), -- 22
  ((false, .right, 34), (true, .right, 35)), -- 23
  ((false, .right, 36), (true, .right, 37)), -- 24
  ((false, .right, 30), (false, .right, 38)), -- 25
  ((false, .right, 18), (false, .left, 20)), -- 26
  ((false, .left, 32), (true, .right, 39)), -- 27
  ((false, .right, 40), (true, .right, 28)), -- 28
  ((false, .left, 41), (true, .left, 4)), -- 29
  ((false, .left, 42), (false, .right, 43)), -- 30
  ((false, .right, 44), (true, .right, 31)), -- 31
  ((false, .right, 45), (true, .right, 46)), -- 32
  ((false, .right, 47), (false, .left, 48)), -- 33
  ((false, .right, 49), (true, .right, 50)), -- 34
  ((false, .right, 51), (true, .right, 52)), -- 35
  ((false, .right, 53), (true, .right, 54)), -- 36
  ((false, .right, 25), (true, .right, 55)), -- 37
  ((false, .right, 56), (true, .right, 38)), -- 38
  ((false, .right, 57), (false, .right, 38)), -- 39
  ((false, .right, 38), (true, .right, 40)), -- 40
  ((false, .left, 58), (true, .left, 4)), -- 41
  ((true, .right, 42), (true, .left, 2)), -- 42
  ((false, .right, 59), (true, .right, 43)), -- 43
  ((false, .right, 60), (true, .right, 44)), -- 44
  ((false, .right, 21), (true, .right, 61)), -- 45
  ((false, .right, 39), (true, .right, 62)), -- 46
  ((false, .left, 27), (false, .right, 40)), -- 47
  ((false, .left, 7), (true, .left, 63)), -- 48
  ((false, .right, 30), (false, .right, 64)), -- 49
  ((false, .right, 39), (false, .left, 20)), -- 50
  ((false, .right, 65), (true, .right, 66)), -- 51
  ((false, .right, 67), (true, .right, 68)), -- 52
  ((false, .right, 30), (false, .right, 69)), -- 53
  ((false, .right, 70), (true, .right, 71)), -- 54
  ((false, .right, 72), (false, .left, 20)), -- 55
  ((false, .right, 31), (true, .right, 56)), -- 56
  ((false, .left, 42), (false, .right, 73)), -- 57
  ((false, .left, 74), (true, .left, 4)), -- 58
  ((false, .right, 75), (true, .right, 43)), -- 59
  ((false, .right, 0), (true, .right, 60)), -- 60
  ((false, .right, 76), (false, .left, 33)), -- 61
  ((false, .right, 77), (true, .right, 78)), -- 62
  ((false, .left, 48), (true, .left, 63)), -- 63
  ((false, .right, 28), (true, .right, 64)), -- 64
  ((false, .left, 27), (false, .right, 60)), -- 65
  ((false, .right, 70), (false, .left, 20)), -- 66
  ((false, .right, 79), (true, .right, 80)), -- 67
  ((false, .right, 71), (true, .right, 81)), -- 68
  ((false, .right, 64), (true, .right, 69)), -- 69
  ((false, .right, 57), (false, .right, 64)), -- 70
  ((false, .left, 34), (true, .left, 82)), -- 71
  ((false, .right, 57), (false, .right, 69)), -- 72
  ((false, .right, 83), (true, .right, 73)), -- 73
  ((false, .left, 84), (true, .left, 4)), -- 74
  ((false, .left, 0), (true, .right, 85)), -- 75
  ((false, .right, 86), (true, .right, 87)), -- 76
  ((false, .right, 88), (true, .right, 254)), -- 77
  ((false, .left, 89), (true, .right, 37)), -- 78
  ((false, .right, 49), (true, .right, 90)), -- 79
  ((false, .right, 25), (true, .right, 91)), -- 80
  ((false, .right, 65), (true, .left, 92)), -- 81
  ((false, .right, 93), (true, .right, 94)), -- 82
  ((true, .right, 95), (true, .right, 73)), -- 83
  ((false, .right, 84), (true, .right, 96)), -- 84
  ((false, .right, 97), (true, .right, 85)), -- 85
  ((false, .right, 98), (true, .right, 99)), -- 86
  ((false, .right, 100), (true, .right, 101)), -- 87
  ((false, .right, 102), (true, .right, 103)), -- 88
  ((false, .right, 104), (true, .right, 105)), -- 89
  ((false, .right, 93), (true, .right, 71)), -- 90
  ((false, .right, 106), (false, .left, 50)), -- 91
  ((false, .left, 107), (true, .left, 24)), -- 92
  ((false, .right, 57), (false, .right, 56)), -- 93
  ((false, .right, 108), (false, .left, 50)), -- 94
  ((true, .right, 109), (true, .right, 95)), -- 95
  ((false, .right, 110), (true, .right, 111)), -- 96
  ((false, .left, 112), (true, .right, 85)), -- 97
  ((false, .right, 113), (true, .right, 16)), -- 98
  ((false, .right, 105), (true, .right, 114)), -- 99
  ((false, .right, 115), (true, .right, 116)), -- 100
  ((false, .right, 117), (true, .right, 118)), -- 101
  ((false, .right, 25), (true, .right, 119)), -- 102
  ((false, .right, 53), (true, .right, 120)), -- 103
  ((false, .right, 121), (true, .right, 122)), -- 104
  ((false, .right, 123), (true, .right, 124)), -- 105
  ((false, .right, 93), (true, .right, 122)), -- 106
  ((false, .right, 121), (true, .right, 125)), -- 107
  ((false, .right, 126), (true, .right, 127)), -- 108
  ((false, .left, 63), (false, .right, 95)), -- 109
  ((false, .right, 33), (true, .right, 128)), -- 110
  ((false, .right, 129), (true, .right, 130)), -- 111
  ((true, .left, 131), (true, .left, 112)), -- 112
  ((false, .right, 23), (true, .right, 132)), -- 113
  ((false, .right, 70), (true, .right, 70)), -- 114
  ((false, .right, 133), (true, .right, 134)), -- 115
  ((false, .right, 135), (true, .right, 136)), -- 116
  ((false, .right, 137), (true, .right, 138)), -- 117
  ((false, .right, 139), (true, .right, 140)), -- 118
  ((false, .right, 141), (true, .right, 142)), -- 119
  ((false, .right, 143), (false, .left, 61)), -- 120
  ((false, .right, 144), (true, .right, 145)), -- 121
  ((false, .right, 25), (true, .right, 66)), -- 122
  ((false, .right, 81), (true, .right, 68)), -- 123
  ((false, .right, 67), (true, .right, 146)), -- 124
  ((false, .right, 25), (true, .right, 147)), -- 125
  ((false, .right, 25), (false, .left, 48)), -- 126
  ((false, .right, 71), (true, .right, 50)), -- 127
  ((false, .right, 148), (true, .right, 12)), -- 128
  ((false, .right, 121), (true, .right, 149)), -- 129
  ((false, .right, 107), (true, .right, 150)), -- 130
  ((false, .left, 63), (false, .left, 112)), -- 131
  ((false, .right, 151), (true, .right, 125)), -- 132
  ((false, .right, 78), (true, .right, 152)), -- 133
  ((false, .right, 153), (true, .right, 154)), -- 134
  ((false, .right, 155), (true, .right, 156)), -- 135
  ((false, .right, 157), (true, .right, 158)), -- 136
  ((false, .right, 159), (true, .right, 160)), -- 137
  ((false, .right, 161), (true, .right, 162)), -- 138
  ((false, .right, 161), (true, .right, 163)), -- 139
  ((false, .right, 164), (true, .right, 165)), -- 140
  ((false, .right, 53), (false, .left, 14)), -- 141
  ((false, .right, 37), (true, .right, 72)), -- 142
  ((false, .left, 166), (false, .left, 2)), -- 143
  ((false, .right, 47), (true, .right, 82)), -- 144
  ((false, .right, 71), (true, .right, 167)), -- 145
  ((false, .right, 71), (true, .right, 168)), -- 146
  ((false, .right, 169), (false, .left, 20)), -- 147
  ((false, .right, 18), (true, .right, 167)), -- 148
  ((false, .right, 25), (true, .right, 170)), -- 149
  ((false, .right, 171), (true, .right, 172)), -- 150
  ((false, .right, 173), (true, .left, 24)), -- 151
  ((false, .right, 174), (true, .right, 175)), -- 152
  ((false, .right, 176), (true, .left, 177)), -- 153
  ((false, .right, 178), (true, .right, 179)), -- 154
  ((false, .right, 180), (true, .right, 181)), -- 155
  ((false, .right, 180), (true, .right, 182)), -- 156
  ((false, .right, 183), (true, .right, 184)), -- 157
  ((false, .right, 185), (true, .right, 186)), -- 158
  ((false, .left, 177), (true, .right, 187)), -- 159
  ((false, .right, 188), (true, .right, 189)), -- 160
  ((false, .right, 190), (true, .right, 191)), -- 161
  ((false, .right, 192), (true, .right, 193)), -- 162
  ((false, .right, 194), (true, .right, 195)), -- 163
  ((false, .right, 196), (true, .right, 197)), -- 164
  ((false, .right, 198), (true, .right, 199)), -- 165
  ((false, .right, 36), (true, .right, 79)), -- 166
  ((false, .right, 47), (true, .left, 92)), -- 167
  ((false, .right, 200), (false, .left, 20)), -- 168
  ((false, .right, 57), (false, .right, 44)), -- 169
  ((false, .right, 201), (false, .left, 20)), -- 170
  ((false, .right, 21), (true, .right, 202)), -- 171
  ((false, .right, 203), (true, .right, 204)), -- 172
  ((false, .right, 30), (false, .right, 44)), -- 173
  ((false, .right, 205), (true, .right, 89)), -- 174
  ((false, .right, 113), (true, .right, 105)), -- 175
  ((false, .right, 113), (true, .right, 206)), -- 176
  ((false, .right, 175), (true, .right, 207)), -- 177
  ((false, .right, 23), (true, .right, 208)), -- 178
  ((false, .right, 105), (true, .right, 105)), -- 179
  ((false, .right, 105), (true, .right, 209)), -- 180
  ((false, .right, 210), (true, .right, 211)), -- 181
  ((false, .right, 187), (true, .right, 212)), -- 182
  ((false, .right, 99), (true, .left, 213)), -- 183
  ((false, .right, 214), (true, .right, 215)), -- 184
  ((false, .right, 192), (true, .right, 212)), -- 185
  ((false, .right, 216), (true, .right, 217)), -- 186
  ((false, .right, 98), (true, .right, 218)), -- 187
  ((false, .right, 219), (true, .right, 220)), -- 188
  ((false, .right, 221), (true, .right, 222)), -- 189
  ((false, .right, 105), (true, .right, 99)), -- 190
  ((false, .right, 220), (true, .right, 223)), -- 191
  ((false, .right, 221), (true, .right, 220)), -- 192
  ((false, .right, 190), (true, .right, 213)), -- 193
  ((false, .right, 159), (true, .right, 224)), -- 194
  ((false, .right, 207), (true, .right, 190)), -- 195
  ((false, .right, 190), (true, .right, 225)), -- 196
  ((false, .right, 226), (true, .right, 159)), -- 197
  ((false, .right, 227), (true, .right, 215)), -- 198
  ((false, .right, 228), (true, .right, 229)), -- 199
  ((false, .right, 114), (true, .right, 114)), -- 200
  ((false, .right, 57), (false, .right, 31)), -- 201
  ((false, .right, 11), (false, .left, 33)), -- 202
  ((false, .right, 175), (true, .right, 34)), -- 203
  ((false, .right, 88), (true, .right, 113)), -- 204
  ((false, .right, 206), (true, .right, 23)), -- 205
  ((false, .right, 23), (true, .right, 230)), -- 206
  ((false, .right, 213), (true, .right, 231)), -- 207
  ((false, .right, 24), (true, .right, 206)), -- 208
  ((false, .right, 221), (true, .right, 232)), -- 209
  ((false, .right, 114), (true, .right, 233)), -- 210
  ((false, .right, 234), (true, .right, 235)), -- 211
  ((false, .right, 236), (true, .right, 178)), -- 212
  ((false, .right, 237), (true, .right, 238)), -- 213
  ((false, .right, 239), (true, .right, 240)), -- 214
  ((false, .right, 183), (true, .right, 233)), -- 215
  ((false, .right, 241), (true, .right, 242)), -- 216
  ((false, .right, 233), (true, .right, 235)), -- 217
  ((false, .left, 154), (true, .right, 70)), -- 218
  ((false, .right, 206), (true, .right, 178)), -- 219
  ((false, .right, 243), (true, .right, 218)), -- 220
  ((false, .right, 206), (true, .right, 243)), -- 221
  ((false, .right, 190), (true, .right, 244)), -- 222
  ((false, .right, 207), (true, .right, 206)), -- 223
  ((false, .right, 244), (true, .right, 244)), -- 224
  ((false, .right, 245), (true, .right, 153)), -- 225
  ((false, .right, 193), (true, .right, 231)), -- 226
  ((false, .right, 206), (true, .right, 187)), -- 227
  ((false, .right, 246), (true, .right, 247)), -- 228
  ((false, .right, 248), (true, .right, 249)), -- 229
  ((false, .right, 250), (true, .right, 149)), -- 230
  ((false, .right, 237), (true, .right, 183)), -- 231
  ((false, .right, 114), (true, .right, 220)), -- 232
  ((false, .right, 86), (true, .right, 70)), -- 233
  ((false, .right, 236), (true, .right, 86)), -- 234
  ((false, .right, 231), (true, .right, 16)), -- 235
  ((false, .right, 179), (true, .right, 113)), -- 236
  ((false, .right, 218), (true, .right, 105)), -- 237
  ((false, .right, 105), (true, .right, 237)), -- 238
  ((false, .right, 114), (true, .right, 16)), -- 239
  ((false, .right, 176), (true, .right, 99)), -- 240
  ((false, .right, 190), (true, .right, 86)), -- 241
  ((false, .right, 240), (true, .right, 236)), -- 242
  ((false, .left, 152), (true, .left, 245)), -- 243
  ((false, .right, 178), (true, .left, 188)), -- 244
  ((false, .right, 16), (true, .right, 244)), -- 245
  ((false, .right, 206), (true, .right, 233)), -- 246
  ((false, .right, 183), (true, .right, 213)), -- 247
  ((false, .right, 213), (true, .right, 250)), -- 248
  ((false, .right, 251), (true, .right, 252)), -- 249
  ((false, .right, 21), (true, .left, 166)), -- 250
  ((false, .right, 252), (true, .right, 253)), -- 251
  ((false, .right, 88), (true, .right, 143)), -- 252
  ((false, .right, 127), (true, .right, 151)) -- 253
]

/-- Finite size check, proved by kernel reduction. -/
theorem rawTable254_size : rawTable254.size = 254 := by decide

/-- Every numerical successor is a working state or the designated terminal. -/
theorem rawTable254_targets_bounded :
    rawTable254.toList.all (fun row =>
      decide (row.1.2.2 ≤ 254 ∧ row.2.2.2 ≤ 254)) = true := by decide

/-- There is exactly one transition into the source terminal label. -/
theorem rawTable254_halt_edge_count :
    ((rawTable254.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 254)).length = 1 := by decide

/-- The fallback is unreachable for Fin 254 indices, by rawTable254_size. -/
def rawAction254 (state : Fin 254) (bit : Bool) : RawAction254 :=
  let row := rawTable254.getD state.val
    ((false, .right, 254), (false, .right, 254))
  if bit then row.2 else row.1

/-- Map the numerical halt label to the existing separate terminal convention. -/
def action254 (state : Fin 254) (bit : Bool) : Action 254 :=
  let raw := rawAction254 state bit
  { write := raw.1
    move := raw.2.1
    next := if h : raw.2.2 < 254 then some ⟨raw.2.2, h⟩ else none }

/-- The literal benchmark uses 254 operational states and two tape symbols. -/
def machine254 : Machine 254 where
  transition := action254

/-- The same table at the typed-state interface used by StateReduction.lean. -/
def typedMachine254 : TypedMachine (Fin 254) where
  transition state bit :=
    let action := action254 state bit
    { write := action.write, move := action.move, next := action.next }

/-- A direct sanity check of the first blank-tape transition. -/
theorem machine254_initial_action :
    machine254.transition ⟨0, by decide⟩ false =
      { write := true, move := .left, next := some ⟨1, by decide⟩ } := by decide

#print axioms rawTable254_size
#print axioms rawTable254_targets_bounded
#print axioms rawTable254_halt_edge_count
#print axioms machine254_initial_action

end SetTheory.BusyBeaver.ZFC
