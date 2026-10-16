import BusyBeaver.Core

/-!
Literal experimental 248-state original-rho6 candidate from report source11.

Source: SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/
11-grammar-machines-raw-candidate-old_rho6-248.tm, placed unchanged in
3cc6ba5b1f200f9baeaa00ce546b168efca7f95d from the batch145 second report
(arrival96836f9eea). Source SHA-256:
e9cf9241e0012c56ecf4dc55f969d4c01e988a5c3839c9e4a49b5fae33591d45.

Credit belongs to the delivered source11 compiler experiment and its prior
rebracketing method, building on ProveIt's research generators, Mira-Cult's
original program and design, Jeff's original verification, and Andrew James
Wade's public MIT-0 backend. This file introduces no machine optimization.
It imports literal data, without importing or reproving those developments.

This is the equality-free/base-three candidate retaining original rho6,
not the separate dual-rho6 248 table or the attributed upstream253 machine.
Its 186 decoder and 62 framework states total248; the numerical count does
not establish a calibrated improvement on the ZFC-consistency benchmark.

The formerly undefined named1.inc/read1 row is filled with write1/right/halt;
it is row13/read1 below. Under undefined-transition halting this preserves
the tape and adds one final move. Core uses Fin248 working states and none
for source terminal248, retaining the final write and move.

Only finite literal facts and the specified short blank-tape prefix are
proved here. No logical adequacy, proof-enumerator/compiler simulation,
full initializer or internal ZFC/PA consistency endpoint is supplied.
-/

namespace SetTheory.BusyBeaver.ZFC

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Write bit, head move, numerical successor (248 is terminal). -/
abbrev RawAction248 := Bool × Move × Nat

/-- Read-zero/read-one actions in numerical working-state order. -/
def rawTable248 : Array (RawAction248 × RawAction248) := #[
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
  ((true, .right, 14), (true, .right, 248)), -- 13
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
  ((false, .right, 54), (true, .right, 169)), -- 54
  ((true, .left, 57), (false, .left, 55)), -- 55
  ((false, .left, 55), (false, .left, 56)), -- 56
  ((false, .left, 47), (true, .left, 57)), -- 57
  ((false, .left, 58), (false, .left, 57)), -- 58
  ((false, .left, 59), (false, .left, 58)), -- 59
  ((false, .left, 60), (false, .left, 59)), -- 60
  ((false, .left, 61), (false, .left, 60)), -- 61
  ((false, .right, 149), (true, .right, 210)), -- 62
  ((false, .right, 151), (true, .right, 211)), -- 63
  ((false, .right, 149), (true, .right, 196)), -- 64
  ((false, .right, 208), (true, .right, 212)), -- 65
  ((false, .right, 196), (true, .right, 63)), -- 66
  ((false, .right, 198), (true, .right, 63)), -- 67
  ((false, .right, 151), (true, .right, 198)), -- 68
  ((false, .right, 68), (true, .right, 211)), -- 69
  ((false, .right, 196), (true, .right, 66)), -- 70
  ((false, .right, 149), (true, .right, 64)), -- 71
  ((false, .right, 196), (true, .right, 151)), -- 72
  ((false, .right, 149), (true, .right, 151)), -- 73
  ((false, .right, 65), (true, .right, 198)), -- 74
  ((false, .right, 71), (true, .right, 68)), -- 75
  ((false, .right, 196), (true, .right, 198)), -- 76
  ((false, .right, 198), (true, .right, 196)), -- 77
  ((false, .right, 72), (true, .right, 210)), -- 78
  ((false, .right, 76), (true, .right, 210)), -- 79
  ((false, .right, 67), (true, .right, 74)), -- 80
  ((false, .right, 77), (true, .right, 211)), -- 81
  ((false, .right, 62), (true, .right, 80)), -- 82
  ((false, .right, 226), (true, .right, 161)), -- 83
  ((false, .right, 240), (true, .right, 83)), -- 84
  ((false, .right, 161), (true, .right, 84)), -- 85
  ((false, .right, 221), (true, .right, 85)), -- 86
  ((false, .right, 208), (true, .right, 86)), -- 87
  ((false, .right, 208), (true, .right, 87)), -- 88
  ((false, .right, 65), (true, .right, 88)), -- 89
  ((false, .right, 62), (true, .right, 89)), -- 90
  ((false, .right, 212), (true, .right, 90)), -- 91
  ((false, .right, 76), (true, .right, 91)), -- 92
  ((false, .right, 69), (true, .right, 92)), -- 93
  ((false, .right, 151), (true, .right, 93)), -- 94
  ((false, .right, 62), (true, .right, 94)), -- 95
  ((false, .right, 62), (true, .right, 95)), -- 96
  ((false, .right, 65), (true, .right, 96)), -- 97
  ((false, .right, 69), (true, .right, 97)), -- 98
  ((false, .right, 68), (true, .right, 98)), -- 99
  ((false, .right, 68), (true, .right, 99)), -- 100
  ((false, .right, 70), (true, .right, 100)), -- 101
  ((false, .right, 82), (true, .right, 101)), -- 102
  ((false, .right, 208), (true, .right, 102)), -- 103
  ((false, .right, 62), (true, .right, 103)), -- 104
  ((false, .right, 67), (true, .right, 104)), -- 105
  ((false, .right, 81), (true, .right, 105)), -- 106
  ((false, .right, 82), (true, .right, 106)), -- 107
  ((false, .right, 69), (true, .right, 107)), -- 108
  ((false, .right, 62), (true, .right, 108)), -- 109
  ((false, .right, 81), (true, .right, 109)), -- 110
  ((false, .right, 67), (true, .right, 110)), -- 111
  ((false, .right, 68), (true, .right, 111)), -- 112
  ((false, .right, 198), (true, .right, 112)), -- 113
  ((false, .right, 70), (true, .right, 113)), -- 114
  ((false, .right, 73), (true, .right, 114)), -- 115
  ((false, .right, 210), (true, .right, 115)), -- 116
  ((false, .right, 66), (true, .right, 116)), -- 117
  ((false, .right, 198), (true, .right, 117)), -- 118
  ((false, .right, 63), (true, .right, 118)), -- 119
  ((false, .right, 64), (true, .right, 119)), -- 120
  ((false, .right, 151), (true, .right, 120)), -- 121
  ((false, .right, 212), (true, .right, 121)), -- 122
  ((false, .right, 78), (true, .right, 122)), -- 123
  ((false, .right, 64), (true, .right, 123)), -- 124
  ((false, .right, 210), (true, .right, 124)), -- 125
  ((false, .right, 79), (true, .right, 125)), -- 126
  ((false, .right, 151), (true, .right, 126)), -- 127
  ((false, .right, 210), (true, .right, 127)), -- 128
  ((false, .right, 210), (true, .right, 128)), -- 129
  ((false, .right, 75), (true, .right, 129)), -- 130
  ((false, .right, 79), (true, .right, 130)), -- 131
  ((false, .right, 78), (true, .right, 131)), -- 132
  ((false, .right, 62), (true, .right, 132)), -- 133
  ((false, .right, 75), (true, .right, 133)), -- 134
  ((false, .right, 191), (true, .right, 134)), -- 135
  ((false, .right, 237), (true, .right, 135)), -- 136
  ((false, .right, 188), (true, .right, 136)), -- 137
  ((false, .right, 201), (true, .right, 137)), -- 138
  ((false, .right, 191), (true, .right, 138)), -- 139
  ((false, .right, 73), (true, .right, 139)), -- 140
  ((false, .right, 73), (true, .right, 140)), -- 141
  ((false, .right, 76), (true, .right, 141)), -- 142
  ((false, .right, 206), (true, .right, 142)), -- 143
  ((false, .right, 78), (true, .right, 143)), -- 144
  ((false, .right, 37), (true, .right, 185)), -- 145
  ((false, .right, 45), (true, .right, 185)), -- 146
  ((false, .right, 41), (true, .right, 148)), -- 147
  ((false, .right, 187), (false, .left, 58)), -- 148
  ((false, .right, 190), (true, .right, 150)), -- 149
  ((false, .right, 192), (true, .right, 147)), -- 150
  ((false, .right, 201), (true, .right, 152)), -- 151
  ((false, .right, 229), (true, .right, 236)), -- 152
  ((false, .right, 154), (true, .right, 158)), -- 153
  ((false, .right, 39), (true, .right, 155)), -- 154
  ((false, .right, 156), (true, .right, 157)), -- 155
  ((false, .right, 35), (false, .left, 58)), -- 156
  ((false, .right, 236), (true, .right, 36)), -- 157
  ((false, .right, 35), (true, .right, 159)), -- 158
  ((false, .right, 228), (false, .left, 56)), -- 159
  ((false, .right, 153), (true, .right, 196)), -- 160
  ((false, .right, 153), (true, .right, 243)), -- 161
  ((false, .right, 153), (true, .right, 248)), -- 162
  ((false, .right, 164), (true, .right, 165)), -- 163
  ((false, .right, 37), (false, .left, 56)), -- 164
  ((false, .right, 223), (true, .right, 166)), -- 165
  ((false, .right, 232), (true, .right, 32)), -- 166
  ((false, .right, 168), (true, .right, 240)), -- 167
  ((false, .right, 39), (false, .left, 56)), -- 168
  ((false, .right, 163), (true, .right, 170)), -- 169
  ((false, .right, 204), (true, .right, 171)), -- 170
  ((false, .right, 205), (true, .right, 172)), -- 171
  ((false, .right, 173), (true, .right, 181)), -- 172
  ((false, .right, 29), (true, .right, 174)), -- 173
  ((false, .right, 175), (false, .left, 56)), -- 174
  ((false, .right, 176), (true, .right, 151)), -- 175
  ((false, .right, 29), (true, .right, 177)), -- 176
  ((false, .right, 178), (false, .left, 56)), -- 177
  ((false, .right, 179), (true, .right, 183)), -- 178
  ((false, .right, 29), (true, .right, 180)), -- 179
  ((false, .right, 144), (false, .left, 56)), -- 180
  ((false, .right, 191), (true, .right, 182)), -- 181
  ((false, .right, 245), (true, .right, 160)), -- 182
  ((false, .right, 40), (true, .right, 184)), -- 183
  ((false, .right, 162), (true, .right, 200)), -- 184
  ((false, .right, 186), (false, .left, 58)), -- 185
  ((false, .right, 42), (true, .right, 167)), -- 186
  ((false, .right, 189), (true, .right, 44)), -- 187
  ((false, .right, 145), (true, .right, 238)), -- 188
  ((false, .right, 44), (true, .right, 44)), -- 189
  ((false, .right, 146), (true, .right, 241)), -- 190
  ((false, .right, 196), (true, .right, 149)), -- 191
  ((false, .right, 244), (true, .right, 193)), -- 192
  ((false, .right, 39), (true, .right, 194)), -- 193
  ((false, .right, 195), (false, .left, 59)), -- 194
  ((false, .right, 42), (true, .right, 237)), -- 195
  ((false, .right, 201), (true, .right, 197)), -- 196
  ((false, .right, 227), (true, .right, 234)), -- 197
  ((false, .right, 201), (true, .right, 199)), -- 198
  ((false, .right, 222), (true, .right, 230)), -- 199
  ((false, .right, 190), (true, .right, 236)), -- 200
  ((false, .right, 245), (true, .right, 202)), -- 201
  ((false, .right, 246), (true, .right, 203)), -- 202
  ((false, .right, 192), (true, .right, 241)), -- 203
  ((false, .right, 188), (true, .right, 230)), -- 204
  ((false, .right, 188), (true, .right, 234)), -- 205
  ((false, .right, 188), (true, .right, 236)), -- 206
  ((false, .right, 201), (true, .right, 44)), -- 207
  ((false, .right, 247), (true, .right, 209)), -- 208
  ((false, .right, 149), (true, .right, 247)), -- 209
  ((false, .right, 149), (true, .right, 189)), -- 210
  ((false, .right, 149), (true, .right, 44)), -- 211
  ((false, .right, 247), (true, .right, 213)), -- 212
  ((false, .right, 210), (true, .right, 247)), -- 213
  ((false, .right, 40), (false, .left, 58)), -- 214
  ((false, .right, 44), (false, .left, 58)), -- 215
  ((false, .right, 217), (false, .left, 58)), -- 216
  ((false, .right, 40), (true, .right, 42)), -- 217
  ((false, .right, 219), (false, .left, 58)), -- 218
  ((false, .right, 40), (true, .right, 44)), -- 219
  ((false, .right, 36), (false, .left, 58)), -- 220
  ((false, .right, 29), (true, .right, 216)), -- 221
  ((false, .right, 29), (true, .right, 218)), -- 222
  ((false, .right, 31), (true, .right, 224)), -- 223
  ((false, .right, 225), (false, .left, 58)), -- 224
  ((false, .right, 38), (true, .right, 40)), -- 225
  ((false, .right, 33), (true, .right, 220)), -- 226
  ((false, .right, 33), (true, .right, 218)), -- 227
  ((false, .right, 35), (false, .left, 57)), -- 228
  ((false, .right, 35), (true, .right, 218)), -- 229
  ((false, .right, 39), (true, .right, 231)), -- 230
  ((false, .right, 30), (false, .left, 58)), -- 231
  ((false, .right, 39), (true, .right, 233)), -- 232
  ((false, .right, 32), (false, .left, 58)), -- 233
  ((false, .right, 39), (true, .right, 235)), -- 234
  ((false, .right, 34), (false, .left, 58)), -- 235
  ((false, .right, 39), (true, .right, 220)), -- 236
  ((false, .right, 39), (true, .right, 215)), -- 237
  ((false, .right, 41), (true, .right, 239)), -- 238
  ((false, .right, 38), (false, .left, 58)), -- 239
  ((false, .right, 41), (true, .right, 214)), -- 240
  ((false, .right, 41), (true, .right, 242)), -- 241
  ((false, .right, 46), (false, .left, 58)), -- 242
  ((false, .right, 43), (false, .left, 57)), -- 243
  ((false, .right, 43), (true, .right, 216)), -- 244
  ((false, .right, 43), (true, .right, 214)), -- 245
  ((false, .right, 45), (true, .right, 215)), -- 246
  ((false, .right, 207), (true, .right, 149)) -- 247
]

/-- Finite size check by kernel reduction. -/
theorem rawTable248_size : rawTable248.size = 248 := by decide

/-- The literal binary table contains exactly 496 transition actions. -/
theorem rawTable248_transition_count :
    (rawTable248.toList.flatMap (fun row => [row.1, row.2])).length = 496 := by decide

/-- Every successor is a working state or the designated terminal. -/
theorem rawTable248_targets_bounded :
    rawTable248.toList.all (fun row =>
      decide (row.1.2.2 ≤ 248 ∧ row.2.2.2 ≤ 248)) = true := by decide

/-- Exactly two actions enter the source terminal label. -/
theorem rawTable248_halt_edge_count :
    ((rawTable248.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 248)).length = 2 := by decide

/-- The fallback is unreachable at Fin 248 indices, by rawTable248_size. -/
def rawAction248 (state : Fin 248) (bit : Bool) : RawAction248 :=
  let row := rawTable248.getD state.val
    ((false, .right, 248), (false, .right, 248))
  if bit then row.2 else row.1

/-- Interpret the numerical halt label with the separate terminal convention. -/
def action248 (state : Fin 248) (bit : Bool) : Action 248 :=
  let raw := rawAction248 state bit
  { write := raw.1
    move := raw.2.1
    next := if h : raw.2.2 < 248 then some ⟨raw.2.2, h⟩ else none }

/-- The frozen experimental table, without a proof-search calibration. -/
def machine248 : Machine 248 where
  transition := action248

/-- The same literal table at the typed-state interface. -/
def typedMachine248 : TypedMachine (Fin 248) where
  transition state bit :=
    let action := action248 state bit
    { write := action.write, move := action.move, next := action.next }

/-- Sanity check of the initial blank-tape action. -/
theorem machine248_initial_action :
    machine248.transition ⟨0, by decide⟩ false =
      { write := true, move := .right, next := some ⟨1, by decide⟩ } := by decide

/-- The formerly undefined read-one row preserves its read bit and halts. -/
theorem machine248_totalized_action :
    machine248.transition ⟨13, by decide⟩ true =
      { write := true, move := .right, next := none } := by decide

#print axioms rawTable248_size
#print axioms rawTable248_transition_count
#print axioms rawTable248_targets_bounded
#print axioms rawTable248_halt_edge_count
#print axioms machine248_initial_action
#print axioms machine248_totalized_action


/-- The emitted program's halt edge, distinct from the normalized missing row. -/
theorem machine248_program_halt_action :
    machine248.transition ⟨162, by decide⟩ true =
      { write := true, move := .right, next := none } := by decide

#print axioms machine248_program_halt_action

namespace Prefix248

/-- Complete checkpoint after the stated finite blank-tape prefix. -/
def checkpoint1024 : Config 248 :=
  { state := some ⟨2, by decide⟩, head := 56,
    tape := [53, 49, 45, 41, 37, 33, 29, 25, 22, 21, 18, 15, 14, 10, 6, 2,
      -2, -6, -10, -14, -17] }

/-- Actual Core transitions from blank tape, without a prepared input. -/
theorem first1024 : machine248.run 1024 = checkpoint1024 := by decide

#print axioms first1024

end Prefix248

end SetTheory.BusyBeaver.ZFC
