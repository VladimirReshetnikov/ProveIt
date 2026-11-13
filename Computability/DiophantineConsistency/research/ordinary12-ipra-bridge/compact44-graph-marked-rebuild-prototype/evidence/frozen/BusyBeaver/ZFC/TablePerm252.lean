import BusyBeaver.Core

/-!
Literal 252-state register-permutation candidate, separate from Table252.lean.

Mira-Cult designed the original254 machine and Jeff supplied its verification;
mira-emmy supplied the public253 reduction at0d544f2a2e3c18f12278441a74b7879f31cbe856.
This candidate additionally folds old5 into64 and permutes physical register
selectors by [0, 3, 4, 5, 8, 1, 6, 2, 7]. The search/generation is documented in Research/ZFC.
Frozen old-label SHA256: 939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713.
Canonical SHA256: 8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797.
Old start64 is canonical0; old halt254 is canonical252 and maps to none,
retaining its final write and head move. These are504 literal binary actions.
Finite table facts below do not prove runtime or consistency calibration.
-/
namespace SetTheory.BusyBeaver.ZFC
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
abbrev RawActionPerm252 := Bool × Move × Nat

def rawTablePerm252 : Array (RawActionPerm252 × RawActionPerm252) := #[
  ((false, .right, 27), (true, .right, 0)), -- 0
  ((true, .left, 2), (false, .left, 3)), -- 1
  ((false, .left, 4), (true, .left, 2)), -- 2
  ((false, .left, 3), (true, .left, 5)), -- 3
  ((false, .left, 47), (true, .left, 2)), -- 4
  ((false, .left, 6), (true, .left, 5)), -- 5
  ((false, .left, 8), (true, .left, 5)), -- 6
  ((true, .right, 9), (false, .left, 7)), -- 7
  ((false, .left, 12), (true, .left, 5)), -- 8
  ((false, .right, 9), (false, .right, 13)), -- 9
  ((false, .right, 14), (true, .right, 15)), -- 10
  ((false, .right, 16), (true, .right, 17)), -- 11
  ((false, .left, 18), (true, .left, 5)), -- 12
  ((false, .left, 19), (false, .right, 13)), -- 13
  ((false, .right, 20), (true, .right, 21)), -- 14
  ((false, .right, 22), (true, .right, 23)), -- 15
  ((false, .right, 24), (true, .right, 25)), -- 16
  ((false, .left, 26), (false, .right, 27)), -- 17
  ((false, .left, 28), (true, .left, 5)), -- 18
  ((true, .left, 3), (false, .left, 3)), -- 19
  ((false, .right, 29), (false, .right, 37)), -- 20
  ((false, .right, 31), (false, .left, 32)), -- 21
  ((false, .right, 33), (true, .right, 34)), -- 22
  ((false, .right, 35), (true, .right, 36)), -- 23
  ((false, .right, 29), (false, .right, 67)), -- 24
  ((false, .right, 17), (false, .left, 19)), -- 25
  ((false, .left, 31), (true, .right, 38)), -- 26
  ((false, .right, 39), (true, .right, 27)), -- 27
  ((false, .left, 40), (true, .left, 5)), -- 28
  ((false, .left, 41), (false, .right, 42)), -- 29
  ((false, .right, 43), (true, .right, 30)), -- 30
  ((false, .right, 44), (true, .right, 45)), -- 31
  ((false, .right, 46), (false, .left, 47)), -- 32
  ((false, .right, 48), (true, .right, 49)), -- 33
  ((false, .right, 50), (true, .right, 51)), -- 34
  ((false, .right, 52), (true, .right, 53)), -- 35
  ((false, .right, 24), (true, .right, 54)), -- 36
  ((false, .right, 55), (true, .right, 37)), -- 37
  ((false, .right, 56), (false, .right, 67)), -- 38
  ((false, .right, 37), (true, .right, 39)), -- 39
  ((false, .left, 57), (true, .left, 5)), -- 40
  ((true, .right, 41), (true, .left, 3)), -- 41
  ((false, .right, 58), (true, .right, 42)), -- 42
  ((false, .right, 59), (true, .right, 43)), -- 43
  ((false, .right, 20), (true, .right, 60)), -- 44
  ((false, .right, 38), (true, .right, 61)), -- 45
  ((false, .left, 26), (false, .right, 43)), -- 46
  ((false, .left, 7), (true, .left, 62)), -- 47
  ((false, .right, 29), (false, .right, 30)), -- 48
  ((false, .right, 38), (false, .left, 19)), -- 49
  ((false, .right, 63), (true, .right, 64)), -- 50
  ((false, .right, 65), (true, .right, 66)), -- 51
  ((false, .right, 29), (false, .right, 0)), -- 52
  ((false, .right, 68), (true, .right, 69)), -- 53
  ((false, .right, 70), (false, .left, 19)), -- 54
  ((false, .right, 30), (true, .right, 55)), -- 55
  ((false, .left, 41), (false, .right, 71)), -- 56
  ((false, .left, 72), (true, .left, 5)), -- 57
  ((false, .right, 73), (true, .right, 42)), -- 58
  ((false, .right, 1), (true, .right, 59)), -- 59
  ((false, .right, 74), (false, .left, 32)), -- 60
  ((false, .right, 75), (true, .right, 76)), -- 61
  ((false, .left, 47), (true, .left, 62)), -- 62
  ((false, .left, 26), (false, .right, 59)), -- 63
  ((false, .right, 68), (false, .left, 19)), -- 64
  ((false, .right, 77), (true, .right, 78)), -- 65
  ((false, .right, 69), (true, .right, 79)), -- 66
  ((false, .right, 0), (true, .right, 67)), -- 67
  ((false, .right, 56), (false, .right, 30)), -- 68
  ((false, .left, 33), (true, .left, 80)), -- 69
  ((false, .right, 56), (false, .right, 0)), -- 70
  ((false, .right, 81), (true, .right, 71)), -- 71
  ((false, .left, 82), (true, .left, 5)), -- 72
  ((false, .left, 1), (true, .right, 83)), -- 73
  ((false, .right, 84), (true, .right, 85)), -- 74
  ((false, .right, 86), (true, .right, 252)), -- 75
  ((false, .left, 87), (true, .right, 36)), -- 76
  ((false, .right, 48), (true, .right, 88)), -- 77
  ((false, .right, 24), (true, .right, 89)), -- 78
  ((false, .right, 63), (true, .left, 90)), -- 79
  ((false, .right, 91), (true, .right, 92)), -- 80
  ((true, .right, 93), (true, .right, 71)), -- 81
  ((false, .right, 82), (true, .right, 94)), -- 82
  ((false, .right, 95), (true, .right, 83)), -- 83
  ((false, .right, 96), (true, .right, 97)), -- 84
  ((false, .right, 98), (true, .right, 99)), -- 85
  ((false, .right, 100), (true, .right, 101)), -- 86
  ((false, .right, 102), (true, .right, 103)), -- 87
  ((false, .right, 91), (true, .right, 69)), -- 88
  ((false, .right, 104), (false, .left, 49)), -- 89
  ((false, .left, 105), (true, .left, 23)), -- 90
  ((false, .right, 56), (false, .right, 39)), -- 91
  ((false, .right, 106), (false, .left, 49)), -- 92
  ((true, .right, 107), (true, .right, 93)), -- 93
  ((false, .right, 108), (true, .right, 109)), -- 94
  ((false, .left, 110), (true, .right, 83)), -- 95
  ((false, .right, 111), (true, .right, 15)), -- 96
  ((false, .right, 103), (true, .right, 112)), -- 97
  ((false, .right, 113), (true, .right, 114)), -- 98
  ((false, .right, 115), (true, .right, 116)), -- 99
  ((false, .right, 24), (true, .right, 117)), -- 100
  ((false, .right, 52), (true, .right, 118)), -- 101
  ((false, .right, 119), (true, .right, 120)), -- 102
  ((false, .right, 121), (true, .right, 122)), -- 103
  ((false, .right, 91), (true, .right, 120)), -- 104
  ((false, .right, 119), (true, .right, 123)), -- 105
  ((false, .right, 124), (true, .right, 125)), -- 106
  ((false, .left, 62), (false, .right, 93)), -- 107
  ((false, .right, 32), (true, .right, 126)), -- 108
  ((false, .right, 127), (true, .right, 128)), -- 109
  ((true, .left, 129), (true, .left, 110)), -- 110
  ((false, .right, 22), (true, .right, 130)), -- 111
  ((false, .right, 68), (true, .right, 68)), -- 112
  ((false, .right, 131), (true, .right, 132)), -- 113
  ((false, .right, 133), (true, .right, 134)), -- 114
  ((false, .right, 135), (true, .right, 136)), -- 115
  ((false, .right, 137), (true, .right, 138)), -- 116
  ((false, .right, 139), (true, .right, 140)), -- 117
  ((false, .right, 141), (false, .left, 60)), -- 118
  ((false, .right, 142), (true, .right, 143)), -- 119
  ((false, .right, 24), (true, .right, 64)), -- 120
  ((false, .right, 79), (true, .right, 66)), -- 121
  ((false, .right, 65), (true, .right, 144)), -- 122
  ((false, .right, 24), (true, .right, 145)), -- 123
  ((false, .right, 24), (false, .left, 47)), -- 124
  ((false, .right, 69), (true, .right, 49)), -- 125
  ((false, .right, 146), (true, .right, 11)), -- 126
  ((false, .right, 119), (true, .right, 147)), -- 127
  ((false, .right, 105), (true, .right, 148)), -- 128
  ((false, .left, 62), (false, .left, 110)), -- 129
  ((false, .right, 149), (true, .right, 123)), -- 130
  ((false, .right, 76), (true, .right, 150)), -- 131
  ((false, .right, 151), (true, .right, 152)), -- 132
  ((false, .right, 153), (true, .right, 154)), -- 133
  ((false, .right, 155), (true, .right, 156)), -- 134
  ((false, .right, 157), (true, .right, 158)), -- 135
  ((false, .right, 159), (true, .right, 160)), -- 136
  ((false, .right, 159), (true, .right, 161)), -- 137
  ((false, .right, 162), (true, .right, 163)), -- 138
  ((false, .right, 52), (false, .left, 13)), -- 139
  ((false, .right, 36), (true, .right, 70)), -- 140
  ((false, .left, 164), (false, .left, 3)), -- 141
  ((false, .right, 46), (true, .right, 80)), -- 142
  ((false, .right, 69), (true, .right, 165)), -- 143
  ((false, .right, 69), (true, .right, 166)), -- 144
  ((false, .right, 167), (false, .left, 19)), -- 145
  ((false, .right, 17), (true, .right, 165)), -- 146
  ((false, .right, 24), (true, .right, 168)), -- 147
  ((false, .right, 169), (true, .right, 170)), -- 148
  ((false, .right, 171), (true, .left, 23)), -- 149
  ((false, .right, 172), (true, .right, 173)), -- 150
  ((false, .right, 174), (true, .left, 175)), -- 151
  ((false, .right, 176), (true, .right, 177)), -- 152
  ((false, .right, 178), (true, .right, 179)), -- 153
  ((false, .right, 178), (true, .right, 180)), -- 154
  ((false, .right, 181), (true, .right, 182)), -- 155
  ((false, .right, 183), (true, .right, 184)), -- 156
  ((false, .left, 175), (true, .right, 185)), -- 157
  ((false, .right, 186), (true, .right, 187)), -- 158
  ((false, .right, 188), (true, .right, 189)), -- 159
  ((false, .right, 190), (true, .right, 191)), -- 160
  ((false, .right, 192), (true, .right, 193)), -- 161
  ((false, .right, 194), (true, .right, 195)), -- 162
  ((false, .right, 196), (true, .right, 197)), -- 163
  ((false, .right, 35), (true, .right, 77)), -- 164
  ((false, .right, 46), (true, .left, 90)), -- 165
  ((false, .right, 198), (false, .left, 19)), -- 166
  ((false, .right, 56), (false, .right, 55)), -- 167
  ((false, .right, 199), (false, .left, 19)), -- 168
  ((false, .right, 20), (true, .right, 200)), -- 169
  ((false, .right, 201), (true, .right, 202)), -- 170
  ((false, .right, 29), (false, .right, 55)), -- 171
  ((false, .right, 203), (true, .right, 87)), -- 172
  ((false, .right, 111), (true, .right, 103)), -- 173
  ((false, .right, 111), (true, .right, 204)), -- 174
  ((false, .right, 173), (true, .right, 205)), -- 175
  ((false, .right, 22), (true, .right, 206)), -- 176
  ((false, .right, 103), (true, .right, 103)), -- 177
  ((false, .right, 103), (true, .right, 207)), -- 178
  ((false, .right, 208), (true, .right, 209)), -- 179
  ((false, .right, 185), (true, .right, 210)), -- 180
  ((false, .right, 97), (true, .left, 211)), -- 181
  ((false, .right, 212), (true, .right, 213)), -- 182
  ((false, .right, 190), (true, .right, 210)), -- 183
  ((false, .right, 214), (true, .right, 215)), -- 184
  ((false, .right, 96), (true, .right, 216)), -- 185
  ((false, .right, 217), (true, .right, 218)), -- 186
  ((false, .right, 219), (true, .right, 220)), -- 187
  ((false, .right, 103), (true, .right, 97)), -- 188
  ((false, .right, 218), (true, .right, 221)), -- 189
  ((false, .right, 219), (true, .right, 218)), -- 190
  ((false, .right, 188), (true, .right, 211)), -- 191
  ((false, .right, 157), (true, .right, 222)), -- 192
  ((false, .right, 205), (true, .right, 188)), -- 193
  ((false, .right, 188), (true, .right, 223)), -- 194
  ((false, .right, 224), (true, .right, 157)), -- 195
  ((false, .right, 225), (true, .right, 213)), -- 196
  ((false, .right, 226), (true, .right, 227)), -- 197
  ((false, .right, 112), (true, .right, 112)), -- 198
  ((false, .right, 56), (false, .right, 37)), -- 199
  ((false, .right, 10), (false, .left, 32)), -- 200
  ((false, .right, 173), (true, .right, 33)), -- 201
  ((false, .right, 86), (true, .right, 111)), -- 202
  ((false, .right, 204), (true, .right, 22)), -- 203
  ((false, .right, 22), (true, .right, 228)), -- 204
  ((false, .right, 211), (true, .right, 229)), -- 205
  ((false, .right, 23), (true, .right, 204)), -- 206
  ((false, .right, 219), (true, .right, 230)), -- 207
  ((false, .right, 112), (true, .right, 231)), -- 208
  ((false, .right, 232), (true, .right, 233)), -- 209
  ((false, .right, 234), (true, .right, 176)), -- 210
  ((false, .right, 235), (true, .right, 236)), -- 211
  ((false, .right, 237), (true, .right, 238)), -- 212
  ((false, .right, 181), (true, .right, 231)), -- 213
  ((false, .right, 239), (true, .right, 240)), -- 214
  ((false, .right, 231), (true, .right, 233)), -- 215
  ((false, .left, 152), (true, .right, 68)), -- 216
  ((false, .right, 204), (true, .right, 176)), -- 217
  ((false, .right, 241), (true, .right, 216)), -- 218
  ((false, .right, 204), (true, .right, 241)), -- 219
  ((false, .right, 188), (true, .right, 242)), -- 220
  ((false, .right, 205), (true, .right, 204)), -- 221
  ((false, .right, 242), (true, .right, 242)), -- 222
  ((false, .right, 243), (true, .right, 151)), -- 223
  ((false, .right, 191), (true, .right, 229)), -- 224
  ((false, .right, 204), (true, .right, 185)), -- 225
  ((false, .right, 244), (true, .right, 245)), -- 226
  ((false, .right, 246), (true, .right, 247)), -- 227
  ((false, .right, 248), (true, .right, 147)), -- 228
  ((false, .right, 235), (true, .right, 181)), -- 229
  ((false, .right, 112), (true, .right, 218)), -- 230
  ((false, .right, 84), (true, .right, 68)), -- 231
  ((false, .right, 234), (true, .right, 84)), -- 232
  ((false, .right, 229), (true, .right, 15)), -- 233
  ((false, .right, 177), (true, .right, 111)), -- 234
  ((false, .right, 216), (true, .right, 103)), -- 235
  ((false, .right, 103), (true, .right, 235)), -- 236
  ((false, .right, 112), (true, .right, 15)), -- 237
  ((false, .right, 174), (true, .right, 97)), -- 238
  ((false, .right, 188), (true, .right, 84)), -- 239
  ((false, .right, 238), (true, .right, 234)), -- 240
  ((false, .left, 150), (true, .left, 243)), -- 241
  ((false, .right, 176), (true, .left, 186)), -- 242
  ((false, .right, 15), (true, .right, 242)), -- 243
  ((false, .right, 204), (true, .right, 231)), -- 244
  ((false, .right, 181), (true, .right, 211)), -- 245
  ((false, .right, 211), (true, .right, 248)), -- 246
  ((false, .right, 249), (true, .right, 250)), -- 247
  ((false, .right, 20), (true, .left, 164)), -- 248
  ((false, .right, 250), (true, .right, 251)), -- 249
  ((false, .right, 86), (true, .right, 141)), -- 250
  ((false, .right, 125), (true, .right, 149)) -- 251
]

theorem rawTablePerm252_size : rawTablePerm252.size = 252 := by decide

theorem rawTablePerm252_transition_count :
    (rawTablePerm252.toList.flatMap (fun row => [row.1, row.2])).length = 504 := by decide

theorem rawTablePerm252_targets_bounded :
    rawTablePerm252.toList.all (fun row =>
      decide (row.1.2.2 ≤ 252 ∧ row.2.2.2 ≤ 252)) = true := by decide

theorem rawTablePerm252_halt_edge_count :
    ((rawTablePerm252.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 252)).length = 1 := by decide

def rawActionPerm252 (state : Fin 252) (bit : Bool) : RawActionPerm252 :=
  let row := rawTablePerm252.getD state.val
    ((false, .right, 252), (false, .right, 252))
  if bit then row.2 else row.1

def actionPerm252 (state : Fin 252) (bit : Bool) : Action 252 :=
  let raw := rawActionPerm252 state bit
  { write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 252 then some ⟨raw.2.2, h⟩ else none }

def machinePerm252 : Machine 252 where
  transition := actionPerm252

def typedMachinePerm252 : TypedMachine (Fin 252) where
  transition state bit :=
    let a := actionPerm252 state bit
    { write := a.write, move := a.move, next := a.next }

theorem machinePerm252_initial_action :
    machinePerm252.transition ⟨0, by decide⟩ false = { write := false, move := .right, next := some ⟨27, by decide⟩ } := by decide

#print axioms rawTablePerm252_size
#print axioms rawTablePerm252_transition_count
#print axioms rawTablePerm252_targets_bounded
#print axioms rawTablePerm252_halt_edge_count
#print axioms machinePerm252_initial_action
end SetTheory.BusyBeaver.ZFC
