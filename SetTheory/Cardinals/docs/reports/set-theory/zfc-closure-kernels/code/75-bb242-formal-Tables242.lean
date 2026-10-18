import Lean.Elab.Tactic.Omega

/-!
Exact inherited-label tables and ordinary finite-block simulation for the
242-state branch-borrowing reduction of combined243. All statements use
arbitrary Int-indexed binary tapes, head coordinates, and shared start95.
The theorem is relative to combined243; its source/logic calibration is
supplied separately in the research report. No consistency premise is used.
Original calculus/program: Mira-Cult. Public verification: Jeff Ketchersid.
Compiler: Andrew James Wade. Inherited ProveIt reductions retain attribution.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace BranchBorrow242
structure Action where
  write : Bool
  right : Bool
  next : Nat
  deriving DecidableEq, Repr
def oldRows : Array (Option (Action × Action)) := #[
  none, -- 0
  none, -- 1
  some (⟨false, false, 2⟩, ⟨true, false, 4⟩), -- 2
  none, -- 3
  some (⟨false, false, 6⟩, ⟨true, false, 4⟩), -- 4
  none, -- 5
  some (⟨false, false, 9⟩, ⟨true, false, 4⟩), -- 6
  some (⟨true, true, 10⟩, ⟨false, false, 7⟩), -- 7
  none, -- 8
  some (⟨false, false, 13⟩, ⟨true, false, 4⟩), -- 9
  some (⟨false, true, 10⟩, ⟨false, true, 14⟩), -- 10
  some (⟨false, true, 15⟩, ⟨true, true, 16⟩), -- 11
  some (⟨false, true, 18⟩, ⟨true, true, 17⟩), -- 12
  some (⟨false, false, 19⟩, ⟨true, false, 4⟩), -- 13
  some (⟨false, false, 20⟩, ⟨false, true, 14⟩), -- 14
  some (⟨false, true, 21⟩, ⟨true, true, 22⟩), -- 15
  some (⟨false, true, 23⟩, ⟨true, true, 24⟩), -- 16
  some (⟨false, true, 25⟩, ⟨false, false, 20⟩), -- 17
  some (⟨false, false, 27⟩, ⟨false, true, 28⟩), -- 18
  some (⟨false, false, 29⟩, ⟨true, false, 4⟩), -- 19
  some (⟨true, false, 2⟩, ⟨false, false, 2⟩), -- 20
  some (⟨false, true, 30⟩, ⟨false, true, 38⟩), -- 21
  some (⟨false, true, 32⟩, ⟨false, false, 33⟩), -- 22
  some (⟨false, true, 34⟩, ⟨true, true, 35⟩), -- 23
  some (⟨false, true, 36⟩, ⟨true, true, 37⟩), -- 24
  some (⟨false, true, 30⟩, ⟨false, true, 69⟩), -- 25
  none, -- 26
  some (⟨false, false, 32⟩, ⟨true, true, 39⟩), -- 27
  some (⟨false, true, 40⟩, ⟨true, true, 28⟩), -- 28
  some (⟨false, false, 41⟩, ⟨true, false, 4⟩), -- 29
  some (⟨false, false, 42⟩, ⟨false, true, 95⟩), -- 30
  some (⟨false, true, 44⟩, ⟨true, true, 31⟩), -- 31
  some (⟨false, true, 45⟩, ⟨true, true, 46⟩), -- 32
  some (⟨false, true, 47⟩, ⟨false, false, 48⟩), -- 33
  some (⟨false, true, 49⟩, ⟨true, true, 50⟩), -- 34
  some (⟨false, true, 51⟩, ⟨true, true, 52⟩), -- 35
  some (⟨false, true, 53⟩, ⟨true, true, 54⟩), -- 36
  some (⟨false, true, 25⟩, ⟨true, true, 55⟩), -- 37
  some (⟨false, true, 56⟩, ⟨true, true, 38⟩), -- 38
  some (⟨false, true, 57⟩, ⟨false, true, 69⟩), -- 39
  some (⟨false, true, 38⟩, ⟨true, true, 40⟩), -- 40
  some (⟨false, false, 58⟩, ⟨true, false, 4⟩), -- 41
  some (⟨true, true, 42⟩, ⟨true, false, 2⟩), -- 42
  none, -- 43
  some (⟨false, true, 60⟩, ⟨true, true, 44⟩), -- 44
  some (⟨false, true, 21⟩, ⟨true, true, 61⟩), -- 45
  some (⟨false, true, 39⟩, ⟨true, true, 62⟩), -- 46
  some (⟨false, false, 27⟩, ⟨false, true, 44⟩), -- 47
  some (⟨false, false, 7⟩, ⟨true, false, 63⟩), -- 48
  some (⟨false, true, 30⟩, ⟨false, true, 31⟩), -- 49
  some (⟨false, true, 39⟩, ⟨false, false, 20⟩), -- 50
  some (⟨false, true, 65⟩, ⟨true, true, 66⟩), -- 51
  some (⟨false, true, 67⟩, ⟨true, true, 68⟩), -- 52
  some (⟨false, true, 30⟩, ⟨false, true, 64⟩), -- 53
  some (⟨false, true, 70⟩, ⟨true, true, 71⟩), -- 54
  some (⟨false, true, 72⟩, ⟨false, false, 20⟩), -- 55
  some (⟨false, true, 31⟩, ⟨true, true, 56⟩), -- 56
  some (⟨false, false, 42⟩, ⟨false, true, 73⟩), -- 57
  some (⟨false, false, 84⟩, ⟨true, false, 4⟩), -- 58
  none, -- 59
  some (⟨false, true, 20⟩, ⟨true, true, 60⟩), -- 60
  some (⟨false, true, 76⟩, ⟨false, false, 33⟩), -- 61
  some (⟨false, true, 77⟩, ⟨true, true, 78⟩), -- 62
  some (⟨false, false, 48⟩, ⟨true, false, 63⟩), -- 63
  some (⟨false, true, 28⟩, ⟨true, true, 64⟩), -- 64
  some (⟨false, false, 27⟩, ⟨false, true, 60⟩), -- 65
  some (⟨false, true, 70⟩, ⟨false, false, 20⟩), -- 66
  some (⟨false, true, 79⟩, ⟨true, true, 80⟩), -- 67
  some (⟨false, true, 71⟩, ⟨true, true, 81⟩), -- 68
  some (⟨false, true, 64⟩, ⟨true, true, 69⟩), -- 69
  some (⟨false, true, 57⟩, ⟨false, true, 31⟩), -- 70
  some (⟨false, false, 34⟩, ⟨true, false, 82⟩), -- 71
  some (⟨false, true, 57⟩, ⟨false, true, 64⟩), -- 72
  some (⟨false, true, 83⟩, ⟨true, true, 73⟩), -- 73
  some (⟨false, true, 132⟩, ⟨true, true, 16⟩), -- 74
  some (⟨true, true, 255⟩, ⟨true, false, 63⟩), -- 75
  some (⟨false, true, 86⟩, ⟨true, true, 87⟩), -- 76
  some (⟨false, true, 88⟩, ⟨true, true, 254⟩), -- 77
  some (⟨false, false, 89⟩, ⟨true, true, 37⟩), -- 78
  some (⟨false, true, 49⟩, ⟨true, true, 90⟩), -- 79
  some (⟨false, true, 25⟩, ⟨true, true, 91⟩), -- 80
  some (⟨false, true, 65⟩, ⟨true, false, 92⟩), -- 81
  some (⟨false, true, 93⟩, ⟨true, true, 94⟩), -- 82
  some (⟨true, true, 95⟩, ⟨true, true, 73⟩), -- 83
  some (⟨false, true, 84⟩, ⟨true, true, 96⟩), -- 84
  none, -- 85
  some (⟨false, true, 98⟩, ⟨true, true, 99⟩), -- 86
  some (⟨false, true, 214⟩, ⟨true, true, 249⟩), -- 87
  some (⟨false, true, 102⟩, ⟨true, true, 103⟩), -- 88
  some (⟨false, true, 104⟩, ⟨true, true, 105⟩), -- 89
  some (⟨false, true, 93⟩, ⟨true, true, 71⟩), -- 90
  some (⟨false, true, 106⟩, ⟨false, false, 50⟩), -- 91
  some (⟨false, false, 107⟩, ⟨true, true, 66⟩), -- 92
  some (⟨false, true, 57⟩, ⟨false, true, 40⟩), -- 93
  some (⟨false, true, 108⟩, ⟨false, false, 50⟩), -- 94
  some (⟨true, true, 109⟩, ⟨true, true, 95⟩), -- 95
  some (⟨false, true, 110⟩, ⟨true, true, 111⟩), -- 96
  none, -- 97
  some (⟨false, true, 23⟩, ⟨true, true, 74⟩), -- 98
  some (⟨false, true, 105⟩, ⟨true, true, 114⟩), -- 99
  some (⟨false, true, 153⟩, ⟨true, true, 184⟩), -- 100
  some (⟨false, true, 194⟩, ⟨true, true, 207⟩), -- 101
  some (⟨false, true, 25⟩, ⟨true, true, 119⟩), -- 102
  some (⟨false, true, 53⟩, ⟨true, true, 120⟩), -- 103
  some (⟨false, true, 121⟩, ⟨true, true, 92⟩), -- 104
  some (⟨false, true, 123⟩, ⟨true, true, 124⟩), -- 105
  some (⟨false, true, 93⟩, ⟨true, true, 92⟩), -- 106
  some (⟨false, true, 121⟩, ⟨true, true, 125⟩), -- 107
  some (⟨false, true, 126⟩, ⟨true, true, 127⟩), -- 108
  some (⟨false, true, 75⟩, ⟨false, true, 95⟩), -- 109
  some (⟨false, true, 33⟩, ⟨true, true, 128⟩), -- 110
  some (⟨false, true, 129⟩, ⟨true, true, 130⟩), -- 111
  some (⟨true, false, 131⟩, ⟨true, false, 112⟩), -- 112
  some (⟨false, true, 23⟩, ⟨true, true, 132⟩), -- 113
  some (⟨false, true, 70⟩, ⟨true, true, 70⟩), -- 114
  some (⟨false, true, 137⟩, ⟨true, true, 229⟩), -- 115
  some (⟨false, true, 183⟩, ⟨true, true, 134⟩), -- 116
  some (⟨false, true, 183⟩, ⟨true, true, 211⟩), -- 117
  some (⟨false, true, 231⟩, ⟨true, true, 159⟩), -- 118
  some (⟨false, true, 141⟩, ⟨true, true, 142⟩), -- 119
  some (⟨false, true, 143⟩, ⟨false, false, 61⟩), -- 120
  some (⟨false, true, 144⟩, ⟨true, true, 145⟩), -- 121
  none, -- 122
  some (⟨false, true, 81⟩, ⟨true, true, 68⟩), -- 123
  some (⟨false, true, 67⟩, ⟨true, true, 146⟩), -- 124
  some (⟨false, true, 25⟩, ⟨true, true, 147⟩), -- 125
  some (⟨false, true, 25⟩, ⟨false, false, 48⟩), -- 126
  some (⟨false, true, 71⟩, ⟨true, true, 50⟩), -- 127
  some (⟨false, true, 148⟩, ⟨true, true, 12⟩), -- 128
  some (⟨false, true, 121⟩, ⟨true, true, 149⟩), -- 129
  some (⟨false, true, 107⟩, ⟨true, true, 150⟩), -- 130
  some (⟨false, false, 48⟩, ⟨false, false, 112⟩), -- 131
  some (⟨false, true, 151⟩, ⟨true, true, 125⟩), -- 132
  some (⟨false, true, 78⟩, ⟨true, true, 152⟩), -- 133
  some (⟨false, true, 213⟩, ⟨true, true, 248⟩), -- 134
  some (⟨false, true, 240⟩, ⟨true, true, 215⟩), -- 135
  some (⟨false, true, 187⟩, ⟨true, true, 215⟩), -- 136
  some (⟨false, true, 159⟩, ⟨true, true, 160⟩), -- 137
  some (⟨false, true, 182⟩, ⟨true, true, 117⟩), -- 138
  some (⟨false, true, 86⟩, ⟨true, true, 235⟩), -- 139
  some (⟨false, true, 139⟩, ⟨true, true, 222⟩), -- 140
  some (⟨false, true, 53⟩, ⟨false, false, 14⟩), -- 141
  some (⟨false, true, 37⟩, ⟨true, true, 72⟩), -- 142
  some (⟨false, false, 166⟩, ⟨false, false, 2⟩), -- 143
  some (⟨false, true, 47⟩, ⟨true, true, 82⟩), -- 144
  some (⟨false, true, 71⟩, ⟨true, true, 167⟩), -- 145
  some (⟨false, true, 71⟩, ⟨true, true, 168⟩), -- 146
  some (⟨false, true, 169⟩, ⟨false, false, 20⟩), -- 147
  some (⟨false, true, 18⟩, ⟨true, true, 167⟩), -- 148
  some (⟨false, true, 25⟩, ⟨true, true, 170⟩), -- 149
  some (⟨false, true, 171⟩, ⟨true, true, 172⟩), -- 150
  some (⟨false, true, 173⟩, ⟨true, false, 24⟩), -- 151
  some (⟨false, true, 174⟩, ⟨true, true, 175⟩), -- 152
  some (⟨false, true, 176⟩, ⟨true, false, 157⟩), -- 153
  some (⟨false, true, 86⟩, ⟨true, true, 242⟩), -- 154
  some (⟨false, true, 154⟩, ⟨true, true, 217⟩), -- 155
  some (⟨false, true, 233⟩, ⟨true, true, 236⟩), -- 156
  some (⟨false, true, 175⟩, ⟨true, true, 207⟩), -- 157
  some (⟨false, true, 221⟩, ⟨true, true, 190⟩), -- 158
  some (⟨false, false, 157⟩, ⟨true, true, 187⟩), -- 159
  some (⟨false, true, 188⟩, ⟨true, true, 189⟩), -- 160
  some (⟨false, true, 179⟩, ⟨true, true, 191⟩), -- 161
  some (⟨false, true, 246⟩, ⟨true, true, 116⟩), -- 162
  some (⟨false, true, 225⟩, ⟨true, true, 193⟩), -- 163
  some (⟨false, true, 234⟩, ⟨true, true, 118⟩), -- 164
  some (⟨false, true, 16⟩, ⟨true, true, 135⟩), -- 165
  some (⟨false, true, 36⟩, ⟨true, true, 79⟩), -- 166
  some (⟨false, true, 47⟩, ⟨true, false, 151⟩), -- 167
  some (⟨false, true, 200⟩, ⟨false, false, 20⟩), -- 168
  some (⟨false, true, 57⟩, ⟨false, true, 56⟩), -- 169
  some (⟨false, true, 201⟩, ⟨false, false, 20⟩), -- 170
  some (⟨false, true, 21⟩, ⟨true, true, 202⟩), -- 171
  some (⟨false, true, 203⟩, ⟨true, true, 204⟩), -- 172
  some (⟨false, true, 30⟩, ⟨false, true, 56⟩), -- 173
  some (⟨false, true, 205⟩, ⟨true, true, 89⟩), -- 174
  some (⟨false, true, 113⟩, ⟨true, true, 105⟩), -- 175
  some (⟨false, true, 113⟩, ⟨true, true, 206⟩), -- 176
  some (⟨false, true, 165⟩, ⟨true, true, 185⟩), -- 177
  some (⟨false, true, 16⟩, ⟨true, true, 206⟩), -- 178
  some (⟨false, true, 105⟩, ⟨true, true, 105⟩), -- 179
  some (⟨false, true, 105⟩, ⟨true, true, 209⟩), -- 180
  some (⟨false, true, 178⟩, ⟨true, true, 241⟩), -- 181
  some (⟨false, true, 187⟩, ⟨true, true, 212⟩), -- 182
  some (⟨false, true, 99⟩, ⟨true, false, 213⟩), -- 183
  some (⟨false, true, 181⟩, ⟨true, true, 162⟩), -- 184
  some (⟨false, true, 192⟩, ⟨true, true, 212⟩), -- 185
  some (⟨false, true, 232⟩, ⟨true, true, 207⟩), -- 186
  some (⟨false, true, 98⟩, ⟨true, true, 218⟩), -- 187
  some (⟨false, true, 219⟩, ⟨true, true, 220⟩), -- 188
  some (⟨false, true, 158⟩, ⟨true, true, 244⟩), -- 189
  some (⟨false, true, 105⟩, ⟨true, true, 99⟩), -- 190
  some (⟨false, true, 186⟩, ⟨true, true, 206⟩), -- 191
  some (⟨false, true, 221⟩, ⟨true, true, 220⟩), -- 192
  some (⟨false, true, 190⟩, ⟨true, true, 213⟩), -- 193
  some (⟨false, true, 159⟩, ⟨true, true, 224⟩), -- 194
  some (⟨false, true, 114⟩, ⟨true, true, 156⟩), -- 195
  some (⟨false, true, 195⟩, ⟨true, true, 140⟩), -- 196
  some (⟨false, true, 196⟩, ⟨true, true, 115⟩), -- 197
  some (⟨false, true, 206⟩, ⟨true, true, 136⟩), -- 198
  some (⟨false, true, 197⟩, ⟨true, true, 227⟩), -- 199
  some (⟨false, true, 114⟩, ⟨true, true, 114⟩), -- 200
  some (⟨false, true, 57⟩, ⟨false, true, 38⟩), -- 201
  some (⟨false, true, 11⟩, ⟨false, false, 33⟩), -- 202
  some (⟨false, true, 175⟩, ⟨true, true, 34⟩), -- 203
  some (⟨false, true, 88⟩, ⟨true, true, 113⟩), -- 204
  some (⟨false, true, 206⟩, ⟨true, true, 23⟩), -- 205
  some (⟨false, true, 23⟩, ⟨true, true, 230⟩), -- 206
  some (⟨false, true, 213⟩, ⟨true, true, 231⟩), -- 207
  some (⟨false, true, 199⟩, ⟨true, true, 190⟩), -- 208
  some (⟨false, true, 221⟩, ⟨true, true, 232⟩), -- 209
  some (⟨false, true, 114⟩, ⟨true, true, 177⟩), -- 210
  some (⟨false, true, 210⟩, ⟨true, true, 190⟩), -- 211
  some (⟨false, true, 236⟩, ⟨true, true, 178⟩), -- 212
  some (⟨false, true, 237⟩, ⟨true, true, 238⟩), -- 213
  some (⟨false, true, 133⟩, ⟨true, true, 100⟩), -- 214
  some (⟨false, true, 183⟩, ⟨true, true, 233⟩), -- 215
  some (⟨false, true, 180⟩, ⟨true, true, 138⟩), -- 216
  some (⟨false, true, 233⟩, ⟨true, true, 235⟩), -- 217
  some (⟨false, false, 86⟩, ⟨true, true, 70⟩), -- 218
  some (⟨false, true, 206⟩, ⟨true, true, 178⟩), -- 219
  some (⟨false, true, 243⟩, ⟨true, true, 218⟩), -- 220
  some (⟨false, true, 206⟩, ⟨true, true, 243⟩), -- 221
  some (⟨false, true, 216⟩, ⟨true, true, 155⟩), -- 222
  some (⟨false, true, 180⟩, ⟨true, true, 208⟩), -- 223
  some (⟨false, true, 244⟩, ⟨true, true, 244⟩), -- 224
  some (⟨false, true, 245⟩, ⟨true, true, 153⟩), -- 225
  some (⟨false, true, 223⟩, ⟨true, true, 164⟩), -- 226
  some (⟨false, true, 193⟩, ⟨true, true, 228⟩), -- 227
  some (⟨false, true, 161⟩, ⟨true, true, 101⟩), -- 228
  some (⟨false, true, 161⟩, ⟨true, true, 192⟩), -- 229
  some (⟨false, true, 250⟩, ⟨true, true, 149⟩), -- 230
  some (⟨false, true, 237⟩, ⟨true, true, 183⟩), -- 231
  some (⟨false, true, 114⟩, ⟨true, true, 220⟩), -- 232
  some (⟨false, true, 86⟩, ⟨true, true, 70⟩), -- 233
  some (⟨false, true, 190⟩, ⟨true, true, 163⟩), -- 234
  some (⟨false, true, 231⟩, ⟨true, true, 16⟩), -- 235
  some (⟨false, true, 179⟩, ⟨true, true, 113⟩), -- 236
  some (⟨false, true, 218⟩, ⟨true, true, 105⟩), -- 237
  some (⟨false, true, 105⟩, ⟨true, true, 237⟩), -- 238
  some (⟨false, true, 179⟩, ⟨true, true, 226⟩), -- 239
  some (⟨false, true, 176⟩, ⟨true, true, 99⟩), -- 240
  some (⟨false, true, 239⟩, ⟨true, true, 198⟩), -- 241
  some (⟨false, true, 240⟩, ⟨true, true, 236⟩), -- 242
  some (⟨false, false, 152⟩, ⟨true, false, 245⟩), -- 243
  some (⟨false, true, 178⟩, ⟨true, false, 188⟩), -- 244
  some (⟨false, true, 16⟩, ⟨true, true, 244⟩), -- 245
  some (⟨false, true, 206⟩, ⟨true, true, 233⟩), -- 246
  none, -- 247
  some (⟨false, true, 213⟩, ⟨true, true, 250⟩), -- 248
  some (⟨false, true, 251⟩, ⟨true, true, 252⟩), -- 249
  some (⟨false, true, 21⟩, ⟨true, false, 166⟩), -- 250
  some (⟨false, true, 252⟩, ⟨true, true, 253⟩), -- 251
  some (⟨false, true, 88⟩, ⟨true, true, 143⟩), -- 252
  some (⟨false, true, 127⟩, ⟨true, true, 151⟩), -- 253
  none, -- 254
  some (⟨true, false, 255⟩, ⟨true, false, 131⟩) -- 255
]
def newRows : Array (Option (Action × Action)) := #[
  none, -- 0
  none, -- 1
  some (⟨false, false, 2⟩, ⟨true, false, 4⟩), -- 2
  none, -- 3
  some (⟨false, false, 6⟩, ⟨true, false, 4⟩), -- 4
  none, -- 5
  some (⟨false, false, 9⟩, ⟨true, false, 4⟩), -- 6
  some (⟨true, true, 10⟩, ⟨false, false, 7⟩), -- 7
  none, -- 8
  some (⟨false, false, 13⟩, ⟨true, false, 4⟩), -- 9
  some (⟨false, true, 10⟩, ⟨false, true, 14⟩), -- 10
  some (⟨false, true, 27⟩, ⟨true, true, 16⟩), -- 11
  some (⟨false, true, 18⟩, ⟨true, true, 17⟩), -- 12
  some (⟨false, false, 19⟩, ⟨true, false, 4⟩), -- 13
  some (⟨false, false, 20⟩, ⟨false, true, 14⟩), -- 14
  none, -- 15
  some (⟨false, true, 23⟩, ⟨true, true, 24⟩), -- 16
  some (⟨false, true, 25⟩, ⟨false, false, 20⟩), -- 17
  some (⟨false, false, 27⟩, ⟨false, true, 28⟩), -- 18
  some (⟨false, false, 29⟩, ⟨true, false, 4⟩), -- 19
  some (⟨true, false, 2⟩, ⟨false, false, 2⟩), -- 20
  some (⟨false, true, 30⟩, ⟨false, true, 38⟩), -- 21
  some (⟨false, true, 32⟩, ⟨false, false, 33⟩), -- 22
  some (⟨false, true, 34⟩, ⟨true, true, 35⟩), -- 23
  some (⟨false, true, 36⟩, ⟨true, true, 37⟩), -- 24
  some (⟨false, true, 30⟩, ⟨false, true, 69⟩), -- 25
  none, -- 26
  some (⟨false, false, 32⟩, ⟨true, true, 22⟩), -- 27
  some (⟨false, true, 40⟩, ⟨true, true, 28⟩), -- 28
  some (⟨false, false, 41⟩, ⟨true, false, 4⟩), -- 29
  some (⟨false, false, 42⟩, ⟨false, true, 95⟩), -- 30
  some (⟨false, true, 44⟩, ⟨true, true, 31⟩), -- 31
  some (⟨false, true, 45⟩, ⟨true, true, 46⟩), -- 32
  some (⟨false, true, 47⟩, ⟨false, false, 48⟩), -- 33
  some (⟨false, true, 49⟩, ⟨true, true, 50⟩), -- 34
  some (⟨false, true, 51⟩, ⟨true, true, 52⟩), -- 35
  some (⟨false, true, 53⟩, ⟨true, true, 54⟩), -- 36
  some (⟨false, true, 25⟩, ⟨true, true, 55⟩), -- 37
  some (⟨false, true, 56⟩, ⟨true, true, 38⟩), -- 38
  some (⟨false, true, 57⟩, ⟨false, true, 69⟩), -- 39
  some (⟨false, true, 38⟩, ⟨true, true, 40⟩), -- 40
  some (⟨false, false, 58⟩, ⟨true, false, 4⟩), -- 41
  some (⟨true, true, 42⟩, ⟨true, false, 2⟩), -- 42
  none, -- 43
  some (⟨false, true, 60⟩, ⟨true, true, 44⟩), -- 44
  some (⟨false, true, 21⟩, ⟨true, true, 61⟩), -- 45
  some (⟨false, true, 39⟩, ⟨true, true, 62⟩), -- 46
  some (⟨false, false, 27⟩, ⟨false, true, 44⟩), -- 47
  some (⟨false, false, 7⟩, ⟨true, false, 63⟩), -- 48
  some (⟨false, true, 30⟩, ⟨false, true, 31⟩), -- 49
  some (⟨false, true, 39⟩, ⟨false, false, 20⟩), -- 50
  some (⟨false, true, 65⟩, ⟨true, true, 66⟩), -- 51
  some (⟨false, true, 67⟩, ⟨true, true, 68⟩), -- 52
  some (⟨false, true, 30⟩, ⟨false, true, 64⟩), -- 53
  some (⟨false, true, 70⟩, ⟨true, true, 71⟩), -- 54
  some (⟨false, true, 72⟩, ⟨false, false, 20⟩), -- 55
  some (⟨false, true, 31⟩, ⟨true, true, 56⟩), -- 56
  some (⟨false, false, 42⟩, ⟨false, true, 73⟩), -- 57
  some (⟨false, false, 84⟩, ⟨true, false, 4⟩), -- 58
  none, -- 59
  some (⟨false, true, 20⟩, ⟨true, true, 60⟩), -- 60
  some (⟨false, true, 76⟩, ⟨false, false, 33⟩), -- 61
  some (⟨false, true, 77⟩, ⟨true, true, 78⟩), -- 62
  some (⟨false, false, 48⟩, ⟨true, false, 63⟩), -- 63
  some (⟨false, true, 28⟩, ⟨true, true, 64⟩), -- 64
  some (⟨false, false, 27⟩, ⟨false, true, 60⟩), -- 65
  some (⟨false, true, 70⟩, ⟨false, false, 20⟩), -- 66
  some (⟨false, true, 79⟩, ⟨true, true, 80⟩), -- 67
  some (⟨false, true, 71⟩, ⟨true, true, 81⟩), -- 68
  some (⟨false, true, 64⟩, ⟨true, true, 69⟩), -- 69
  some (⟨false, true, 57⟩, ⟨false, true, 31⟩), -- 70
  some (⟨false, false, 34⟩, ⟨true, false, 82⟩), -- 71
  some (⟨false, true, 57⟩, ⟨false, true, 64⟩), -- 72
  some (⟨false, true, 83⟩, ⟨true, true, 73⟩), -- 73
  some (⟨false, true, 132⟩, ⟨true, true, 16⟩), -- 74
  some (⟨true, true, 255⟩, ⟨true, false, 63⟩), -- 75
  some (⟨false, true, 86⟩, ⟨true, true, 87⟩), -- 76
  some (⟨false, true, 88⟩, ⟨true, true, 254⟩), -- 77
  some (⟨false, false, 89⟩, ⟨true, true, 37⟩), -- 78
  some (⟨false, true, 49⟩, ⟨true, true, 90⟩), -- 79
  some (⟨false, true, 25⟩, ⟨true, true, 91⟩), -- 80
  some (⟨false, true, 65⟩, ⟨true, false, 92⟩), -- 81
  some (⟨false, true, 93⟩, ⟨true, true, 94⟩), -- 82
  some (⟨true, true, 95⟩, ⟨true, true, 73⟩), -- 83
  some (⟨false, true, 84⟩, ⟨true, true, 96⟩), -- 84
  none, -- 85
  some (⟨false, true, 98⟩, ⟨true, true, 99⟩), -- 86
  some (⟨false, true, 214⟩, ⟨true, true, 249⟩), -- 87
  some (⟨false, true, 102⟩, ⟨true, true, 103⟩), -- 88
  some (⟨false, true, 104⟩, ⟨true, true, 105⟩), -- 89
  some (⟨false, true, 93⟩, ⟨true, true, 71⟩), -- 90
  some (⟨false, true, 106⟩, ⟨false, false, 50⟩), -- 91
  some (⟨false, false, 107⟩, ⟨true, true, 66⟩), -- 92
  some (⟨false, true, 57⟩, ⟨false, true, 40⟩), -- 93
  some (⟨false, true, 108⟩, ⟨false, false, 50⟩), -- 94
  some (⟨true, true, 109⟩, ⟨true, true, 95⟩), -- 95
  some (⟨false, true, 110⟩, ⟨true, true, 111⟩), -- 96
  none, -- 97
  some (⟨false, true, 23⟩, ⟨true, true, 74⟩), -- 98
  some (⟨false, true, 105⟩, ⟨true, true, 114⟩), -- 99
  some (⟨false, true, 153⟩, ⟨true, true, 184⟩), -- 100
  some (⟨false, true, 194⟩, ⟨true, true, 207⟩), -- 101
  some (⟨false, true, 25⟩, ⟨true, true, 119⟩), -- 102
  some (⟨false, true, 53⟩, ⟨true, true, 120⟩), -- 103
  some (⟨false, true, 121⟩, ⟨true, true, 92⟩), -- 104
  some (⟨false, true, 123⟩, ⟨true, true, 124⟩), -- 105
  some (⟨false, true, 93⟩, ⟨true, true, 92⟩), -- 106
  some (⟨false, true, 121⟩, ⟨true, true, 125⟩), -- 107
  some (⟨false, true, 126⟩, ⟨true, true, 127⟩), -- 108
  some (⟨false, true, 75⟩, ⟨false, true, 95⟩), -- 109
  some (⟨false, true, 33⟩, ⟨true, true, 128⟩), -- 110
  some (⟨false, true, 129⟩, ⟨true, true, 130⟩), -- 111
  some (⟨true, false, 131⟩, ⟨true, false, 112⟩), -- 112
  some (⟨false, true, 23⟩, ⟨true, true, 132⟩), -- 113
  some (⟨false, true, 70⟩, ⟨true, true, 70⟩), -- 114
  some (⟨false, true, 137⟩, ⟨true, true, 229⟩), -- 115
  some (⟨false, true, 183⟩, ⟨true, true, 134⟩), -- 116
  some (⟨false, true, 183⟩, ⟨true, true, 211⟩), -- 117
  some (⟨false, true, 231⟩, ⟨true, true, 159⟩), -- 118
  some (⟨false, true, 141⟩, ⟨true, true, 142⟩), -- 119
  some (⟨false, true, 143⟩, ⟨false, false, 61⟩), -- 120
  some (⟨false, true, 144⟩, ⟨true, true, 145⟩), -- 121
  none, -- 122
  some (⟨false, true, 81⟩, ⟨true, true, 68⟩), -- 123
  some (⟨false, true, 67⟩, ⟨true, true, 146⟩), -- 124
  some (⟨false, true, 25⟩, ⟨true, true, 147⟩), -- 125
  some (⟨false, true, 25⟩, ⟨false, false, 48⟩), -- 126
  some (⟨false, true, 71⟩, ⟨true, true, 50⟩), -- 127
  some (⟨false, true, 148⟩, ⟨true, true, 12⟩), -- 128
  some (⟨false, true, 121⟩, ⟨true, true, 149⟩), -- 129
  some (⟨false, true, 107⟩, ⟨true, true, 150⟩), -- 130
  some (⟨false, false, 48⟩, ⟨false, false, 112⟩), -- 131
  some (⟨false, true, 151⟩, ⟨true, true, 125⟩), -- 132
  some (⟨false, true, 78⟩, ⟨true, true, 152⟩), -- 133
  some (⟨false, true, 213⟩, ⟨true, true, 248⟩), -- 134
  some (⟨false, true, 240⟩, ⟨true, true, 215⟩), -- 135
  some (⟨false, true, 187⟩, ⟨true, true, 215⟩), -- 136
  some (⟨false, true, 159⟩, ⟨true, true, 160⟩), -- 137
  some (⟨false, true, 182⟩, ⟨true, true, 117⟩), -- 138
  some (⟨false, true, 86⟩, ⟨true, true, 235⟩), -- 139
  some (⟨false, true, 139⟩, ⟨true, true, 222⟩), -- 140
  some (⟨false, true, 53⟩, ⟨false, false, 14⟩), -- 141
  some (⟨false, true, 37⟩, ⟨true, true, 72⟩), -- 142
  some (⟨false, false, 166⟩, ⟨false, false, 2⟩), -- 143
  some (⟨false, true, 47⟩, ⟨true, true, 82⟩), -- 144
  some (⟨false, true, 71⟩, ⟨true, true, 167⟩), -- 145
  some (⟨false, true, 71⟩, ⟨true, true, 168⟩), -- 146
  some (⟨false, true, 169⟩, ⟨false, false, 20⟩), -- 147
  some (⟨false, true, 18⟩, ⟨true, true, 167⟩), -- 148
  some (⟨false, true, 25⟩, ⟨true, true, 170⟩), -- 149
  some (⟨false, true, 171⟩, ⟨true, true, 172⟩), -- 150
  some (⟨false, true, 173⟩, ⟨true, false, 24⟩), -- 151
  some (⟨false, true, 174⟩, ⟨true, true, 175⟩), -- 152
  some (⟨false, true, 176⟩, ⟨true, false, 157⟩), -- 153
  some (⟨false, true, 86⟩, ⟨true, true, 242⟩), -- 154
  some (⟨false, true, 154⟩, ⟨true, true, 217⟩), -- 155
  some (⟨false, true, 233⟩, ⟨true, true, 236⟩), -- 156
  some (⟨false, true, 175⟩, ⟨true, true, 207⟩), -- 157
  some (⟨false, true, 221⟩, ⟨true, true, 190⟩), -- 158
  some (⟨false, false, 157⟩, ⟨true, true, 187⟩), -- 159
  some (⟨false, true, 188⟩, ⟨true, true, 189⟩), -- 160
  some (⟨false, true, 179⟩, ⟨true, true, 191⟩), -- 161
  some (⟨false, true, 246⟩, ⟨true, true, 116⟩), -- 162
  some (⟨false, true, 225⟩, ⟨true, true, 193⟩), -- 163
  some (⟨false, true, 234⟩, ⟨true, true, 118⟩), -- 164
  some (⟨false, true, 16⟩, ⟨true, true, 135⟩), -- 165
  some (⟨false, true, 36⟩, ⟨true, true, 79⟩), -- 166
  some (⟨false, true, 47⟩, ⟨true, false, 151⟩), -- 167
  some (⟨false, true, 200⟩, ⟨false, false, 20⟩), -- 168
  some (⟨false, true, 57⟩, ⟨false, true, 56⟩), -- 169
  some (⟨false, true, 201⟩, ⟨false, false, 20⟩), -- 170
  some (⟨false, true, 21⟩, ⟨true, true, 202⟩), -- 171
  some (⟨false, true, 203⟩, ⟨true, true, 204⟩), -- 172
  some (⟨false, true, 30⟩, ⟨false, true, 56⟩), -- 173
  some (⟨false, true, 205⟩, ⟨true, true, 89⟩), -- 174
  some (⟨false, true, 113⟩, ⟨true, true, 105⟩), -- 175
  some (⟨false, true, 113⟩, ⟨true, true, 206⟩), -- 176
  some (⟨false, true, 165⟩, ⟨true, true, 185⟩), -- 177
  some (⟨false, true, 16⟩, ⟨true, true, 206⟩), -- 178
  some (⟨false, true, 105⟩, ⟨true, true, 105⟩), -- 179
  some (⟨false, true, 105⟩, ⟨true, true, 209⟩), -- 180
  some (⟨false, true, 178⟩, ⟨true, true, 241⟩), -- 181
  some (⟨false, true, 187⟩, ⟨true, true, 212⟩), -- 182
  some (⟨false, true, 99⟩, ⟨true, false, 213⟩), -- 183
  some (⟨false, true, 181⟩, ⟨true, true, 162⟩), -- 184
  some (⟨false, true, 192⟩, ⟨true, true, 212⟩), -- 185
  some (⟨false, true, 232⟩, ⟨true, true, 207⟩), -- 186
  some (⟨false, true, 98⟩, ⟨true, true, 218⟩), -- 187
  some (⟨false, true, 219⟩, ⟨true, true, 220⟩), -- 188
  some (⟨false, true, 158⟩, ⟨true, true, 244⟩), -- 189
  some (⟨false, true, 105⟩, ⟨true, true, 99⟩), -- 190
  some (⟨false, true, 186⟩, ⟨true, true, 206⟩), -- 191
  some (⟨false, true, 221⟩, ⟨true, true, 220⟩), -- 192
  some (⟨false, true, 190⟩, ⟨true, true, 213⟩), -- 193
  some (⟨false, true, 159⟩, ⟨true, true, 224⟩), -- 194
  some (⟨false, true, 114⟩, ⟨true, true, 156⟩), -- 195
  some (⟨false, true, 195⟩, ⟨true, true, 140⟩), -- 196
  some (⟨false, true, 196⟩, ⟨true, true, 115⟩), -- 197
  some (⟨false, true, 206⟩, ⟨true, true, 136⟩), -- 198
  some (⟨false, true, 197⟩, ⟨true, true, 227⟩), -- 199
  some (⟨false, true, 114⟩, ⟨true, true, 114⟩), -- 200
  some (⟨false, true, 57⟩, ⟨false, true, 38⟩), -- 201
  some (⟨false, true, 11⟩, ⟨false, false, 33⟩), -- 202
  some (⟨false, true, 175⟩, ⟨true, true, 34⟩), -- 203
  some (⟨false, true, 88⟩, ⟨true, true, 113⟩), -- 204
  some (⟨false, true, 206⟩, ⟨true, true, 23⟩), -- 205
  some (⟨false, true, 23⟩, ⟨true, true, 230⟩), -- 206
  some (⟨false, true, 213⟩, ⟨true, true, 231⟩), -- 207
  some (⟨false, true, 199⟩, ⟨true, true, 190⟩), -- 208
  some (⟨false, true, 221⟩, ⟨true, true, 232⟩), -- 209
  some (⟨false, true, 114⟩, ⟨true, true, 177⟩), -- 210
  some (⟨false, true, 210⟩, ⟨true, true, 190⟩), -- 211
  some (⟨false, true, 236⟩, ⟨true, true, 178⟩), -- 212
  some (⟨false, true, 237⟩, ⟨true, true, 238⟩), -- 213
  some (⟨false, true, 133⟩, ⟨true, true, 100⟩), -- 214
  some (⟨false, true, 183⟩, ⟨true, true, 233⟩), -- 215
  some (⟨false, true, 180⟩, ⟨true, true, 138⟩), -- 216
  some (⟨false, true, 233⟩, ⟨true, true, 235⟩), -- 217
  some (⟨false, false, 86⟩, ⟨true, true, 70⟩), -- 218
  some (⟨false, true, 206⟩, ⟨true, true, 178⟩), -- 219
  some (⟨false, true, 243⟩, ⟨true, true, 218⟩), -- 220
  some (⟨false, true, 206⟩, ⟨true, true, 243⟩), -- 221
  some (⟨false, true, 216⟩, ⟨true, true, 155⟩), -- 222
  some (⟨false, true, 180⟩, ⟨true, true, 208⟩), -- 223
  some (⟨false, true, 244⟩, ⟨true, true, 244⟩), -- 224
  some (⟨false, true, 245⟩, ⟨true, true, 153⟩), -- 225
  some (⟨false, true, 223⟩, ⟨true, true, 164⟩), -- 226
  some (⟨false, true, 193⟩, ⟨true, true, 228⟩), -- 227
  some (⟨false, true, 161⟩, ⟨true, true, 101⟩), -- 228
  some (⟨false, true, 161⟩, ⟨true, true, 192⟩), -- 229
  some (⟨false, true, 250⟩, ⟨true, true, 149⟩), -- 230
  some (⟨false, true, 237⟩, ⟨true, true, 183⟩), -- 231
  some (⟨false, true, 114⟩, ⟨true, true, 220⟩), -- 232
  some (⟨false, true, 86⟩, ⟨true, true, 70⟩), -- 233
  some (⟨false, true, 190⟩, ⟨true, true, 163⟩), -- 234
  some (⟨false, true, 231⟩, ⟨true, true, 16⟩), -- 235
  some (⟨false, true, 179⟩, ⟨true, true, 113⟩), -- 236
  some (⟨false, true, 218⟩, ⟨true, true, 105⟩), -- 237
  some (⟨false, true, 105⟩, ⟨true, true, 237⟩), -- 238
  some (⟨false, true, 179⟩, ⟨true, true, 226⟩), -- 239
  some (⟨false, true, 176⟩, ⟨true, true, 99⟩), -- 240
  some (⟨false, true, 239⟩, ⟨true, true, 198⟩), -- 241
  some (⟨false, true, 240⟩, ⟨true, true, 236⟩), -- 242
  some (⟨false, false, 152⟩, ⟨true, false, 245⟩), -- 243
  some (⟨false, true, 178⟩, ⟨true, false, 188⟩), -- 244
  some (⟨false, true, 16⟩, ⟨true, true, 244⟩), -- 245
  some (⟨false, true, 206⟩, ⟨true, true, 233⟩), -- 246
  none, -- 247
  some (⟨false, true, 213⟩, ⟨true, true, 250⟩), -- 248
  some (⟨false, true, 251⟩, ⟨true, true, 252⟩), -- 249
  some (⟨false, true, 21⟩, ⟨true, false, 166⟩), -- 250
  some (⟨false, true, 252⟩, ⟨true, true, 253⟩), -- 251
  some (⟨false, true, 88⟩, ⟨true, true, 143⟩), -- 252
  some (⟨false, true, 127⟩, ⟨true, true, 151⟩), -- 253
  none, -- 254
  some (⟨true, false, 255⟩, ⟨true, false, 131⟩) -- 255
]

def oldFinite (q : Fin 256) (b : Bool) : Option Action :=
  (oldRows[q.val]'q.isLt).map (fun pair => if b then pair.2 else pair.1)
def newFinite (q : Fin 256) (b : Bool) : Option Action :=
  (newRows[q.val]'q.isLt).map (fun pair => if b then pair.2 else pair.1)
def oldRow (q : Nat) (b : Bool) : Option Action :=
  if h : q < 256 then oldFinite ⟨q, h⟩ b else none
def newRow (q : Nat) (b : Bool) : Option Action :=
  if h : q < 256 then newFinite ⟨q, h⟩ b else none

def incoming (q : Nat) (b : Bool) (a : Action) : Prop :=
  ((a.next = 18 ∨ a.next = 47 ∨ a.next = 65) →
    a.right = true ∧ a.write = false) ∧
  (a.next = 27 → (q = 18 ∨ q = 47 ∨ q = 65) ∧
    b = false ∧ a.right = false) ∧
  (a.next = 15 → q = 11 ∧ b = false)
instance (q : Nat) (b : Bool) (a : Action) : Decidable (incoming q b a) := by
  unfold incoming
  infer_instance

def checkIncoming (q : Fin 256) (b : Bool) : Bool :=
  match oldFinite q b with
  | none => true
  | some a => decide (incoming q.val b a)

theorem incoming_finite : ∀ (q : Fin 256) (b : Bool),
    checkIncoming q b = true := by decide

def patched (q : Nat) (b : Bool) : Option Action :=
  if q = 15 then none
  else if q = 11 ∧ b = false then some ⟨false, true, 27⟩
  else if q = 27 ∧ b = true then some ⟨true, true, 22⟩
  else oldRow q b

theorem patch_finite : ∀ (q : Fin 256) (b : Bool),
    newFinite q b = patched q.val b := by decide

theorem newRow_patch (q : Nat) (b : Bool) : newRow q b = patched q b := by
  by_cases h : q < 256
  · simpa [newRow, h] using patch_finite ⟨q, h⟩ b
  · have h15 : q ≠ 15 := by omega
    have h11 : q ≠ 11 := by omega
    have h27 : q ≠ 27 := by omega
    simp [newRow, patched, oldRow, h, h15, h11, h27]

theorem incoming_all (q : Nat) (b : Bool) (a : Action)
    (hrow : oldRow q b = some a) : incoming q b a := by
  by_cases hq : q < 256
  · have hh := incoming_finite ⟨q, hq⟩ b
    have hr : oldFinite ⟨q, hq⟩ b = some a := by simpa [oldRow, hq] using hrow
    simp only [checkIncoming, hr] at hh
    exact of_decide_eq_true hh
  · simp [oldRow, hq] at hrow

def workingCount (rows : Array (Option (Action × Action))) : Nat :=
  rows.foldl (fun n a => if a.isSome then n + 1 else n) 0

theorem old_size : oldRows.size = 256 := by decide
theorem new_size : newRows.size = 256 := by decide
theorem old_working_count : workingCount oldRows = 243 := by decide
theorem new_working_count : workingCount newRows = 242 := by decide

theorem old_halt (b : Bool) : oldRow 254 b = none := by cases b <;> rfl
theorem new_halt (b : Bool) : newRow 254 b = none := by cases b <;> rfl

end BranchBorrow242
