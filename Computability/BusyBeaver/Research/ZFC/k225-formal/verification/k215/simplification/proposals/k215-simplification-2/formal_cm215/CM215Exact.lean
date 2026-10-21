import MarkerTransfer

/-!
Literal native tables transcribed from the SHA-256-pinned K215 and CM215 files.
The native labels are represented in Fin 303. Only 215 labels have outgoing
rows; holes and the distinguished halt label 254 have no row. No added
working states are hidden in the ambient finite type.

K215: 9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2
CM215: e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252
-/
namespace CM215Exact
open MarkerTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def old : TM := fun q b =>
  match q.val with
  | 0 => if b then some ⟨true, true, 0⟩ else some ⟨true, true, 94⟩
  | 1 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 1⟩
  | 2 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 3⟩
  | 3 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 5⟩
  | 4 => if b then some ⟨false, false, 4⟩ else some ⟨true, true, 6⟩
  | 5 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 9⟩
  | 6 => if b then some ⟨false, true, 10⟩ else some ⟨false, true, 6⟩
  | 7 => if b then some ⟨true, true, 205⟩ else some ⟨false, true, 86⟩
  | 8 => if b then some ⟨true, true, 13⟩ else some ⟨false, true, 14⟩
  | 9 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 15⟩
  | 10 => if b then some ⟨false, true, 10⟩ else some ⟨false, false, 16⟩
  | 11 => if b then some ⟨true, true, 115⟩ else some ⟨false, false, 26⟩
  | 12 => if b then some ⟨true, true, 20⟩ else some ⟨false, true, 19⟩
  | 13 => if b then some ⟨true, false, 31⟩ else some ⟨false, false, 91⟩
  | 14 => if b then some ⟨false, true, 22⟩ else some ⟨false, false, 11⟩
  | 15 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 23⟩
  | 16 => if b then some ⟨false, false, 1⟩ else some ⟨true, false, 1⟩
  | 17 => if b then some ⟨false, true, 32⟩ else some ⟨false, true, 24⟩
  | 18 => if b then some ⟨true, true, 217⟩ else some ⟨false, true, 218⟩
  | 19 => if b then some ⟨true, true, 29⟩ else some ⟨false, true, 28⟩
  | 20 => if b then some ⟨true, true, 31⟩ else some ⟨false, true, 30⟩
  | 21 => if b then some ⟨false, true, 60⟩ else some ⟨false, true, 24⟩
  | 22 => if b then some ⟨true, true, 22⟩ else some ⟨false, true, 33⟩
  | 23 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 34⟩
  | 24 => if b then some ⟨false, true, 0⟩ else some ⟨false, false, 35⟩
  | 25 => if b then some ⟨true, true, 25⟩ else some ⟨false, true, 36⟩
  | 26 => if b then some ⟨true, true, 38⟩ else some ⟨false, true, 37⟩
  | 27 => if b then some ⟨false, false, 40⟩ else some ⟨false, true, 39⟩
  | 28 => if b then some ⟨true, true, 42⟩ else some ⟨false, true, 41⟩
  | 29 => if b then some ⟨true, true, 44⟩ else some ⟨false, true, 43⟩
  | 30 => if b then some ⟨true, true, 46⟩ else some ⟨false, true, 45⟩
  | 31 => if b then some ⟨true, true, 47⟩ else some ⟨false, true, 21⟩
  | 32 => if b then some ⟨true, true, 32⟩ else some ⟨false, true, 48⟩
  | 33 => if b then some ⟨true, true, 33⟩ else some ⟨false, true, 32⟩
  | 34 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 50⟩
  | 35 => if b then some ⟨true, false, 1⟩ else some ⟨true, true, 35⟩
  | 36 => if b then some ⟨true, true, 36⟩ else some ⟨false, true, 51⟩
  | 37 => if b then some ⟨true, true, 117⟩ else some ⟨false, true, 17⟩
  | 38 => if b then some ⟨true, true, 53⟩ else some ⟨false, true, 13⟩
  | 39 => if b then some ⟨false, true, 36⟩ else some ⟨false, false, 11⟩
  | 40 => if b then some ⟨true, false, 54⟩ else some ⟨false, false, 4⟩
  | 41 => if b then some ⟨false, true, 25⟩ else some ⟨false, true, 24⟩
  | 42 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 13⟩
  | 43 => if b then some ⟨true, true, 57⟩ else some ⟨false, true, 56⟩
  | 44 => if b then some ⟨true, true, 59⟩ else some ⟨false, true, 58⟩
  | 45 => if b then some ⟨false, true, 55⟩ else some ⟨false, true, 24⟩
  | 46 => if b then some ⟨true, true, 62⟩ else some ⟨false, true, 61⟩
  | 47 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 63⟩
  | 48 => if b then some ⟨true, true, 48⟩ else some ⟨false, true, 25⟩
  | 49 => if b then some ⟨false, true, 64⟩ else some ⟨false, false, 35⟩
  | 50 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 75⟩
  | 51 => if b then some ⟨true, true, 51⟩ else some ⟨false, true, 16⟩
  | 52 => if b then some ⟨true, true, 150⟩ else some ⟨false, true, 154⟩
  | 53 => if b then some ⟨true, true, 69⟩ else some ⟨false, true, 68⟩
  | 54 => if b then some ⟨true, false, 54⟩ else some ⟨false, false, 40⟩
  | 55 => if b then some ⟨true, true, 55⟩ else some ⟨false, true, 22⟩
  | 56 => if b then some ⟨false, true, 51⟩ else some ⟨false, false, 11⟩
  | 57 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 61⟩
  | 58 => if b then some ⟨true, true, 71⟩ else some ⟨false, true, 70⟩
  | 59 => if b then some ⟨true, true, 72⟩ else some ⟨false, true, 62⟩
  | 60 => if b then some ⟨true, true, 60⟩ else some ⟨false, true, 55⟩
  | 61 => if b then some ⟨false, true, 25⟩ else some ⟨false, true, 49⟩
  | 62 => if b then some ⟨true, false, 73⟩ else some ⟨false, false, 28⟩
  | 63 => if b then some ⟨true, false, 30⟩ else some ⟨false, false, 123⟩
  | 64 => if b then some ⟨true, true, 64⟩ else some ⟨false, true, 74⟩
  | 65 => if b then some ⟨true, true, 157⟩ else some ⟨false, true, 99⟩
  | 66 => if b then some ⟨true, false, 54⟩ else some ⟨true, true, 198⟩
  | 67 => if b then some ⟨true, true, 152⟩ else some ⟨false, true, 151⟩
  | 68 => if b then some ⟨true, true, 254⟩ else some ⟨false, true, 77⟩
  | 69 => if b then some ⟨true, true, 31⟩ else some ⟨false, false, 213⟩
  | 70 => if b then some ⟨true, true, 63⟩ else some ⟨false, true, 41⟩
  | 71 => if b then some ⟨true, true, 80⟩ else some ⟨false, false, 91⟩
  | 72 => if b then some ⟨true, false, 81⟩ else some ⟨false, true, 56⟩
  | 73 => if b then some ⟨true, true, 83⟩ else some ⟨false, true, 82⟩
  | 74 => if b then some ⟨true, true, 64⟩ else some ⟨true, true, 0⟩
  | 75 => if b then some ⟨true, true, 84⟩ else some ⟨false, true, 75⟩
  | 76 => if b then some ⟨true, false, 148⟩ else some ⟨false, false, 152⟩
  | 77 => if b then some ⟨true, true, 88⟩ else some ⟨false, true, 87⟩
  | 78 => if b then some ⟨true, true, 225⟩ else some ⟨false, true, 100⟩
  | 80 => if b then some ⟨true, false, 138⟩ else some ⟨false, true, 91⟩
  | 81 => if b then some ⟨true, true, 57⟩ else some ⟨false, false, 111⟩
  | 82 => if b then some ⟨false, true, 33⟩ else some ⟨false, true, 49⟩
  | 83 => if b then some ⟨false, false, 42⟩ else some ⟨false, true, 93⟩
  | 84 => if b then some ⟨true, true, 214⟩ else some ⟨false, true, 95⟩
  | 85 => if b then some ⟨true, true, 12⟩ else some ⟨false, true, 98⟩
  | 86 => if b then some ⟨true, true, 99⟩ else some ⟨false, true, 90⟩
  | 87 => if b then some ⟨true, true, 21⟩ else some ⟨false, true, 301⟩
  | 88 => if b then some ⟨true, true, 103⟩ else some ⟨false, true, 122⟩
  | 89 => if b then some ⟨true, true, 116⟩ else some ⟨false, true, 157⟩
  | 90 => if b then some ⟨true, true, 106⟩ else some ⟨false, true, 105⟩
  | 91 => if b then some ⟨true, true, 81⟩ else some ⟨false, true, 82⟩
  | 92 => if b then some ⟨true, true, 212⟩ else some ⟨false, true, 104⟩
  | 93 => if b then some ⟨true, true, 109⟩ else some ⟨false, true, 108⟩
  | 94 => if b then some ⟨false, true, 0⟩ else some ⟨false, true, 66⟩
  | 95 => if b then some ⟨true, true, 110⟩ else some ⟨false, true, 27⟩
  | 96 => if b then some ⟨false, false, 302⟩ else some ⟨false, true, 196⟩
  | 97 => if b then some ⟨true, false, 97⟩ else some ⟨true, false, 113⟩
  | 98 => if b then some ⟨true, true, 114⟩ else some ⟨false, true, 19⟩
  | 99 => if b then some ⟨true, true, 61⟩ else some ⟨false, true, 61⟩
  | 100 => if b then some ⟨true, true, 142⟩ else some ⟨false, true, 69⟩
  | 101 => if b then some ⟨true, true, 204⟩ else some ⟨false, true, 67⟩
  | 103 => if b then some ⟨false, false, 302⟩ else some ⟨false, true, 108⟩
  | 104 => if b then some ⟨true, true, 124⟩ else some ⟨false, true, 123⟩
  | 105 => if b then some ⟨true, true, 59⟩ else some ⟨false, true, 72⟩
  | 106 => if b then some ⟨true, true, 125⟩ else some ⟨false, true, 58⟩
  | 107 => if b then some ⟨true, true, 126⟩ else some ⟨false, true, 21⟩
  | 108 => if b then some ⟨false, false, 10⟩ else some ⟨false, true, 21⟩
  | 109 => if b then some ⟨true, true, 42⟩ else some ⟨false, true, 62⟩
  | 110 => if b then some ⟨true, true, 8⟩ else some ⟨false, true, 127⟩
  | 111 => if b then some ⟨true, true, 128⟩ else some ⟨false, true, 104⟩
  | 112 => if b then some ⟨true, true, 200⟩ else some ⟨false, true, 157⟩
  | 113 => if b then some ⟨false, false, 97⟩ else some ⟨false, false, 302⟩
  | 114 => if b then some ⟨true, true, 107⟩ else some ⟨false, true, 130⟩
  | 115 => if b then some ⟨true, true, 185⟩ else some ⟨false, true, 76⟩
  | 116 => if b then some ⟨true, true, 194⟩ else some ⟨false, true, 172⟩
  | 117 => if b then some ⟨false, false, 302⟩ else some ⟨false, true, 134⟩
  | 118 => if b then some ⟨true, true, 153⟩ else some ⟨false, true, 155⟩
  | 119 => if b then some ⟨true, true, 217⟩ else some ⟨false, true, 167⟩
  | 122 => if b then some ⟨false, false, 1⟩ else some ⟨false, false, 137⟩
  | 123 => if b then some ⟨true, true, 73⟩ else some ⟨false, true, 39⟩
  | 124 => if b then some ⟨true, true, 138⟩ else some ⟨false, true, 62⟩
  | 125 => if b then some ⟨true, true, 139⟩ else some ⟨false, true, 62⟩
  | 126 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 71⟩
  | 127 => if b then some ⟨true, true, 138⟩ else some ⟨false, true, 14⟩
  | 128 => if b then some ⟨true, true, 141⟩ else some ⟨false, true, 21⟩
  | 129 => if b then some ⟨true, true, 189⟩ else some ⟨false, true, 154⟩
  | 130 => if b then some ⟨true, false, 20⟩ else some ⟨false, true, 144⟩
  | 131 => if b then some ⟨true, true, 193⟩ else some ⟨false, true, 136⟩
  | 132 => if b then some ⟨true, true, 180⟩ else some ⟨false, true, 222⟩
  | 133 => if b then some ⟨true, true, 187⟩ else some ⟨false, true, 76⟩
  | 134 => if b then some ⟨true, true, 12⟩ else some ⟨false, true, 163⟩
  | 135 => if b then some ⟨true, true, 164⟩ else some ⟨false, true, 221⟩
  | 136 => if b then some ⟨true, true, 148⟩ else some ⟨false, true, 12⟩
  | 137 => if b then some ⟨true, true, 70⟩ else some ⟨false, true, 30⟩
  | 138 => if b then some ⟨true, false, 130⟩ else some ⟨false, true, 39⟩
  | 139 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 160⟩
  | 141 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 161⟩
  | 142 => if b then some ⟨true, true, 143⟩ else some ⟨false, true, 90⟩
  | 143 => if b then some ⟨true, true, 147⟩ else some ⟨false, true, 213⟩
  | 144 => if b then some ⟨false, true, 48⟩ else some ⟨false, true, 24⟩
  | 145 => if b then some ⟨true, true, 193⟩ else some ⟨false, true, 147⟩
  | 146 => if b then some ⟨true, true, 96⟩ else some ⟨false, true, 78⟩
  | 147 => if b then some ⟨true, true, 166⟩ else some ⟨false, true, 98⟩
  | 148 => if b then some ⟨true, true, 173⟩ else some ⟨false, true, 186⟩
  | 149 => if b then some ⟨true, true, 166⟩ else some ⟨false, true, 12⟩
  | 150 => if b then some ⟨true, false, 173⟩ else some ⟨false, true, 90⟩
  | 151 => if b then some ⟨true, true, 165⟩ else some ⟨false, true, 90⟩
  | 152 => if b then some ⟨true, false, 170⟩ else some ⟨false, false, 159⟩
  | 153 => if b then some ⟨true, true, 90⟩ else some ⟨false, true, 86⟩
  | 154 => if b then some ⟨true, true, 12⟩ else some ⟨false, true, 166⟩
  | 155 => if b then some ⟨true, true, 150⟩ else some ⟨false, true, 85⟩
  | 156 => if b then some ⟨true, true, 176⟩ else some ⟨false, true, 171⟩
  | 157 => if b then some ⟨true, false, 148⟩ else some ⟨false, false, 67⟩
  | 158 => if b then some ⟨true, true, 220⟩ else some ⟨false, true, 155⟩
  | 159 => if b then some ⟨true, true, 118⟩ else some ⟨false, true, 166⟩
  | 160 => if b then some ⟨true, true, 99⟩ else some ⟨false, true, 99⟩
  | 161 => if b then some ⟨false, true, 32⟩ else some ⟨false, true, 49⟩
  | 162 => if b then some ⟨false, false, 302⟩ else some ⟨false, true, 174⟩
  | 163 => if b then some ⟨true, true, 162⟩ else some ⟨false, true, 17⟩
  | 164 => if b then some ⟨true, true, 98⟩ else some ⟨false, false, 201⟩
  | 165 => if b then some ⟨true, true, 190⟩ else some ⟨false, true, 176⟩
  | 166 => if b then some ⟨true, true, 179⟩ else some ⟨false, true, 19⟩
  | 167 => if b then some ⟨true, true, 172⟩ else some ⟨false, true, 184⟩
  | 168 => if b then some ⟨true, true, 98⟩ else some ⟨false, true, 166⟩
  | 169 => if b then some ⟨true, true, 171⟩ else some ⟨false, true, 131⟩
  | 170 => if b then some ⟨true, true, 169⟩ else some ⟨false, true, 99⟩
  | 171 => if b then some ⟨true, true, 149⟩ else some ⟨false, false, 7⟩
  | 172 => if b then some ⟨true, true, 184⟩ else some ⟨false, false, 112⟩
  | 173 => if b then some ⟨true, true, 182⟩ else some ⟨false, true, 153⟩
  | 174 => if b then some ⟨true, true, 135⟩ else some ⟨false, true, 11⟩
  | 176 => if b then some ⟨true, true, 150⟩ else some ⟨false, true, 168⟩
  | 177 => if b then some ⟨true, true, 172⟩ else some ⟨false, true, 203⟩
  | 178 => if b then some ⟨true, true, 189⟩ else some ⟨false, true, 189⟩
  | 179 => if b then some ⟨true, true, 128⟩ else some ⟨false, true, 194⟩
  | 180 => if b then some ⟨true, true, 172⟩ else some ⟨false, true, 152⟩
  | 181 => if b then some ⟨true, true, 89⟩ else some ⟨false, true, 177⟩
  | 182 => if b then some ⟨true, true, 61⟩ else some ⟨false, true, 76⟩
  | 184 => if b then some ⟨true, true, 90⟩ else some ⟨false, true, 152⟩
  | 185 => if b then some ⟨true, true, 146⟩ else some ⟨false, true, 168⟩
  | 186 => if b then some ⟨true, true, 86⟩ else some ⟨false, true, 147⟩
  | 187 => if b then some ⟨true, true, 76⟩ else some ⟨false, true, 186⟩
  | 188 => if b then some ⟨true, true, 181⟩ else some ⟨false, true, 151⟩
  | 189 => if b then some ⟨true, false, 156⟩ else some ⟨false, true, 149⟩
  | 190 => if b then some ⟨true, true, 52⟩ else some ⟨false, true, 99⟩
  | 193 => if b then some ⟨true, true, 52⟩ else some ⟨false, true, 176⟩
  | 194 => if b then some ⟨true, false, 137⟩ else some ⟨false, true, 17⟩
  | 195 => if b then some ⟨true, true, 188⟩ else some ⟨false, true, 150⟩
  | 196 => if b then some ⟨true, true, 122⟩ else some ⟨false, true, 77⟩
  | 197 => if b then some ⟨true, true, 130⟩ else some ⟨false, true, 109⟩
  | 198 => if b then some ⟨true, false, 113⟩ else some ⟨true, false, 40⟩
  | 199 => if b then some ⟨true, true, 166⟩ else some ⟨false, true, 180⟩
  | 200 => if b then some ⟨true, true, 119⟩ else some ⟨false, true, 157⟩
  | 201 => if b then some ⟨true, true, 196⟩ else some ⟨false, true, 195⟩
  | 203 => if b then some ⟨true, true, 101⟩ else some ⟨false, true, 207⟩
  | 204 => if b then some ⟨true, true, 215⟩ else some ⟨false, true, 153⟩
  | 205 => if b then some ⟨true, true, 206⟩ else some ⟨false, true, 164⟩
  | 206 => if b then some ⟨true, true, 199⟩ else some ⟨false, true, 186⟩
  | 207 => if b then some ⟨true, true, 7⟩ else some ⟨false, true, 65⟩
  | 209 => if b then some ⟨true, true, 133⟩ else some ⟨false, true, 157⟩
  | 210 => if b then some ⟨true, true, 201⟩ else some ⟨false, true, 171⟩
  | 211 => if b then some ⟨true, true, 129⟩ else some ⟨false, true, 159⟩
  | 212 => if b then some ⟨true, true, 98⟩ else some ⟨false, true, 107⟩
  | 213 => if b then some ⟨true, true, 90⟩ else some ⟨false, true, 92⟩
  | 214 => if b then some ⟨true, true, 26⟩ else some ⟨false, true, 111⟩
  | 215 => if b then some ⟨true, true, 112⟩ else some ⟨false, true, 223⟩
  | 216 => if b then some ⟨true, true, 178⟩ else some ⟨false, true, 157⟩
  | 217 => if b then some ⟨true, true, 167⟩ else some ⟨false, true, 216⟩
  | 218 => if b then some ⟨true, true, 145⟩ else some ⟨false, true, 147⟩
  | 220 => if b then some ⟨true, true, 18⟩ else some ⟨false, true, 211⟩
  | 221 => if b then some ⟨true, true, 28⟩ else some ⟨false, true, 213⟩
  | 222 => if b then some ⟨true, true, 209⟩ else some ⟨false, true, 170⟩
  | 223 => if b then some ⟨true, true, 158⟩ else some ⟨false, true, 132⟩
  | 225 => if b then some ⟨true, true, 197⟩ else some ⟨false, true, 210⟩
  | 301 => if b then some ⟨true, true, 103⟩ else some ⟨false, true, 45⟩
  | 302 => if b then some ⟨false, false, 302⟩ else some ⟨false, false, 4⟩
  | _ => none

def new : TM := fun q b =>
  match q.val with
  | 0 => if b then some ⟨true, true, 0⟩ else some ⟨true, true, 94⟩
  | 1 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 1⟩
  | 2 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 3⟩
  | 3 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 5⟩
  | 4 => if b then some ⟨false, false, 4⟩ else some ⟨true, true, 6⟩
  | 5 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 9⟩
  | 6 => if b then some ⟨false, true, 10⟩ else some ⟨false, true, 6⟩
  | 7 => if b then some ⟨true, true, 205⟩ else some ⟨false, true, 86⟩
  | 8 => if b then some ⟨true, true, 13⟩ else some ⟨false, true, 14⟩
  | 9 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 15⟩
  | 10 => if b then some ⟨false, true, 10⟩ else some ⟨false, false, 16⟩
  | 11 => if b then some ⟨true, true, 115⟩ else some ⟨false, false, 26⟩
  | 12 => if b then some ⟨true, true, 20⟩ else some ⟨false, true, 19⟩
  | 13 => if b then some ⟨true, false, 31⟩ else some ⟨false, false, 91⟩
  | 14 => if b then some ⟨false, true, 22⟩ else some ⟨false, false, 11⟩
  | 15 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 23⟩
  | 16 => if b then some ⟨false, false, 1⟩ else some ⟨true, false, 1⟩
  | 17 => if b then some ⟨false, true, 32⟩ else some ⟨false, true, 24⟩
  | 18 => if b then some ⟨true, true, 217⟩ else some ⟨false, true, 218⟩
  | 19 => if b then some ⟨true, true, 29⟩ else some ⟨false, true, 28⟩
  | 20 => if b then some ⟨true, true, 31⟩ else some ⟨false, true, 30⟩
  | 21 => if b then some ⟨false, true, 60⟩ else some ⟨false, true, 24⟩
  | 22 => if b then some ⟨true, true, 22⟩ else some ⟨false, true, 33⟩
  | 23 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 34⟩
  | 24 => if b then some ⟨false, true, 0⟩ else some ⟨false, false, 35⟩
  | 25 => if b then some ⟨true, true, 25⟩ else some ⟨false, true, 36⟩
  | 26 => if b then some ⟨true, true, 38⟩ else some ⟨false, true, 37⟩
  | 27 => if b then some ⟨false, false, 40⟩ else some ⟨false, true, 39⟩
  | 28 => if b then some ⟨true, true, 42⟩ else some ⟨false, true, 41⟩
  | 29 => if b then some ⟨true, true, 44⟩ else some ⟨false, true, 43⟩
  | 30 => if b then some ⟨true, true, 46⟩ else some ⟨false, true, 45⟩
  | 31 => if b then some ⟨true, true, 47⟩ else some ⟨false, true, 21⟩
  | 32 => if b then some ⟨true, true, 32⟩ else some ⟨false, true, 48⟩
  | 33 => if b then some ⟨true, true, 33⟩ else some ⟨false, true, 32⟩
  | 34 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 50⟩
  | 35 => if b then some ⟨true, false, 1⟩ else some ⟨true, true, 35⟩
  | 36 => if b then some ⟨true, true, 36⟩ else some ⟨false, true, 51⟩
  | 37 => if b then some ⟨true, true, 117⟩ else some ⟨false, true, 17⟩
  | 38 => if b then some ⟨true, true, 53⟩ else some ⟨false, true, 13⟩
  | 39 => if b then some ⟨false, true, 36⟩ else some ⟨false, false, 11⟩
  | 40 => if b then some ⟨true, false, 54⟩ else some ⟨false, false, 4⟩
  | 41 => if b then some ⟨false, true, 25⟩ else some ⟨false, true, 24⟩
  | 42 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 13⟩
  | 43 => if b then some ⟨true, true, 57⟩ else some ⟨false, true, 56⟩
  | 44 => if b then some ⟨true, true, 59⟩ else some ⟨false, true, 58⟩
  | 45 => if b then some ⟨false, true, 55⟩ else some ⟨false, true, 24⟩
  | 46 => if b then some ⟨true, true, 62⟩ else some ⟨false, true, 61⟩
  | 47 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 63⟩
  | 48 => if b then some ⟨true, true, 48⟩ else some ⟨false, true, 25⟩
  | 49 => if b then some ⟨false, true, 64⟩ else some ⟨false, false, 35⟩
  | 50 => if b then some ⟨true, false, 2⟩ else some ⟨false, false, 75⟩
  | 51 => if b then some ⟨true, true, 51⟩ else some ⟨false, true, 16⟩
  | 52 => if b then some ⟨true, true, 150⟩ else some ⟨false, false, 176⟩
  | 53 => if b then some ⟨true, true, 69⟩ else some ⟨false, true, 68⟩
  | 54 => if b then some ⟨true, false, 54⟩ else some ⟨false, false, 40⟩
  | 55 => if b then some ⟨true, true, 55⟩ else some ⟨false, true, 22⟩
  | 56 => if b then some ⟨false, true, 51⟩ else some ⟨false, false, 11⟩
  | 57 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 61⟩
  | 58 => if b then some ⟨true, true, 71⟩ else some ⟨false, true, 70⟩
  | 59 => if b then some ⟨true, true, 72⟩ else some ⟨false, true, 62⟩
  | 60 => if b then some ⟨true, true, 60⟩ else some ⟨false, true, 55⟩
  | 61 => if b then some ⟨false, true, 25⟩ else some ⟨false, true, 49⟩
  | 62 => if b then some ⟨true, false, 73⟩ else some ⟨false, false, 28⟩
  | 63 => if b then some ⟨true, false, 30⟩ else some ⟨false, false, 123⟩
  | 64 => if b then some ⟨true, true, 64⟩ else some ⟨false, true, 74⟩
  | 65 => if b then some ⟨true, true, 157⟩ else some ⟨false, true, 99⟩
  | 66 => if b then some ⟨true, false, 54⟩ else some ⟨true, true, 198⟩
  | 67 => if b then some ⟨true, true, 152⟩ else some ⟨false, true, 151⟩
  | 68 => if b then some ⟨true, true, 254⟩ else some ⟨false, true, 77⟩
  | 69 => if b then some ⟨true, true, 31⟩ else some ⟨false, false, 213⟩
  | 70 => if b then some ⟨true, true, 63⟩ else some ⟨false, true, 41⟩
  | 71 => if b then some ⟨true, true, 80⟩ else some ⟨false, false, 91⟩
  | 72 => if b then some ⟨true, false, 81⟩ else some ⟨false, true, 56⟩
  | 73 => if b then some ⟨true, true, 83⟩ else some ⟨false, true, 82⟩
  | 74 => if b then some ⟨true, true, 64⟩ else some ⟨true, true, 0⟩
  | 75 => if b then some ⟨true, true, 84⟩ else some ⟨false, true, 75⟩
  | 76 => if b then some ⟨true, false, 148⟩ else some ⟨false, false, 152⟩
  | 77 => if b then some ⟨true, true, 88⟩ else some ⟨false, true, 87⟩
  | 78 => if b then some ⟨true, true, 225⟩ else some ⟨false, true, 100⟩
  | 80 => if b then some ⟨true, false, 138⟩ else some ⟨false, true, 91⟩
  | 81 => if b then some ⟨true, true, 57⟩ else some ⟨false, false, 111⟩
  | 82 => if b then some ⟨false, true, 33⟩ else some ⟨false, true, 49⟩
  | 83 => if b then some ⟨false, false, 42⟩ else some ⟨false, true, 93⟩
  | 84 => if b then some ⟨true, true, 214⟩ else some ⟨false, true, 95⟩
  | 85 => if b then some ⟨true, true, 12⟩ else some ⟨false, true, 98⟩
  | 86 => if b then some ⟨true, true, 99⟩ else some ⟨false, true, 90⟩
  | 87 => if b then some ⟨true, true, 21⟩ else some ⟨false, true, 301⟩
  | 88 => if b then some ⟨true, true, 103⟩ else some ⟨false, true, 122⟩
  | 89 => if b then some ⟨true, true, 116⟩ else some ⟨false, true, 157⟩
  | 90 => if b then some ⟨true, true, 106⟩ else some ⟨false, true, 105⟩
  | 91 => if b then some ⟨true, true, 81⟩ else some ⟨false, true, 82⟩
  | 92 => if b then some ⟨true, true, 212⟩ else some ⟨false, true, 104⟩
  | 93 => if b then some ⟨true, true, 109⟩ else some ⟨false, true, 108⟩
  | 94 => if b then some ⟨false, true, 0⟩ else some ⟨false, true, 66⟩
  | 95 => if b then some ⟨true, true, 110⟩ else some ⟨false, true, 27⟩
  | 96 => if b then some ⟨false, false, 302⟩ else some ⟨false, true, 196⟩
  | 97 => if b then some ⟨true, false, 97⟩ else some ⟨true, false, 113⟩
  | 98 => if b then some ⟨true, true, 114⟩ else some ⟨false, true, 19⟩
  | 99 => if b then some ⟨true, true, 61⟩ else some ⟨false, true, 61⟩
  | 100 => if b then some ⟨true, true, 142⟩ else some ⟨false, true, 69⟩
  | 101 => if b then some ⟨true, true, 204⟩ else some ⟨false, true, 67⟩
  | 103 => if b then some ⟨false, false, 302⟩ else some ⟨false, true, 108⟩
  | 104 => if b then some ⟨true, true, 124⟩ else some ⟨false, true, 123⟩
  | 105 => if b then some ⟨true, true, 59⟩ else some ⟨false, true, 72⟩
  | 106 => if b then some ⟨true, true, 125⟩ else some ⟨false, true, 58⟩
  | 107 => if b then some ⟨true, true, 126⟩ else some ⟨false, true, 21⟩
  | 108 => if b then some ⟨false, false, 10⟩ else some ⟨false, true, 21⟩
  | 109 => if b then some ⟨true, true, 42⟩ else some ⟨false, true, 62⟩
  | 110 => if b then some ⟨true, true, 8⟩ else some ⟨false, true, 127⟩
  | 111 => if b then some ⟨true, true, 128⟩ else some ⟨false, true, 104⟩
  | 112 => if b then some ⟨true, true, 200⟩ else some ⟨false, true, 157⟩
  | 113 => if b then some ⟨false, false, 97⟩ else some ⟨false, false, 302⟩
  | 114 => if b then some ⟨true, true, 107⟩ else some ⟨false, true, 130⟩
  | 115 => if b then some ⟨true, true, 185⟩ else some ⟨false, true, 76⟩
  | 116 => if b then some ⟨true, true, 194⟩ else some ⟨false, true, 172⟩
  | 117 => if b then some ⟨false, false, 302⟩ else some ⟨false, true, 134⟩
  | 118 => if b then some ⟨true, true, 153⟩ else some ⟨false, true, 155⟩
  | 119 => if b then some ⟨true, true, 217⟩ else some ⟨false, true, 167⟩
  | 122 => if b then some ⟨false, false, 1⟩ else some ⟨false, false, 137⟩
  | 123 => if b then some ⟨true, true, 73⟩ else some ⟨false, true, 39⟩
  | 124 => if b then some ⟨true, true, 138⟩ else some ⟨false, true, 62⟩
  | 125 => if b then some ⟨true, true, 139⟩ else some ⟨false, true, 62⟩
  | 126 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 71⟩
  | 127 => if b then some ⟨true, true, 138⟩ else some ⟨false, true, 14⟩
  | 128 => if b then some ⟨true, true, 141⟩ else some ⟨false, true, 21⟩
  | 129 => if b then some ⟨true, true, 189⟩ else some ⟨false, true, 154⟩
  | 130 => if b then some ⟨true, false, 20⟩ else some ⟨false, true, 144⟩
  | 131 => if b then some ⟨true, true, 193⟩ else some ⟨false, true, 136⟩
  | 132 => if b then some ⟨true, true, 180⟩ else some ⟨false, true, 222⟩
  | 133 => if b then some ⟨true, true, 187⟩ else some ⟨false, true, 76⟩
  | 134 => if b then some ⟨true, true, 12⟩ else some ⟨false, true, 163⟩
  | 135 => if b then some ⟨true, true, 164⟩ else some ⟨false, true, 221⟩
  | 136 => if b then some ⟨true, true, 148⟩ else some ⟨false, true, 12⟩
  | 137 => if b then some ⟨true, true, 70⟩ else some ⟨false, true, 30⟩
  | 138 => if b then some ⟨true, false, 130⟩ else some ⟨false, true, 39⟩
  | 139 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 160⟩
  | 141 => if b then some ⟨false, false, 16⟩ else some ⟨false, true, 161⟩
  | 142 => if b then some ⟨true, true, 143⟩ else some ⟨false, true, 90⟩
  | 143 => if b then some ⟨true, true, 147⟩ else some ⟨false, true, 213⟩
  | 144 => if b then some ⟨false, true, 48⟩ else some ⟨false, true, 24⟩
  | 145 => if b then some ⟨true, true, 193⟩ else some ⟨false, true, 147⟩
  | 146 => if b then some ⟨true, true, 96⟩ else some ⟨false, true, 78⟩
  | 147 => if b then some ⟨true, true, 166⟩ else some ⟨false, true, 98⟩
  | 148 => if b then some ⟨true, true, 173⟩ else some ⟨false, true, 186⟩
  | 149 => if b then some ⟨true, true, 166⟩ else some ⟨false, true, 12⟩
  | 150 => if b then some ⟨true, false, 173⟩ else some ⟨false, true, 90⟩
  | 151 => if b then some ⟨true, true, 165⟩ else some ⟨false, true, 90⟩
  | 152 => if b then some ⟨true, false, 170⟩ else some ⟨false, false, 159⟩
  | 153 => if b then some ⟨true, true, 90⟩ else some ⟨false, true, 86⟩
  | 154 => if b then some ⟨true, true, 12⟩ else some ⟨false, true, 166⟩
  | 155 => if b then some ⟨true, true, 150⟩ else some ⟨false, true, 85⟩
  | 156 => if b then some ⟨true, true, 52⟩ else some ⟨false, true, 171⟩
  | 157 => if b then some ⟨true, false, 148⟩ else some ⟨false, false, 67⟩
  | 158 => if b then some ⟨true, true, 220⟩ else some ⟨false, true, 155⟩
  | 159 => if b then some ⟨true, true, 118⟩ else some ⟨false, true, 166⟩
  | 160 => if b then some ⟨true, true, 99⟩ else some ⟨false, true, 99⟩
  | 161 => if b then some ⟨false, true, 32⟩ else some ⟨false, true, 49⟩
  | 162 => if b then some ⟨false, false, 302⟩ else some ⟨false, true, 174⟩
  | 163 => if b then some ⟨true, true, 162⟩ else some ⟨false, true, 17⟩
  | 164 => if b then some ⟨true, true, 98⟩ else some ⟨false, false, 201⟩
  | 165 => if b then some ⟨true, true, 190⟩ else some ⟨false, true, 52⟩
  | 166 => if b then some ⟨true, true, 179⟩ else some ⟨false, true, 19⟩
  | 167 => if b then some ⟨true, true, 172⟩ else some ⟨false, true, 184⟩
  | 168 => if b then some ⟨true, true, 98⟩ else some ⟨false, true, 166⟩
  | 169 => if b then some ⟨true, true, 171⟩ else some ⟨false, true, 131⟩
  | 170 => if b then some ⟨true, true, 169⟩ else some ⟨false, true, 99⟩
  | 171 => if b then some ⟨true, true, 149⟩ else some ⟨false, false, 7⟩
  | 172 => if b then some ⟨true, true, 184⟩ else some ⟨false, false, 112⟩
  | 173 => if b then some ⟨true, true, 182⟩ else some ⟨false, true, 153⟩
  | 174 => if b then some ⟨true, true, 135⟩ else some ⟨false, true, 11⟩
  | 176 => if b then some ⟨true, true, 129⟩ else some ⟨false, true, 185⟩
  | 177 => if b then some ⟨true, true, 172⟩ else some ⟨false, true, 203⟩
  | 178 => if b then some ⟨true, true, 189⟩ else some ⟨false, true, 189⟩
  | 179 => if b then some ⟨true, true, 128⟩ else some ⟨false, true, 194⟩
  | 180 => if b then some ⟨true, true, 172⟩ else some ⟨false, true, 152⟩
  | 181 => if b then some ⟨true, true, 89⟩ else some ⟨false, true, 177⟩
  | 182 => if b then some ⟨true, true, 61⟩ else some ⟨false, true, 76⟩
  | 184 => if b then some ⟨true, true, 90⟩ else some ⟨false, true, 152⟩
  | 185 => if b then some ⟨true, true, 146⟩ else some ⟨false, true, 168⟩
  | 186 => if b then some ⟨true, true, 86⟩ else some ⟨false, true, 147⟩
  | 187 => if b then some ⟨true, true, 76⟩ else some ⟨false, true, 186⟩
  | 188 => if b then some ⟨true, true, 181⟩ else some ⟨false, true, 151⟩
  | 189 => if b then some ⟨true, false, 156⟩ else some ⟨false, true, 149⟩
  | 190 => if b then some ⟨true, true, 52⟩ else some ⟨false, true, 99⟩
  | 193 => if b then some ⟨true, true, 52⟩ else some ⟨false, true, 52⟩
  | 194 => if b then some ⟨true, false, 137⟩ else some ⟨false, true, 17⟩
  | 195 => if b then some ⟨true, true, 188⟩ else some ⟨false, true, 150⟩
  | 196 => if b then some ⟨true, true, 122⟩ else some ⟨false, true, 77⟩
  | 197 => if b then some ⟨true, true, 130⟩ else some ⟨false, true, 109⟩
  | 198 => if b then some ⟨true, false, 113⟩ else some ⟨true, false, 40⟩
  | 199 => if b then some ⟨true, true, 166⟩ else some ⟨false, true, 180⟩
  | 200 => if b then some ⟨true, true, 119⟩ else some ⟨false, true, 157⟩
  | 201 => if b then some ⟨true, true, 196⟩ else some ⟨false, true, 195⟩
  | 203 => if b then some ⟨true, true, 101⟩ else some ⟨false, true, 207⟩
  | 204 => if b then some ⟨true, true, 215⟩ else some ⟨false, true, 153⟩
  | 205 => if b then some ⟨true, true, 206⟩ else some ⟨false, true, 164⟩
  | 206 => if b then some ⟨true, true, 199⟩ else some ⟨false, true, 186⟩
  | 207 => if b then some ⟨true, true, 7⟩ else some ⟨false, true, 65⟩
  | 209 => if b then some ⟨true, true, 133⟩ else some ⟨false, true, 157⟩
  | 210 => if b then some ⟨true, true, 201⟩ else some ⟨false, true, 171⟩
  | 211 => if b then some ⟨true, true, 129⟩ else some ⟨false, true, 159⟩
  | 212 => if b then some ⟨true, true, 98⟩ else some ⟨false, true, 107⟩
  | 213 => if b then some ⟨true, true, 90⟩ else some ⟨false, true, 92⟩
  | 214 => if b then some ⟨true, true, 26⟩ else some ⟨false, true, 111⟩
  | 215 => if b then some ⟨true, true, 112⟩ else some ⟨false, true, 223⟩
  | 216 => if b then some ⟨true, true, 178⟩ else some ⟨false, true, 157⟩
  | 217 => if b then some ⟨true, true, 167⟩ else some ⟨false, true, 216⟩
  | 218 => if b then some ⟨true, true, 145⟩ else some ⟨false, true, 147⟩
  | 220 => if b then some ⟨true, true, 18⟩ else some ⟨false, true, 211⟩
  | 221 => if b then some ⟨true, true, 28⟩ else some ⟨false, true, 213⟩
  | 222 => if b then some ⟨true, true, 209⟩ else some ⟨false, true, 170⟩
  | 223 => if b then some ⟨true, true, 158⟩ else some ⟨false, true, 132⟩
  | 225 => if b then some ⟨true, true, 197⟩ else some ⟨false, true, 210⟩
  | 301 => if b then some ⟨true, true, 103⟩ else some ⟨false, true, 45⟩
  | 302 => if b then some ⟨false, false, 302⟩ else some ⟨false, false, 4⟩
  | _ => none

theorem facts : Facts old new where
  common := by decide
  old52 := by decide
  old176 := by decide
  new52 := by decide
  new176 := by decide
  new129 := by decide
  new185 := by decide
  in52 := by decide
  in176 := by decide
  in156 := by decide

def workingCount (M : TM) : Nat :=
  ((List.finRange 303).filter fun q => (M q false).isSome || (M q true).isSome).length

theorem old_count : workingCount old = 215 := by decide
theorem new_count : workingCount new = 215 := by decide

theorem old_total_on_working : ∀ q, (old q false).isSome = (old q true).isSome := by decide
theorem new_total_on_working : ∀ q, (new q false).isSome = (new q true).isSome := by decide

def closedRow (M : TM) : Option Row → Prop
  | none => True
  | some r => r.target = 254 ∨ (M r.target false).isSome = true

instance (M : TM) (r : Option Row) : Decidable (closedRow M r) := by
  cases r <;> unfold closedRow <;> infer_instance

theorem old_closed : ∀ q b, closedRow old (old q b) := by decide
theorem new_closed : ∀ q b, closedRow new (new q b) := by decide

theorem old_halt : ∀ b, old 254 b = none := by decide
theorem new_halt : ∀ b, new 254 b = none := by decide

/-- Whole-tape equivalence for the two exact literal tables, from native start 0. -/
theorem all_tapes_equihalt (h : Int) (t : Tape) :
    (∃ n, Halt old (PositiveSimulation.iter (next old) n ⟨0, h, t⟩)) ↔
    (∃ n, Halt new (PositiveSimulation.iter (next new) n ⟨0, h, t⟩)) :=
  MarkerTransfer.all_tapes_equihalt facts h t

/-- Exact-table blank halting equivalence. This is a transfer theorem,
not a new formalization of the inherited numerical-calculus/ZFC calibration. -/
theorem blank_equihalt :
    (∃ n, Halt old (PositiveSimulation.iter (next old) n ⟨0, 0, fun _ => false⟩)) ↔
    (∃ n, Halt new (PositiveSimulation.iter (next new) n ⟨0, 0, fun _ => false⟩)) :=
  all_tapes_equihalt 0 (fun _ => false)

#print axioms facts
#print axioms old_count
#print axioms new_count
#print axioms all_tapes_equihalt
#print axioms blank_equihalt
end CM215Exact
