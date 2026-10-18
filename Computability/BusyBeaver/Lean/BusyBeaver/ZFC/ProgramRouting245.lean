import BusyBeaver.ZFC.RMBisim

/-!
Exact logical decoder for the routed 245 candidate, arrival 8286787dd0.
The pinned 6460-leaf certificate is stored as 203 distinct binary subtrees;
its complete unfolding still has 6459 internal nodes and maximum depth 51.
203 is a register-program storage count, not a binary Turing-machine state count.
All logical register indices and break/continue depths are retained exactly.
The proof below identifies this program's decoder for every fuel >= 51, then
uses RegisterPath's full consume/execute semantics for arbitrary pointers and
register files. No equivalence to Prog254, machine simulation, or consistency
calibration is asserted by this unit.

Original machine/calculus: Mira-Cult; public verification: Jeff Ketchersid;
compiler framework: Andrew James Wade. The new grammar/routing submission and
prior ProveIt constructions retain their original attribution and notices.
-/
set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC
namespace ProgramRouting245
open RegisterPath

abbrev Row := Edge × Edge
private def row000 : Row := ((.decnz 8), (.brk 1))
private def row001 : Row := ((.inc 6), (.cont 3))
private def row002 : Row := ((.inc 8), (.node 1))
private def row003 : Row := ((.decnz 0), (.node 2))
private def row004 : Row := ((.inc 0), (.cont 2))
private def row005 : Row := ((.decnz 6), (.node 4))
private def row006 : Row := ((.node 5), (.inc 0))
private def row007 : Row := ((.node 3), (.node 6))
private def row008 : Row := ((.node 0), (.node 7))
private def row009 : Row := ((.decnz 6), (.brk 1))
private def row010 : Row := ((.inc 6), (.cont 2))
private def row011 : Row := ((.decnz 7), (.node 10))
private def row012 : Row := ((.node 9), (.node 11))
private def row013 : Row := ((.node 12), (.cont 3))
private def row014 : Row := ((.inc 7), (.node 13))
private def row015 : Row := ((.decnz 8), (.node 14))
private def row016 : Row := ((.inc 8), (.cont 2))
private def row017 : Row := ((.decnz 7), (.node 16))
private def row018 : Row := ((.node 15), (.node 17))
private def row019 : Row := ((.inc 3), (.cont 2))
private def row020 : Row := ((.decnz 6), (.node 19))
private def row021 : Row := ((.node 18), (.node 20))
private def row022 : Row := ((.inc 4), (.cont 2))
private def row023 : Row := ((.decnz 6), (.node 22))
private def row024 : Row := ((.node 18), (.node 23))
private def row025 : Row := ((.decnz 1), (.node 10))
private def row026 : Row := ((.inc 1), (.cont 2))
private def row027 : Row := ((.decnz 2), (.node 26))
private def row028 : Row := ((.inc 7), (.node 1))
private def row029 : Row := ((.decnz 1), (.node 28))
private def row030 : Row := ((.decnz 6), (.node 26))
private def row031 : Row := ((.inc 7), (.node 30))
private def row032 : Row := ((.node 31), (.cont 3))
private def row033 : Row := ((.decnz 6), (.node 32))
private def row034 : Row := ((.node 29), (.node 33))
private def row035 : Row := ((.inc 2), (.cont 2))
private def row036 : Row := ((.decnz 7), (.node 35))
private def row037 : Row := ((.node 34), (.node 36))
private def row038 : Row := ((.node 27), (.node 37))
private def row039 : Row := ((.node 25), (.node 38))
private def row040 : Row := ((.inc 1), (.node 1))
private def row041 : Row := ((.decnz 4), (.node 40))
private def row042 : Row := ((.node 41), (.node 23))
private def row043 : Row := ((.decnz 5), (.node 40))
private def row044 : Row := ((.inc 5), (.cont 2))
private def row045 : Row := ((.decnz 6), (.node 44))
private def row046 : Row := ((.node 43), (.node 45))
private def row047 : Row := ((.node 39), (.node 46))
private def row048 : Row := ((.node 42), (.node 47))
private def row049 : Row := ((.node 39), (.node 48))
private def row050 : Row := ((.decnz 2), (.node 14))
private def row051 : Row := ((.node 50), (.node 36))
private def row052 : Row := ((.inc 1), (.inc 1))
private def row053 : Row := ((.node 52), (.node 52))
private def row054 : Row := ((.node 53), (.cont 2))
private def row055 : Row := ((.decnz 7), (.node 54))
private def row056 : Row := ((.node 34), (.node 55))
private def row057 : Row := ((.node 51), (.node 56))
private def row058 : Row := ((.node 57), (.node 52))
private def row059 : Row := ((.node 49), (.node 58))
private def row060 : Row := ((.node 18), (.node 45))
private def row061 : Row := ((.decnz 3), (.node 40))
private def row062 : Row := ((.node 61), (.node 20))
private def row063 : Row := ((.node 39), (.node 62))
private def row064 : Row := ((.node 63), (.node 39))
private def row065 : Row := ((.node 18), (.node 30))
private def row066 : Row := ((.node 65), (.node 57))
private def row067 : Row := ((.node 64), (.node 66))
private def row068 : Row := ((.node 39), (.node 42))
private def row069 : Row := ((.node 68), (.node 57))
private def row070 : Row := ((.node 67), (.node 69))
private def row071 : Row := ((.node 60), (.node 70))
private def row072 : Row := ((.node 68), (.node 63))
private def row073 : Row := ((.node 72), (.node 57))
private def row074 : Row := ((.node 47), (.node 63))
private def row075 : Row := ((.node 57), (.node 57))
private def row076 : Row := ((.node 57), (.inc 1))
private def row077 : Row := ((.node 68), (.node 76))
private def row078 : Row := ((.node 63), (.node 77))
private def row079 : Row := ((.node 64), (.node 46))
private def row080 : Row := ((.node 79), (.node 76))
private def row081 : Row := ((.node 52), (.node 80))
private def row082 : Row := ((.node 78), (.node 81))
private def row083 : Row := ((.node 57), (.node 82))
private def row084 : Row := ((.node 59), (.inc 1))
private def row085 : Row := ((.node 75), (.node 68))
private def row086 : Row := ((.node 84), (.node 85))
private def row087 : Row := ((.node 52), (.node 86))
private def row088 : Row := ((.node 39), (.inc 1))
private def row089 : Row := ((.node 88), (.node 57))
private def row090 : Row := ((.node 58), (.node 89))
private def row091 : Row := ((.node 89), (.node 90))
private def row092 : Row := ((.node 91), (.node 47))
private def row093 : Row := ((.node 59), (.node 92))
private def row094 : Row := ((.node 49), (.node 76))
private def row095 : Row := ((.node 85), (.node 74))
private def row096 : Row := ((.node 94), (.node 95))
private def row097 : Row := ((.node 58), (.node 57))
private def row098 : Row := ((.node 72), (.node 58))
private def row099 : Row := ((.node 97), (.node 84))
private def row100 : Row := ((.node 98), (.node 99))
private def row101 : Row := ((.node 47), (.node 100))
private def row102 : Row := ((.node 78), (.node 80))
private def row103 : Row := ((.node 102), (.node 95))
private def row104 : Row := ((.node 101), (.node 103))
private def row105 : Row := ((.node 52), (.node 104))
private def row106 : Row := ((.node 57), (.node 58))
private def row107 : Row := ((.node 105), (.node 106))
private def row108 : Row := ((.node 97), (.node 107))
private def row109 : Row := ((.node 96), (.node 108))
private def row110 : Row := ((.node 83), (.node 109))
private def row111 : Row := ((.node 98), (.node 85))
private def row112 : Row := ((.node 59), (.node 111))
private def row113 : Row := ((.node 84), (.node 92))
private def row114 : Row := ((.node 112), (.node 113))
private def row115 : Row := ((.node 110), (.node 114))
private def row116 : Row := ((.node 93), (.node 115))
private def row117 : Row := ((.node 87), (.node 116))
private def row118 : Row := ((.node 68), (.node 94))
private def row119 : Row := ((.node 63), (.node 74))
private def row120 : Row := ((.node 119), (.node 80))
private def row121 : Row := ((.node 78), (.node 106))
private def row122 : Row := ((.node 74), (.node 76))
private def row123 : Row := ((.node 121), (.node 122))
private def row124 : Row := ((.node 120), (.node 123))
private def row125 : Row := ((.node 118), (.node 124))
private def row126 : Row := ((.node 57), (.node 89))
private def row127 : Row := ((.node 89), (.node 126))
private def row128 : Row := ((.node 127), (.node 91))
private def row129 : Row := ((.node 81), (.node 128))
private def row130 : Row := ((.node 129), (.node 63))
private def row131 : Row := ((.node 75), (.node 130))
private def row132 : Row := ((.node 131), (.node 102))
private def row133 : Row := ((.node 125), (.node 132))
private def row134 : Row := ((.node 117), (.node 133))
private def row135 : Row := ((.node 106), (.node 127))
private def row136 : Row := ((.node 74), (.node 74))
private def row137 : Row := ((.node 136), (.node 122))
private def row138 : Row := ((.node 118), (.node 137))
private def row139 : Row := ((.node 138), (.node 128))
private def row140 : Row := ((.node 131), (.node 139))
private def row141 : Row := ((.node 135), (.node 140))
private def row142 : Row := ((.node 134), (.node 141))
private def row143 : Row := ((.node 142), (.node 106))
private def row144 : Row := ((.node 83), (.node 143))
private def row145 : Row := ((.node 47), (.node 122))
private def row146 : Row := ((.node 72), (.node 91))
private def row147 : Row := ((.node 145), (.node 146))
private def row148 : Row := ((.node 147), (.node 135))
private def row149 : Row := ((.node 106), (.node 148))
private def row150 : Row := ((.node 127), (.node 94))
private def row151 : Row := ((.node 91), (.node 150))
private def row152 : Row := ((.node 149), (.node 151))
private def row153 : Row := ((.node 144), (.node 152))
private def row154 : Row := ((.node 75), (.node 153))
private def row155 : Row := ((.node 94), (.node 99))
private def row156 : Row := ((.node 63), (.node 155))
private def row157 : Row := ((.node 154), (.node 156))
private def row158 : Row := ((.node 74), (.node 157))
private def row159 : Row := ((.node 63), (.node 84))
private def row160 : Row := ((.decnz 3), (.node 28))
private def row161 : Row := ((.node 127), (.node 160))
private def row162 : Row := ((.node 127), (.node 161))
private def row163 : Row := ((.node 97), (.node 162))
private def row164 : Row := ((.node 159), (.node 163))
private def row165 : Row := ((.node 158), (.node 164))
private def row166 : Row := ((.node 73), (.node 165))
private def row167 : Row := ((.node 71), (.node 166))
private def row168 : Row := ((.decnz 5), (.cont 2))
private def row169 : Row := ((.node 45), (.inc 5))
private def row170 : Row := ((.node 168), (.node 169))
private def row171 : Row := ((.decnz 6), (.node 170))
private def row172 : Row := ((.decnz 5), (.cont 1))
private def row173 : Row := ((.node 172), (.brk 1))
private def row174 : Row := ((.decnz 5), (.node 173))
private def row175 : Row := ((.node 171), (.node 174))
private def row176 : Row := ((.decnz 1), (.cont 1))
private def row177 : Row := ((.node 175), (.node 176))
private def row178 : Row := ((.decnz 4), (.node 44))
private def row179 : Row := ((.node 11), (.node 178))
private def row180 : Row := ((.node 177), (.node 179))
private def row181 : Row := ((.node 180), (.node 177))
private def row182 : Row := ((.node 167), (.node 181))
private def row183 : Row := ((.node 59), (.node 182))
private def row184 : Row := ((.node 183), (.brk 1))
private def row185 : Row := ((.decnz 3), (.node 184))
private def row186 : Row := ((.node 175), .halt)
private def row187 : Row := ((.node 51), (.node 45))
private def row188 : Row := ((.node 186), (.node 187))
private def row189 : Row := ((.inc 6), (.node 188))
private def row190 : Row := ((.node 185), (.node 189))
private def row191 : Row := ((.node 190), (.brk 1))
private def row192 : Row := ((.decnz 3), (.node 191))
private def row193 : Row := ((.node 192), (.node 47))
private def row194 : Row := ((.node 193), (.brk 1))
private def row195 : Row := ((.decnz 3), (.node 194))
private def row196 : Row := ((.node 69), (.node 25))
private def row197 : Row := ((.node 175), (.node 68))
private def row198 : Row := ((.node 196), (.node 197))
private def row199 : Row := ((.node 195), (.node 198))
private def row200 : Row := ((.node 24), (.node 199))
private def row201 : Row := ((.node 21), (.node 200))
private def row202 : Row := ((.node 8), (.node 201))

private def rawLookup (n : Nat) : Row :=
  if n < 101 then
    if n < 50 then
      if n < 25 then
        if n < 12 then
          if n < 6 then
            if n < 3 then
              if n < 1 then
                row000
              else
                if n < 2 then
                  row001
                else
                  row002
            else
              if n < 4 then
                row003
              else
                if n < 5 then
                  row004
                else
                  row005
          else
            if n < 9 then
              if n < 7 then
                row006
              else
                if n < 8 then
                  row007
                else
                  row008
            else
              if n < 10 then
                row009
              else
                if n < 11 then
                  row010
                else
                  row011
        else
          if n < 18 then
            if n < 15 then
              if n < 13 then
                row012
              else
                if n < 14 then
                  row013
                else
                  row014
            else
              if n < 16 then
                row015
              else
                if n < 17 then
                  row016
                else
                  row017
          else
            if n < 21 then
              if n < 19 then
                row018
              else
                if n < 20 then
                  row019
                else
                  row020
            else
              if n < 23 then
                if n < 22 then
                  row021
                else
                  row022
              else
                if n < 24 then
                  row023
                else
                  row024
      else
        if n < 37 then
          if n < 31 then
            if n < 28 then
              if n < 26 then
                row025
              else
                if n < 27 then
                  row026
                else
                  row027
            else
              if n < 29 then
                row028
              else
                if n < 30 then
                  row029
                else
                  row030
          else
            if n < 34 then
              if n < 32 then
                row031
              else
                if n < 33 then
                  row032
                else
                  row033
            else
              if n < 35 then
                row034
              else
                if n < 36 then
                  row035
                else
                  row036
        else
          if n < 43 then
            if n < 40 then
              if n < 38 then
                row037
              else
                if n < 39 then
                  row038
                else
                  row039
            else
              if n < 41 then
                row040
              else
                if n < 42 then
                  row041
                else
                  row042
          else
            if n < 46 then
              if n < 44 then
                row043
              else
                if n < 45 then
                  row044
                else
                  row045
            else
              if n < 48 then
                if n < 47 then
                  row046
                else
                  row047
              else
                if n < 49 then
                  row048
                else
                  row049
    else
      if n < 75 then
        if n < 62 then
          if n < 56 then
            if n < 53 then
              if n < 51 then
                row050
              else
                if n < 52 then
                  row051
                else
                  row052
            else
              if n < 54 then
                row053
              else
                if n < 55 then
                  row054
                else
                  row055
          else
            if n < 59 then
              if n < 57 then
                row056
              else
                if n < 58 then
                  row057
                else
                  row058
            else
              if n < 60 then
                row059
              else
                if n < 61 then
                  row060
                else
                  row061
        else
          if n < 68 then
            if n < 65 then
              if n < 63 then
                row062
              else
                if n < 64 then
                  row063
                else
                  row064
            else
              if n < 66 then
                row065
              else
                if n < 67 then
                  row066
                else
                  row067
          else
            if n < 71 then
              if n < 69 then
                row068
              else
                if n < 70 then
                  row069
                else
                  row070
            else
              if n < 73 then
                if n < 72 then
                  row071
                else
                  row072
              else
                if n < 74 then
                  row073
                else
                  row074
      else
        if n < 88 then
          if n < 81 then
            if n < 78 then
              if n < 76 then
                row075
              else
                if n < 77 then
                  row076
                else
                  row077
            else
              if n < 79 then
                row078
              else
                if n < 80 then
                  row079
                else
                  row080
          else
            if n < 84 then
              if n < 82 then
                row081
              else
                if n < 83 then
                  row082
                else
                  row083
            else
              if n < 86 then
                if n < 85 then
                  row084
                else
                  row085
              else
                if n < 87 then
                  row086
                else
                  row087
        else
          if n < 94 then
            if n < 91 then
              if n < 89 then
                row088
              else
                if n < 90 then
                  row089
                else
                  row090
            else
              if n < 92 then
                row091
              else
                if n < 93 then
                  row092
                else
                  row093
          else
            if n < 97 then
              if n < 95 then
                row094
              else
                if n < 96 then
                  row095
                else
                  row096
            else
              if n < 99 then
                if n < 98 then
                  row097
                else
                  row098
              else
                if n < 100 then
                  row099
                else
                  row100
  else
    if n < 152 then
      if n < 126 then
        if n < 113 then
          if n < 107 then
            if n < 104 then
              if n < 102 then
                row101
              else
                if n < 103 then
                  row102
                else
                  row103
            else
              if n < 105 then
                row104
              else
                if n < 106 then
                  row105
                else
                  row106
          else
            if n < 110 then
              if n < 108 then
                row107
              else
                if n < 109 then
                  row108
                else
                  row109
            else
              if n < 111 then
                row110
              else
                if n < 112 then
                  row111
                else
                  row112
        else
          if n < 119 then
            if n < 116 then
              if n < 114 then
                row113
              else
                if n < 115 then
                  row114
                else
                  row115
            else
              if n < 117 then
                row116
              else
                if n < 118 then
                  row117
                else
                  row118
          else
            if n < 122 then
              if n < 120 then
                row119
              else
                if n < 121 then
                  row120
                else
                  row121
            else
              if n < 124 then
                if n < 123 then
                  row122
                else
                  row123
              else
                if n < 125 then
                  row124
                else
                  row125
      else
        if n < 139 then
          if n < 132 then
            if n < 129 then
              if n < 127 then
                row126
              else
                if n < 128 then
                  row127
                else
                  row128
            else
              if n < 130 then
                row129
              else
                if n < 131 then
                  row130
                else
                  row131
          else
            if n < 135 then
              if n < 133 then
                row132
              else
                if n < 134 then
                  row133
                else
                  row134
            else
              if n < 137 then
                if n < 136 then
                  row135
                else
                  row136
              else
                if n < 138 then
                  row137
                else
                  row138
        else
          if n < 145 then
            if n < 142 then
              if n < 140 then
                row139
              else
                if n < 141 then
                  row140
                else
                  row141
            else
              if n < 143 then
                row142
              else
                if n < 144 then
                  row143
                else
                  row144
          else
            if n < 148 then
              if n < 146 then
                row145
              else
                if n < 147 then
                  row146
                else
                  row147
            else
              if n < 150 then
                if n < 149 then
                  row148
                else
                  row149
              else
                if n < 151 then
                  row150
                else
                  row151
    else
      if n < 177 then
        if n < 164 then
          if n < 158 then
            if n < 155 then
              if n < 153 then
                row152
              else
                if n < 154 then
                  row153
                else
                  row154
            else
              if n < 156 then
                row155
              else
                if n < 157 then
                  row156
                else
                  row157
          else
            if n < 161 then
              if n < 159 then
                row158
              else
                if n < 160 then
                  row159
                else
                  row160
            else
              if n < 162 then
                row161
              else
                if n < 163 then
                  row162
                else
                  row163
        else
          if n < 170 then
            if n < 167 then
              if n < 165 then
                row164
              else
                if n < 166 then
                  row165
                else
                  row166
            else
              if n < 168 then
                row167
              else
                if n < 169 then
                  row168
                else
                  row169
          else
            if n < 173 then
              if n < 171 then
                row170
              else
                if n < 172 then
                  row171
                else
                  row172
            else
              if n < 175 then
                if n < 174 then
                  row173
                else
                  row174
              else
                if n < 176 then
                  row175
                else
                  row176
      else
        if n < 190 then
          if n < 183 then
            if n < 180 then
              if n < 178 then
                row177
              else
                if n < 179 then
                  row178
                else
                  row179
            else
              if n < 181 then
                row180
              else
                if n < 182 then
                  row181
                else
                  row182
          else
            if n < 186 then
              if n < 184 then
                row183
              else
                if n < 185 then
                  row184
                else
                  row185
            else
              if n < 188 then
                if n < 187 then
                  row186
                else
                  row187
              else
                if n < 189 then
                  row188
                else
                  row189
        else
          if n < 196 then
            if n < 193 then
              if n < 191 then
                row190
              else
                if n < 192 then
                  row191
                else
                  row192
            else
              if n < 194 then
                row193
              else
                if n < 195 then
                  row194
                else
                  row195
          else
            if n < 199 then
              if n < 197 then
                row196
              else
                if n < 198 then
                  row197
                else
                  row198
            else
              if n < 201 then
                if n < 200 then
                  row199
                else
                  row200
              else
                if n < 202 then
                  row201
                else
                  row202

def nodes (n : Nat) : Row :=
  if n < 203 then rawLookup n else (.halt, .halt)

def program : Program where
  nodes := nodes
  root := 202
  nnodes := 203

theorem program_root : program.root = 202 := rfl
theorem program_nnodes : program.nnodes = 203 := rfl

theorem nodes_default (n : Nat) (hn : 203 ≤ n) : program.nodes n = (.halt, .halt) := by
  simp only [program, nodes, if_neg (Nat.not_lt.mpr hn)]

end ProgramRouting245

namespace TreeRouting245
open RegisterPath RMBisim ProgramRouting245

/-- Compose exact child unfoldings; the fuel bound is explicit and arbitrary. -/
private theorem parent_eq {p : Program} {n h₀ h₁ : Nat} {e₀ e₁ : Edge} {t₀ t₁ : Tree}
    (hrow : p.nodes n = (e₀, e₁))
    (hl : ∀ f, h₀ ≤ f → sub p f e₀ = t₀)
    (hr : ∀ f, h₁ ≤ f → sub p f e₁ = t₁) :
    ∀ f, max h₀ h₁ + 1 ≤ f → toTree p f n = .node t₀ t₁ := by
  intro f hf
  cases f with
  | zero => cases hf
  | succ f =>
      have hm : max h₀ h₁ ≤ f := Nat.le_of_succ_le_succ hf
      rw [toTree_succ, hrow]
      change Tree.node (sub p f e₀) (sub p f e₁) = .node t₀ t₁
      rw [hl f (Nat.le_trans (Nat.le_max_left _ _) hm),
        hr f (Nat.le_trans (Nat.le_max_right _ _) hm)]

private def t000 : Tree := .node (.leaf (.decnz 8)) (.leaf (.brk 1))
private theorem row000_eq : program.nodes 0 = ((.decnz 8), (.brk 1)) := by decide +kernel
private theorem node000_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 0 = t000 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row000_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t001 : Tree := .node (.leaf (.inc 6)) (.leaf (.cont 3))
private theorem row001_eq : program.nodes 1 = ((.inc 6), (.cont 3)) := by decide +kernel
private theorem node001_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 1 = t001 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row001_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t002 : Tree := .node (.leaf (.inc 8)) t001
private theorem row002_eq : program.nodes 2 = ((.inc 8), (.node 1)) := by decide +kernel
private theorem node002_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 2 = t002 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row002_eq
    (fun _ _ => rfl) (fun f hf => node001_eq f hf) f hf

private def t003 : Tree := .node (.leaf (.decnz 0)) t002
private theorem row003_eq : program.nodes 3 = ((.decnz 0), (.node 2)) := by decide +kernel
private theorem node003_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 3 = t003 := by
  exact parent_eq (h₀ := 0) (h₁ := 2) row003_eq
    (fun _ _ => rfl) (fun f hf => node002_eq f hf) f hf

private def t004 : Tree := .node (.leaf (.inc 0)) (.leaf (.cont 2))
private theorem row004_eq : program.nodes 4 = ((.inc 0), (.cont 2)) := by decide +kernel
private theorem node004_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 4 = t004 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row004_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t005 : Tree := .node (.leaf (.decnz 6)) t004
private theorem row005_eq : program.nodes 5 = ((.decnz 6), (.node 4)) := by decide +kernel
private theorem node005_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 5 = t005 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row005_eq
    (fun _ _ => rfl) (fun f hf => node004_eq f hf) f hf

private def t006 : Tree := .node t005 (.leaf (.inc 0))
private theorem row006_eq : program.nodes 6 = ((.node 5), (.inc 0)) := by decide +kernel
private theorem node006_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 6 = t006 := by
  exact parent_eq (h₀ := 2) (h₁ := 0) row006_eq
    (fun f hf => node005_eq f hf) (fun _ _ => rfl) f hf

private def t007 : Tree := .node t003 t006
private theorem row007_eq : program.nodes 7 = ((.node 3), (.node 6)) := by decide +kernel
private theorem node007_eq (f : Nat) (hf : 4 ≤ f) : toTree program f 7 = t007 := by
  exact parent_eq (h₀ := 3) (h₁ := 3) row007_eq
    (fun f hf => node003_eq f hf) (fun f hf => node006_eq f hf) f hf

private def t008 : Tree := .node t000 t007
private theorem row008_eq : program.nodes 8 = ((.node 0), (.node 7)) := by decide +kernel
private theorem node008_eq (f : Nat) (hf : 5 ≤ f) : toTree program f 8 = t008 := by
  exact parent_eq (h₀ := 1) (h₁ := 4) row008_eq
    (fun f hf => node000_eq f hf) (fun f hf => node007_eq f hf) f hf

private def t009 : Tree := .node (.leaf (.decnz 6)) (.leaf (.brk 1))
private theorem row009_eq : program.nodes 9 = ((.decnz 6), (.brk 1)) := by decide +kernel
private theorem node009_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 9 = t009 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row009_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t010 : Tree := .node (.leaf (.inc 6)) (.leaf (.cont 2))
private theorem row010_eq : program.nodes 10 = ((.inc 6), (.cont 2)) := by decide +kernel
private theorem node010_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 10 = t010 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row010_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t011 : Tree := .node (.leaf (.decnz 7)) t010
private theorem row011_eq : program.nodes 11 = ((.decnz 7), (.node 10)) := by decide +kernel
private theorem node011_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 11 = t011 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row011_eq
    (fun _ _ => rfl) (fun f hf => node010_eq f hf) f hf

private def t012 : Tree := .node t009 t011
private theorem row012_eq : program.nodes 12 = ((.node 9), (.node 11)) := by decide +kernel
private theorem node012_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 12 = t012 := by
  exact parent_eq (h₀ := 1) (h₁ := 2) row012_eq
    (fun f hf => node009_eq f hf) (fun f hf => node011_eq f hf) f hf

private def t013 : Tree := .node t012 (.leaf (.cont 3))
private theorem row013_eq : program.nodes 13 = ((.node 12), (.cont 3)) := by decide +kernel
private theorem node013_eq (f : Nat) (hf : 4 ≤ f) : toTree program f 13 = t013 := by
  exact parent_eq (h₀ := 3) (h₁ := 0) row013_eq
    (fun f hf => node012_eq f hf) (fun _ _ => rfl) f hf

private def t014 : Tree := .node (.leaf (.inc 7)) t013
private theorem row014_eq : program.nodes 14 = ((.inc 7), (.node 13)) := by decide +kernel
private theorem node014_eq (f : Nat) (hf : 5 ≤ f) : toTree program f 14 = t014 := by
  exact parent_eq (h₀ := 0) (h₁ := 4) row014_eq
    (fun _ _ => rfl) (fun f hf => node013_eq f hf) f hf

private def t015 : Tree := .node (.leaf (.decnz 8)) t014
private theorem row015_eq : program.nodes 15 = ((.decnz 8), (.node 14)) := by decide +kernel
private theorem node015_eq (f : Nat) (hf : 6 ≤ f) : toTree program f 15 = t015 := by
  exact parent_eq (h₀ := 0) (h₁ := 5) row015_eq
    (fun _ _ => rfl) (fun f hf => node014_eq f hf) f hf

private def t016 : Tree := .node (.leaf (.inc 8)) (.leaf (.cont 2))
private theorem row016_eq : program.nodes 16 = ((.inc 8), (.cont 2)) := by decide +kernel
private theorem node016_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 16 = t016 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row016_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t017 : Tree := .node (.leaf (.decnz 7)) t016
private theorem row017_eq : program.nodes 17 = ((.decnz 7), (.node 16)) := by decide +kernel
private theorem node017_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 17 = t017 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row017_eq
    (fun _ _ => rfl) (fun f hf => node016_eq f hf) f hf

private def t018 : Tree := .node t015 t017
private theorem row018_eq : program.nodes 18 = ((.node 15), (.node 17)) := by decide +kernel
private theorem node018_eq (f : Nat) (hf : 7 ≤ f) : toTree program f 18 = t018 := by
  exact parent_eq (h₀ := 6) (h₁ := 2) row018_eq
    (fun f hf => node015_eq f hf) (fun f hf => node017_eq f hf) f hf

private def t019 : Tree := .node (.leaf (.inc 3)) (.leaf (.cont 2))
private theorem row019_eq : program.nodes 19 = ((.inc 3), (.cont 2)) := by decide +kernel
private theorem node019_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 19 = t019 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row019_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t020 : Tree := .node (.leaf (.decnz 6)) t019
private theorem row020_eq : program.nodes 20 = ((.decnz 6), (.node 19)) := by decide +kernel
private theorem node020_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 20 = t020 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row020_eq
    (fun _ _ => rfl) (fun f hf => node019_eq f hf) f hf

private def t021 : Tree := .node t018 t020
private theorem row021_eq : program.nodes 21 = ((.node 18), (.node 20)) := by decide +kernel
private theorem node021_eq (f : Nat) (hf : 8 ≤ f) : toTree program f 21 = t021 := by
  exact parent_eq (h₀ := 7) (h₁ := 2) row021_eq
    (fun f hf => node018_eq f hf) (fun f hf => node020_eq f hf) f hf

private def t022 : Tree := .node (.leaf (.inc 4)) (.leaf (.cont 2))
private theorem row022_eq : program.nodes 22 = ((.inc 4), (.cont 2)) := by decide +kernel
private theorem node022_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 22 = t022 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row022_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t023 : Tree := .node (.leaf (.decnz 6)) t022
private theorem row023_eq : program.nodes 23 = ((.decnz 6), (.node 22)) := by decide +kernel
private theorem node023_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 23 = t023 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row023_eq
    (fun _ _ => rfl) (fun f hf => node022_eq f hf) f hf

private def t024 : Tree := .node t018 t023
private theorem row024_eq : program.nodes 24 = ((.node 18), (.node 23)) := by decide +kernel
private theorem node024_eq (f : Nat) (hf : 8 ≤ f) : toTree program f 24 = t024 := by
  exact parent_eq (h₀ := 7) (h₁ := 2) row024_eq
    (fun f hf => node018_eq f hf) (fun f hf => node023_eq f hf) f hf

private def t025 : Tree := .node (.leaf (.decnz 1)) t010
private theorem row025_eq : program.nodes 25 = ((.decnz 1), (.node 10)) := by decide +kernel
private theorem node025_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 25 = t025 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row025_eq
    (fun _ _ => rfl) (fun f hf => node010_eq f hf) f hf

private def t026 : Tree := .node (.leaf (.inc 1)) (.leaf (.cont 2))
private theorem row026_eq : program.nodes 26 = ((.inc 1), (.cont 2)) := by decide +kernel
private theorem node026_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 26 = t026 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row026_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t027 : Tree := .node (.leaf (.decnz 2)) t026
private theorem row027_eq : program.nodes 27 = ((.decnz 2), (.node 26)) := by decide +kernel
private theorem node027_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 27 = t027 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row027_eq
    (fun _ _ => rfl) (fun f hf => node026_eq f hf) f hf

private def t028 : Tree := .node (.leaf (.inc 7)) t001
private theorem row028_eq : program.nodes 28 = ((.inc 7), (.node 1)) := by decide +kernel
private theorem node028_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 28 = t028 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row028_eq
    (fun _ _ => rfl) (fun f hf => node001_eq f hf) f hf

private def t029 : Tree := .node (.leaf (.decnz 1)) t028
private theorem row029_eq : program.nodes 29 = ((.decnz 1), (.node 28)) := by decide +kernel
private theorem node029_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 29 = t029 := by
  exact parent_eq (h₀ := 0) (h₁ := 2) row029_eq
    (fun _ _ => rfl) (fun f hf => node028_eq f hf) f hf

private def t030 : Tree := .node (.leaf (.decnz 6)) t026
private theorem row030_eq : program.nodes 30 = ((.decnz 6), (.node 26)) := by decide +kernel
private theorem node030_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 30 = t030 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row030_eq
    (fun _ _ => rfl) (fun f hf => node026_eq f hf) f hf

private def t031 : Tree := .node (.leaf (.inc 7)) t030
private theorem row031_eq : program.nodes 31 = ((.inc 7), (.node 30)) := by decide +kernel
private theorem node031_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 31 = t031 := by
  exact parent_eq (h₀ := 0) (h₁ := 2) row031_eq
    (fun _ _ => rfl) (fun f hf => node030_eq f hf) f hf

private def t032 : Tree := .node t031 (.leaf (.cont 3))
private theorem row032_eq : program.nodes 32 = ((.node 31), (.cont 3)) := by decide +kernel
private theorem node032_eq (f : Nat) (hf : 4 ≤ f) : toTree program f 32 = t032 := by
  exact parent_eq (h₀ := 3) (h₁ := 0) row032_eq
    (fun f hf => node031_eq f hf) (fun _ _ => rfl) f hf

private def t033 : Tree := .node (.leaf (.decnz 6)) t032
private theorem row033_eq : program.nodes 33 = ((.decnz 6), (.node 32)) := by decide +kernel
private theorem node033_eq (f : Nat) (hf : 5 ≤ f) : toTree program f 33 = t033 := by
  exact parent_eq (h₀ := 0) (h₁ := 4) row033_eq
    (fun _ _ => rfl) (fun f hf => node032_eq f hf) f hf

private def t034 : Tree := .node t029 t033
private theorem row034_eq : program.nodes 34 = ((.node 29), (.node 33)) := by decide +kernel
private theorem node034_eq (f : Nat) (hf : 6 ≤ f) : toTree program f 34 = t034 := by
  exact parent_eq (h₀ := 3) (h₁ := 5) row034_eq
    (fun f hf => node029_eq f hf) (fun f hf => node033_eq f hf) f hf

private def t035 : Tree := .node (.leaf (.inc 2)) (.leaf (.cont 2))
private theorem row035_eq : program.nodes 35 = ((.inc 2), (.cont 2)) := by decide +kernel
private theorem node035_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 35 = t035 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row035_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t036 : Tree := .node (.leaf (.decnz 7)) t035
private theorem row036_eq : program.nodes 36 = ((.decnz 7), (.node 35)) := by decide +kernel
private theorem node036_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 36 = t036 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row036_eq
    (fun _ _ => rfl) (fun f hf => node035_eq f hf) f hf

private def t037 : Tree := .node t034 t036
private theorem row037_eq : program.nodes 37 = ((.node 34), (.node 36)) := by decide +kernel
private theorem node037_eq (f : Nat) (hf : 7 ≤ f) : toTree program f 37 = t037 := by
  exact parent_eq (h₀ := 6) (h₁ := 2) row037_eq
    (fun f hf => node034_eq f hf) (fun f hf => node036_eq f hf) f hf

private def t038 : Tree := .node t027 t037
private theorem row038_eq : program.nodes 38 = ((.node 27), (.node 37)) := by decide +kernel
private theorem node038_eq (f : Nat) (hf : 8 ≤ f) : toTree program f 38 = t038 := by
  exact parent_eq (h₀ := 2) (h₁ := 7) row038_eq
    (fun f hf => node027_eq f hf) (fun f hf => node037_eq f hf) f hf

private def t039 : Tree := .node t025 t038
private theorem row039_eq : program.nodes 39 = ((.node 25), (.node 38)) := by decide +kernel
private theorem node039_eq (f : Nat) (hf : 9 ≤ f) : toTree program f 39 = t039 := by
  exact parent_eq (h₀ := 2) (h₁ := 8) row039_eq
    (fun f hf => node025_eq f hf) (fun f hf => node038_eq f hf) f hf

private def t040 : Tree := .node (.leaf (.inc 1)) t001
private theorem row040_eq : program.nodes 40 = ((.inc 1), (.node 1)) := by decide +kernel
private theorem node040_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 40 = t040 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row040_eq
    (fun _ _ => rfl) (fun f hf => node001_eq f hf) f hf

private def t041 : Tree := .node (.leaf (.decnz 4)) t040
private theorem row041_eq : program.nodes 41 = ((.decnz 4), (.node 40)) := by decide +kernel
private theorem node041_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 41 = t041 := by
  exact parent_eq (h₀ := 0) (h₁ := 2) row041_eq
    (fun _ _ => rfl) (fun f hf => node040_eq f hf) f hf

private def t042 : Tree := .node t041 t023
private theorem row042_eq : program.nodes 42 = ((.node 41), (.node 23)) := by decide +kernel
private theorem node042_eq (f : Nat) (hf : 4 ≤ f) : toTree program f 42 = t042 := by
  exact parent_eq (h₀ := 3) (h₁ := 2) row042_eq
    (fun f hf => node041_eq f hf) (fun f hf => node023_eq f hf) f hf

private def t043 : Tree := .node (.leaf (.decnz 5)) t040
private theorem row043_eq : program.nodes 43 = ((.decnz 5), (.node 40)) := by decide +kernel
private theorem node043_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 43 = t043 := by
  exact parent_eq (h₀ := 0) (h₁ := 2) row043_eq
    (fun _ _ => rfl) (fun f hf => node040_eq f hf) f hf

private def t044 : Tree := .node (.leaf (.inc 5)) (.leaf (.cont 2))
private theorem row044_eq : program.nodes 44 = ((.inc 5), (.cont 2)) := by decide +kernel
private theorem node044_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 44 = t044 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row044_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t045 : Tree := .node (.leaf (.decnz 6)) t044
private theorem row045_eq : program.nodes 45 = ((.decnz 6), (.node 44)) := by decide +kernel
private theorem node045_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 45 = t045 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row045_eq
    (fun _ _ => rfl) (fun f hf => node044_eq f hf) f hf

private def t046 : Tree := .node t043 t045
private theorem row046_eq : program.nodes 46 = ((.node 43), (.node 45)) := by decide +kernel
private theorem node046_eq (f : Nat) (hf : 4 ≤ f) : toTree program f 46 = t046 := by
  exact parent_eq (h₀ := 3) (h₁ := 2) row046_eq
    (fun f hf => node043_eq f hf) (fun f hf => node045_eq f hf) f hf

private def t047 : Tree := .node t039 t046
private theorem row047_eq : program.nodes 47 = ((.node 39), (.node 46)) := by decide +kernel
private theorem node047_eq (f : Nat) (hf : 10 ≤ f) : toTree program f 47 = t047 := by
  exact parent_eq (h₀ := 9) (h₁ := 4) row047_eq
    (fun f hf => node039_eq f hf) (fun f hf => node046_eq f hf) f hf

private def t048 : Tree := .node t042 t047
private theorem row048_eq : program.nodes 48 = ((.node 42), (.node 47)) := by decide +kernel
private theorem node048_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 48 = t048 := by
  exact parent_eq (h₀ := 4) (h₁ := 10) row048_eq
    (fun f hf => node042_eq f hf) (fun f hf => node047_eq f hf) f hf

private def t049 : Tree := .node t039 t048
private theorem row049_eq : program.nodes 49 = ((.node 39), (.node 48)) := by decide +kernel
private theorem node049_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 49 = t049 := by
  exact parent_eq (h₀ := 9) (h₁ := 11) row049_eq
    (fun f hf => node039_eq f hf) (fun f hf => node048_eq f hf) f hf

private def t050 : Tree := .node (.leaf (.decnz 2)) t014
private theorem row050_eq : program.nodes 50 = ((.decnz 2), (.node 14)) := by decide +kernel
private theorem node050_eq (f : Nat) (hf : 6 ≤ f) : toTree program f 50 = t050 := by
  exact parent_eq (h₀ := 0) (h₁ := 5) row050_eq
    (fun _ _ => rfl) (fun f hf => node014_eq f hf) f hf

private def t051 : Tree := .node t050 t036
private theorem row051_eq : program.nodes 51 = ((.node 50), (.node 36)) := by decide +kernel
private theorem node051_eq (f : Nat) (hf : 7 ≤ f) : toTree program f 51 = t051 := by
  exact parent_eq (h₀ := 6) (h₁ := 2) row051_eq
    (fun f hf => node050_eq f hf) (fun f hf => node036_eq f hf) f hf

private def t052 : Tree := .node (.leaf (.inc 1)) (.leaf (.inc 1))
private theorem row052_eq : program.nodes 52 = ((.inc 1), (.inc 1)) := by decide +kernel
private theorem node052_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 52 = t052 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row052_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t053 : Tree := .node t052 t052
private theorem row053_eq : program.nodes 53 = ((.node 52), (.node 52)) := by decide +kernel
private theorem node053_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 53 = t053 := by
  exact parent_eq (h₀ := 1) (h₁ := 1) row053_eq
    (fun f hf => node052_eq f hf) (fun f hf => node052_eq f hf) f hf

private def t054 : Tree := .node t053 (.leaf (.cont 2))
private theorem row054_eq : program.nodes 54 = ((.node 53), (.cont 2)) := by decide +kernel
private theorem node054_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 54 = t054 := by
  exact parent_eq (h₀ := 2) (h₁ := 0) row054_eq
    (fun f hf => node053_eq f hf) (fun _ _ => rfl) f hf

private def t055 : Tree := .node (.leaf (.decnz 7)) t054
private theorem row055_eq : program.nodes 55 = ((.decnz 7), (.node 54)) := by decide +kernel
private theorem node055_eq (f : Nat) (hf : 4 ≤ f) : toTree program f 55 = t055 := by
  exact parent_eq (h₀ := 0) (h₁ := 3) row055_eq
    (fun _ _ => rfl) (fun f hf => node054_eq f hf) f hf

private def t056 : Tree := .node t034 t055
private theorem row056_eq : program.nodes 56 = ((.node 34), (.node 55)) := by decide +kernel
private theorem node056_eq (f : Nat) (hf : 7 ≤ f) : toTree program f 56 = t056 := by
  exact parent_eq (h₀ := 6) (h₁ := 4) row056_eq
    (fun f hf => node034_eq f hf) (fun f hf => node055_eq f hf) f hf

private def t057 : Tree := .node t051 t056
private theorem row057_eq : program.nodes 57 = ((.node 51), (.node 56)) := by decide +kernel
private theorem node057_eq (f : Nat) (hf : 8 ≤ f) : toTree program f 57 = t057 := by
  exact parent_eq (h₀ := 7) (h₁ := 7) row057_eq
    (fun f hf => node051_eq f hf) (fun f hf => node056_eq f hf) f hf

private def t058 : Tree := .node t057 t052
private theorem row058_eq : program.nodes 58 = ((.node 57), (.node 52)) := by decide +kernel
private theorem node058_eq (f : Nat) (hf : 9 ≤ f) : toTree program f 58 = t058 := by
  exact parent_eq (h₀ := 8) (h₁ := 1) row058_eq
    (fun f hf => node057_eq f hf) (fun f hf => node052_eq f hf) f hf

private def t059 : Tree := .node t049 t058
private theorem row059_eq : program.nodes 59 = ((.node 49), (.node 58)) := by decide +kernel
private theorem node059_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 59 = t059 := by
  exact parent_eq (h₀ := 12) (h₁ := 9) row059_eq
    (fun f hf => node049_eq f hf) (fun f hf => node058_eq f hf) f hf

private def t060 : Tree := .node t018 t045
private theorem row060_eq : program.nodes 60 = ((.node 18), (.node 45)) := by decide +kernel
private theorem node060_eq (f : Nat) (hf : 8 ≤ f) : toTree program f 60 = t060 := by
  exact parent_eq (h₀ := 7) (h₁ := 2) row060_eq
    (fun f hf => node018_eq f hf) (fun f hf => node045_eq f hf) f hf

private def t061 : Tree := .node (.leaf (.decnz 3)) t040
private theorem row061_eq : program.nodes 61 = ((.decnz 3), (.node 40)) := by decide +kernel
private theorem node061_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 61 = t061 := by
  exact parent_eq (h₀ := 0) (h₁ := 2) row061_eq
    (fun _ _ => rfl) (fun f hf => node040_eq f hf) f hf

private def t062 : Tree := .node t061 t020
private theorem row062_eq : program.nodes 62 = ((.node 61), (.node 20)) := by decide +kernel
private theorem node062_eq (f : Nat) (hf : 4 ≤ f) : toTree program f 62 = t062 := by
  exact parent_eq (h₀ := 3) (h₁ := 2) row062_eq
    (fun f hf => node061_eq f hf) (fun f hf => node020_eq f hf) f hf

private def t063 : Tree := .node t039 t062
private theorem row063_eq : program.nodes 63 = ((.node 39), (.node 62)) := by decide +kernel
private theorem node063_eq (f : Nat) (hf : 10 ≤ f) : toTree program f 63 = t063 := by
  exact parent_eq (h₀ := 9) (h₁ := 4) row063_eq
    (fun f hf => node039_eq f hf) (fun f hf => node062_eq f hf) f hf

private def t064 : Tree := .node t063 t039
private theorem row064_eq : program.nodes 64 = ((.node 63), (.node 39)) := by decide +kernel
private theorem node064_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 64 = t064 := by
  exact parent_eq (h₀ := 10) (h₁ := 9) row064_eq
    (fun f hf => node063_eq f hf) (fun f hf => node039_eq f hf) f hf

private def t065 : Tree := .node t018 t030
private theorem row065_eq : program.nodes 65 = ((.node 18), (.node 30)) := by decide +kernel
private theorem node065_eq (f : Nat) (hf : 8 ≤ f) : toTree program f 65 = t065 := by
  exact parent_eq (h₀ := 7) (h₁ := 2) row065_eq
    (fun f hf => node018_eq f hf) (fun f hf => node030_eq f hf) f hf

private def t066 : Tree := .node t065 t057
private theorem row066_eq : program.nodes 66 = ((.node 65), (.node 57)) := by decide +kernel
private theorem node066_eq (f : Nat) (hf : 9 ≤ f) : toTree program f 66 = t066 := by
  exact parent_eq (h₀ := 8) (h₁ := 8) row066_eq
    (fun f hf => node065_eq f hf) (fun f hf => node057_eq f hf) f hf

private def t067 : Tree := .node t064 t066
private theorem row067_eq : program.nodes 67 = ((.node 64), (.node 66)) := by decide +kernel
private theorem node067_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 67 = t067 := by
  exact parent_eq (h₀ := 11) (h₁ := 9) row067_eq
    (fun f hf => node064_eq f hf) (fun f hf => node066_eq f hf) f hf

private def t068 : Tree := .node t039 t042
private theorem row068_eq : program.nodes 68 = ((.node 39), (.node 42)) := by decide +kernel
private theorem node068_eq (f : Nat) (hf : 10 ≤ f) : toTree program f 68 = t068 := by
  exact parent_eq (h₀ := 9) (h₁ := 4) row068_eq
    (fun f hf => node039_eq f hf) (fun f hf => node042_eq f hf) f hf

private def t069 : Tree := .node t068 t057
private theorem row069_eq : program.nodes 69 = ((.node 68), (.node 57)) := by decide +kernel
private theorem node069_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 69 = t069 := by
  exact parent_eq (h₀ := 10) (h₁ := 8) row069_eq
    (fun f hf => node068_eq f hf) (fun f hf => node057_eq f hf) f hf

private def t070 : Tree := .node t067 t069
private theorem row070_eq : program.nodes 70 = ((.node 67), (.node 69)) := by decide +kernel
private theorem node070_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 70 = t070 := by
  exact parent_eq (h₀ := 12) (h₁ := 11) row070_eq
    (fun f hf => node067_eq f hf) (fun f hf => node069_eq f hf) f hf

private def t071 : Tree := .node t060 t070
private theorem row071_eq : program.nodes 71 = ((.node 60), (.node 70)) := by decide +kernel
private theorem node071_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 71 = t071 := by
  exact parent_eq (h₀ := 8) (h₁ := 13) row071_eq
    (fun f hf => node060_eq f hf) (fun f hf => node070_eq f hf) f hf

private def t072 : Tree := .node t068 t063
private theorem row072_eq : program.nodes 72 = ((.node 68), (.node 63)) := by decide +kernel
private theorem node072_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 72 = t072 := by
  exact parent_eq (h₀ := 10) (h₁ := 10) row072_eq
    (fun f hf => node068_eq f hf) (fun f hf => node063_eq f hf) f hf

private def t073 : Tree := .node t072 t057
private theorem row073_eq : program.nodes 73 = ((.node 72), (.node 57)) := by decide +kernel
private theorem node073_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 73 = t073 := by
  exact parent_eq (h₀ := 11) (h₁ := 8) row073_eq
    (fun f hf => node072_eq f hf) (fun f hf => node057_eq f hf) f hf

private def t074 : Tree := .node t047 t063
private theorem row074_eq : program.nodes 74 = ((.node 47), (.node 63)) := by decide +kernel
private theorem node074_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 74 = t074 := by
  exact parent_eq (h₀ := 10) (h₁ := 10) row074_eq
    (fun f hf => node047_eq f hf) (fun f hf => node063_eq f hf) f hf

private def t075 : Tree := .node t057 t057
private theorem row075_eq : program.nodes 75 = ((.node 57), (.node 57)) := by decide +kernel
private theorem node075_eq (f : Nat) (hf : 9 ≤ f) : toTree program f 75 = t075 := by
  exact parent_eq (h₀ := 8) (h₁ := 8) row075_eq
    (fun f hf => node057_eq f hf) (fun f hf => node057_eq f hf) f hf

private def t076 : Tree := .node t057 (.leaf (.inc 1))
private theorem row076_eq : program.nodes 76 = ((.node 57), (.inc 1)) := by decide +kernel
private theorem node076_eq (f : Nat) (hf : 9 ≤ f) : toTree program f 76 = t076 := by
  exact parent_eq (h₀ := 8) (h₁ := 0) row076_eq
    (fun f hf => node057_eq f hf) (fun _ _ => rfl) f hf

private def t077 : Tree := .node t068 t076
private theorem row077_eq : program.nodes 77 = ((.node 68), (.node 76)) := by decide +kernel
private theorem node077_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 77 = t077 := by
  exact parent_eq (h₀ := 10) (h₁ := 9) row077_eq
    (fun f hf => node068_eq f hf) (fun f hf => node076_eq f hf) f hf

private def t078 : Tree := .node t063 t077
private theorem row078_eq : program.nodes 78 = ((.node 63), (.node 77)) := by decide +kernel
private theorem node078_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 78 = t078 := by
  exact parent_eq (h₀ := 10) (h₁ := 11) row078_eq
    (fun f hf => node063_eq f hf) (fun f hf => node077_eq f hf) f hf

private def t079 : Tree := .node t064 t046
private theorem row079_eq : program.nodes 79 = ((.node 64), (.node 46)) := by decide +kernel
private theorem node079_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 79 = t079 := by
  exact parent_eq (h₀ := 11) (h₁ := 4) row079_eq
    (fun f hf => node064_eq f hf) (fun f hf => node046_eq f hf) f hf

private def t080 : Tree := .node t079 t076
private theorem row080_eq : program.nodes 80 = ((.node 79), (.node 76)) := by decide +kernel
private theorem node080_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 80 = t080 := by
  exact parent_eq (h₀ := 12) (h₁ := 9) row080_eq
    (fun f hf => node079_eq f hf) (fun f hf => node076_eq f hf) f hf

private def t081 : Tree := .node t052 t080
private theorem row081_eq : program.nodes 81 = ((.node 52), (.node 80)) := by decide +kernel
private theorem node081_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 81 = t081 := by
  exact parent_eq (h₀ := 1) (h₁ := 13) row081_eq
    (fun f hf => node052_eq f hf) (fun f hf => node080_eq f hf) f hf

private def t082 : Tree := .node t078 t081
private theorem row082_eq : program.nodes 82 = ((.node 78), (.node 81)) := by decide +kernel
private theorem node082_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 82 = t082 := by
  exact parent_eq (h₀ := 12) (h₁ := 14) row082_eq
    (fun f hf => node078_eq f hf) (fun f hf => node081_eq f hf) f hf

private def t083 : Tree := .node t057 t082
private theorem row083_eq : program.nodes 83 = ((.node 57), (.node 82)) := by decide +kernel
private theorem node083_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 83 = t083 := by
  exact parent_eq (h₀ := 8) (h₁ := 15) row083_eq
    (fun f hf => node057_eq f hf) (fun f hf => node082_eq f hf) f hf

private def t084 : Tree := .node t059 (.leaf (.inc 1))
private theorem row084_eq : program.nodes 84 = ((.node 59), (.inc 1)) := by decide +kernel
private theorem node084_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 84 = t084 := by
  exact parent_eq (h₀ := 13) (h₁ := 0) row084_eq
    (fun f hf => node059_eq f hf) (fun _ _ => rfl) f hf

private def t085 : Tree := .node t075 t068
private theorem row085_eq : program.nodes 85 = ((.node 75), (.node 68)) := by decide +kernel
private theorem node085_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 85 = t085 := by
  exact parent_eq (h₀ := 9) (h₁ := 10) row085_eq
    (fun f hf => node075_eq f hf) (fun f hf => node068_eq f hf) f hf

private def t086 : Tree := .node t084 t085
private theorem row086_eq : program.nodes 86 = ((.node 84), (.node 85)) := by decide +kernel
private theorem node086_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 86 = t086 := by
  exact parent_eq (h₀ := 14) (h₁ := 11) row086_eq
    (fun f hf => node084_eq f hf) (fun f hf => node085_eq f hf) f hf

private def t087 : Tree := .node t052 t086
private theorem row087_eq : program.nodes 87 = ((.node 52), (.node 86)) := by decide +kernel
private theorem node087_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 87 = t087 := by
  exact parent_eq (h₀ := 1) (h₁ := 15) row087_eq
    (fun f hf => node052_eq f hf) (fun f hf => node086_eq f hf) f hf

private def t088 : Tree := .node t039 (.leaf (.inc 1))
private theorem row088_eq : program.nodes 88 = ((.node 39), (.inc 1)) := by decide +kernel
private theorem node088_eq (f : Nat) (hf : 10 ≤ f) : toTree program f 88 = t088 := by
  exact parent_eq (h₀ := 9) (h₁ := 0) row088_eq
    (fun f hf => node039_eq f hf) (fun _ _ => rfl) f hf

private def t089 : Tree := .node t088 t057
private theorem row089_eq : program.nodes 89 = ((.node 88), (.node 57)) := by decide +kernel
private theorem node089_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 89 = t089 := by
  exact parent_eq (h₀ := 10) (h₁ := 8) row089_eq
    (fun f hf => node088_eq f hf) (fun f hf => node057_eq f hf) f hf

private def t090 : Tree := .node t058 t089
private theorem row090_eq : program.nodes 90 = ((.node 58), (.node 89)) := by decide +kernel
private theorem node090_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 90 = t090 := by
  exact parent_eq (h₀ := 9) (h₁ := 11) row090_eq
    (fun f hf => node058_eq f hf) (fun f hf => node089_eq f hf) f hf

private def t091 : Tree := .node t089 t090
private theorem row091_eq : program.nodes 91 = ((.node 89), (.node 90)) := by decide +kernel
private theorem node091_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 91 = t091 := by
  exact parent_eq (h₀ := 11) (h₁ := 12) row091_eq
    (fun f hf => node089_eq f hf) (fun f hf => node090_eq f hf) f hf

private def t092 : Tree := .node t091 t047
private theorem row092_eq : program.nodes 92 = ((.node 91), (.node 47)) := by decide +kernel
private theorem node092_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 92 = t092 := by
  exact parent_eq (h₀ := 13) (h₁ := 10) row092_eq
    (fun f hf => node091_eq f hf) (fun f hf => node047_eq f hf) f hf

private def t093 : Tree := .node t059 t092
private theorem row093_eq : program.nodes 93 = ((.node 59), (.node 92)) := by decide +kernel
private theorem node093_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 93 = t093 := by
  exact parent_eq (h₀ := 13) (h₁ := 14) row093_eq
    (fun f hf => node059_eq f hf) (fun f hf => node092_eq f hf) f hf

private def t094 : Tree := .node t049 t076
private theorem row094_eq : program.nodes 94 = ((.node 49), (.node 76)) := by decide +kernel
private theorem node094_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 94 = t094 := by
  exact parent_eq (h₀ := 12) (h₁ := 9) row094_eq
    (fun f hf => node049_eq f hf) (fun f hf => node076_eq f hf) f hf

private def t095 : Tree := .node t085 t074
private theorem row095_eq : program.nodes 95 = ((.node 85), (.node 74)) := by decide +kernel
private theorem node095_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 95 = t095 := by
  exact parent_eq (h₀ := 11) (h₁ := 11) row095_eq
    (fun f hf => node085_eq f hf) (fun f hf => node074_eq f hf) f hf

private def t096 : Tree := .node t094 t095
private theorem row096_eq : program.nodes 96 = ((.node 94), (.node 95)) := by decide +kernel
private theorem node096_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 96 = t096 := by
  exact parent_eq (h₀ := 13) (h₁ := 12) row096_eq
    (fun f hf => node094_eq f hf) (fun f hf => node095_eq f hf) f hf

private def t097 : Tree := .node t058 t057
private theorem row097_eq : program.nodes 97 = ((.node 58), (.node 57)) := by decide +kernel
private theorem node097_eq (f : Nat) (hf : 10 ≤ f) : toTree program f 97 = t097 := by
  exact parent_eq (h₀ := 9) (h₁ := 8) row097_eq
    (fun f hf => node058_eq f hf) (fun f hf => node057_eq f hf) f hf

private def t098 : Tree := .node t072 t058
private theorem row098_eq : program.nodes 98 = ((.node 72), (.node 58)) := by decide +kernel
private theorem node098_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 98 = t098 := by
  exact parent_eq (h₀ := 11) (h₁ := 9) row098_eq
    (fun f hf => node072_eq f hf) (fun f hf => node058_eq f hf) f hf

private def t099 : Tree := .node t097 t084
private theorem row099_eq : program.nodes 99 = ((.node 97), (.node 84)) := by decide +kernel
private theorem node099_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 99 = t099 := by
  exact parent_eq (h₀ := 10) (h₁ := 14) row099_eq
    (fun f hf => node097_eq f hf) (fun f hf => node084_eq f hf) f hf

private def t100 : Tree := .node t098 t099
private theorem row100_eq : program.nodes 100 = ((.node 98), (.node 99)) := by decide +kernel
private theorem node100_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 100 = t100 := by
  exact parent_eq (h₀ := 12) (h₁ := 15) row100_eq
    (fun f hf => node098_eq f hf) (fun f hf => node099_eq f hf) f hf

private def t101 : Tree := .node t047 t100
private theorem row101_eq : program.nodes 101 = ((.node 47), (.node 100)) := by decide +kernel
private theorem node101_eq (f : Nat) (hf : 17 ≤ f) : toTree program f 101 = t101 := by
  exact parent_eq (h₀ := 10) (h₁ := 16) row101_eq
    (fun f hf => node047_eq f hf) (fun f hf => node100_eq f hf) f hf

private def t102 : Tree := .node t078 t080
private theorem row102_eq : program.nodes 102 = ((.node 78), (.node 80)) := by decide +kernel
private theorem node102_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 102 = t102 := by
  exact parent_eq (h₀ := 12) (h₁ := 13) row102_eq
    (fun f hf => node078_eq f hf) (fun f hf => node080_eq f hf) f hf

private def t103 : Tree := .node t102 t095
private theorem row103_eq : program.nodes 103 = ((.node 102), (.node 95)) := by decide +kernel
private theorem node103_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 103 = t103 := by
  exact parent_eq (h₀ := 14) (h₁ := 12) row103_eq
    (fun f hf => node102_eq f hf) (fun f hf => node095_eq f hf) f hf

private def t104 : Tree := .node t101 t103
private theorem row104_eq : program.nodes 104 = ((.node 101), (.node 103)) := by decide +kernel
private theorem node104_eq (f : Nat) (hf : 18 ≤ f) : toTree program f 104 = t104 := by
  exact parent_eq (h₀ := 17) (h₁ := 15) row104_eq
    (fun f hf => node101_eq f hf) (fun f hf => node103_eq f hf) f hf

private def t105 : Tree := .node t052 t104
private theorem row105_eq : program.nodes 105 = ((.node 52), (.node 104)) := by decide +kernel
private theorem node105_eq (f : Nat) (hf : 19 ≤ f) : toTree program f 105 = t105 := by
  exact parent_eq (h₀ := 1) (h₁ := 18) row105_eq
    (fun f hf => node052_eq f hf) (fun f hf => node104_eq f hf) f hf

private def t106 : Tree := .node t057 t058
private theorem row106_eq : program.nodes 106 = ((.node 57), (.node 58)) := by decide +kernel
private theorem node106_eq (f : Nat) (hf : 10 ≤ f) : toTree program f 106 = t106 := by
  exact parent_eq (h₀ := 8) (h₁ := 9) row106_eq
    (fun f hf => node057_eq f hf) (fun f hf => node058_eq f hf) f hf

private def t107 : Tree := .node t105 t106
private theorem row107_eq : program.nodes 107 = ((.node 105), (.node 106)) := by decide +kernel
private theorem node107_eq (f : Nat) (hf : 20 ≤ f) : toTree program f 107 = t107 := by
  exact parent_eq (h₀ := 19) (h₁ := 10) row107_eq
    (fun f hf => node105_eq f hf) (fun f hf => node106_eq f hf) f hf

private def t108 : Tree := .node t097 t107
private theorem row108_eq : program.nodes 108 = ((.node 97), (.node 107)) := by decide +kernel
private theorem node108_eq (f : Nat) (hf : 21 ≤ f) : toTree program f 108 = t108 := by
  exact parent_eq (h₀ := 10) (h₁ := 20) row108_eq
    (fun f hf => node097_eq f hf) (fun f hf => node107_eq f hf) f hf

private def t109 : Tree := .node t096 t108
private theorem row109_eq : program.nodes 109 = ((.node 96), (.node 108)) := by decide +kernel
private theorem node109_eq (f : Nat) (hf : 22 ≤ f) : toTree program f 109 = t109 := by
  exact parent_eq (h₀ := 14) (h₁ := 21) row109_eq
    (fun f hf => node096_eq f hf) (fun f hf => node108_eq f hf) f hf

private def t110 : Tree := .node t083 t109
private theorem row110_eq : program.nodes 110 = ((.node 83), (.node 109)) := by decide +kernel
private theorem node110_eq (f : Nat) (hf : 23 ≤ f) : toTree program f 110 = t110 := by
  exact parent_eq (h₀ := 16) (h₁ := 22) row110_eq
    (fun f hf => node083_eq f hf) (fun f hf => node109_eq f hf) f hf

private def t111 : Tree := .node t098 t085
private theorem row111_eq : program.nodes 111 = ((.node 98), (.node 85)) := by decide +kernel
private theorem node111_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 111 = t111 := by
  exact parent_eq (h₀ := 12) (h₁ := 11) row111_eq
    (fun f hf => node098_eq f hf) (fun f hf => node085_eq f hf) f hf

private def t112 : Tree := .node t059 t111
private theorem row112_eq : program.nodes 112 = ((.node 59), (.node 111)) := by decide +kernel
private theorem node112_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 112 = t112 := by
  exact parent_eq (h₀ := 13) (h₁ := 13) row112_eq
    (fun f hf => node059_eq f hf) (fun f hf => node111_eq f hf) f hf

private def t113 : Tree := .node t084 t092
private theorem row113_eq : program.nodes 113 = ((.node 84), (.node 92)) := by decide +kernel
private theorem node113_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 113 = t113 := by
  exact parent_eq (h₀ := 14) (h₁ := 14) row113_eq
    (fun f hf => node084_eq f hf) (fun f hf => node092_eq f hf) f hf

private def t114 : Tree := .node t112 t113
private theorem row114_eq : program.nodes 114 = ((.node 112), (.node 113)) := by decide +kernel
private theorem node114_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 114 = t114 := by
  exact parent_eq (h₀ := 14) (h₁ := 15) row114_eq
    (fun f hf => node112_eq f hf) (fun f hf => node113_eq f hf) f hf

private def t115 : Tree := .node t110 t114
private theorem row115_eq : program.nodes 115 = ((.node 110), (.node 114)) := by decide +kernel
private theorem node115_eq (f : Nat) (hf : 24 ≤ f) : toTree program f 115 = t115 := by
  exact parent_eq (h₀ := 23) (h₁ := 16) row115_eq
    (fun f hf => node110_eq f hf) (fun f hf => node114_eq f hf) f hf

private def t116 : Tree := .node t093 t115
private theorem row116_eq : program.nodes 116 = ((.node 93), (.node 115)) := by decide +kernel
private theorem node116_eq (f : Nat) (hf : 25 ≤ f) : toTree program f 116 = t116 := by
  exact parent_eq (h₀ := 15) (h₁ := 24) row116_eq
    (fun f hf => node093_eq f hf) (fun f hf => node115_eq f hf) f hf

private def t117 : Tree := .node t087 t116
private theorem row117_eq : program.nodes 117 = ((.node 87), (.node 116)) := by decide +kernel
private theorem node117_eq (f : Nat) (hf : 26 ≤ f) : toTree program f 117 = t117 := by
  exact parent_eq (h₀ := 16) (h₁ := 25) row117_eq
    (fun f hf => node087_eq f hf) (fun f hf => node116_eq f hf) f hf

private def t118 : Tree := .node t068 t094
private theorem row118_eq : program.nodes 118 = ((.node 68), (.node 94)) := by decide +kernel
private theorem node118_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 118 = t118 := by
  exact parent_eq (h₀ := 10) (h₁ := 13) row118_eq
    (fun f hf => node068_eq f hf) (fun f hf => node094_eq f hf) f hf

private def t119 : Tree := .node t063 t074
private theorem row119_eq : program.nodes 119 = ((.node 63), (.node 74)) := by decide +kernel
private theorem node119_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 119 = t119 := by
  exact parent_eq (h₀ := 10) (h₁ := 11) row119_eq
    (fun f hf => node063_eq f hf) (fun f hf => node074_eq f hf) f hf

private def t120 : Tree := .node t119 t080
private theorem row120_eq : program.nodes 120 = ((.node 119), (.node 80)) := by decide +kernel
private theorem node120_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 120 = t120 := by
  exact parent_eq (h₀ := 12) (h₁ := 13) row120_eq
    (fun f hf => node119_eq f hf) (fun f hf => node080_eq f hf) f hf

private def t121 : Tree := .node t078 t106
private theorem row121_eq : program.nodes 121 = ((.node 78), (.node 106)) := by decide +kernel
private theorem node121_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 121 = t121 := by
  exact parent_eq (h₀ := 12) (h₁ := 10) row121_eq
    (fun f hf => node078_eq f hf) (fun f hf => node106_eq f hf) f hf

private def t122 : Tree := .node t074 t076
private theorem row122_eq : program.nodes 122 = ((.node 74), (.node 76)) := by decide +kernel
private theorem node122_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 122 = t122 := by
  exact parent_eq (h₀ := 11) (h₁ := 9) row122_eq
    (fun f hf => node074_eq f hf) (fun f hf => node076_eq f hf) f hf

private def t123 : Tree := .node t121 t122
private theorem row123_eq : program.nodes 123 = ((.node 121), (.node 122)) := by decide +kernel
private theorem node123_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 123 = t123 := by
  exact parent_eq (h₀ := 13) (h₁ := 12) row123_eq
    (fun f hf => node121_eq f hf) (fun f hf => node122_eq f hf) f hf

private def t124 : Tree := .node t120 t123
private theorem row124_eq : program.nodes 124 = ((.node 120), (.node 123)) := by decide +kernel
private theorem node124_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 124 = t124 := by
  exact parent_eq (h₀ := 14) (h₁ := 14) row124_eq
    (fun f hf => node120_eq f hf) (fun f hf => node123_eq f hf) f hf

private def t125 : Tree := .node t118 t124
private theorem row125_eq : program.nodes 125 = ((.node 118), (.node 124)) := by decide +kernel
private theorem node125_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 125 = t125 := by
  exact parent_eq (h₀ := 14) (h₁ := 15) row125_eq
    (fun f hf => node118_eq f hf) (fun f hf => node124_eq f hf) f hf

private def t126 : Tree := .node t057 t089
private theorem row126_eq : program.nodes 126 = ((.node 57), (.node 89)) := by decide +kernel
private theorem node126_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 126 = t126 := by
  exact parent_eq (h₀ := 8) (h₁ := 11) row126_eq
    (fun f hf => node057_eq f hf) (fun f hf => node089_eq f hf) f hf

private def t127 : Tree := .node t089 t126
private theorem row127_eq : program.nodes 127 = ((.node 89), (.node 126)) := by decide +kernel
private theorem node127_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 127 = t127 := by
  exact parent_eq (h₀ := 11) (h₁ := 12) row127_eq
    (fun f hf => node089_eq f hf) (fun f hf => node126_eq f hf) f hf

private def t128 : Tree := .node t127 t091
private theorem row128_eq : program.nodes 128 = ((.node 127), (.node 91)) := by decide +kernel
private theorem node128_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 128 = t128 := by
  exact parent_eq (h₀ := 13) (h₁ := 13) row128_eq
    (fun f hf => node127_eq f hf) (fun f hf => node091_eq f hf) f hf

private def t129 : Tree := .node t081 t128
private theorem row129_eq : program.nodes 129 = ((.node 81), (.node 128)) := by decide +kernel
private theorem node129_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 129 = t129 := by
  exact parent_eq (h₀ := 14) (h₁ := 14) row129_eq
    (fun f hf => node081_eq f hf) (fun f hf => node128_eq f hf) f hf

private def t130 : Tree := .node t129 t063
private theorem row130_eq : program.nodes 130 = ((.node 129), (.node 63)) := by decide +kernel
private theorem node130_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 130 = t130 := by
  exact parent_eq (h₀ := 15) (h₁ := 10) row130_eq
    (fun f hf => node129_eq f hf) (fun f hf => node063_eq f hf) f hf

private def t131 : Tree := .node t075 t130
private theorem row131_eq : program.nodes 131 = ((.node 75), (.node 130)) := by decide +kernel
private theorem node131_eq (f : Nat) (hf : 17 ≤ f) : toTree program f 131 = t131 := by
  exact parent_eq (h₀ := 9) (h₁ := 16) row131_eq
    (fun f hf => node075_eq f hf) (fun f hf => node130_eq f hf) f hf

private def t132 : Tree := .node t131 t102
private theorem row132_eq : program.nodes 132 = ((.node 131), (.node 102)) := by decide +kernel
private theorem node132_eq (f : Nat) (hf : 18 ≤ f) : toTree program f 132 = t132 := by
  exact parent_eq (h₀ := 17) (h₁ := 14) row132_eq
    (fun f hf => node131_eq f hf) (fun f hf => node102_eq f hf) f hf

private def t133 : Tree := .node t125 t132
private theorem row133_eq : program.nodes 133 = ((.node 125), (.node 132)) := by decide +kernel
private theorem node133_eq (f : Nat) (hf : 19 ≤ f) : toTree program f 133 = t133 := by
  exact parent_eq (h₀ := 16) (h₁ := 18) row133_eq
    (fun f hf => node125_eq f hf) (fun f hf => node132_eq f hf) f hf

private def t134 : Tree := .node t117 t133
private theorem row134_eq : program.nodes 134 = ((.node 117), (.node 133)) := by decide +kernel
private theorem node134_eq (f : Nat) (hf : 27 ≤ f) : toTree program f 134 = t134 := by
  exact parent_eq (h₀ := 26) (h₁ := 19) row134_eq
    (fun f hf => node117_eq f hf) (fun f hf => node133_eq f hf) f hf

private def t135 : Tree := .node t106 t127
private theorem row135_eq : program.nodes 135 = ((.node 106), (.node 127)) := by decide +kernel
private theorem node135_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 135 = t135 := by
  exact parent_eq (h₀ := 10) (h₁ := 13) row135_eq
    (fun f hf => node106_eq f hf) (fun f hf => node127_eq f hf) f hf

private def t136 : Tree := .node t074 t074
private theorem row136_eq : program.nodes 136 = ((.node 74), (.node 74)) := by decide +kernel
private theorem node136_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 136 = t136 := by
  exact parent_eq (h₀ := 11) (h₁ := 11) row136_eq
    (fun f hf => node074_eq f hf) (fun f hf => node074_eq f hf) f hf

private def t137 : Tree := .node t136 t122
private theorem row137_eq : program.nodes 137 = ((.node 136), (.node 122)) := by decide +kernel
private theorem node137_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 137 = t137 := by
  exact parent_eq (h₀ := 12) (h₁ := 12) row137_eq
    (fun f hf => node136_eq f hf) (fun f hf => node122_eq f hf) f hf

private def t138 : Tree := .node t118 t137
private theorem row138_eq : program.nodes 138 = ((.node 118), (.node 137)) := by decide +kernel
private theorem node138_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 138 = t138 := by
  exact parent_eq (h₀ := 14) (h₁ := 13) row138_eq
    (fun f hf => node118_eq f hf) (fun f hf => node137_eq f hf) f hf

private def t139 : Tree := .node t138 t128
private theorem row139_eq : program.nodes 139 = ((.node 138), (.node 128)) := by decide +kernel
private theorem node139_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 139 = t139 := by
  exact parent_eq (h₀ := 15) (h₁ := 14) row139_eq
    (fun f hf => node138_eq f hf) (fun f hf => node128_eq f hf) f hf

private def t140 : Tree := .node t131 t139
private theorem row140_eq : program.nodes 140 = ((.node 131), (.node 139)) := by decide +kernel
private theorem node140_eq (f : Nat) (hf : 18 ≤ f) : toTree program f 140 = t140 := by
  exact parent_eq (h₀ := 17) (h₁ := 16) row140_eq
    (fun f hf => node131_eq f hf) (fun f hf => node139_eq f hf) f hf

private def t141 : Tree := .node t135 t140
private theorem row141_eq : program.nodes 141 = ((.node 135), (.node 140)) := by decide +kernel
private theorem node141_eq (f : Nat) (hf : 19 ≤ f) : toTree program f 141 = t141 := by
  exact parent_eq (h₀ := 14) (h₁ := 18) row141_eq
    (fun f hf => node135_eq f hf) (fun f hf => node140_eq f hf) f hf

private def t142 : Tree := .node t134 t141
private theorem row142_eq : program.nodes 142 = ((.node 134), (.node 141)) := by decide +kernel
private theorem node142_eq (f : Nat) (hf : 28 ≤ f) : toTree program f 142 = t142 := by
  exact parent_eq (h₀ := 27) (h₁ := 19) row142_eq
    (fun f hf => node134_eq f hf) (fun f hf => node141_eq f hf) f hf

private def t143 : Tree := .node t142 t106
private theorem row143_eq : program.nodes 143 = ((.node 142), (.node 106)) := by decide +kernel
private theorem node143_eq (f : Nat) (hf : 29 ≤ f) : toTree program f 143 = t143 := by
  exact parent_eq (h₀ := 28) (h₁ := 10) row143_eq
    (fun f hf => node142_eq f hf) (fun f hf => node106_eq f hf) f hf

private def t144 : Tree := .node t083 t143
private theorem row144_eq : program.nodes 144 = ((.node 83), (.node 143)) := by decide +kernel
private theorem node144_eq (f : Nat) (hf : 30 ≤ f) : toTree program f 144 = t144 := by
  exact parent_eq (h₀ := 16) (h₁ := 29) row144_eq
    (fun f hf => node083_eq f hf) (fun f hf => node143_eq f hf) f hf

private def t145 : Tree := .node t047 t122
private theorem row145_eq : program.nodes 145 = ((.node 47), (.node 122)) := by decide +kernel
private theorem node145_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 145 = t145 := by
  exact parent_eq (h₀ := 10) (h₁ := 12) row145_eq
    (fun f hf => node047_eq f hf) (fun f hf => node122_eq f hf) f hf

private def t146 : Tree := .node t072 t091
private theorem row146_eq : program.nodes 146 = ((.node 72), (.node 91)) := by decide +kernel
private theorem node146_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 146 = t146 := by
  exact parent_eq (h₀ := 11) (h₁ := 13) row146_eq
    (fun f hf => node072_eq f hf) (fun f hf => node091_eq f hf) f hf

private def t147 : Tree := .node t145 t146
private theorem row147_eq : program.nodes 147 = ((.node 145), (.node 146)) := by decide +kernel
private theorem node147_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 147 = t147 := by
  exact parent_eq (h₀ := 13) (h₁ := 14) row147_eq
    (fun f hf => node145_eq f hf) (fun f hf => node146_eq f hf) f hf

private def t148 : Tree := .node t147 t135
private theorem row148_eq : program.nodes 148 = ((.node 147), (.node 135)) := by decide +kernel
private theorem node148_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 148 = t148 := by
  exact parent_eq (h₀ := 15) (h₁ := 14) row148_eq
    (fun f hf => node147_eq f hf) (fun f hf => node135_eq f hf) f hf

private def t149 : Tree := .node t106 t148
private theorem row149_eq : program.nodes 149 = ((.node 106), (.node 148)) := by decide +kernel
private theorem node149_eq (f : Nat) (hf : 17 ≤ f) : toTree program f 149 = t149 := by
  exact parent_eq (h₀ := 10) (h₁ := 16) row149_eq
    (fun f hf => node106_eq f hf) (fun f hf => node148_eq f hf) f hf

private def t150 : Tree := .node t127 t094
private theorem row150_eq : program.nodes 150 = ((.node 127), (.node 94)) := by decide +kernel
private theorem node150_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 150 = t150 := by
  exact parent_eq (h₀ := 13) (h₁ := 13) row150_eq
    (fun f hf => node127_eq f hf) (fun f hf => node094_eq f hf) f hf

private def t151 : Tree := .node t091 t150
private theorem row151_eq : program.nodes 151 = ((.node 91), (.node 150)) := by decide +kernel
private theorem node151_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 151 = t151 := by
  exact parent_eq (h₀ := 13) (h₁ := 14) row151_eq
    (fun f hf => node091_eq f hf) (fun f hf => node150_eq f hf) f hf

private def t152 : Tree := .node t149 t151
private theorem row152_eq : program.nodes 152 = ((.node 149), (.node 151)) := by decide +kernel
private theorem node152_eq (f : Nat) (hf : 18 ≤ f) : toTree program f 152 = t152 := by
  exact parent_eq (h₀ := 17) (h₁ := 15) row152_eq
    (fun f hf => node149_eq f hf) (fun f hf => node151_eq f hf) f hf

private def t153 : Tree := .node t144 t152
private theorem row153_eq : program.nodes 153 = ((.node 144), (.node 152)) := by decide +kernel
private theorem node153_eq (f : Nat) (hf : 31 ≤ f) : toTree program f 153 = t153 := by
  exact parent_eq (h₀ := 30) (h₁ := 18) row153_eq
    (fun f hf => node144_eq f hf) (fun f hf => node152_eq f hf) f hf

private def t154 : Tree := .node t075 t153
private theorem row154_eq : program.nodes 154 = ((.node 75), (.node 153)) := by decide +kernel
private theorem node154_eq (f : Nat) (hf : 32 ≤ f) : toTree program f 154 = t154 := by
  exact parent_eq (h₀ := 9) (h₁ := 31) row154_eq
    (fun f hf => node075_eq f hf) (fun f hf => node153_eq f hf) f hf

private def t155 : Tree := .node t094 t099
private theorem row155_eq : program.nodes 155 = ((.node 94), (.node 99)) := by decide +kernel
private theorem node155_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 155 = t155 := by
  exact parent_eq (h₀ := 13) (h₁ := 15) row155_eq
    (fun f hf => node094_eq f hf) (fun f hf => node099_eq f hf) f hf

private def t156 : Tree := .node t063 t155
private theorem row156_eq : program.nodes 156 = ((.node 63), (.node 155)) := by decide +kernel
private theorem node156_eq (f : Nat) (hf : 17 ≤ f) : toTree program f 156 = t156 := by
  exact parent_eq (h₀ := 10) (h₁ := 16) row156_eq
    (fun f hf => node063_eq f hf) (fun f hf => node155_eq f hf) f hf

private def t157 : Tree := .node t154 t156
private theorem row157_eq : program.nodes 157 = ((.node 154), (.node 156)) := by decide +kernel
private theorem node157_eq (f : Nat) (hf : 33 ≤ f) : toTree program f 157 = t157 := by
  exact parent_eq (h₀ := 32) (h₁ := 17) row157_eq
    (fun f hf => node154_eq f hf) (fun f hf => node156_eq f hf) f hf

private def t158 : Tree := .node t074 t157
private theorem row158_eq : program.nodes 158 = ((.node 74), (.node 157)) := by decide +kernel
private theorem node158_eq (f : Nat) (hf : 34 ≤ f) : toTree program f 158 = t158 := by
  exact parent_eq (h₀ := 11) (h₁ := 33) row158_eq
    (fun f hf => node074_eq f hf) (fun f hf => node157_eq f hf) f hf

private def t159 : Tree := .node t063 t084
private theorem row159_eq : program.nodes 159 = ((.node 63), (.node 84)) := by decide +kernel
private theorem node159_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 159 = t159 := by
  exact parent_eq (h₀ := 10) (h₁ := 14) row159_eq
    (fun f hf => node063_eq f hf) (fun f hf => node084_eq f hf) f hf

private def t160 : Tree := .node (.leaf (.decnz 3)) t028
private theorem row160_eq : program.nodes 160 = ((.decnz 3), (.node 28)) := by decide +kernel
private theorem node160_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 160 = t160 := by
  exact parent_eq (h₀ := 0) (h₁ := 2) row160_eq
    (fun _ _ => rfl) (fun f hf => node028_eq f hf) f hf

private def t161 : Tree := .node t127 t160
private theorem row161_eq : program.nodes 161 = ((.node 127), (.node 160)) := by decide +kernel
private theorem node161_eq (f : Nat) (hf : 14 ≤ f) : toTree program f 161 = t161 := by
  exact parent_eq (h₀ := 13) (h₁ := 3) row161_eq
    (fun f hf => node127_eq f hf) (fun f hf => node160_eq f hf) f hf

private def t162 : Tree := .node t127 t161
private theorem row162_eq : program.nodes 162 = ((.node 127), (.node 161)) := by decide +kernel
private theorem node162_eq (f : Nat) (hf : 15 ≤ f) : toTree program f 162 = t162 := by
  exact parent_eq (h₀ := 13) (h₁ := 14) row162_eq
    (fun f hf => node127_eq f hf) (fun f hf => node161_eq f hf) f hf

private def t163 : Tree := .node t097 t162
private theorem row163_eq : program.nodes 163 = ((.node 97), (.node 162)) := by decide +kernel
private theorem node163_eq (f : Nat) (hf : 16 ≤ f) : toTree program f 163 = t163 := by
  exact parent_eq (h₀ := 10) (h₁ := 15) row163_eq
    (fun f hf => node097_eq f hf) (fun f hf => node162_eq f hf) f hf

private def t164 : Tree := .node t159 t163
private theorem row164_eq : program.nodes 164 = ((.node 159), (.node 163)) := by decide +kernel
private theorem node164_eq (f : Nat) (hf : 17 ≤ f) : toTree program f 164 = t164 := by
  exact parent_eq (h₀ := 15) (h₁ := 16) row164_eq
    (fun f hf => node159_eq f hf) (fun f hf => node163_eq f hf) f hf

private def t165 : Tree := .node t158 t164
private theorem row165_eq : program.nodes 165 = ((.node 158), (.node 164)) := by decide +kernel
private theorem node165_eq (f : Nat) (hf : 35 ≤ f) : toTree program f 165 = t165 := by
  exact parent_eq (h₀ := 34) (h₁ := 17) row165_eq
    (fun f hf => node158_eq f hf) (fun f hf => node164_eq f hf) f hf

private def t166 : Tree := .node t073 t165
private theorem row166_eq : program.nodes 166 = ((.node 73), (.node 165)) := by decide +kernel
private theorem node166_eq (f : Nat) (hf : 36 ≤ f) : toTree program f 166 = t166 := by
  exact parent_eq (h₀ := 12) (h₁ := 35) row166_eq
    (fun f hf => node073_eq f hf) (fun f hf => node165_eq f hf) f hf

private def t167 : Tree := .node t071 t166
private theorem row167_eq : program.nodes 167 = ((.node 71), (.node 166)) := by decide +kernel
private theorem node167_eq (f : Nat) (hf : 37 ≤ f) : toTree program f 167 = t167 := by
  exact parent_eq (h₀ := 14) (h₁ := 36) row167_eq
    (fun f hf => node071_eq f hf) (fun f hf => node166_eq f hf) f hf

private def t168 : Tree := .node (.leaf (.decnz 5)) (.leaf (.cont 2))
private theorem row168_eq : program.nodes 168 = ((.decnz 5), (.cont 2)) := by decide +kernel
private theorem node168_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 168 = t168 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row168_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t169 : Tree := .node t045 (.leaf (.inc 5))
private theorem row169_eq : program.nodes 169 = ((.node 45), (.inc 5)) := by decide +kernel
private theorem node169_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 169 = t169 := by
  exact parent_eq (h₀ := 2) (h₁ := 0) row169_eq
    (fun f hf => node045_eq f hf) (fun _ _ => rfl) f hf

private def t170 : Tree := .node t168 t169
private theorem row170_eq : program.nodes 170 = ((.node 168), (.node 169)) := by decide +kernel
private theorem node170_eq (f : Nat) (hf : 4 ≤ f) : toTree program f 170 = t170 := by
  exact parent_eq (h₀ := 1) (h₁ := 3) row170_eq
    (fun f hf => node168_eq f hf) (fun f hf => node169_eq f hf) f hf

private def t171 : Tree := .node (.leaf (.decnz 6)) t170
private theorem row171_eq : program.nodes 171 = ((.decnz 6), (.node 170)) := by decide +kernel
private theorem node171_eq (f : Nat) (hf : 5 ≤ f) : toTree program f 171 = t171 := by
  exact parent_eq (h₀ := 0) (h₁ := 4) row171_eq
    (fun _ _ => rfl) (fun f hf => node170_eq f hf) f hf

private def t172 : Tree := .node (.leaf (.decnz 5)) (.leaf (.cont 1))
private theorem row172_eq : program.nodes 172 = ((.decnz 5), (.cont 1)) := by decide +kernel
private theorem node172_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 172 = t172 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row172_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t173 : Tree := .node t172 (.leaf (.brk 1))
private theorem row173_eq : program.nodes 173 = ((.node 172), (.brk 1)) := by decide +kernel
private theorem node173_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 173 = t173 := by
  exact parent_eq (h₀ := 1) (h₁ := 0) row173_eq
    (fun f hf => node172_eq f hf) (fun _ _ => rfl) f hf

private def t174 : Tree := .node (.leaf (.decnz 5)) t173
private theorem row174_eq : program.nodes 174 = ((.decnz 5), (.node 173)) := by decide +kernel
private theorem node174_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 174 = t174 := by
  exact parent_eq (h₀ := 0) (h₁ := 2) row174_eq
    (fun _ _ => rfl) (fun f hf => node173_eq f hf) f hf

private def t175 : Tree := .node t171 t174
private theorem row175_eq : program.nodes 175 = ((.node 171), (.node 174)) := by decide +kernel
private theorem node175_eq (f : Nat) (hf : 6 ≤ f) : toTree program f 175 = t175 := by
  exact parent_eq (h₀ := 5) (h₁ := 3) row175_eq
    (fun f hf => node171_eq f hf) (fun f hf => node174_eq f hf) f hf

private def t176 : Tree := .node (.leaf (.decnz 1)) (.leaf (.cont 1))
private theorem row176_eq : program.nodes 176 = ((.decnz 1), (.cont 1)) := by decide +kernel
private theorem node176_eq (f : Nat) (hf : 1 ≤ f) : toTree program f 176 = t176 := by
  exact parent_eq (h₀ := 0) (h₁ := 0) row176_eq
    (fun _ _ => rfl) (fun _ _ => rfl) f hf

private def t177 : Tree := .node t175 t176
private theorem row177_eq : program.nodes 177 = ((.node 175), (.node 176)) := by decide +kernel
private theorem node177_eq (f : Nat) (hf : 7 ≤ f) : toTree program f 177 = t177 := by
  exact parent_eq (h₀ := 6) (h₁ := 1) row177_eq
    (fun f hf => node175_eq f hf) (fun f hf => node176_eq f hf) f hf

private def t178 : Tree := .node (.leaf (.decnz 4)) t044
private theorem row178_eq : program.nodes 178 = ((.decnz 4), (.node 44)) := by decide +kernel
private theorem node178_eq (f : Nat) (hf : 2 ≤ f) : toTree program f 178 = t178 := by
  exact parent_eq (h₀ := 0) (h₁ := 1) row178_eq
    (fun _ _ => rfl) (fun f hf => node044_eq f hf) f hf

private def t179 : Tree := .node t011 t178
private theorem row179_eq : program.nodes 179 = ((.node 11), (.node 178)) := by decide +kernel
private theorem node179_eq (f : Nat) (hf : 3 ≤ f) : toTree program f 179 = t179 := by
  exact parent_eq (h₀ := 2) (h₁ := 2) row179_eq
    (fun f hf => node011_eq f hf) (fun f hf => node178_eq f hf) f hf

private def t180 : Tree := .node t177 t179
private theorem row180_eq : program.nodes 180 = ((.node 177), (.node 179)) := by decide +kernel
private theorem node180_eq (f : Nat) (hf : 8 ≤ f) : toTree program f 180 = t180 := by
  exact parent_eq (h₀ := 7) (h₁ := 3) row180_eq
    (fun f hf => node177_eq f hf) (fun f hf => node179_eq f hf) f hf

private def t181 : Tree := .node t180 t177
private theorem row181_eq : program.nodes 181 = ((.node 180), (.node 177)) := by decide +kernel
private theorem node181_eq (f : Nat) (hf : 9 ≤ f) : toTree program f 181 = t181 := by
  exact parent_eq (h₀ := 8) (h₁ := 7) row181_eq
    (fun f hf => node180_eq f hf) (fun f hf => node177_eq f hf) f hf

private def t182 : Tree := .node t167 t181
private theorem row182_eq : program.nodes 182 = ((.node 167), (.node 181)) := by decide +kernel
private theorem node182_eq (f : Nat) (hf : 38 ≤ f) : toTree program f 182 = t182 := by
  exact parent_eq (h₀ := 37) (h₁ := 9) row182_eq
    (fun f hf => node167_eq f hf) (fun f hf => node181_eq f hf) f hf

private def t183 : Tree := .node t059 t182
private theorem row183_eq : program.nodes 183 = ((.node 59), (.node 182)) := by decide +kernel
private theorem node183_eq (f : Nat) (hf : 39 ≤ f) : toTree program f 183 = t183 := by
  exact parent_eq (h₀ := 13) (h₁ := 38) row183_eq
    (fun f hf => node059_eq f hf) (fun f hf => node182_eq f hf) f hf

private def t184 : Tree := .node t183 (.leaf (.brk 1))
private theorem row184_eq : program.nodes 184 = ((.node 183), (.brk 1)) := by decide +kernel
private theorem node184_eq (f : Nat) (hf : 40 ≤ f) : toTree program f 184 = t184 := by
  exact parent_eq (h₀ := 39) (h₁ := 0) row184_eq
    (fun f hf => node183_eq f hf) (fun _ _ => rfl) f hf

private def t185 : Tree := .node (.leaf (.decnz 3)) t184
private theorem row185_eq : program.nodes 185 = ((.decnz 3), (.node 184)) := by decide +kernel
private theorem node185_eq (f : Nat) (hf : 41 ≤ f) : toTree program f 185 = t185 := by
  exact parent_eq (h₀ := 0) (h₁ := 40) row185_eq
    (fun _ _ => rfl) (fun f hf => node184_eq f hf) f hf

private def t186 : Tree := .node t175 (.leaf .halt)
private theorem row186_eq : program.nodes 186 = ((.node 175), .halt) := by decide +kernel
private theorem node186_eq (f : Nat) (hf : 7 ≤ f) : toTree program f 186 = t186 := by
  exact parent_eq (h₀ := 6) (h₁ := 0) row186_eq
    (fun f hf => node175_eq f hf) (fun _ _ => rfl) f hf

private def t187 : Tree := .node t051 t045
private theorem row187_eq : program.nodes 187 = ((.node 51), (.node 45)) := by decide +kernel
private theorem node187_eq (f : Nat) (hf : 8 ≤ f) : toTree program f 187 = t187 := by
  exact parent_eq (h₀ := 7) (h₁ := 2) row187_eq
    (fun f hf => node051_eq f hf) (fun f hf => node045_eq f hf) f hf

private def t188 : Tree := .node t186 t187
private theorem row188_eq : program.nodes 188 = ((.node 186), (.node 187)) := by decide +kernel
private theorem node188_eq (f : Nat) (hf : 9 ≤ f) : toTree program f 188 = t188 := by
  exact parent_eq (h₀ := 7) (h₁ := 8) row188_eq
    (fun f hf => node186_eq f hf) (fun f hf => node187_eq f hf) f hf

private def t189 : Tree := .node (.leaf (.inc 6)) t188
private theorem row189_eq : program.nodes 189 = ((.inc 6), (.node 188)) := by decide +kernel
private theorem node189_eq (f : Nat) (hf : 10 ≤ f) : toTree program f 189 = t189 := by
  exact parent_eq (h₀ := 0) (h₁ := 9) row189_eq
    (fun _ _ => rfl) (fun f hf => node188_eq f hf) f hf

private def t190 : Tree := .node t185 t189
private theorem row190_eq : program.nodes 190 = ((.node 185), (.node 189)) := by decide +kernel
private theorem node190_eq (f : Nat) (hf : 42 ≤ f) : toTree program f 190 = t190 := by
  exact parent_eq (h₀ := 41) (h₁ := 10) row190_eq
    (fun f hf => node185_eq f hf) (fun f hf => node189_eq f hf) f hf

private def t191 : Tree := .node t190 (.leaf (.brk 1))
private theorem row191_eq : program.nodes 191 = ((.node 190), (.brk 1)) := by decide +kernel
private theorem node191_eq (f : Nat) (hf : 43 ≤ f) : toTree program f 191 = t191 := by
  exact parent_eq (h₀ := 42) (h₁ := 0) row191_eq
    (fun f hf => node190_eq f hf) (fun _ _ => rfl) f hf

private def t192 : Tree := .node (.leaf (.decnz 3)) t191
private theorem row192_eq : program.nodes 192 = ((.decnz 3), (.node 191)) := by decide +kernel
private theorem node192_eq (f : Nat) (hf : 44 ≤ f) : toTree program f 192 = t192 := by
  exact parent_eq (h₀ := 0) (h₁ := 43) row192_eq
    (fun _ _ => rfl) (fun f hf => node191_eq f hf) f hf

private def t193 : Tree := .node t192 t047
private theorem row193_eq : program.nodes 193 = ((.node 192), (.node 47)) := by decide +kernel
private theorem node193_eq (f : Nat) (hf : 45 ≤ f) : toTree program f 193 = t193 := by
  exact parent_eq (h₀ := 44) (h₁ := 10) row193_eq
    (fun f hf => node192_eq f hf) (fun f hf => node047_eq f hf) f hf

private def t194 : Tree := .node t193 (.leaf (.brk 1))
private theorem row194_eq : program.nodes 194 = ((.node 193), (.brk 1)) := by decide +kernel
private theorem node194_eq (f : Nat) (hf : 46 ≤ f) : toTree program f 194 = t194 := by
  exact parent_eq (h₀ := 45) (h₁ := 0) row194_eq
    (fun f hf => node193_eq f hf) (fun _ _ => rfl) f hf

private def t195 : Tree := .node (.leaf (.decnz 3)) t194
private theorem row195_eq : program.nodes 195 = ((.decnz 3), (.node 194)) := by decide +kernel
private theorem node195_eq (f : Nat) (hf : 47 ≤ f) : toTree program f 195 = t195 := by
  exact parent_eq (h₀ := 0) (h₁ := 46) row195_eq
    (fun _ _ => rfl) (fun f hf => node194_eq f hf) f hf

private def t196 : Tree := .node t069 t025
private theorem row196_eq : program.nodes 196 = ((.node 69), (.node 25)) := by decide +kernel
private theorem node196_eq (f : Nat) (hf : 12 ≤ f) : toTree program f 196 = t196 := by
  exact parent_eq (h₀ := 11) (h₁ := 2) row196_eq
    (fun f hf => node069_eq f hf) (fun f hf => node025_eq f hf) f hf

private def t197 : Tree := .node t175 t068
private theorem row197_eq : program.nodes 197 = ((.node 175), (.node 68)) := by decide +kernel
private theorem node197_eq (f : Nat) (hf : 11 ≤ f) : toTree program f 197 = t197 := by
  exact parent_eq (h₀ := 6) (h₁ := 10) row197_eq
    (fun f hf => node175_eq f hf) (fun f hf => node068_eq f hf) f hf

private def t198 : Tree := .node t196 t197
private theorem row198_eq : program.nodes 198 = ((.node 196), (.node 197)) := by decide +kernel
private theorem node198_eq (f : Nat) (hf : 13 ≤ f) : toTree program f 198 = t198 := by
  exact parent_eq (h₀ := 12) (h₁ := 11) row198_eq
    (fun f hf => node196_eq f hf) (fun f hf => node197_eq f hf) f hf

private def t199 : Tree := .node t195 t198
private theorem row199_eq : program.nodes 199 = ((.node 195), (.node 198)) := by decide +kernel
private theorem node199_eq (f : Nat) (hf : 48 ≤ f) : toTree program f 199 = t199 := by
  exact parent_eq (h₀ := 47) (h₁ := 13) row199_eq
    (fun f hf => node195_eq f hf) (fun f hf => node198_eq f hf) f hf

private def t200 : Tree := .node t024 t199
private theorem row200_eq : program.nodes 200 = ((.node 24), (.node 199)) := by decide +kernel
private theorem node200_eq (f : Nat) (hf : 49 ≤ f) : toTree program f 200 = t200 := by
  exact parent_eq (h₀ := 8) (h₁ := 48) row200_eq
    (fun f hf => node024_eq f hf) (fun f hf => node199_eq f hf) f hf

private def t201 : Tree := .node t021 t200
private theorem row201_eq : program.nodes 201 = ((.node 21), (.node 200)) := by decide +kernel
private theorem node201_eq (f : Nat) (hf : 50 ≤ f) : toTree program f 201 = t201 := by
  exact parent_eq (h₀ := 8) (h₁ := 49) row201_eq
    (fun f hf => node021_eq f hf) (fun f hf => node200_eq f hf) f hf

private def t202 : Tree := .node t008 t201
private theorem row202_eq : program.nodes 202 = ((.node 8), (.node 201)) := by decide +kernel
private theorem node202_eq (f : Nat) (hf : 51 ≤ f) : toTree program f 202 = t202 := by
  exact parent_eq (h₀ := 5) (h₁ := 50) row202_eq
    (fun f hf => node008_eq f hf) (fun f hf => node201_eq f hf) f hf

/-- The exact complete certificate tree, with shared subterms only. -/
def tree : Tree := t202

/-- Exact identity for every sufficient decoder fuel, not one sampled execution. -/
theorem tree_eq_fuel (f : Nat) (hf : 51 ≤ f) :
    toTree program f program.root = tree := node202_eq f hf

/-- The tree used by the actual RegisterPath program semantics. -/
theorem tree_eq : ptree program = tree := tree_eq_fuel 204 (by decide)

theorem walk_eq_tree (P : List Bool) (i : Nat) :
    walk program (program.nnodes + 1) program.root P i = twalk tree (P.drop i) i := by
  rw [walk_tree]
  change twalk (toTree program 204 program.root) (P.drop i) i = twalk tree (P.drop i) i
  rw [tree_eq_fuel 204 (by decide)]

/-- Complete pointer consumption and all five leaf effects are inherited exactly. -/
theorem step_eq_tree (P : List Bool) (R : Registers) :
    step program ⟨P, R⟩ = match tsite tree P with
      | some (e, Q) => execute e Q R
      | none => none := by
  rw [step_tsite, tree_eq]
  cases hsite : tsite tree P with
  | none => rfl
  | some eQ =>
      rcases eQ with ⟨e, Q⟩
      rfl

def leafCount : Tree → Nat
  | .none => 0
  | .leaf _ => 1
  | .node a b => leafCount a + leafCount b

def nodeCount : Tree → Nat
  | .none | .leaf _ => 0
  | .node a b => nodeCount a + nodeCount b + 1

def depth : Tree → Nat
  | .none | .leaf _ => 0
  | .node a b => max (depth a) (depth b) + 1

def haltCount : Tree → Nat
  | .none => 0
  | .leaf e => if e = .halt then 1 else 0
  | .node a b => haltCount a + haltCount b

theorem leaf_count : leafCount tree = 6460 := by decide +kernel
theorem node_count : nodeCount tree = 6459 := by decide +kernel
theorem depth_eq : depth tree = 51 := by decide +kernel
theorem halt_count : haltCount tree = 1 := by decide +kernel

end TreeRouting245
end SetTheory.BusyBeaver.ZFC
