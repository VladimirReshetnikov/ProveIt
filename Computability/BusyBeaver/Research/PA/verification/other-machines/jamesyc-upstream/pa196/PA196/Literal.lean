module
public import M6.Zip

/-!
Exact PA196 machine generated from `data/pa196.tm`.
SHA-256: e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8

The transition lookup is a balanced decision tree with at most eight state
comparisons, preceded by one domain test in `machine`.
No generated assertion is trusted: the finite claims below use kernel reduction.
-/
@[expose] public section
namespace PA196.Literal
open M6.Zip

/-- Transition data on the working domain `q < 196`. -/
def transition (q : Nat) (read : Bool) : Bool × Bool × Nat :=
  if q < 98 then
    if q < 49 then
      if q < 24 then
        if q < 12 then
          if q < 6 then
            if q < 3 then
              if q < 1 then
                if read then (true, true, 61) else (true, true, 1)
              else
                if q < 2 then
                  if read then (true, true, 1) else (true, true, 82)
                else
                  if read then (true, false, 3) else (false, false, 2)
            else
              if q < 4 then
                if read then (true, false, 3) else (false, false, 4)
              else
                if q < 5 then
                  if read then (true, false, 3) else (false, false, 6)
                else
                  if read then (false, false, 5) else (true, true, 7)
          else
            if q < 9 then
              if q < 7 then
                if read then (true, false, 3) else (false, false, 9)
              else
                if q < 8 then
                  if read then (false, true, 10) else (false, true, 7)
                else
                  if read then (true, true, 13) else (false, true, 14)
            else
              if q < 10 then
                if read then (true, false, 3) else (false, false, 15)
              else
                if q < 11 then
                  if read then (false, true, 10) else (false, false, 16)
                else
                  if read then (true, true, 18) else (false, false, 26)
        else
          if q < 18 then
            if q < 15 then
              if q < 13 then
                if read then (true, true, 20) else (false, true, 19)
              else
                if q < 14 then
                  if read then (true, false, 31) else (false, false, 79)
                else
                  if read then (false, true, 22) else (false, false, 11)
            else
              if q < 16 then
                if read then (true, false, 3) else (false, false, 23)
              else
                if q < 17 then
                  if read then (false, false, 2) else (true, false, 2)
                else
                  if read then (false, true, 32) else (false, true, 24)
          else
            if q < 21 then
              if q < 19 then
                if read then (false, false, 95) else (false, true, 84)
              else
                if q < 20 then
                  if read then (true, true, 29) else (false, true, 28)
                else
                  if read then (true, true, 31) else (false, true, 30)
            else
              if q < 22 then
                if read then (false, true, 57) else (false, true, 24)
              else
                if q < 23 then
                  if read then (true, true, 22) else (false, true, 33)
                else
                  if read then (true, false, 3) else (false, false, 34)
      else
        if q < 36 then
          if q < 30 then
            if q < 27 then
              if q < 25 then
                if read then (false, true, 1) else (false, false, 35)
              else
                if q < 26 then
                  if read then (true, true, 25) else (false, true, 36)
                else
                  if read then (true, true, 41) else (false, true, 122)
            else
              if q < 28 then
                if read then (false, false, 39) else (false, true, 38)
              else
                if q < 29 then
                  if read then (true, true, 41) else (false, true, 40)
                else
                  if read then (true, true, 43) else (false, true, 42)
          else
            if q < 33 then
              if q < 31 then
                if read then (true, true, 45) else (false, true, 44)
              else
                if q < 32 then
                  if read then (true, true, 46) else (false, true, 21)
                else
                  if read then (true, true, 32) else (false, true, 47)
            else
              if q < 34 then
                if read then (true, true, 33) else (false, true, 32)
              else
                if q < 35 then
                  if read then (true, false, 3) else (false, false, 69)
                else
                  if read then (true, false, 2) else (true, true, 35)
        else
          if q < 42 then
            if q < 39 then
              if q < 37 then
                if read then (true, true, 36) else (false, true, 49)
              else
                if q < 38 then
                  if read then (true, true, 20) else (false, true, 28)
                else
                  if read then (false, true, 36) else (false, false, 11)
            else
              if q < 40 then
                if read then (true, false, 51) else (false, false, 5)
              else
                if q < 41 then
                  if read then (false, true, 25) else (false, true, 24)
                else
                  if read then (false, false, 16) else (false, true, 13)
          else
            if q < 45 then
              if q < 43 then
                if read then (true, true, 54) else (false, true, 53)
              else
                if q < 44 then
                  if read then (true, true, 56) else (false, true, 55)
                else
                  if read then (false, true, 52) else (false, true, 24)
            else
              if q < 47 then
                if q < 46 then
                  if read then (true, true, 59) else (false, true, 58)
                else
                  if read then (false, false, 16) else (false, true, 60)
              else
                if q < 48 then
                  if read then (true, true, 47) else (false, true, 25)
                else
                  if read then (false, true, 61) else (false, false, 35)
    else
      if q < 73 then
        if q < 61 then
          if q < 55 then
            if q < 52 then
              if q < 50 then
                if read then (true, true, 49) else (false, true, 16)
              else
                if q < 51 then
                  if read then (true, true, 64) else (false, true, 63)
                else
                  if read then (true, false, 51) else (false, false, 39)
            else
              if q < 53 then
                if read then (true, true, 52) else (false, true, 22)
              else
                if q < 54 then
                  if read then (false, true, 49) else (false, false, 11)
                else
                  if read then (false, false, 16) else (false, true, 58)
          else
            if q < 58 then
              if q < 56 then
                if read then (true, true, 66) else (false, true, 65)
              else
                if q < 57 then
                  if read then (true, true, 67) else (false, true, 59)
                else
                  if read then (true, true, 57) else (false, true, 52)
            else
              if q < 59 then
                if read then (false, true, 25) else (false, true, 48)
              else
                if q < 60 then
                  if read then (true, false, 68) else (false, false, 28)
                else
                  if read then (true, false, 30) else (false, false, 102)
        else
          if q < 67 then
            if q < 64 then
              if q < 62 then
                if read then (true, true, 61) else (false, true, 0)
              else
                if q < 63 then
                  if read then (true, false, 51) else (true, true, 125)
                else
                  if read then (true, true, 196) else (false, true, 70)
            else
              if q < 65 then
                if read then (true, true, 31) else (false, false, 126)
              else
                if q < 66 then
                  if read then (true, true, 60) else (false, true, 40)
                else
                  if read then (true, true, 71) else (false, false, 79)
          else
            if q < 70 then
              if q < 68 then
                if read then (true, false, 72) else (false, true, 53)
              else
                if q < 69 then
                  if read then (true, true, 74) else (false, true, 73)
                else
                  if read then (true, true, 75) else (false, true, 69)
            else
              if q < 71 then
                if read then (true, true, 77) else (false, true, 76)
              else
                if q < 72 then
                  if read then (true, false, 110) else (false, true, 79)
                else
                  if read then (true, true, 54) else (false, false, 98)
      else
        if q < 85 then
          if q < 79 then
            if q < 76 then
              if q < 74 then
                if read then (false, true, 33) else (false, true, 48)
              else
                if q < 75 then
                  if read then (false, false, 41) else (false, true, 81)
                else
                  if read then (true, true, 132) else (false, true, 50)
            else
              if q < 77 then
                if read then (true, true, 21) else (false, true, 130)
              else
                if q < 78 then
                  if read then (true, true, 90) else (false, true, 101)
                else
                  if read then (true, true, 93) else (false, true, 92)
          else
            if q < 82 then
              if q < 80 then
                if read then (true, true, 72) else (false, true, 73)
              else
                if q < 81 then
                  if read then (true, true, 119) else (false, true, 91)
                else
                  if read then (true, true, 96) else (false, true, 95)
            else
              if q < 83 then
                if read then (false, true, 1) else (false, true, 62)
              else
                if q < 84 then
                  if read then (true, true, 97) else (false, true, 27)
                else
                  if read then (true, true, 88) else (false, true, 89)
        else
          if q < 91 then
            if q < 88 then
              if q < 86 then
                if read then (true, false, 85) else (true, false, 99)
              else
                if q < 87 then
                  if read then (true, true, 100) else (false, true, 19)
                else
                  if read then (true, true, 58) else (false, true, 58)
            else
              if q < 89 then
                if read then (true, true, 115) else (false, true, 117)
              else
                if q < 90 then
                  if read then (true, true, 195) else (false, false, 26)
                else
                  if read then (false, false, 131) else (false, true, 95)
          else
            if q < 94 then
              if q < 92 then
                if read then (true, true, 103) else (false, true, 102)
              else
                if q < 93 then
                  if read then (true, true, 56) else (false, true, 67)
                else
                  if read then (true, true, 104) else (false, true, 55)
            else
              if q < 96 then
                if q < 95 then
                  if read then (true, true, 105) else (false, true, 21)
                else
                  if read then (false, false, 10) else (false, true, 21)
              else
                if q < 97 then
                  if read then (true, true, 41) else (false, true, 59)
                else
                  if read then (true, true, 8) else (false, true, 106)
  else
    if q < 147 then
      if q < 122 then
        if q < 110 then
          if q < 104 then
            if q < 101 then
              if q < 99 then
                if read then (true, true, 107) else (false, true, 91)
              else
                if q < 100 then
                  if read then (false, false, 85) else (false, false, 131)
                else
                  if read then (true, true, 94) else (false, true, 108)
            else
              if q < 102 then
                if read then (false, false, 2) else (false, false, 109)
              else
                if q < 103 then
                  if read then (true, true, 68) else (false, true, 38)
                else
                  if read then (true, true, 110) else (false, true, 59)
          else
            if q < 107 then
              if q < 105 then
                if read then (true, true, 111) else (false, true, 59)
              else
                if q < 106 then
                  if read then (false, false, 16) else (false, true, 66)
                else
                  if read then (true, true, 110) else (false, true, 14)
            else
              if q < 108 then
                if read then (true, true, 112) else (false, true, 21)
              else
                if q < 109 then
                  if read then (true, false, 20) else (false, true, 113)
                else
                  if read then (true, true, 65) else (false, true, 30)
        else
          if q < 116 then
            if q < 113 then
              if q < 111 then
                if read then (true, false, 108) else (false, true, 38)
              else
                if q < 112 then
                  if read then (false, false, 16) else (false, true, 121)
                else
                  if read then (false, false, 16) else (false, true, 114)
            else
              if q < 114 then
                if read then (false, true, 47) else (false, true, 24)
              else
                if q < 115 then
                  if read then (false, true, 32) else (false, true, 48)
                else
                  if read then (true, true, 86) else (false, true, 70)
          else
            if q < 119 then
              if q < 117 then
                if read then (true, true, 118) else (false, true, 19)
              else
                if q < 118 then
                  if read then (true, true, 28) else (false, true, 126)
                else
                  if read then (true, true, 107) else (false, true, 122)
            else
              if q < 120 then
                if read then (true, true, 86) else (false, true, 94)
              else
                if q < 121 then
                  if read then (true, true, 98) else (false, true, 83)
                else
                  if read then (true, true, 87) else (false, true, 87)
      else
        if q < 134 then
          if q < 128 then
            if q < 125 then
              if q < 123 then
                if read then (true, false, 109) else (false, true, 17)
              else
                if q < 124 then
                  if read then (true, true, 101) else (false, true, 70)
                else
                  if read then (true, true, 108) else (false, true, 96)
            else
              if q < 126 then
                if read then (true, false, 99) else (true, false, 39)
              else
                if q < 127 then
                  if read then (true, true, 78) else (false, true, 80)
                else
                  if read then (true, true, 133) else (false, true, 120)
          else
            if q < 131 then
              if q < 129 then
                if read then (true, true, 123) else (false, true, 124)
              else
                if q < 130 then
                  if read then (true, true, 128) else (false, true, 123)
                else
                  if read then (true, true, 90) else (false, true, 44)
            else
              if q < 132 then
                if read then (false, false, 131) else (false, false, 5)
              else
                if q < 133 then
                  if read then (true, true, 59) else (false, true, 127)
                else
                  if read then (true, true, 37) else (false, true, 11)
        else
          if q < 140 then
            if q < 137 then
              if q < 135 then
                if read then (true, true, 58) else (false, true, 78)
              else
                if q < 136 then
                  if read then (true, true, 58) else (false, true, 134)
                else
                  if read then (true, true, 135) else (false, true, 86)
            else
              if q < 138 then
                if read then (true, true, 136) else (false, true, 12)
              else
                if q < 139 then
                  if read then (true, true, 140) else (false, false, 168)
                else
                  if read then (true, true, 140) else (false, true, 116)
          else
            if q < 143 then
              if q < 141 then
                if read then (true, true, 78) else (false, false, 158)
              else
                if q < 142 then
                  if read then (true, true, 137) else (false, true, 140)
                else
                  if read then (true, true, 141) else (false, true, 139)
            else
              if q < 145 then
                if q < 144 then
                  if read then (true, true, 142) else (false, true, 138)
                else
                  if read then (true, true, 160) else (false, true, 19)
              else
                if q < 146 then
                  if read then (true, true, 136) else (false, true, 144)
                else
                  if read then (true, true, 144) else (false, true, 145)
    else
      if q < 171 then
        if q < 159 then
          if q < 153 then
            if q < 150 then
              if q < 148 then
                if read then (true, true, 138) else (false, true, 143)
              else
                if q < 149 then
                  if read then (true, true, 147) else (false, true, 126)
                else
                  if read then (true, true, 135) else (false, true, 116)
            else
              if q < 151 then
                if read then (true, true, 149) else (false, true, 12)
              else
                if q < 152 then
                  if read then (true, true, 137) else (false, true, 136)
                else
                  if read then (true, true, 78) else (false, true, 149)
          else
            if q < 156 then
              if q < 154 then
                if read then (true, true, 134) else (false, true, 86)
              else
                if q < 155 then
                  if read then (true, true, 183) else (false, true, 152)
                else
                  if read then (true, true, 174) else (false, true, 150)
            else
              if q < 157 then
                if read then (true, true, 155) else (false, true, 148)
              else
                if q < 158 then
                  if read then (true, true, 156) else (false, true, 78)
                else
                  if read then (true, true, 150) else (false, true, 157)
        else
          if q < 165 then
            if q < 162 then
              if q < 160 then
                if read then (true, true, 153) else (false, true, 116)
              else
                if q < 161 then
                  if read then (true, false, 185) else (false, true, 58)
                else
                  if read then (true, true, 58) else (false, true, 141)
            else
              if q < 163 then
                if read then (true, true, 161) else (false, true, 160)
              else
                if q < 164 then
                  if read then (true, true, 162) else (false, true, 139)
                else
                  if read then (true, true, 163) else (false, true, 162)
          else
            if q < 168 then
              if q < 166 then
                if read then (true, true, 164) else (false, true, 158)
              else
                if q < 167 then
                  if read then (true, true, 165) else (false, true, 86)
                else
                  if read then (true, true, 159) else (false, true, 146)
            else
              if q < 169 then
                if read then (true, true, 167) else (false, true, 166)
              else
                if q < 170 then
                  if read then (true, true, 168) else (false, true, 12)
                else
                  if read then (true, true, 139) else (false, true, 58)
      else
        if q < 183 then
          if q < 177 then
            if q < 174 then
              if q < 172 then
                if read then (true, true, 161) else (false, true, 151)
              else
                if q < 173 then
                  if read then (true, true, 171) else (false, true, 170)
                else
                  if read then (true, true, 137) else (false, true, 172)
            else
              if q < 175 then
                if read then (true, true, 154) else (false, false, 172)
              else
                if q < 176 then
                  if read then (true, true, 183) else (false, true, 174)
                else
                  if read then (true, true, 175) else (false, true, 173)
          else
            if q < 180 then
              if q < 178 then
                if read then (true, true, 154) else (false, true, 176)
              else
                if q < 179 then
                  if read then (true, true, 177) else (false, true, 169)
                else
                  if read then (true, true, 159) else (false, false, 142)
            else
              if q < 181 then
                if read then (true, true, 179) else (false, true, 179)
              else
                if q < 182 then
                  if read then (true, true, 180) else (false, true, 178)
                else
                  if read then (true, true, 181) else (false, true, 64)
        else
          if q < 189 then
            if q < 186 then
              if q < 184 then
                if read then (true, false, 167) else (false, false, 158)
              else
                if q < 185 then
                  if read then (true, true, 78) else (false, true, 183)
                else
                  if read then (true, true, 184) else (false, true, 179)
            else
              if q < 187 then
                if read then (true, true, 185) else (false, true, 145)
              else
                if q < 188 then
                  if read then (true, true, 186) else (false, true, 184)
                else
                  if read then (true, true, 187) else (false, true, 116)
          else
            if q < 192 then
              if q < 190 then
                if read then (true, true, 122) else (false, true, 183)
              else
                if q < 191 then
                  if read then (true, true, 189) else (false, true, 152)
                else
                  if read then (true, true, 190) else (false, true, 188)
            else
              if q < 194 then
                if q < 193 then
                  if read then (true, true, 191) else (false, true, 182)
                else
                  if read then (false, false, 131) else (false, true, 129)
              else
                if q < 195 then
                  if read then (true, true, 193) else (false, true, 192)
                else
                  if read then (true, true, 194) else (false, true, 137)

/-- A binary Turing machine; all labels at least 196 have no transition. -/
def machine : TMN := fun q read =>
  if q < 196 then some (transition q read) else none

def workingLabels : List Nat := List.range 196
def start : Nat := 0
def root : Nat := 75
def halt : Nat := 196

theorem working_count : workingLabels.length = 196 := by decide +kernel
theorem row_count : workingLabels.length * 2 = 392 := by decide +kernel
theorem working_nodup : workingLabels.Nodup := by decide +kernel
theorem start_working : start ∈ workingLabels := by decide +kernel
theorem halt_not_working : halt ∉ workingLabels := by decide +kernel

theorem terminal_row (b : Bool) : machine 196 b = none := by
  simp only [machine, Nat.lt_irrefl, ↓reduceIte]

theorem domain (q : Nat) (b : Bool) : machine q b ≠ none ↔ q < 196 := by
  simp only [machine]
  split <;> simp_all

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem all_rows_closed : (List.range 196).all (fun q =>
    [false,true].all (fun b => decide ((transition q b).2.2 ≤ 196))) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem unique_halting_row_check : (List.range 196).all (fun q =>
    [false,true].all (fun b =>
      decide ((transition q b).2.2 = 196 ↔ q = 63 ∧ b = true))) = true := by
  decide +kernel

theorem unique_halting_row {q : Nat} {b w d : Bool}
    (h : machine q b = some (w,d,196)) : q = 63 ∧ b = true := by
  have hq : q < 196 := (domain q b).mp (by rw [h]; simp)
  have hx := List.all_eq_true.mp unique_halting_row_check q (List.mem_range.mpr hq)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have hh := of_decide_eq_true (List.all_eq_true.mp hx b hb)
  simp only [machine, hq, ↓reduceIte, Option.some.injEq] at h
  exact hh.mp (by rw [h])

theorem halt_transition : machine 63 true = some (true,true,196) := rfl

end PA196.Literal
