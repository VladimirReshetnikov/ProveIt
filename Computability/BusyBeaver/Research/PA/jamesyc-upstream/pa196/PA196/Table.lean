module
public import M6.Native
/-! The exact PA196 table in the unchanged engine's control labels. -/
@[expose] public section
namespace PA196.Table
open M6.Zip
def machine : TMN := fun q read =>
  if q < 111 then
    if q < 53 then
      if q < 25 then
        if q < 13 then
          if q < 6 then
            if q < 3 then
              if q < 1 then
                if q = 0 then
                  if read then some (true, true, 0) else some (true, true, 94)
                else none
              else
                if q < 2 then
                  if q = 1 then
                    if read then some (true, false, 2) else some (false, false, 1)
                  else none
                else
                  if q = 2 then
                    if read then some (true, false, 2) else some (false, false, 3)
                  else none
            else
              if q < 4 then
                if q = 3 then
                  if read then some (true, false, 2) else some (false, false, 5)
                else none
              else
                if q < 5 then
                  if q = 4 then
                    if read then some (false, false, 4) else some (true, true, 6)
                  else none
                else
                  if q = 5 then
                    if read then some (true, false, 2) else some (false, false, 9)
                  else none
          else
            if q < 10 then
              if q < 8 then
                if q = 6 then
                  if read then some (false, true, 10) else some (false, true, 6)
                else none
              else
                if q < 9 then
                  if q = 8 then
                    if read then some (true, true, 13) else some (false, true, 14)
                  else none
                else
                  if q = 9 then
                    if read then some (true, false, 2) else some (false, false, 15)
                  else none
            else
              if q < 11 then
                if q = 10 then
                  if read then some (false, true, 10) else some (false, false, 16)
                else none
              else
                if q < 12 then
                  if q = 11 then
                    if read then some (true, true, 18) else some (false, false, 26)
                  else none
                else
                  if q = 12 then
                    if read then some (true, true, 20) else some (false, true, 19)
                  else none
        else
          if q < 19 then
            if q < 16 then
              if q < 14 then
                if q = 13 then
                  if read then some (true, false, 31) else some (false, false, 91)
                else none
              else
                if q < 15 then
                  if q = 14 then
                    if read then some (false, true, 22) else some (false, false, 11)
                  else none
                else
                  if q = 15 then
                    if read then some (true, false, 2) else some (false, false, 23)
                  else none
            else
              if q < 17 then
                if q = 16 then
                  if read then some (false, false, 1) else some (true, false, 1)
                else none
              else
                if q < 18 then
                  if q = 17 then
                    if read then some (false, true, 32) else some (false, true, 24)
                  else none
                else
                  if q = 18 then
                    if read then some (false, false, 108) else some (false, true, 96)
                  else none
          else
            if q < 22 then
              if q < 20 then
                if q = 19 then
                  if read then some (true, true, 29) else some (false, true, 28)
                else none
              else
                if q < 21 then
                  if q = 20 then
                    if read then some (true, true, 31) else some (false, true, 30)
                  else none
                else
                  if q = 21 then
                    if read then some (false, true, 60) else some (false, true, 24)
                  else none
            else
              if q < 23 then
                if q = 22 then
                  if read then some (true, true, 22) else some (false, true, 33)
                else none
              else
                if q < 24 then
                  if q = 23 then
                    if read then some (true, false, 2) else some (false, false, 34)
                  else none
                else
                  if q = 24 then
                    if read then some (false, true, 0) else some (false, false, 35)
                  else none
      else
        if q < 38 then
          if q < 31 then
            if q < 28 then
              if q < 26 then
                if q = 25 then
                  if read then some (true, true, 25) else some (false, true, 36)
                else none
              else
                if q < 27 then
                  if q = 26 then
                    if read then some (true, true, 42) else some (false, true, 194)
                  else none
                else
                  if q = 27 then
                    if read then some (false, false, 40) else some (false, true, 39)
                  else none
            else
              if q < 29 then
                if q = 28 then
                  if read then some (true, true, 42) else some (false, true, 41)
                else none
              else
                if q < 30 then
                  if q = 29 then
                    if read then some (true, true, 44) else some (false, true, 43)
                  else none
                else
                  if q = 30 then
                    if read then some (true, true, 46) else some (false, true, 45)
                  else none
          else
            if q < 34 then
              if q < 32 then
                if q = 31 then
                  if read then some (true, true, 47) else some (false, true, 21)
                else none
              else
                if q < 33 then
                  if q = 32 then
                    if read then some (true, true, 32) else some (false, true, 48)
                  else none
                else
                  if q = 33 then
                    if read then some (true, true, 33) else some (false, true, 32)
                  else none
            else
              if q < 35 then
                if q = 34 then
                  if read then some (true, false, 2) else some (false, false, 75)
                else none
              else
                if q < 36 then
                  if q = 35 then
                    if read then some (true, false, 1) else some (true, true, 35)
                  else none
                else
                  if q = 36 then
                    if read then some (true, true, 36) else some (false, true, 51)
                  else none
        else
          if q < 44 then
            if q < 41 then
              if q < 39 then
                if q = 38 then
                  if read then some (true, true, 20) else some (false, true, 28)
                else none
              else
                if q < 40 then
                  if q = 39 then
                    if read then some (false, true, 36) else some (false, false, 11)
                  else none
                else
                  if q = 40 then
                    if read then some (true, false, 54) else some (false, false, 4)
                  else none
            else
              if q < 42 then
                if q = 41 then
                  if read then some (false, true, 25) else some (false, true, 24)
                else none
              else
                if q < 43 then
                  if q = 42 then
                    if read then some (false, false, 16) else some (false, true, 13)
                  else none
                else
                  if q = 43 then
                    if read then some (true, true, 57) else some (false, true, 56)
                  else none
          else
            if q < 47 then
              if q < 45 then
                if q = 44 then
                  if read then some (true, true, 59) else some (false, true, 58)
                else none
              else
                if q < 46 then
                  if q = 45 then
                    if read then some (false, true, 55) else some (false, true, 24)
                  else none
                else
                  if q = 46 then
                    if read then some (true, true, 62) else some (false, true, 61)
                  else none
            else
              if q < 49 then
                if q < 48 then
                  if q = 47 then
                    if read then some (false, false, 16) else some (false, true, 63)
                  else none
                else
                  if q = 48 then
                    if read then some (true, true, 48) else some (false, true, 25)
                  else none
              else
                if q < 51 then
                  if q = 49 then
                    if read then some (false, true, 64) else some (false, false, 35)
                  else none
                else
                  if q = 51 then
                    if read then some (true, true, 51) else some (false, true, 16)
                  else none
    else
      if q < 82 then
        if q < 66 then
          if q < 59 then
            if q < 56 then
              if q < 54 then
                if q = 53 then
                  if read then some (true, true, 69) else some (false, true, 68)
                else none
              else
                if q < 55 then
                  if q = 54 then
                    if read then some (true, false, 54) else some (false, false, 40)
                  else none
                else
                  if q = 55 then
                    if read then some (true, true, 55) else some (false, true, 22)
                  else none
            else
              if q < 57 then
                if q = 56 then
                  if read then some (false, true, 51) else some (false, false, 11)
                else none
              else
                if q < 58 then
                  if q = 57 then
                    if read then some (false, false, 16) else some (false, true, 61)
                  else none
                else
                  if q = 58 then
                    if read then some (true, true, 71) else some (false, true, 70)
                  else none
          else
            if q < 62 then
              if q < 60 then
                if q = 59 then
                  if read then some (true, true, 72) else some (false, true, 62)
                else none
              else
                if q < 61 then
                  if q = 60 then
                    if read then some (true, true, 60) else some (false, true, 55)
                  else none
                else
                  if q = 61 then
                    if read then some (false, true, 25) else some (false, true, 49)
                  else none
            else
              if q < 63 then
                if q = 62 then
                  if read then some (true, false, 73) else some (false, false, 28)
                else none
              else
                if q < 64 then
                  if q = 63 then
                    if read then some (true, false, 30) else some (false, false, 123)
                  else none
                else
                  if q = 64 then
                    if read then some (true, true, 64) else some (false, true, 74)
                  else none
        else
          if q < 73 then
            if q < 70 then
              if q < 68 then
                if q = 66 then
                  if read then some (true, false, 54) else some (true, true, 198)
                else none
              else
                if q < 69 then
                  if q = 68 then
                    if read then some (true, true, 254) else some (false, true, 77)
                  else none
                else
                  if q = 69 then
                    if read then some (true, true, 31) else some (false, false, 213)
                  else none
            else
              if q < 71 then
                if q = 70 then
                  if read then some (true, true, 63) else some (false, true, 41)
                else none
              else
                if q < 72 then
                  if q = 71 then
                    if read then some (true, true, 80) else some (false, false, 91)
                  else none
                else
                  if q = 72 then
                    if read then some (true, false, 81) else some (false, true, 56)
                  else none
          else
            if q < 77 then
              if q < 74 then
                if q = 73 then
                  if read then some (true, true, 83) else some (false, true, 82)
                else none
              else
                if q < 75 then
                  if q = 74 then
                    if read then some (true, true, 64) else some (true, true, 0)
                  else none
                else
                  if q = 75 then
                    if read then some (true, true, 84) else some (false, true, 75)
                  else none
            else
              if q < 80 then
                if q = 77 then
                  if read then some (true, true, 88) else some (false, true, 87)
                else none
              else
                if q < 81 then
                  if q = 80 then
                    if read then some (true, false, 138) else some (false, true, 91)
                  else none
                else
                  if q = 81 then
                    if read then some (true, true, 57) else some (false, false, 111)
                  else none
      else
        if q < 97 then
          if q < 91 then
            if q < 87 then
              if q < 83 then
                if q = 82 then
                  if read then some (false, true, 33) else some (false, true, 49)
                else none
              else
                if q < 84 then
                  if q = 83 then
                    if read then some (false, false, 42) else some (false, true, 93)
                  else none
                else
                  if q = 84 then
                    if read then some (true, true, 310) else some (false, true, 53)
                  else none
            else
              if q < 88 then
                if q = 87 then
                  if read then some (true, true, 21) else some (false, true, 301)
                else none
              else
                if q < 90 then
                  if q = 88 then
                    if read then some (true, true, 103) else some (false, true, 122)
                  else none
                else
                  if q = 90 then
                    if read then some (true, true, 106) else some (false, true, 105)
                  else none
          else
            if q < 94 then
              if q < 92 then
                if q = 91 then
                  if read then some (true, true, 81) else some (false, true, 82)
                else none
              else
                if q < 93 then
                  if q = 92 then
                    if read then some (true, true, 185) else some (false, true, 104)
                  else none
                else
                  if q = 93 then
                    if read then some (true, true, 109) else some (false, true, 108)
                  else none
            else
              if q < 95 then
                if q = 94 then
                  if read then some (false, true, 0) else some (false, true, 66)
                else none
              else
                if q < 96 then
                  if q = 95 then
                    if read then some (true, true, 110) else some (false, true, 27)
                  else none
                else
                  if q = 96 then
                    if read then some (true, true, 100) else some (false, true, 101)
                  else none
        else
          if q < 104 then
            if q < 100 then
              if q < 98 then
                if q = 97 then
                  if read then some (true, false, 97) else some (true, false, 113)
                else none
              else
                if q < 99 then
                  if q = 98 then
                    if read then some (true, true, 114) else some (false, true, 19)
                  else none
                else
                  if q = 99 then
                    if read then some (true, true, 61) else some (false, true, 61)
                  else none
            else
              if q < 101 then
                if q = 100 then
                  if read then some (true, true, 164) else some (false, true, 174)
                else none
              else
                if q < 103 then
                  if q = 101 then
                    if read then some (true, true, 1367) else some (false, false, 26)
                  else none
                else
                  if q = 103 then
                    if read then some (false, false, 302) else some (false, true, 108)
                  else none
          else
            if q < 107 then
              if q < 105 then
                if q = 104 then
                  if read then some (true, true, 124) else some (false, true, 123)
                else none
              else
                if q < 106 then
                  if q = 105 then
                    if read then some (true, true, 59) else some (false, true, 72)
                  else none
                else
                  if q = 106 then
                    if read then some (true, true, 125) else some (false, true, 58)
                  else none
            else
              if q < 109 then
                if q < 108 then
                  if q = 107 then
                    if read then some (true, true, 126) else some (false, true, 21)
                  else none
                else
                  if q = 108 then
                    if read then some (false, false, 10) else some (false, true, 21)
                  else none
              else
                if q < 110 then
                  if q = 109 then
                    if read then some (true, true, 42) else some (false, true, 62)
                  else none
                else
                  if q = 110 then
                    if read then some (true, true, 8) else some (false, true, 127)
                  else none
  else
    if q < 1316 then
      if q < 194 then
        if q < 138 then
          if q < 125 then
            if q < 122 then
              if q < 113 then
                if q = 111 then
                  if read then some (true, true, 128) else some (false, true, 104)
                else none
              else
                if q < 114 then
                  if q = 113 then
                    if read then some (false, false, 97) else some (false, false, 302)
                  else none
                else
                  if q = 114 then
                    if read then some (true, true, 107) else some (false, true, 130)
                  else none
            else
              if q < 123 then
                if q = 122 then
                  if read then some (false, false, 1) else some (false, false, 137)
                else none
              else
                if q < 124 then
                  if q = 123 then
                    if read then some (true, true, 73) else some (false, true, 39)
                  else none
                else
                  if q = 124 then
                    if read then some (true, true, 138) else some (false, true, 62)
                  else none
          else
            if q < 128 then
              if q < 126 then
                if q = 125 then
                  if read then some (true, true, 139) else some (false, true, 62)
                else none
              else
                if q < 127 then
                  if q = 126 then
                    if read then some (false, false, 16) else some (false, true, 71)
                  else none
                else
                  if q = 127 then
                    if read then some (true, true, 138) else some (false, true, 14)
                  else none
            else
              if q < 130 then
                if q = 128 then
                  if read then some (true, true, 141) else some (false, true, 21)
                else none
              else
                if q < 137 then
                  if q = 130 then
                    if read then some (true, false, 20) else some (false, true, 144)
                  else none
                else
                  if q = 137 then
                    if read then some (true, true, 70) else some (false, true, 30)
                  else none
        else
          if q < 166 then
            if q < 144 then
              if q < 139 then
                if q = 138 then
                  if read then some (true, false, 130) else some (false, true, 39)
                else none
              else
                if q < 141 then
                  if q = 139 then
                    if read then some (false, false, 16) else some (false, true, 190)
                  else none
                else
                  if q = 141 then
                    if read then some (false, false, 16) else some (false, true, 161)
                  else none
            else
              if q < 161 then
                if q = 144 then
                  if read then some (false, true, 48) else some (false, true, 24)
                else none
              else
                if q < 164 then
                  if q = 161 then
                    if read then some (false, true, 32) else some (false, true, 49)
                  else none
                else
                  if q = 164 then
                    if read then some (true, true, 98) else some (false, true, 77)
                  else none
          else
            if q < 185 then
              if q < 174 then
                if q = 166 then
                  if read then some (true, true, 179) else some (false, true, 19)
                else none
              else
                if q < 179 then
                  if q = 174 then
                    if read then some (true, true, 28) else some (false, true, 213)
                  else none
                else
                  if q = 179 then
                    if read then some (true, true, 128) else some (false, true, 194)
                  else none
            else
              if q < 188 then
                if q = 185 then
                  if read then some (true, true, 98) else some (false, true, 107)
                else none
              else
                if q < 190 then
                  if q = 188 then
                    if read then some (true, true, 111) else some (false, true, 95)
                  else none
                else
                  if q = 190 then
                    if read then some (true, true, 99) else some (false, true, 99)
                  else none
      else
        if q < 1300 then
          if q < 217 then
            if q < 198 then
              if q < 196 then
                if q = 194 then
                  if read then some (true, false, 137) else some (false, true, 17)
                else none
              else
                if q < 197 then
                  if q = 196 then
                    if read then some (true, true, 122) else some (false, true, 77)
                  else none
                else
                  if q = 197 then
                    if read then some (true, true, 130) else some (false, true, 109)
                  else none
            else
              if q < 213 then
                if q = 198 then
                  if read then some (true, false, 113) else some (true, false, 40)
                else none
              else
                if q < 214 then
                  if q = 213 then
                    if read then some (true, true, 90) else some (false, true, 92)
                  else none
                else
                  if q = 214 then
                    if read then some (true, true, 312) else some (false, true, 188)
                  else none
          else
            if q < 302 then
              if q < 221 then
                if q = 217 then
                  if read then some (true, true, 196) else some (false, true, 197)
                else none
              else
                if q < 301 then
                  if q = 221 then
                    if read then some (true, true, 217) else some (false, true, 196)
                  else none
                else
                  if q = 301 then
                    if read then some (true, true, 103) else some (false, true, 45)
                  else none
            else
              if q < 310 then
                if q = 302 then
                  if read then some (false, false, 302) else some (false, false, 4)
                else none
              else
                if q < 312 then
                  if q = 310 then
                    if read then some (true, true, 62) else some (false, true, 214)
                  else none
                else
                  if q = 312 then
                    if read then some (true, true, 38) else some (false, true, 11)
                  else none
        else
          if q < 1307 then
            if q < 1303 then
              if q < 1301 then
                if q = 1300 then
                  if read then some (true, true, 61) else some (false, true, 90)
                else none
              else
                if q < 1302 then
                  if q = 1301 then
                    if read then some (true, true, 61) else some (false, true, 1300)
                  else none
                else
                  if q = 1302 then
                    if read then some (true, true, 1301) else some (false, true, 98)
                  else none
            else
              if q < 1305 then
                if q = 1303 then
                  if read then some (true, true, 1302) else some (false, true, 12)
                else none
              else
                if q < 1306 then
                  if q = 1305 then
                    if read then some (true, true, 1307) else some (false, false, 1339)
                  else none
                else
                  if q = 1306 then
                    if read then some (true, true, 1307) else some (false, true, 166)
                  else none
          else
            if q < 1310 then
              if q < 1308 then
                if q = 1307 then
                  if read then some (true, true, 90) else some (false, false, 1329)
                else none
              else
                if q < 1309 then
                  if q = 1308 then
                    if read then some (true, true, 1303) else some (false, true, 1307)
                  else none
                else
                  if q = 1309 then
                    if read then some (true, true, 1308) else some (false, true, 1306)
                  else none
            else
              if q < 1313 then
                if q < 1312 then
                  if q = 1310 then
                    if read then some (true, true, 1309) else some (false, true, 1305)
                  else none
                else
                  if q = 1312 then
                    if read then some (true, true, 1331) else some (false, true, 19)
                  else none
              else
                if q < 1314 then
                  if q = 1313 then
                    if read then some (true, true, 1302) else some (false, true, 1312)
                  else none
                else
                  if q = 1314 then
                    if read then some (true, true, 1312) else some (false, true, 1313)
                  else none
    else
      if q < 1342 then
        if q < 1330 then
          if q < 1322 then
            if q < 1319 then
              if q < 1317 then
                if q = 1316 then
                  if read then some (true, true, 1305) else some (false, true, 1310)
                else none
              else
                if q < 1318 then
                  if q = 1317 then
                    if read then some (true, true, 1316) else some (false, true, 213)
                  else none
                else
                  if q = 1318 then
                    if read then some (true, true, 1301) else some (false, true, 166)
                  else none
            else
              if q < 1320 then
                if q = 1319 then
                  if read then some (true, true, 1318) else some (false, true, 12)
                else none
              else
                if q < 1321 then
                  if q = 1320 then
                    if read then some (true, true, 1303) else some (false, true, 1302)
                  else none
                else
                  if q = 1321 then
                    if read then some (true, true, 90) else some (false, true, 1318)
                  else none
          else
            if q < 1327 then
              if q < 1324 then
                if q = 1322 then
                  if read then some (true, true, 1300) else some (false, true, 98)
                else none
              else
                if q < 1326 then
                  if q = 1324 then
                    if read then some (true, true, 1355) else some (false, true, 1321)
                  else none
                else
                  if q = 1326 then
                    if read then some (true, true, 1345) else some (false, true, 1319)
                  else none
            else
              if q < 1328 then
                if q = 1327 then
                  if read then some (true, true, 1326) else some (false, true, 1317)
                else none
              else
                if q < 1329 then
                  if q = 1328 then
                    if read then some (true, true, 1327) else some (false, true, 90)
                  else none
                else
                  if q = 1329 then
                    if read then some (true, true, 1319) else some (false, true, 1328)
                  else none
        else
          if q < 1336 then
            if q < 1333 then
              if q < 1331 then
                if q = 1330 then
                  if read then some (true, true, 1322) else some (false, true, 166)
                else none
              else
                if q < 1332 then
                  if q = 1331 then
                    if read then some (true, false, 1357) else some (false, true, 61)
                  else none
                else
                  if q = 1332 then
                    if read then some (true, true, 61) else some (false, true, 1308)
                  else none
            else
              if q < 1334 then
                if q = 1333 then
                  if read then some (true, true, 1332) else some (false, true, 1331)
                else none
              else
                if q < 1335 then
                  if q = 1334 then
                    if read then some (true, true, 1333) else some (false, true, 1306)
                  else none
                else
                  if q = 1335 then
                    if read then some (true, true, 1334) else some (false, true, 1333)
                  else none
          else
            if q < 1339 then
              if q < 1337 then
                if q = 1336 then
                  if read then some (true, true, 1335) else some (false, true, 1329)
                else none
              else
                if q < 1338 then
                  if q = 1337 then
                    if read then some (true, true, 1336) else some (false, true, 98)
                  else none
                else
                  if q = 1338 then
                    if read then some (true, true, 1330) else some (false, true, 1314)
                  else none
            else
              if q < 1340 then
                if q = 1339 then
                  if read then some (true, true, 1338) else some (false, true, 1337)
                else none
              else
                if q < 1341 then
                  if q = 1340 then
                    if read then some (true, true, 1339) else some (false, true, 12)
                  else none
                else
                  if q = 1341 then
                    if read then some (true, true, 1306) else some (false, true, 61)
                  else none
      else
        if q < 1355 then
          if q < 1348 then
            if q < 1345 then
              if q < 1343 then
                if q = 1342 then
                  if read then some (true, true, 1332) else some (false, true, 1320)
                else none
              else
                if q < 1344 then
                  if q = 1343 then
                    if read then some (true, true, 1342) else some (false, true, 1341)
                  else none
                else
                  if q = 1344 then
                    if read then some (true, true, 1303) else some (false, true, 1343)
                  else none
            else
              if q < 1346 then
                if q = 1345 then
                  if read then some (true, true, 1324) else some (false, false, 1343)
                else none
              else
                if q < 1347 then
                  if q = 1346 then
                    if read then some (true, true, 1355) else some (false, true, 1345)
                  else none
                else
                  if q = 1347 then
                    if read then some (true, true, 1346) else some (false, true, 1344)
                  else none
          else
            if q < 1352 then
              if q < 1349 then
                if q = 1348 then
                  if read then some (true, true, 1324) else some (false, true, 1347)
                else none
              else
                if q < 1350 then
                  if q = 1349 then
                    if read then some (true, true, 1348) else some (false, true, 1340)
                  else none
                else
                  if q = 1350 then
                    if read then some (true, true, 1330) else some (false, false, 1309)
                  else none
            else
              if q < 1353 then
                if q = 1352 then
                  if read then some (true, true, 1350) else some (false, true, 1350)
                else none
              else
                if q < 1354 then
                  if q = 1353 then
                    if read then some (true, true, 1352) else some (false, true, 1349)
                  else none
                else
                  if q = 1354 then
                    if read then some (true, true, 1353) else some (false, true, 69)
                  else none
        else
          if q < 1361 then
            if q < 1358 then
              if q < 1356 then
                if q = 1355 then
                  if read then some (true, false, 1338) else some (false, false, 1329)
                else none
              else
                if q < 1357 then
                  if q = 1356 then
                    if read then some (true, true, 90) else some (false, true, 1355)
                  else none
                else
                  if q = 1357 then
                    if read then some (true, true, 1356) else some (false, true, 1350)
                  else none
            else
              if q < 1359 then
                if q = 1358 then
                  if read then some (true, true, 1357) else some (false, true, 1313)
                else none
              else
                if q < 1360 then
                  if q = 1359 then
                    if read then some (true, true, 1358) else some (false, true, 1356)
                  else none
                else
                  if q = 1360 then
                    if read then some (true, true, 1359) else some (false, true, 166)
                  else none
          else
            if q < 1364 then
              if q < 1362 then
                if q = 1361 then
                  if read then some (true, true, 194) else some (false, true, 1355)
                else none
              else
                if q < 1363 then
                  if q = 1362 then
                    if read then some (true, true, 1361) else some (false, true, 1321)
                  else none
                else
                  if q = 1363 then
                    if read then some (true, true, 1362) else some (false, true, 1360)
                  else none
            else
              if q < 1366 then
                if q < 1365 then
                  if q = 1364 then
                    if read then some (true, true, 1363) else some (false, true, 1354)
                  else none
                else
                  if q = 1365 then
                    if read then some (false, false, 302) else some (false, true, 221)
                  else none
              else
                if q < 1367 then
                  if q = 1366 then
                    if read then some (true, true, 1365) else some (false, true, 1364)
                  else none
                else
                  if q = 1367 then
                    if read then some (true, true, 1366) else some (false, true, 1303)
                  else none

def workingLabels : List Nat := [74, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 66, 68, 69, 70, 71, 72, 73, 75, 77, 80, 81, 82, 83, 84, 87, 88, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 114, 122, 123, 124, 125, 126, 127, 128, 130, 137, 138, 139, 141, 144, 161, 164, 166, 174, 179, 185, 188, 190, 194, 196, 197, 198, 213, 214, 217, 221, 301, 302, 310, 312, 1300, 1301, 1302, 1303, 1305, 1306, 1307, 1308, 1309, 1310, 1312, 1313, 1314, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1324, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367]
def start : Nat := 74
def root : Nat := 84
def halt : Nat := 254
theorem working_count : workingLabels.length = 196 := by decide +kernel
theorem terminal_row (b : Bool) : machine 254 b = none := by cases b <;> rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem native_boxes : M6.Runtime.BoxLemmas machine :=
  M6.Native.boxLemmas (by decide +kernel) (by rfl)
#print axioms native_boxes
end PA196.Table
