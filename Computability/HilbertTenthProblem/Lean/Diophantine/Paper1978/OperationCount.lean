import Diophantine.Common.ArithmeticCertificate
import Diophantine.Paper1978.Theorem3

/-!
# Jones 1978, Corollary 1: an arithmetic certificate for the system (1.3)

The article counts the additions and multiplications needed to write the system (1.3),
regarding subtraction as a form of addition, and reports 243.  Here the count is made literal
in the calculator model of `Diophantine.ArithmeticCertificate`: numerals are free, and every
intermediate value may be reused.  The schedule below evaluates both sides of all 36 equations
of (1.3) with 241 instructions (89 additions, 24 subtractions, 128 multiplications), so the
certificate is checked with 113 addition checks and 128 multiplication checks, and 36 equality
tests.  The inputs are `n, x` followed by the 67 unknowns of `Sys13` in its argument order.

Combining the equations into one, `∑ (Lᵢ − Rᵢ)² = 0`, costs 36 subtractions, 36 squarings and
35 additions more: 348 instructions, within the article's 350.

This proves an upper bound on a certificate's operation count.  It says nothing about the size
of the witnesses, the time to find them, or the authors' own evaluation order.
-/

namespace Jones1978.OperationCount

open Diophantine.ArithmeticCertificate

/-- The literal schedule. -/
def schedule : Schedule 69 241
  | ⟨0, _⟩ => ⟨.mul, .constant (2), .input 0⟩
  | ⟨1, _⟩ => ⟨.add, .input 20, .input 21⟩
  | ⟨2, _⟩ => ⟨.mul, .previous ⟨1, by change 1 < 2; decide⟩, .previous ⟨1, by change 1 < 2; decide⟩⟩
  | ⟨3, _⟩ => ⟨.mul, .constant (3), .input 21⟩
  | ⟨4, _⟩ => ⟨.add, .previous ⟨2, by change 2 < 4; decide⟩, .previous ⟨3, by change 3 < 4; decide⟩⟩
  | ⟨5, _⟩ => ⟨.add, .previous ⟨4, by change 4 < 5; decide⟩, .input 20⟩
  | ⟨6, _⟩ => ⟨.mul, .input 32, .input 26⟩
  | ⟨7, _⟩ => ⟨.add, .previous ⟨6, by change 6 < 7; decide⟩, .input 32⟩
  | ⟨8, _⟩ => ⟨.mul, .input 9, .input 26⟩
  | ⟨9, _⟩ => ⟨.add, .input 9, .previous ⟨8, by change 8 < 9; decide⟩⟩
  | ⟨10, _⟩ => ⟨.mul, .previous ⟨8, by change 8 < 10; decide⟩, .input 21⟩
  | ⟨11, _⟩ => ⟨.add, .previous ⟨9, by change 9 < 11; decide⟩, .previous ⟨10, by change 10 < 11; decide⟩⟩
  | ⟨12, _⟩ => ⟨.add, .input 1, .input 40⟩
  | ⟨13, _⟩ => ⟨.mul, .input 40, .input 26⟩
  | ⟨14, _⟩ => ⟨.add, .previous ⟨12, by change 12 < 14; decide⟩, .previous ⟨13, by change 13 < 14; decide⟩⟩
  | ⟨15, _⟩ => ⟨.mul, .previous ⟨13, by change 13 < 15; decide⟩, .input 20⟩
  | ⟨16, _⟩ => ⟨.add, .previous ⟨14, by change 14 < 16; decide⟩, .previous ⟨15, by change 15 < 16; decide⟩⟩
  | ⟨17, _⟩ => ⟨.sub, .previous ⟨11, by change 11 < 17; decide⟩, .input 25⟩
  | ⟨18, _⟩ => ⟨.mul, .previous ⟨17, by change 17 < 18; decide⟩, .previous ⟨17, by change 17 < 18; decide⟩⟩
  | ⟨19, _⟩ => ⟨.mul, .input 1, .input 1⟩
  | ⟨20, _⟩ => ⟨.add, .previous ⟨18, by change 18 < 20; decide⟩, .previous ⟨19, by change 19 < 20; decide⟩⟩
  | ⟨21, _⟩ => ⟨.add, .previous ⟨20, by change 20 < 21; decide⟩, .input 27⟩
  | ⟨22, _⟩ => ⟨.add, .previous ⟨21, by change 21 < 22; decide⟩, .constant (1)⟩
  | ⟨23, _⟩ => ⟨.mul, .constant (3), .input 0⟩
  | ⟨24, _⟩ => ⟨.mul, .input 25, .input 25⟩
  | ⟨25, _⟩ => ⟨.mul, .input 25, .previous ⟨24, by change 24 < 25; decide⟩⟩
  | ⟨26, _⟩ => ⟨.add, .previous ⟨23, by change 23 < 26; decide⟩, .previous ⟨25, by change 25 < 26; decide⟩⟩
  | ⟨27, _⟩ => ⟨.mul, .input 24, .input 24⟩
  | ⟨28, _⟩ => ⟨.mul, .previous ⟨27, by change 27 < 28; decide⟩, .previous ⟨27, by change 27 < 28; decide⟩⟩
  | ⟨29, _⟩ => ⟨.mul, .input 24, .previous ⟨28, by change 28 < 29; decide⟩⟩
  | ⟨30, _⟩ => ⟨.mul, .previous ⟨28, by change 28 < 30; decide⟩, .previous ⟨29, by change 29 < 30; decide⟩⟩
  | ⟨31, _⟩ => ⟨.mul, .previous ⟨30, by change 30 < 31; decide⟩, .previous ⟨30, by change 30 < 31; decide⟩⟩
  | ⟨32, _⟩ => ⟨.mul, .input 24, .previous ⟨29, by change 29 < 32; decide⟩⟩
  | ⟨33, _⟩ => ⟨.add, .previous ⟨32, by change 32 < 33; decide⟩, .constant (2)⟩
  | ⟨34, _⟩ => ⟨.mul, .previous ⟨31, by change 31 < 34; decide⟩, .previous ⟨33, by change 33 < 34; decide⟩⟩
  | ⟨35, _⟩ => ⟨.add, .input 17, .constant (1)⟩
  | ⟨36, _⟩ => ⟨.mul, .previous ⟨35, by change 35 < 36; decide⟩, .previous ⟨35, by change 35 < 36; decide⟩⟩
  | ⟨37, _⟩ => ⟨.mul, .previous ⟨34, by change 34 < 37; decide⟩, .previous ⟨36, by change 36 < 37; decide⟩⟩
  | ⟨38, _⟩ => ⟨.add, .previous ⟨37, by change 37 < 38; decide⟩, .constant (1)⟩
  | ⟨39, _⟩ => ⟨.mul, .input 47, .input 47⟩
  | ⟨40, _⟩ => ⟨.add, .input 19, .input 6⟩
  | ⟨41, _⟩ => ⟨.mul, .input 6, .input 26⟩
  | ⟨42, _⟩ => ⟨.add, .previous ⟨40, by change 40 < 42; decide⟩, .previous ⟨41, by change 41 < 42; decide⟩⟩
  | ⟨43, _⟩ => ⟨.mul, .previous ⟨41, by change 41 < 43; decide⟩, .input 18⟩
  | ⟨44, _⟩ => ⟨.add, .previous ⟨42, by change 42 < 44; decide⟩, .previous ⟨43, by change 43 < 44; decide⟩⟩
  | ⟨45, _⟩ => ⟨.mul, .input 16, .input 44⟩
  | ⟨46, _⟩ => ⟨.add, .input 25, .previous ⟨45, by change 45 < 46; decide⟩⟩
  | ⟨47, _⟩ => ⟨.add, .input 15, .input 3⟩
  | ⟨48, _⟩ => ⟨.mul, .input 3, .input 26⟩
  | ⟨49, _⟩ => ⟨.add, .previous ⟨47, by change 47 < 49; decide⟩, .previous ⟨48, by change 48 < 49; decide⟩⟩
  | ⟨50, _⟩ => ⟨.mul, .previous ⟨48, by change 48 < 50; decide⟩, .input 22⟩
  | ⟨51, _⟩ => ⟨.add, .previous ⟨49, by change 49 < 51; decide⟩, .previous ⟨50, by change 50 < 51; decide⟩⟩
  | ⟨52, _⟩ => ⟨.mul, .input 16, .input 45⟩
  | ⟨53, _⟩ => ⟨.add, .input 25, .previous ⟨52, by change 52 < 53; decide⟩⟩
  | ⟨54, _⟩ => ⟨.add, .input 18, .input 22⟩
  | ⟨55, _⟩ => ⟨.mul, .previous ⟨54, by change 54 < 55; decide⟩, .previous ⟨54, by change 54 < 55; decide⟩⟩
  | ⟨56, _⟩ => ⟨.mul, .constant (3), .previous ⟨55, by change 55 < 56; decide⟩⟩
  | ⟨57, _⟩ => ⟨.mul, .constant (9), .input 22⟩
  | ⟨58, _⟩ => ⟨.add, .previous ⟨56, by change 56 < 58; decide⟩, .previous ⟨57, by change 57 < 58; decide⟩⟩
  | ⟨59, _⟩ => ⟨.mul, .constant (3), .input 18⟩
  | ⟨60, _⟩ => ⟨.add, .previous ⟨58, by change 58 < 60; decide⟩, .previous ⟨59, by change 59 < 60; decide⟩⟩
  | ⟨61, _⟩ => ⟨.mul, .constant (2), .input 17⟩
  | ⟨62, _⟩ => ⟨.sub, .previous ⟨60, by change 60 < 62; decide⟩, .previous ⟨61, by change 61 < 62; decide⟩⟩
  | ⟨63, _⟩ => ⟨.mul, .previous ⟨62, by change 62 < 63; decide⟩, .previous ⟨62, by change 62 < 63; decide⟩⟩
  | ⟨64, _⟩ => ⟨.add, .constant (1), .input 26⟩
  | ⟨65, _⟩ => ⟨.mul, .input 17, .input 26⟩
  | ⟨66, _⟩ => ⟨.add, .previous ⟨64, by change 64 < 66; decide⟩, .previous ⟨65, by change 65 < 66; decide⟩⟩
  | ⟨67, _⟩ => ⟨.mul, .previous ⟨66, by change 66 < 67; decide⟩, .previous ⟨66, by change 66 < 67; decide⟩⟩
  | ⟨68, _⟩ => ⟨.sub, .input 25, .input 19⟩
  | ⟨69, _⟩ => ⟨.sub, .previous ⟨68, by change 68 < 69; decide⟩, .input 15⟩
  | ⟨70, _⟩ => ⟨.mul, .previous ⟨69, by change 69 < 70; decide⟩, .previous ⟨69, by change 69 < 70; decide⟩⟩
  | ⟨71, _⟩ => ⟨.add, .constant (1), .previous ⟨70, by change 70 < 71; decide⟩⟩
  | ⟨72, _⟩ => ⟨.mul, .previous ⟨67, by change 67 < 72; decide⟩, .previous ⟨71, by change 71 < 72; decide⟩⟩
  | ⟨73, _⟩ => ⟨.mul, .input 19, .input 19⟩
  | ⟨74, _⟩ => ⟨.sub, .input 26, .previous ⟨73, by change 73 < 74; decide⟩⟩
  | ⟨75, _⟩ => ⟨.mul, .input 15, .input 15⟩
  | ⟨76, _⟩ => ⟨.sub, .previous ⟨74, by change 74 < 76; decide⟩, .previous ⟨75, by change 75 < 76; decide⟩⟩
  | ⟨77, _⟩ => ⟨.mul, .previous ⟨72, by change 72 < 77; decide⟩, .previous ⟨76, by change 76 < 77; decide⟩⟩
  | ⟨78, _⟩ => ⟨.sub, .previous ⟨77, by change 77 < 78; decide⟩, .previous ⟨70, by change 70 < 78; decide⟩⟩
  | ⟨79, _⟩ => ⟨.add, .input 8, .constant (1)⟩
  | ⟨80, _⟩ => ⟨.mul, .previous ⟨79, by change 79 < 80; decide⟩, .previous ⟨67, by change 67 < 80; decide⟩⟩
  | ⟨81, _⟩ => ⟨.sub, .previous ⟨78, by change 78 < 81; decide⟩, .previous ⟨80, by change 80 < 81; decide⟩⟩
  | ⟨82, _⟩ => ⟨.mul, .previous ⟨81, by change 81 < 82; decide⟩, .previous ⟨81, by change 81 < 82; decide⟩⟩
  | ⟨83, _⟩ => ⟨.add, .previous ⟨63, by change 63 < 83; decide⟩, .previous ⟨82, by change 82 < 83; decide⟩⟩
  | ⟨84, _⟩ => ⟨.add, .previous ⟨60, by change 60 < 84; decide⟩, .constant (2)⟩
  | ⟨85, _⟩ => ⟨.sub, .previous ⟨84, by change 84 < 85; decide⟩, .previous ⟨61, by change 61 < 85; decide⟩⟩
  | ⟨86, _⟩ => ⟨.mul, .previous ⟨85, by change 85 < 86; decide⟩, .previous ⟨85, by change 85 < 86; decide⟩⟩
  | ⟨87, _⟩ => ⟨.mul, .input 19, .input 15⟩
  | ⟨88, _⟩ => ⟨.sub, .input 25, .previous ⟨87, by change 87 < 88; decide⟩⟩
  | ⟨89, _⟩ => ⟨.mul, .previous ⟨88, by change 88 < 89; decide⟩, .previous ⟨88, by change 88 < 89; decide⟩⟩
  | ⟨90, _⟩ => ⟨.add, .constant (1), .previous ⟨89, by change 89 < 90; decide⟩⟩
  | ⟨91, _⟩ => ⟨.mul, .previous ⟨67, by change 67 < 91; decide⟩, .previous ⟨90, by change 90 < 91; decide⟩⟩
  | ⟨92, _⟩ => ⟨.mul, .previous ⟨91, by change 91 < 92; decide⟩, .previous ⟨76, by change 76 < 92; decide⟩⟩
  | ⟨93, _⟩ => ⟨.sub, .previous ⟨92, by change 92 < 93; decide⟩, .previous ⟨89, by change 89 < 93; decide⟩⟩
  | ⟨94, _⟩ => ⟨.sub, .previous ⟨93, by change 93 < 94; decide⟩, .previous ⟨80, by change 80 < 94; decide⟩⟩
  | ⟨95, _⟩ => ⟨.mul, .previous ⟨94, by change 94 < 95; decide⟩, .previous ⟨94, by change 94 < 95; decide⟩⟩
  | ⟨96, _⟩ => ⟨.add, .previous ⟨86, by change 86 < 96; decide⟩, .previous ⟨95, by change 95 < 96; decide⟩⟩
  | ⟨97, _⟩ => ⟨.mul, .previous ⟨83, by change 83 < 97; decide⟩, .previous ⟨96, by change 96 < 97; decide⟩⟩
  | ⟨98, _⟩ => ⟨.mul, .constant (3), .input 8⟩
  | ⟨99, _⟩ => ⟨.add, .previous ⟨98, by change 98 < 99; decide⟩, .constant (2)⟩
  | ⟨100, _⟩ => ⟨.sub, .previous ⟨99, by change 99 < 100; decide⟩, .input 17⟩
  | ⟨101, _⟩ => ⟨.mul, .previous ⟨97, by change 97 < 101; decide⟩, .previous ⟨100, by change 100 < 101; decide⟩⟩
  | ⟨102, _⟩ => ⟨.add, .previous ⟨23, by change 23 < 102; decide⟩, .input 8⟩
  | ⟨103, _⟩ => ⟨.sub, .previous ⟨102, by change 102 < 103; decide⟩, .input 17⟩
  | ⟨104, _⟩ => ⟨.mul, .previous ⟨101, by change 101 < 104; decide⟩, .previous ⟨103, by change 103 < 104; decide⟩⟩
  | ⟨105, _⟩ => ⟨.mul, .input 16, .input 39⟩
  | ⟨106, _⟩ => ⟨.add, .input 17, .input 16⟩
  | ⟨107, _⟩ => ⟨.add, .previous ⟨106, by change 106 < 107; decide⟩, .input 3⟩
  | ⟨108, _⟩ => ⟨.add, .previous ⟨107, by change 107 < 108; decide⟩, .input 6⟩
  | ⟨109, _⟩ => ⟨.add, .previous ⟨108, by change 108 < 109; decide⟩, .input 8⟩
  | ⟨110, _⟩ => ⟨.add, .previous ⟨109, by change 109 < 110; decide⟩, .input 18⟩
  | ⟨111, _⟩ => ⟨.add, .previous ⟨110, by change 110 < 111; decide⟩, .input 22⟩
  | ⟨112, _⟩ => ⟨.add, .previous ⟨111, by change 111 < 112; decide⟩, .input 54⟩
  | ⟨113, _⟩ => ⟨.add, .previous ⟨112, by change 112 < 113; decide⟩, .input 55⟩
  | ⟨114, _⟩ => ⟨.add, .previous ⟨113, by change 113 < 114; decide⟩, .input 56⟩
  | ⟨115, _⟩ => ⟨.add, .previous ⟨114, by change 114 < 115; decide⟩, .input 57⟩
  | ⟨116, _⟩ => ⟨.add, .previous ⟨115, by change 115 < 116; decide⟩, .input 58⟩
  | ⟨117, _⟩ => ⟨.mul, .input 48, .input 48⟩
  | ⟨118, _⟩ => ⟨.mul, .input 48, .previous ⟨117, by change 117 < 118; decide⟩⟩
  | ⟨119, _⟩ => ⟨.add, .input 48, .constant (2)⟩
  | ⟨120, _⟩ => ⟨.mul, .previous ⟨118, by change 118 < 120; decide⟩, .previous ⟨119, by change 119 < 120; decide⟩⟩
  | ⟨121, _⟩ => ⟨.add, .input 41, .constant (1)⟩
  | ⟨122, _⟩ => ⟨.mul, .previous ⟨121, by change 121 < 122; decide⟩, .previous ⟨121, by change 121 < 122; decide⟩⟩
  | ⟨123, _⟩ => ⟨.mul, .previous ⟨120, by change 120 < 123; decide⟩, .previous ⟨122, by change 122 < 123; decide⟩⟩
  | ⟨124, _⟩ => ⟨.add, .previous ⟨123, by change 123 < 124; decide⟩, .constant (1)⟩
  | ⟨125, _⟩ => ⟨.mul, .input 28, .input 28⟩
  | ⟨126, _⟩ => ⟨.mul, .input 41, .input 17⟩
  | ⟨127, _⟩ => ⟨.add, .previous ⟨126, by change 126 < 127; decide⟩, .input 41⟩
  | ⟨128, _⟩ => ⟨.add, .input 64, .input 41⟩
  | ⟨129, _⟩ => ⟨.mul, .previous ⟨128, by change 128 < 129; decide⟩, .input 49⟩
  | ⟨130, _⟩ => ⟨.add, .input 3, .previous ⟨129, by change 129 < 130; decide⟩⟩
  | ⟨131, _⟩ => ⟨.add, .input 65, .input 41⟩
  | ⟨132, _⟩ => ⟨.mul, .previous ⟨131, by change 131 < 132; decide⟩, .input 50⟩
  | ⟨133, _⟩ => ⟨.add, .input 6, .previous ⟨132, by change 132 < 133; decide⟩⟩
  | ⟨134, _⟩ => ⟨.add, .input 66, .input 41⟩
  | ⟨135, _⟩ => ⟨.mul, .previous ⟨134, by change 134 < 135; decide⟩, .input 51⟩
  | ⟨136, _⟩ => ⟨.add, .input 8, .previous ⟨135, by change 135 < 136; decide⟩⟩
  | ⟨137, _⟩ => ⟨.add, .input 67, .input 41⟩
  | ⟨138, _⟩ => ⟨.mul, .previous ⟨137, by change 137 < 138; decide⟩, .input 52⟩
  | ⟨139, _⟩ => ⟨.add, .input 18, .previous ⟨138, by change 138 < 139; decide⟩⟩
  | ⟨140, _⟩ => ⟨.add, .input 68, .input 41⟩
  | ⟨141, _⟩ => ⟨.mul, .previous ⟨140, by change 140 < 141; decide⟩, .input 53⟩
  | ⟨142, _⟩ => ⟨.add, .input 22, .previous ⟨141, by change 141 < 142; decide⟩⟩
  | ⟨143, _⟩ => ⟨.mul, .input 31, .input 31⟩
  | ⟨144, _⟩ => ⟨.mul, .input 31, .previous ⟨143, by change 143 < 144; decide⟩⟩
  | ⟨145, _⟩ => ⟨.add, .input 31, .constant (2)⟩
  | ⟨146, _⟩ => ⟨.mul, .previous ⟨144, by change 144 < 146; decide⟩, .previous ⟨145, by change 145 < 146; decide⟩⟩
  | ⟨147, _⟩ => ⟨.add, .input 30, .constant (1)⟩
  | ⟨148, _⟩ => ⟨.mul, .previous ⟨147, by change 147 < 148; decide⟩, .previous ⟨147, by change 147 < 148; decide⟩⟩
  | ⟨149, _⟩ => ⟨.mul, .previous ⟨146, by change 146 < 149; decide⟩, .previous ⟨148, by change 148 < 149; decide⟩⟩
  | ⟨150, _⟩ => ⟨.add, .previous ⟨149, by change 149 < 150; decide⟩, .constant (1)⟩
  | ⟨151, _⟩ => ⟨.mul, .input 29, .input 29⟩
  | ⟨152, _⟩ => ⟨.sub, .input 31, .input 17⟩
  | ⟨153, _⟩ => ⟨.mul, .input 30, .previous ⟨152, by change 152 < 153; decide⟩⟩
  | ⟨154, _⟩ => ⟨.mul, .previous ⟨153, by change 153 < 154; decide⟩, .previous ⟨128, by change 128 < 154; decide⟩⟩
  | ⟨155, _⟩ => ⟨.mul, .previous ⟨154, by change 154 < 155; decide⟩, .previous ⟨131, by change 131 < 155; decide⟩⟩
  | ⟨156, _⟩ => ⟨.mul, .previous ⟨155, by change 155 < 156; decide⟩, .previous ⟨134, by change 134 < 156; decide⟩⟩
  | ⟨157, _⟩ => ⟨.mul, .previous ⟨156, by change 156 < 157; decide⟩, .previous ⟨137, by change 137 < 157; decide⟩⟩
  | ⟨158, _⟩ => ⟨.mul, .previous ⟨157, by change 157 < 158; decide⟩, .previous ⟨140, by change 140 < 158; decide⟩⟩
  | ⟨159, _⟩ => ⟨.add, .constant (1), .input 38⟩
  | ⟨160, _⟩ => ⟨.mul, .previous ⟨159, by change 159 < 160; decide⟩, .previous ⟨152, by change 152 < 160; decide⟩⟩
  | ⟨161, _⟩ => ⟨.add, .input 16, .previous ⟨160, by change 160 < 161; decide⟩⟩
  | ⟨162, _⟩ => ⟨.mul, .input 16, .input 54⟩
  | ⟨163, _⟩ => ⟨.mul, .previous ⟨128, by change 128 < 163; decide⟩, .input 59⟩
  | ⟨164, _⟩ => ⟨.add, .previous ⟨162, by change 162 < 164; decide⟩, .previous ⟨163, by change 163 < 164; decide⟩⟩
  | ⟨165, _⟩ => ⟨.mul, .input 16, .input 55⟩
  | ⟨166, _⟩ => ⟨.mul, .previous ⟨131, by change 131 < 166; decide⟩, .input 60⟩
  | ⟨167, _⟩ => ⟨.add, .previous ⟨165, by change 165 < 167; decide⟩, .previous ⟨166, by change 166 < 167; decide⟩⟩
  | ⟨168, _⟩ => ⟨.mul, .input 16, .input 56⟩
  | ⟨169, _⟩ => ⟨.mul, .previous ⟨134, by change 134 < 169; decide⟩, .input 61⟩
  | ⟨170, _⟩ => ⟨.add, .previous ⟨168, by change 168 < 170; decide⟩, .previous ⟨169, by change 169 < 170; decide⟩⟩
  | ⟨171, _⟩ => ⟨.mul, .input 16, .input 57⟩
  | ⟨172, _⟩ => ⟨.mul, .previous ⟨137, by change 137 < 172; decide⟩, .input 62⟩
  | ⟨173, _⟩ => ⟨.add, .previous ⟨171, by change 171 < 173; decide⟩, .previous ⟨172, by change 172 < 173; decide⟩⟩
  | ⟨174, _⟩ => ⟨.mul, .input 16, .input 58⟩
  | ⟨175, _⟩ => ⟨.mul, .previous ⟨140, by change 140 < 175; decide⟩, .input 63⟩
  | ⟨176, _⟩ => ⟨.add, .previous ⟨174, by change 174 < 176; decide⟩, .previous ⟨175, by change 175 < 176; decide⟩⟩
  | ⟨177, _⟩ => ⟨.mul, .input 36, .input 36⟩
  | ⟨178, _⟩ => ⟨.sub, .previous ⟨177, by change 177 < 178; decide⟩, .constant (1)⟩
  | ⟨179, _⟩ => ⟨.mul, .input 34, .input 34⟩
  | ⟨180, _⟩ => ⟨.mul, .previous ⟨178, by change 178 < 180; decide⟩, .previous ⟨179, by change 179 < 180; decide⟩⟩
  | ⟨181, _⟩ => ⟨.add, .previous ⟨180, by change 180 < 181; decide⟩, .constant (1)⟩
  | ⟨182, _⟩ => ⟨.mul, .input 37, .input 37⟩
  | ⟨183, _⟩ => ⟨.mul, .input 46, .input 46⟩
  | ⟨184, _⟩ => ⟨.mul, .previous ⟨177, by change 177 < 184; decide⟩, .previous ⟨183, by change 183 < 184; decide⟩⟩
  | ⟨185, _⟩ => ⟨.sub, .previous ⟨184, by change 184 < 185; decide⟩, .constant (1)⟩
  | ⟨186, _⟩ => ⟨.mul, .input 35, .input 35⟩
  | ⟨187, _⟩ => ⟨.mul, .previous ⟨185, by change 185 < 187; decide⟩, .previous ⟨186, by change 186 < 187; decide⟩⟩
  | ⟨188, _⟩ => ⟨.add, .previous ⟨187, by change 187 < 188; decide⟩, .constant (1)⟩
  | ⟨189, _⟩ => ⟨.mul, .input 43, .input 43⟩
  | ⟨190, _⟩ => ⟨.mul, .input 34, .input 35⟩
  | ⟨191, _⟩ => ⟨.mul, .previous ⟨190, by change 190 < 191; decide⟩, .input 23⟩
  | ⟨192, _⟩ => ⟨.sub, .input 4, .previous ⟨191, by change 191 < 192; decide⟩⟩
  | ⟨193, _⟩ => ⟨.mul, .previous ⟨192, by change 192 < 193; decide⟩, .previous ⟨192, by change 192 < 193; decide⟩⟩
  | ⟨194, _⟩ => ⟨.mul, .constant (5), .previous ⟨193, by change 193 < 194; decide⟩⟩
  | ⟨195, _⟩ => ⟨.add, .previous ⟨194, by change 194 < 195; decide⟩, .input 33⟩
  | ⟨196, _⟩ => ⟨.mul, .previous ⟨179, by change 179 < 196; decide⟩, .previous ⟨186, by change 186 < 196; decide⟩⟩
  | ⟨197, _⟩ => ⟨.mul, .constant (9), .input 31⟩
  | ⟨198, _⟩ => ⟨.mul, .previous ⟨197, by change 197 < 198; decide⟩, .input 46⟩
  | ⟨199, _⟩ => ⟨.mul, .previous ⟨198, by change 198 < 199; decide⟩, .input 23⟩
  | ⟨200, _⟩ => ⟨.sub, .input 31, .input 24⟩
  | ⟨201, _⟩ => ⟨.add, .previous ⟨200, by change 200 < 201; decide⟩, .constant (1)⟩
  | ⟨202, _⟩ => ⟨.sub, .input 36, .constant (1)⟩
  | ⟨203, _⟩ => ⟨.mul, .input 12, .previous ⟨202, by change 202 < 203; decide⟩⟩
  | ⟨204, _⟩ => ⟨.add, .previous ⟨201, by change 201 < 204; decide⟩, .previous ⟨203, by change 203 < 204; decide⟩⟩
  | ⟨205, _⟩ => ⟨.add, .input 24, .constant (1)⟩
  | ⟨206, _⟩ => ⟨.mul, .input 36, .input 46⟩
  | ⟨207, _⟩ => ⟨.sub, .previous ⟨206, by change 206 < 207; decide⟩, .constant (1)⟩
  | ⟨208, _⟩ => ⟨.mul, .input 13, .previous ⟨207, by change 207 < 208; decide⟩⟩
  | ⟨209, _⟩ => ⟨.add, .previous ⟨205, by change 205 < 209; decide⟩, .previous ⟨208, by change 208 < 209; decide⟩⟩
  | ⟨210, _⟩ => ⟨.add, .previous ⟨206, by change 206 < 210; decide⟩, .input 36⟩
  | ⟨211, _⟩ => ⟨.add, .input 14, .input 31⟩
  | ⟨212, _⟩ => ⟨.add, .previous ⟨211, by change 211 < 212; decide⟩, .constant (1)⟩
  | ⟨213, _⟩ => ⟨.mul, .input 5, .input 5⟩
  | ⟨214, _⟩ => ⟨.mul, .input 2, .input 2⟩
  | ⟨215, _⟩ => ⟨.sub, .previous ⟨214, by change 214 < 215; decide⟩, .constant (1)⟩
  | ⟨216, _⟩ => ⟨.mul, .input 4, .input 4⟩
  | ⟨217, _⟩ => ⟨.mul, .previous ⟨215, by change 215 < 217; decide⟩, .previous ⟨216, by change 216 < 217; decide⟩⟩
  | ⟨218, _⟩ => ⟨.add, .previous ⟨217, by change 217 < 218; decide⟩, .constant (1)⟩
  | ⟨219, _⟩ => ⟨.mul, .input 7, .input 7⟩
  | ⟨220, _⟩ => ⟨.mul, .constant (4), .previous ⟨215, by change 215 < 220; decide⟩⟩
  | ⟨221, _⟩ => ⟨.mul, .input 10, .input 10⟩
  | ⟨222, _⟩ => ⟨.mul, .previous ⟨220, by change 220 < 222; decide⟩, .previous ⟨221, by change 221 < 222; decide⟩⟩
  | ⟨223, _⟩ => ⟨.mul, .previous ⟨216, by change 216 < 223; decide⟩, .previous ⟨216, by change 216 < 223; decide⟩⟩
  | ⟨224, _⟩ => ⟨.mul, .previous ⟨222, by change 222 < 224; decide⟩, .previous ⟨223, by change 223 < 224; decide⟩⟩
  | ⟨225, _⟩ => ⟨.add, .previous ⟨224, by change 224 < 225; decide⟩, .constant (1)⟩
  | ⟨226, _⟩ => ⟨.mul, .input 42, .input 7⟩
  | ⟨227, _⟩ => ⟨.add, .input 5, .previous ⟨226, by change 226 < 227; decide⟩⟩
  | ⟨228, _⟩ => ⟨.mul, .previous ⟨227, by change 227 < 228; decide⟩, .previous ⟨227, by change 227 < 228; decide⟩⟩
  | ⟨229, _⟩ => ⟨.sub, .previous ⟨219, by change 219 < 229; decide⟩, .input 2⟩
  | ⟨230, _⟩ => ⟨.mul, .previous ⟨219, by change 219 < 230; decide⟩, .previous ⟨229, by change 229 < 230; decide⟩⟩
  | ⟨231, _⟩ => ⟨.add, .input 2, .previous ⟨230, by change 230 < 231; decide⟩⟩
  | ⟨232, _⟩ => ⟨.mul, .previous ⟨231, by change 231 < 232; decide⟩, .previous ⟨231, by change 231 < 232; decide⟩⟩
  | ⟨233, _⟩ => ⟨.sub, .previous ⟨232, by change 232 < 233; decide⟩, .constant (1)⟩
  | ⟨234, _⟩ => ⟨.add, .input 31, .constant (1)⟩
  | ⟨235, _⟩ => ⟨.mul, .constant (2), .input 11⟩
  | ⟨236, _⟩ => ⟨.mul, .previous ⟨235, by change 235 < 236; decide⟩, .input 4⟩
  | ⟨237, _⟩ => ⟨.add, .previous ⟨234, by change 234 < 237; decide⟩, .previous ⟨236, by change 236 < 237; decide⟩⟩
  | ⟨238, _⟩ => ⟨.mul, .previous ⟨237, by change 237 < 238; decide⟩, .previous ⟨237, by change 237 < 238; decide⟩⟩
  | ⟨239, _⟩ => ⟨.mul, .previous ⟨233, by change 233 < 239; decide⟩, .previous ⟨238, by change 238 < 239; decide⟩⟩
  | ⟨240, _⟩ => ⟨.add, .previous ⟨239, by change 239 < 240; decide⟩, .constant (1)⟩
  | ⟨idx + 241, hidx⟩ => False.elim (by omega)

private def node0 (inputs : Fin 69 → ℕ) : ℤ :=
  (2 : ℤ) * (inputs 0 : ℤ)

private def node1 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 20 : ℤ) + (inputs 21 : ℤ)

private def node2 (inputs : Fin 69 → ℕ) : ℤ :=
  node1 inputs * node1 inputs

private def node3 (inputs : Fin 69 → ℕ) : ℤ :=
  (3 : ℤ) * (inputs 21 : ℤ)

private def node4 (inputs : Fin 69 → ℕ) : ℤ :=
  node2 inputs + node3 inputs

private def node5 (inputs : Fin 69 → ℕ) : ℤ :=
  node4 inputs + (inputs 20 : ℤ)

private def node6 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 32 : ℤ) * (inputs 26 : ℤ)

private def node7 (inputs : Fin 69 → ℕ) : ℤ :=
  node6 inputs + (inputs 32 : ℤ)

private def node8 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 9 : ℤ) * (inputs 26 : ℤ)

private def node9 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 9 : ℤ) + node8 inputs

private def node10 (inputs : Fin 69 → ℕ) : ℤ :=
  node8 inputs * (inputs 21 : ℤ)

private def node11 (inputs : Fin 69 → ℕ) : ℤ :=
  node9 inputs + node10 inputs

private def node12 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 1 : ℤ) + (inputs 40 : ℤ)

private def node13 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 40 : ℤ) * (inputs 26 : ℤ)

private def node14 (inputs : Fin 69 → ℕ) : ℤ :=
  node12 inputs + node13 inputs

private def node15 (inputs : Fin 69 → ℕ) : ℤ :=
  node13 inputs * (inputs 20 : ℤ)

private def node16 (inputs : Fin 69 → ℕ) : ℤ :=
  node14 inputs + node15 inputs

private def node17 (inputs : Fin 69 → ℕ) : ℤ :=
  node11 inputs - (inputs 25 : ℤ)

private def node18 (inputs : Fin 69 → ℕ) : ℤ :=
  node17 inputs * node17 inputs

private def node19 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 1 : ℤ) * (inputs 1 : ℤ)

private def node20 (inputs : Fin 69 → ℕ) : ℤ :=
  node18 inputs + node19 inputs

private def node21 (inputs : Fin 69 → ℕ) : ℤ :=
  node20 inputs + (inputs 27 : ℤ)

private def node22 (inputs : Fin 69 → ℕ) : ℤ :=
  node21 inputs + (1 : ℤ)

private def node23 (inputs : Fin 69 → ℕ) : ℤ :=
  (3 : ℤ) * (inputs 0 : ℤ)

private def node24 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 25 : ℤ) * (inputs 25 : ℤ)

private def node25 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 25 : ℤ) * node24 inputs

private def node26 (inputs : Fin 69 → ℕ) : ℤ :=
  node23 inputs + node25 inputs

private def node27 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 24 : ℤ) * (inputs 24 : ℤ)

private def node28 (inputs : Fin 69 → ℕ) : ℤ :=
  node27 inputs * node27 inputs

private def node29 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 24 : ℤ) * node28 inputs

private def node30 (inputs : Fin 69 → ℕ) : ℤ :=
  node28 inputs * node29 inputs

private def node31 (inputs : Fin 69 → ℕ) : ℤ :=
  node30 inputs * node30 inputs

private def node32 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 24 : ℤ) * node29 inputs

private def node33 (inputs : Fin 69 → ℕ) : ℤ :=
  node32 inputs + (2 : ℤ)

private def node34 (inputs : Fin 69 → ℕ) : ℤ :=
  node31 inputs * node33 inputs

private def node35 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 17 : ℤ) + (1 : ℤ)

private def node36 (inputs : Fin 69 → ℕ) : ℤ :=
  node35 inputs * node35 inputs

private def node37 (inputs : Fin 69 → ℕ) : ℤ :=
  node34 inputs * node36 inputs

private def node38 (inputs : Fin 69 → ℕ) : ℤ :=
  node37 inputs + (1 : ℤ)

private def node39 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 47 : ℤ) * (inputs 47 : ℤ)

private def node40 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 19 : ℤ) + (inputs 6 : ℤ)

private def node41 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 6 : ℤ) * (inputs 26 : ℤ)

private def node42 (inputs : Fin 69 → ℕ) : ℤ :=
  node40 inputs + node41 inputs

private def node43 (inputs : Fin 69 → ℕ) : ℤ :=
  node41 inputs * (inputs 18 : ℤ)

private def node44 (inputs : Fin 69 → ℕ) : ℤ :=
  node42 inputs + node43 inputs

private def node45 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 44 : ℤ)

private def node46 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 25 : ℤ) + node45 inputs

private def node47 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 15 : ℤ) + (inputs 3 : ℤ)

private def node48 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 3 : ℤ) * (inputs 26 : ℤ)

private def node49 (inputs : Fin 69 → ℕ) : ℤ :=
  node47 inputs + node48 inputs

private def node50 (inputs : Fin 69 → ℕ) : ℤ :=
  node48 inputs * (inputs 22 : ℤ)

private def node51 (inputs : Fin 69 → ℕ) : ℤ :=
  node49 inputs + node50 inputs

private def node52 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 45 : ℤ)

private def node53 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 25 : ℤ) + node52 inputs

private def node54 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 18 : ℤ) + (inputs 22 : ℤ)

private def node55 (inputs : Fin 69 → ℕ) : ℤ :=
  node54 inputs * node54 inputs

private def node56 (inputs : Fin 69 → ℕ) : ℤ :=
  (3 : ℤ) * node55 inputs

private def node57 (inputs : Fin 69 → ℕ) : ℤ :=
  (9 : ℤ) * (inputs 22 : ℤ)

private def node58 (inputs : Fin 69 → ℕ) : ℤ :=
  node56 inputs + node57 inputs

private def node59 (inputs : Fin 69 → ℕ) : ℤ :=
  (3 : ℤ) * (inputs 18 : ℤ)

private def node60 (inputs : Fin 69 → ℕ) : ℤ :=
  node58 inputs + node59 inputs

private def node61 (inputs : Fin 69 → ℕ) : ℤ :=
  (2 : ℤ) * (inputs 17 : ℤ)

private def node62 (inputs : Fin 69 → ℕ) : ℤ :=
  node60 inputs - node61 inputs

private def node63 (inputs : Fin 69 → ℕ) : ℤ :=
  node62 inputs * node62 inputs

private def node64 (inputs : Fin 69 → ℕ) : ℤ :=
  (1 : ℤ) + (inputs 26 : ℤ)

private def node65 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 17 : ℤ) * (inputs 26 : ℤ)

private def node66 (inputs : Fin 69 → ℕ) : ℤ :=
  node64 inputs + node65 inputs

private def node67 (inputs : Fin 69 → ℕ) : ℤ :=
  node66 inputs * node66 inputs

private def node68 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 25 : ℤ) - (inputs 19 : ℤ)

private def node69 (inputs : Fin 69 → ℕ) : ℤ :=
  node68 inputs - (inputs 15 : ℤ)

private def node70 (inputs : Fin 69 → ℕ) : ℤ :=
  node69 inputs * node69 inputs

private def node71 (inputs : Fin 69 → ℕ) : ℤ :=
  (1 : ℤ) + node70 inputs

private def node72 (inputs : Fin 69 → ℕ) : ℤ :=
  node67 inputs * node71 inputs

private def node73 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 19 : ℤ) * (inputs 19 : ℤ)

private def node74 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 26 : ℤ) - node73 inputs

private def node75 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 15 : ℤ) * (inputs 15 : ℤ)

private def node76 (inputs : Fin 69 → ℕ) : ℤ :=
  node74 inputs - node75 inputs

private def node77 (inputs : Fin 69 → ℕ) : ℤ :=
  node72 inputs * node76 inputs

private def node78 (inputs : Fin 69 → ℕ) : ℤ :=
  node77 inputs - node70 inputs

private def node79 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 8 : ℤ) + (1 : ℤ)

private def node80 (inputs : Fin 69 → ℕ) : ℤ :=
  node79 inputs * node67 inputs

private def node81 (inputs : Fin 69 → ℕ) : ℤ :=
  node78 inputs - node80 inputs

private def node82 (inputs : Fin 69 → ℕ) : ℤ :=
  node81 inputs * node81 inputs

private def node83 (inputs : Fin 69 → ℕ) : ℤ :=
  node63 inputs + node82 inputs

private def node84 (inputs : Fin 69 → ℕ) : ℤ :=
  node60 inputs + (2 : ℤ)

private def node85 (inputs : Fin 69 → ℕ) : ℤ :=
  node84 inputs - node61 inputs

private def node86 (inputs : Fin 69 → ℕ) : ℤ :=
  node85 inputs * node85 inputs

private def node87 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 19 : ℤ) * (inputs 15 : ℤ)

private def node88 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 25 : ℤ) - node87 inputs

private def node89 (inputs : Fin 69 → ℕ) : ℤ :=
  node88 inputs * node88 inputs

private def node90 (inputs : Fin 69 → ℕ) : ℤ :=
  (1 : ℤ) + node89 inputs

private def node91 (inputs : Fin 69 → ℕ) : ℤ :=
  node67 inputs * node90 inputs

private def node92 (inputs : Fin 69 → ℕ) : ℤ :=
  node91 inputs * node76 inputs

private def node93 (inputs : Fin 69 → ℕ) : ℤ :=
  node92 inputs - node89 inputs

private def node94 (inputs : Fin 69 → ℕ) : ℤ :=
  node93 inputs - node80 inputs

private def node95 (inputs : Fin 69 → ℕ) : ℤ :=
  node94 inputs * node94 inputs

private def node96 (inputs : Fin 69 → ℕ) : ℤ :=
  node86 inputs + node95 inputs

private def node97 (inputs : Fin 69 → ℕ) : ℤ :=
  node83 inputs * node96 inputs

private def node98 (inputs : Fin 69 → ℕ) : ℤ :=
  (3 : ℤ) * (inputs 8 : ℤ)

private def node99 (inputs : Fin 69 → ℕ) : ℤ :=
  node98 inputs + (2 : ℤ)

private def node100 (inputs : Fin 69 → ℕ) : ℤ :=
  node99 inputs - (inputs 17 : ℤ)

private def node101 (inputs : Fin 69 → ℕ) : ℤ :=
  node97 inputs * node100 inputs

private def node102 (inputs : Fin 69 → ℕ) : ℤ :=
  node23 inputs + (inputs 8 : ℤ)

private def node103 (inputs : Fin 69 → ℕ) : ℤ :=
  node102 inputs - (inputs 17 : ℤ)

private def node104 (inputs : Fin 69 → ℕ) : ℤ :=
  node101 inputs * node103 inputs

private def node105 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 39 : ℤ)

private def node106 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 17 : ℤ) + (inputs 16 : ℤ)

private def node107 (inputs : Fin 69 → ℕ) : ℤ :=
  node106 inputs + (inputs 3 : ℤ)

private def node108 (inputs : Fin 69 → ℕ) : ℤ :=
  node107 inputs + (inputs 6 : ℤ)

private def node109 (inputs : Fin 69 → ℕ) : ℤ :=
  node108 inputs + (inputs 8 : ℤ)

private def node110 (inputs : Fin 69 → ℕ) : ℤ :=
  node109 inputs + (inputs 18 : ℤ)

private def node111 (inputs : Fin 69 → ℕ) : ℤ :=
  node110 inputs + (inputs 22 : ℤ)

private def node112 (inputs : Fin 69 → ℕ) : ℤ :=
  node111 inputs + (inputs 54 : ℤ)

private def node113 (inputs : Fin 69 → ℕ) : ℤ :=
  node112 inputs + (inputs 55 : ℤ)

private def node114 (inputs : Fin 69 → ℕ) : ℤ :=
  node113 inputs + (inputs 56 : ℤ)

private def node115 (inputs : Fin 69 → ℕ) : ℤ :=
  node114 inputs + (inputs 57 : ℤ)

private def node116 (inputs : Fin 69 → ℕ) : ℤ :=
  node115 inputs + (inputs 58 : ℤ)

private def node117 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 48 : ℤ) * (inputs 48 : ℤ)

private def node118 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 48 : ℤ) * node117 inputs

private def node119 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 48 : ℤ) + (2 : ℤ)

private def node120 (inputs : Fin 69 → ℕ) : ℤ :=
  node118 inputs * node119 inputs

private def node121 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 41 : ℤ) + (1 : ℤ)

private def node122 (inputs : Fin 69 → ℕ) : ℤ :=
  node121 inputs * node121 inputs

private def node123 (inputs : Fin 69 → ℕ) : ℤ :=
  node120 inputs * node122 inputs

private def node124 (inputs : Fin 69 → ℕ) : ℤ :=
  node123 inputs + (1 : ℤ)

private def node125 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 28 : ℤ) * (inputs 28 : ℤ)

private def node126 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 41 : ℤ) * (inputs 17 : ℤ)

private def node127 (inputs : Fin 69 → ℕ) : ℤ :=
  node126 inputs + (inputs 41 : ℤ)

private def node128 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 64 : ℤ) + (inputs 41 : ℤ)

private def node129 (inputs : Fin 69 → ℕ) : ℤ :=
  node128 inputs * (inputs 49 : ℤ)

private def node130 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 3 : ℤ) + node129 inputs

private def node131 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 65 : ℤ) + (inputs 41 : ℤ)

private def node132 (inputs : Fin 69 → ℕ) : ℤ :=
  node131 inputs * (inputs 50 : ℤ)

private def node133 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 6 : ℤ) + node132 inputs

private def node134 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 66 : ℤ) + (inputs 41 : ℤ)

private def node135 (inputs : Fin 69 → ℕ) : ℤ :=
  node134 inputs * (inputs 51 : ℤ)

private def node136 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 8 : ℤ) + node135 inputs

private def node137 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 67 : ℤ) + (inputs 41 : ℤ)

private def node138 (inputs : Fin 69 → ℕ) : ℤ :=
  node137 inputs * (inputs 52 : ℤ)

private def node139 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 18 : ℤ) + node138 inputs

private def node140 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 68 : ℤ) + (inputs 41 : ℤ)

private def node141 (inputs : Fin 69 → ℕ) : ℤ :=
  node140 inputs * (inputs 53 : ℤ)

private def node142 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 22 : ℤ) + node141 inputs

private def node143 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) * (inputs 31 : ℤ)

private def node144 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) * node143 inputs

private def node145 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) + (2 : ℤ)

private def node146 (inputs : Fin 69 → ℕ) : ℤ :=
  node144 inputs * node145 inputs

private def node147 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 30 : ℤ) + (1 : ℤ)

private def node148 (inputs : Fin 69 → ℕ) : ℤ :=
  node147 inputs * node147 inputs

private def node149 (inputs : Fin 69 → ℕ) : ℤ :=
  node146 inputs * node148 inputs

private def node150 (inputs : Fin 69 → ℕ) : ℤ :=
  node149 inputs + (1 : ℤ)

private def node151 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 29 : ℤ) * (inputs 29 : ℤ)

private def node152 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) - (inputs 17 : ℤ)

private def node153 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 30 : ℤ) * node152 inputs

private def node154 (inputs : Fin 69 → ℕ) : ℤ :=
  node153 inputs * node128 inputs

private def node155 (inputs : Fin 69 → ℕ) : ℤ :=
  node154 inputs * node131 inputs

private def node156 (inputs : Fin 69 → ℕ) : ℤ :=
  node155 inputs * node134 inputs

private def node157 (inputs : Fin 69 → ℕ) : ℤ :=
  node156 inputs * node137 inputs

private def node158 (inputs : Fin 69 → ℕ) : ℤ :=
  node157 inputs * node140 inputs

private def node159 (inputs : Fin 69 → ℕ) : ℤ :=
  (1 : ℤ) + (inputs 38 : ℤ)

private def node160 (inputs : Fin 69 → ℕ) : ℤ :=
  node159 inputs * node152 inputs

private def node161 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) + node160 inputs

private def node162 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 54 : ℤ)

private def node163 (inputs : Fin 69 → ℕ) : ℤ :=
  node128 inputs * (inputs 59 : ℤ)

private def node164 (inputs : Fin 69 → ℕ) : ℤ :=
  node162 inputs + node163 inputs

private def node165 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 55 : ℤ)

private def node166 (inputs : Fin 69 → ℕ) : ℤ :=
  node131 inputs * (inputs 60 : ℤ)

private def node167 (inputs : Fin 69 → ℕ) : ℤ :=
  node165 inputs + node166 inputs

private def node168 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 56 : ℤ)

private def node169 (inputs : Fin 69 → ℕ) : ℤ :=
  node134 inputs * (inputs 61 : ℤ)

private def node170 (inputs : Fin 69 → ℕ) : ℤ :=
  node168 inputs + node169 inputs

private def node171 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 57 : ℤ)

private def node172 (inputs : Fin 69 → ℕ) : ℤ :=
  node137 inputs * (inputs 62 : ℤ)

private def node173 (inputs : Fin 69 → ℕ) : ℤ :=
  node171 inputs + node172 inputs

private def node174 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 58 : ℤ)

private def node175 (inputs : Fin 69 → ℕ) : ℤ :=
  node140 inputs * (inputs 63 : ℤ)

private def node176 (inputs : Fin 69 → ℕ) : ℤ :=
  node174 inputs + node175 inputs

private def node177 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 36 : ℤ) * (inputs 36 : ℤ)

private def node178 (inputs : Fin 69 → ℕ) : ℤ :=
  node177 inputs - (1 : ℤ)

private def node179 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 34 : ℤ) * (inputs 34 : ℤ)

private def node180 (inputs : Fin 69 → ℕ) : ℤ :=
  node178 inputs * node179 inputs

private def node181 (inputs : Fin 69 → ℕ) : ℤ :=
  node180 inputs + (1 : ℤ)

private def node182 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 37 : ℤ) * (inputs 37 : ℤ)

private def node183 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 46 : ℤ) * (inputs 46 : ℤ)

private def node184 (inputs : Fin 69 → ℕ) : ℤ :=
  node177 inputs * node183 inputs

private def node185 (inputs : Fin 69 → ℕ) : ℤ :=
  node184 inputs - (1 : ℤ)

private def node186 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 35 : ℤ) * (inputs 35 : ℤ)

private def node187 (inputs : Fin 69 → ℕ) : ℤ :=
  node185 inputs * node186 inputs

private def node188 (inputs : Fin 69 → ℕ) : ℤ :=
  node187 inputs + (1 : ℤ)

private def node189 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 43 : ℤ) * (inputs 43 : ℤ)

private def node190 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 34 : ℤ) * (inputs 35 : ℤ)

private def node191 (inputs : Fin 69 → ℕ) : ℤ :=
  node190 inputs * (inputs 23 : ℤ)

private def node192 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 4 : ℤ) - node191 inputs

private def node193 (inputs : Fin 69 → ℕ) : ℤ :=
  node192 inputs * node192 inputs

private def node194 (inputs : Fin 69 → ℕ) : ℤ :=
  (5 : ℤ) * node193 inputs

private def node195 (inputs : Fin 69 → ℕ) : ℤ :=
  node194 inputs + (inputs 33 : ℤ)

private def node196 (inputs : Fin 69 → ℕ) : ℤ :=
  node179 inputs * node186 inputs

private def node197 (inputs : Fin 69 → ℕ) : ℤ :=
  (9 : ℤ) * (inputs 31 : ℤ)

private def node198 (inputs : Fin 69 → ℕ) : ℤ :=
  node197 inputs * (inputs 46 : ℤ)

private def node199 (inputs : Fin 69 → ℕ) : ℤ :=
  node198 inputs * (inputs 23 : ℤ)

private def node200 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) - (inputs 24 : ℤ)

private def node201 (inputs : Fin 69 → ℕ) : ℤ :=
  node200 inputs + (1 : ℤ)

private def node202 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 36 : ℤ) - (1 : ℤ)

private def node203 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 12 : ℤ) * node202 inputs

private def node204 (inputs : Fin 69 → ℕ) : ℤ :=
  node201 inputs + node203 inputs

private def node205 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 24 : ℤ) + (1 : ℤ)

private def node206 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 36 : ℤ) * (inputs 46 : ℤ)

private def node207 (inputs : Fin 69 → ℕ) : ℤ :=
  node206 inputs - (1 : ℤ)

private def node208 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 13 : ℤ) * node207 inputs

private def node209 (inputs : Fin 69 → ℕ) : ℤ :=
  node205 inputs + node208 inputs

private def node210 (inputs : Fin 69 → ℕ) : ℤ :=
  node206 inputs + (inputs 36 : ℤ)

private def node211 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 14 : ℤ) + (inputs 31 : ℤ)

private def node212 (inputs : Fin 69 → ℕ) : ℤ :=
  node211 inputs + (1 : ℤ)

private def node213 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 5 : ℤ) * (inputs 5 : ℤ)

private def node214 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 2 : ℤ) * (inputs 2 : ℤ)

private def node215 (inputs : Fin 69 → ℕ) : ℤ :=
  node214 inputs - (1 : ℤ)

private def node216 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 4 : ℤ) * (inputs 4 : ℤ)

private def node217 (inputs : Fin 69 → ℕ) : ℤ :=
  node215 inputs * node216 inputs

private def node218 (inputs : Fin 69 → ℕ) : ℤ :=
  node217 inputs + (1 : ℤ)

private def node219 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 7 : ℤ) * (inputs 7 : ℤ)

private def node220 (inputs : Fin 69 → ℕ) : ℤ :=
  (4 : ℤ) * node215 inputs

private def node221 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 10 : ℤ) * (inputs 10 : ℤ)

private def node222 (inputs : Fin 69 → ℕ) : ℤ :=
  node220 inputs * node221 inputs

private def node223 (inputs : Fin 69 → ℕ) : ℤ :=
  node216 inputs * node216 inputs

private def node224 (inputs : Fin 69 → ℕ) : ℤ :=
  node222 inputs * node223 inputs

private def node225 (inputs : Fin 69 → ℕ) : ℤ :=
  node224 inputs + (1 : ℤ)

private def node226 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 42 : ℤ) * (inputs 7 : ℤ)

private def node227 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 5 : ℤ) + node226 inputs

private def node228 (inputs : Fin 69 → ℕ) : ℤ :=
  node227 inputs * node227 inputs

private def node229 (inputs : Fin 69 → ℕ) : ℤ :=
  node219 inputs - (inputs 2 : ℤ)

private def node230 (inputs : Fin 69 → ℕ) : ℤ :=
  node219 inputs * node229 inputs

private def node231 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 2 : ℤ) + node230 inputs

private def node232 (inputs : Fin 69 → ℕ) : ℤ :=
  node231 inputs * node231 inputs

private def node233 (inputs : Fin 69 → ℕ) : ℤ :=
  node232 inputs - (1 : ℤ)

private def node234 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) + (1 : ℤ)

private def node235 (inputs : Fin 69 → ℕ) : ℤ :=
  (2 : ℤ) * (inputs 11 : ℤ)

private def node236 (inputs : Fin 69 → ℕ) : ℤ :=
  node235 inputs * (inputs 4 : ℤ)

private def node237 (inputs : Fin 69 → ℕ) : ℤ :=
  node234 inputs + node236 inputs

private def node238 (inputs : Fin 69 → ℕ) : ℤ :=
  node237 inputs * node237 inputs

private def node239 (inputs : Fin 69 → ℕ) : ℤ :=
  node233 inputs * node238 inputs

private def node240 (inputs : Fin 69 → ℕ) : ℤ :=
  node239 inputs + (1 : ℤ)

/-- The canonical signed evaluation of the schedule. -/
def evaluation (inputs : Fin 69 → ℕ) : Fin 241 → ℤ
  | ⟨0, _⟩ => node0 inputs
  | ⟨1, _⟩ => node1 inputs
  | ⟨2, _⟩ => node2 inputs
  | ⟨3, _⟩ => node3 inputs
  | ⟨4, _⟩ => node4 inputs
  | ⟨5, _⟩ => node5 inputs
  | ⟨6, _⟩ => node6 inputs
  | ⟨7, _⟩ => node7 inputs
  | ⟨8, _⟩ => node8 inputs
  | ⟨9, _⟩ => node9 inputs
  | ⟨10, _⟩ => node10 inputs
  | ⟨11, _⟩ => node11 inputs
  | ⟨12, _⟩ => node12 inputs
  | ⟨13, _⟩ => node13 inputs
  | ⟨14, _⟩ => node14 inputs
  | ⟨15, _⟩ => node15 inputs
  | ⟨16, _⟩ => node16 inputs
  | ⟨17, _⟩ => node17 inputs
  | ⟨18, _⟩ => node18 inputs
  | ⟨19, _⟩ => node19 inputs
  | ⟨20, _⟩ => node20 inputs
  | ⟨21, _⟩ => node21 inputs
  | ⟨22, _⟩ => node22 inputs
  | ⟨23, _⟩ => node23 inputs
  | ⟨24, _⟩ => node24 inputs
  | ⟨25, _⟩ => node25 inputs
  | ⟨26, _⟩ => node26 inputs
  | ⟨27, _⟩ => node27 inputs
  | ⟨28, _⟩ => node28 inputs
  | ⟨29, _⟩ => node29 inputs
  | ⟨30, _⟩ => node30 inputs
  | ⟨31, _⟩ => node31 inputs
  | ⟨32, _⟩ => node32 inputs
  | ⟨33, _⟩ => node33 inputs
  | ⟨34, _⟩ => node34 inputs
  | ⟨35, _⟩ => node35 inputs
  | ⟨36, _⟩ => node36 inputs
  | ⟨37, _⟩ => node37 inputs
  | ⟨38, _⟩ => node38 inputs
  | ⟨39, _⟩ => node39 inputs
  | ⟨40, _⟩ => node40 inputs
  | ⟨41, _⟩ => node41 inputs
  | ⟨42, _⟩ => node42 inputs
  | ⟨43, _⟩ => node43 inputs
  | ⟨44, _⟩ => node44 inputs
  | ⟨45, _⟩ => node45 inputs
  | ⟨46, _⟩ => node46 inputs
  | ⟨47, _⟩ => node47 inputs
  | ⟨48, _⟩ => node48 inputs
  | ⟨49, _⟩ => node49 inputs
  | ⟨50, _⟩ => node50 inputs
  | ⟨51, _⟩ => node51 inputs
  | ⟨52, _⟩ => node52 inputs
  | ⟨53, _⟩ => node53 inputs
  | ⟨54, _⟩ => node54 inputs
  | ⟨55, _⟩ => node55 inputs
  | ⟨56, _⟩ => node56 inputs
  | ⟨57, _⟩ => node57 inputs
  | ⟨58, _⟩ => node58 inputs
  | ⟨59, _⟩ => node59 inputs
  | ⟨60, _⟩ => node60 inputs
  | ⟨61, _⟩ => node61 inputs
  | ⟨62, _⟩ => node62 inputs
  | ⟨63, _⟩ => node63 inputs
  | ⟨64, _⟩ => node64 inputs
  | ⟨65, _⟩ => node65 inputs
  | ⟨66, _⟩ => node66 inputs
  | ⟨67, _⟩ => node67 inputs
  | ⟨68, _⟩ => node68 inputs
  | ⟨69, _⟩ => node69 inputs
  | ⟨70, _⟩ => node70 inputs
  | ⟨71, _⟩ => node71 inputs
  | ⟨72, _⟩ => node72 inputs
  | ⟨73, _⟩ => node73 inputs
  | ⟨74, _⟩ => node74 inputs
  | ⟨75, _⟩ => node75 inputs
  | ⟨76, _⟩ => node76 inputs
  | ⟨77, _⟩ => node77 inputs
  | ⟨78, _⟩ => node78 inputs
  | ⟨79, _⟩ => node79 inputs
  | ⟨80, _⟩ => node80 inputs
  | ⟨81, _⟩ => node81 inputs
  | ⟨82, _⟩ => node82 inputs
  | ⟨83, _⟩ => node83 inputs
  | ⟨84, _⟩ => node84 inputs
  | ⟨85, _⟩ => node85 inputs
  | ⟨86, _⟩ => node86 inputs
  | ⟨87, _⟩ => node87 inputs
  | ⟨88, _⟩ => node88 inputs
  | ⟨89, _⟩ => node89 inputs
  | ⟨90, _⟩ => node90 inputs
  | ⟨91, _⟩ => node91 inputs
  | ⟨92, _⟩ => node92 inputs
  | ⟨93, _⟩ => node93 inputs
  | ⟨94, _⟩ => node94 inputs
  | ⟨95, _⟩ => node95 inputs
  | ⟨96, _⟩ => node96 inputs
  | ⟨97, _⟩ => node97 inputs
  | ⟨98, _⟩ => node98 inputs
  | ⟨99, _⟩ => node99 inputs
  | ⟨100, _⟩ => node100 inputs
  | ⟨101, _⟩ => node101 inputs
  | ⟨102, _⟩ => node102 inputs
  | ⟨103, _⟩ => node103 inputs
  | ⟨104, _⟩ => node104 inputs
  | ⟨105, _⟩ => node105 inputs
  | ⟨106, _⟩ => node106 inputs
  | ⟨107, _⟩ => node107 inputs
  | ⟨108, _⟩ => node108 inputs
  | ⟨109, _⟩ => node109 inputs
  | ⟨110, _⟩ => node110 inputs
  | ⟨111, _⟩ => node111 inputs
  | ⟨112, _⟩ => node112 inputs
  | ⟨113, _⟩ => node113 inputs
  | ⟨114, _⟩ => node114 inputs
  | ⟨115, _⟩ => node115 inputs
  | ⟨116, _⟩ => node116 inputs
  | ⟨117, _⟩ => node117 inputs
  | ⟨118, _⟩ => node118 inputs
  | ⟨119, _⟩ => node119 inputs
  | ⟨120, _⟩ => node120 inputs
  | ⟨121, _⟩ => node121 inputs
  | ⟨122, _⟩ => node122 inputs
  | ⟨123, _⟩ => node123 inputs
  | ⟨124, _⟩ => node124 inputs
  | ⟨125, _⟩ => node125 inputs
  | ⟨126, _⟩ => node126 inputs
  | ⟨127, _⟩ => node127 inputs
  | ⟨128, _⟩ => node128 inputs
  | ⟨129, _⟩ => node129 inputs
  | ⟨130, _⟩ => node130 inputs
  | ⟨131, _⟩ => node131 inputs
  | ⟨132, _⟩ => node132 inputs
  | ⟨133, _⟩ => node133 inputs
  | ⟨134, _⟩ => node134 inputs
  | ⟨135, _⟩ => node135 inputs
  | ⟨136, _⟩ => node136 inputs
  | ⟨137, _⟩ => node137 inputs
  | ⟨138, _⟩ => node138 inputs
  | ⟨139, _⟩ => node139 inputs
  | ⟨140, _⟩ => node140 inputs
  | ⟨141, _⟩ => node141 inputs
  | ⟨142, _⟩ => node142 inputs
  | ⟨143, _⟩ => node143 inputs
  | ⟨144, _⟩ => node144 inputs
  | ⟨145, _⟩ => node145 inputs
  | ⟨146, _⟩ => node146 inputs
  | ⟨147, _⟩ => node147 inputs
  | ⟨148, _⟩ => node148 inputs
  | ⟨149, _⟩ => node149 inputs
  | ⟨150, _⟩ => node150 inputs
  | ⟨151, _⟩ => node151 inputs
  | ⟨152, _⟩ => node152 inputs
  | ⟨153, _⟩ => node153 inputs
  | ⟨154, _⟩ => node154 inputs
  | ⟨155, _⟩ => node155 inputs
  | ⟨156, _⟩ => node156 inputs
  | ⟨157, _⟩ => node157 inputs
  | ⟨158, _⟩ => node158 inputs
  | ⟨159, _⟩ => node159 inputs
  | ⟨160, _⟩ => node160 inputs
  | ⟨161, _⟩ => node161 inputs
  | ⟨162, _⟩ => node162 inputs
  | ⟨163, _⟩ => node163 inputs
  | ⟨164, _⟩ => node164 inputs
  | ⟨165, _⟩ => node165 inputs
  | ⟨166, _⟩ => node166 inputs
  | ⟨167, _⟩ => node167 inputs
  | ⟨168, _⟩ => node168 inputs
  | ⟨169, _⟩ => node169 inputs
  | ⟨170, _⟩ => node170 inputs
  | ⟨171, _⟩ => node171 inputs
  | ⟨172, _⟩ => node172 inputs
  | ⟨173, _⟩ => node173 inputs
  | ⟨174, _⟩ => node174 inputs
  | ⟨175, _⟩ => node175 inputs
  | ⟨176, _⟩ => node176 inputs
  | ⟨177, _⟩ => node177 inputs
  | ⟨178, _⟩ => node178 inputs
  | ⟨179, _⟩ => node179 inputs
  | ⟨180, _⟩ => node180 inputs
  | ⟨181, _⟩ => node181 inputs
  | ⟨182, _⟩ => node182 inputs
  | ⟨183, _⟩ => node183 inputs
  | ⟨184, _⟩ => node184 inputs
  | ⟨185, _⟩ => node185 inputs
  | ⟨186, _⟩ => node186 inputs
  | ⟨187, _⟩ => node187 inputs
  | ⟨188, _⟩ => node188 inputs
  | ⟨189, _⟩ => node189 inputs
  | ⟨190, _⟩ => node190 inputs
  | ⟨191, _⟩ => node191 inputs
  | ⟨192, _⟩ => node192 inputs
  | ⟨193, _⟩ => node193 inputs
  | ⟨194, _⟩ => node194 inputs
  | ⟨195, _⟩ => node195 inputs
  | ⟨196, _⟩ => node196 inputs
  | ⟨197, _⟩ => node197 inputs
  | ⟨198, _⟩ => node198 inputs
  | ⟨199, _⟩ => node199 inputs
  | ⟨200, _⟩ => node200 inputs
  | ⟨201, _⟩ => node201 inputs
  | ⟨202, _⟩ => node202 inputs
  | ⟨203, _⟩ => node203 inputs
  | ⟨204, _⟩ => node204 inputs
  | ⟨205, _⟩ => node205 inputs
  | ⟨206, _⟩ => node206 inputs
  | ⟨207, _⟩ => node207 inputs
  | ⟨208, _⟩ => node208 inputs
  | ⟨209, _⟩ => node209 inputs
  | ⟨210, _⟩ => node210 inputs
  | ⟨211, _⟩ => node211 inputs
  | ⟨212, _⟩ => node212 inputs
  | ⟨213, _⟩ => node213 inputs
  | ⟨214, _⟩ => node214 inputs
  | ⟨215, _⟩ => node215 inputs
  | ⟨216, _⟩ => node216 inputs
  | ⟨217, _⟩ => node217 inputs
  | ⟨218, _⟩ => node218 inputs
  | ⟨219, _⟩ => node219 inputs
  | ⟨220, _⟩ => node220 inputs
  | ⟨221, _⟩ => node221 inputs
  | ⟨222, _⟩ => node222 inputs
  | ⟨223, _⟩ => node223 inputs
  | ⟨224, _⟩ => node224 inputs
  | ⟨225, _⟩ => node225 inputs
  | ⟨226, _⟩ => node226 inputs
  | ⟨227, _⟩ => node227 inputs
  | ⟨228, _⟩ => node228 inputs
  | ⟨229, _⟩ => node229 inputs
  | ⟨230, _⟩ => node230 inputs
  | ⟨231, _⟩ => node231 inputs
  | ⟨232, _⟩ => node232 inputs
  | ⟨233, _⟩ => node233 inputs
  | ⟨234, _⟩ => node234 inputs
  | ⟨235, _⟩ => node235 inputs
  | ⟨236, _⟩ => node236 inputs
  | ⟨237, _⟩ => node237 inputs
  | ⟨238, _⟩ => node238 inputs
  | ⟨239, _⟩ => node239 inputs
  | ⟨240, _⟩ => node240 inputs
  | ⟨idx + 241, hidx⟩ => False.elim (by omega)

theorem evaluation_valid (inputs : Fin 69 → ℕ) :
    Valid schedule inputs (evaluation inputs) := by
  intro idx
  apply ((schedule idx).check_iff inputs _ _).mpr
  fin_cases idx <;> rfl

/-- Every valid supplied trace is the canonical evaluation. -/
theorem valid_iff_eq_evaluation (inputs : Fin 69 → ℕ) (trace : Fin 241 → ℤ) :
    Valid schedule inputs trace ↔ trace = evaluation inputs :=
  ⟨fun h => h.unique (evaluation_valid inputs), fun h => h ▸ evaluation_valid inputs⟩

theorem assignment_counts :
    operationCount schedule .add = 89 ∧ operationCount schedule .sub = 24 ∧
      operationCount schedule .mul = 128 := by
  decide +kernel

theorem check_counts :
    additionChecks schedule = 113 ∧ multiplicationChecks schedule = 128 ∧
      additionChecks schedule + multiplicationChecks schedule = 241 := by
  rcases assignment_counts with ⟨ha, hs, hm⟩
  norm_num [additionChecks, multiplicationChecks, ha, hs, hm]


/-- The thirty-six equality tests, one for each equation of (1.3). -/
def FinalEqualities (inputs : Fin 69 → ℕ) (trace : Fin 241 → ℤ) : Prop :=
  trace 0 = trace 5 ∧
  (inputs 25 : ℤ) = trace 7 ∧
  trace 11 = trace 16 ∧
  trace 22 = (inputs 26 : ℤ) ∧
  (inputs 24 : ℤ) = trace 26 ∧
  trace 38 = trace 39 ∧
  trace 44 = trace 46 ∧
  trace 51 = trace 53 ∧
  trace 104 = trace 105 ∧
  (inputs 48 : ℤ) = trace 116 ∧
  trace 124 = trace 125 ∧
  (inputs 31 : ℤ) = trace 127 ∧
  (inputs 31 : ℤ) = trace 130 ∧
  (inputs 31 : ℤ) = trace 133 ∧
  (inputs 31 : ℤ) = trace 136 ∧
  (inputs 31 : ℤ) = trace 139 ∧
  (inputs 31 : ℤ) = trace 142 ∧
  trace 150 = trace 151 ∧
  (inputs 46 : ℤ) = trace 158 ∧
  (inputs 23 : ℤ) = trace 161 ∧
  (inputs 23 : ℤ) = trace 164 ∧
  (inputs 23 : ℤ) = trace 167 ∧
  (inputs 23 : ℤ) = trace 170 ∧
  (inputs 23 : ℤ) = trace 173 ∧
  (inputs 23 : ℤ) = trace 176 ∧
  trace 181 = trace 182 ∧
  trace 188 = trace 189 ∧
  trace 195 = trace 196 ∧
  (inputs 36 : ℤ) = trace 199 ∧
  (inputs 34 : ℤ) = trace 204 ∧
  (inputs 35 : ℤ) = trace 209 ∧
  (inputs 2 : ℤ) = trace 210 ∧
  (inputs 4 : ℤ) = trace 212 ∧
  trace 213 = trace 218 ∧
  trace 219 = trace 225 ∧
  trace 228 = trace 240

/-! ### Reading each intermediate as a subterm of (1.3) -/

private theorem cadd {a b a' b' : ℤ} (ha : a = a') (hb : b = b') : a + b = a' + b' := by rw [ha, hb]
private theorem csub {a b a' b' : ℤ} (ha : a = a') (hb : b = b') : a - b = a' - b' := by rw [ha, hb]
private theorem cmul {a b a' b' : ℤ} (ha : a = a') (hb : b = b') : a * b = a' * b' := by rw [ha, hb]
private theorem pw1 {u x : ℤ} (hu : u = x) : u = x ^ 1 := by rw [hu, pow_one]
private theorem pw {u v x : ℤ} (a b : ℕ) (hu : u = x ^ a) (hv : v = x ^ b) : u * v = x ^ (a + b) := by
  rw [hu, hv, pow_add]

private theorem e0_0 (inputs : Fin 69 → ℕ) :
    node0 inputs = ((2 : ℤ) * (inputs 0 : ℤ)) :=
  cmul rfl rfl

private theorem e1_1 (inputs : Fin 69 → ℕ) :
    node1 inputs = ((inputs 20 : ℤ) + (inputs 21 : ℤ)) :=
  cadd rfl rfl

private theorem e2_2 (inputs : Fin 69 → ℕ) :
    node2 inputs = ((inputs 20 : ℤ) + (inputs 21 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e1_1 inputs)) (pw1 (e1_1 inputs))

private theorem e3_3 (inputs : Fin 69 → ℕ) :
    node3 inputs = ((3 : ℤ) * (inputs 21 : ℤ)) :=
  cmul rfl rfl

private theorem e4_4 (inputs : Fin 69 → ℕ) :
    node4 inputs = (((inputs 20 : ℤ) + (inputs 21 : ℤ)) ^ 2 + ((3 : ℤ) * (inputs 21 : ℤ))) :=
  cadd (e2_2 inputs) (e3_3 inputs)

private theorem e5_5 (inputs : Fin 69 → ℕ) :
    node5 inputs = ((((inputs 20 : ℤ) + (inputs 21 : ℤ)) ^ 2 + ((3 : ℤ) * (inputs 21 : ℤ))) + (inputs 20 : ℤ)) :=
  cadd (e4_4 inputs) rfl

private theorem e6_6 (inputs : Fin 69 → ℕ) :
    node6 inputs = ((inputs 32 : ℤ) * (inputs 26 : ℤ)) :=
  cmul rfl rfl

private theorem e7_7 (inputs : Fin 69 → ℕ) :
    node7 inputs = (((inputs 32 : ℤ) * (inputs 26 : ℤ)) + (inputs 32 : ℤ)) :=
  cadd (e6_6 inputs) rfl

private theorem e8_8 (inputs : Fin 69 → ℕ) :
    node8 inputs = ((inputs 9 : ℤ) * (inputs 26 : ℤ)) :=
  cmul rfl rfl

private theorem e9_9 (inputs : Fin 69 → ℕ) :
    node9 inputs = ((inputs 9 : ℤ) + ((inputs 9 : ℤ) * (inputs 26 : ℤ))) :=
  cadd rfl (e8_8 inputs)

private theorem e10_10 (inputs : Fin 69 → ℕ) :
    node10 inputs = (((inputs 9 : ℤ) * (inputs 26 : ℤ)) * (inputs 21 : ℤ)) :=
  cmul (e8_8 inputs) rfl

private theorem e11_11 (inputs : Fin 69 → ℕ) :
    node11 inputs = (((inputs 9 : ℤ) + ((inputs 9 : ℤ) * (inputs 26 : ℤ))) + (((inputs 9 : ℤ) * (inputs 26 : ℤ)) * (inputs 21 : ℤ))) :=
  cadd (e9_9 inputs) (e10_10 inputs)

private theorem e12_12 (inputs : Fin 69 → ℕ) :
    node12 inputs = ((inputs 1 : ℤ) + (inputs 40 : ℤ)) :=
  cadd rfl rfl

private theorem e13_13 (inputs : Fin 69 → ℕ) :
    node13 inputs = ((inputs 40 : ℤ) * (inputs 26 : ℤ)) :=
  cmul rfl rfl

private theorem e14_14 (inputs : Fin 69 → ℕ) :
    node14 inputs = (((inputs 1 : ℤ) + (inputs 40 : ℤ)) + ((inputs 40 : ℤ) * (inputs 26 : ℤ))) :=
  cadd (e12_12 inputs) (e13_13 inputs)

private theorem e15_15 (inputs : Fin 69 → ℕ) :
    node15 inputs = (((inputs 40 : ℤ) * (inputs 26 : ℤ)) * (inputs 20 : ℤ)) :=
  cmul (e13_13 inputs) rfl

private theorem e16_16 (inputs : Fin 69 → ℕ) :
    node16 inputs = ((((inputs 1 : ℤ) + (inputs 40 : ℤ)) + ((inputs 40 : ℤ) * (inputs 26 : ℤ))) + (((inputs 40 : ℤ) * (inputs 26 : ℤ)) * (inputs 20 : ℤ))) :=
  cadd (e14_14 inputs) (e15_15 inputs)

private theorem e17_17 (inputs : Fin 69 → ℕ) :
    node17 inputs = ((((inputs 9 : ℤ) + ((inputs 9 : ℤ) * (inputs 26 : ℤ))) + (((inputs 9 : ℤ) * (inputs 26 : ℤ)) * (inputs 21 : ℤ))) - (inputs 25 : ℤ)) :=
  csub (e11_11 inputs) rfl

private theorem e18_18 (inputs : Fin 69 → ℕ) :
    node18 inputs = ((((inputs 9 : ℤ) + ((inputs 9 : ℤ) * (inputs 26 : ℤ))) + (((inputs 9 : ℤ) * (inputs 26 : ℤ)) * (inputs 21 : ℤ))) - (inputs 25 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e17_17 inputs)) (pw1 (e17_17 inputs))

private theorem e19_19 (inputs : Fin 69 → ℕ) :
    node19 inputs = (inputs 1 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e20_20 (inputs : Fin 69 → ℕ) :
    node20 inputs = (((((inputs 9 : ℤ) + ((inputs 9 : ℤ) * (inputs 26 : ℤ))) + (((inputs 9 : ℤ) * (inputs 26 : ℤ)) * (inputs 21 : ℤ))) - (inputs 25 : ℤ)) ^ 2 + (inputs 1 : ℤ) ^ 2) :=
  cadd (e18_18 inputs) (e19_19 inputs)

private theorem e21_21 (inputs : Fin 69 → ℕ) :
    node21 inputs = ((((((inputs 9 : ℤ) + ((inputs 9 : ℤ) * (inputs 26 : ℤ))) + (((inputs 9 : ℤ) * (inputs 26 : ℤ)) * (inputs 21 : ℤ))) - (inputs 25 : ℤ)) ^ 2 + (inputs 1 : ℤ) ^ 2) + (inputs 27 : ℤ)) :=
  cadd (e20_20 inputs) rfl

private theorem e22_22 (inputs : Fin 69 → ℕ) :
    node22 inputs = (((((((inputs 9 : ℤ) + ((inputs 9 : ℤ) * (inputs 26 : ℤ))) + (((inputs 9 : ℤ) * (inputs 26 : ℤ)) * (inputs 21 : ℤ))) - (inputs 25 : ℤ)) ^ 2 + (inputs 1 : ℤ) ^ 2) + (inputs 27 : ℤ)) + (1 : ℤ)) :=
  cadd (e21_21 inputs) rfl

private theorem e23_23 (inputs : Fin 69 → ℕ) :
    node23 inputs = ((3 : ℤ) * (inputs 0 : ℤ)) :=
  cmul rfl rfl

private theorem e24_24 (inputs : Fin 69 → ℕ) :
    node24 inputs = (inputs 25 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e25_25 (inputs : Fin 69 → ℕ) :
    node25 inputs = (inputs 25 : ℤ) ^ 3 :=
  pw 1 2 (pw1 rfl) (e24_24 inputs)

private theorem e26_26 (inputs : Fin 69 → ℕ) :
    node26 inputs = (((3 : ℤ) * (inputs 0 : ℤ)) + (inputs 25 : ℤ) ^ 3) :=
  cadd (e23_23 inputs) (e25_25 inputs)

private theorem e27_27 (inputs : Fin 69 → ℕ) :
    node27 inputs = (inputs 24 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e28_28 (inputs : Fin 69 → ℕ) :
    node28 inputs = (inputs 24 : ℤ) ^ 4 :=
  pw 2 2 (e27_27 inputs) (e27_27 inputs)

private theorem e29_29 (inputs : Fin 69 → ℕ) :
    node29 inputs = (inputs 24 : ℤ) ^ 5 :=
  pw 1 4 (pw1 rfl) (e28_28 inputs)

private theorem e30_30 (inputs : Fin 69 → ℕ) :
    node30 inputs = (inputs 24 : ℤ) ^ 9 :=
  pw 4 5 (e28_28 inputs) (e29_29 inputs)

private theorem e31_31 (inputs : Fin 69 → ℕ) :
    node31 inputs = (inputs 24 : ℤ) ^ 18 :=
  pw 9 9 (e30_30 inputs) (e30_30 inputs)

private theorem e32_32 (inputs : Fin 69 → ℕ) :
    node32 inputs = (inputs 24 : ℤ) ^ 6 :=
  pw 1 5 (pw1 rfl) (e29_29 inputs)

private theorem e33_33 (inputs : Fin 69 → ℕ) :
    node33 inputs = ((inputs 24 : ℤ) ^ 6 + (2 : ℤ)) :=
  cadd (e32_32 inputs) rfl

private theorem e34_34 (inputs : Fin 69 → ℕ) :
    node34 inputs = ((inputs 24 : ℤ) ^ 18 * ((inputs 24 : ℤ) ^ 6 + (2 : ℤ))) :=
  cmul (e31_31 inputs) (e33_33 inputs)

private theorem e35_35 (inputs : Fin 69 → ℕ) :
    node35 inputs = ((inputs 17 : ℤ) + (1 : ℤ)) :=
  cadd rfl rfl

private theorem e36_36 (inputs : Fin 69 → ℕ) :
    node36 inputs = ((inputs 17 : ℤ) + (1 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e35_35 inputs)) (pw1 (e35_35 inputs))

private theorem e37_37 (inputs : Fin 69 → ℕ) :
    node37 inputs = (((inputs 24 : ℤ) ^ 18 * ((inputs 24 : ℤ) ^ 6 + (2 : ℤ))) * ((inputs 17 : ℤ) + (1 : ℤ)) ^ 2) :=
  cmul (e34_34 inputs) (e36_36 inputs)

private theorem e38_38 (inputs : Fin 69 → ℕ) :
    node38 inputs = ((((inputs 24 : ℤ) ^ 18 * ((inputs 24 : ℤ) ^ 6 + (2 : ℤ))) * ((inputs 17 : ℤ) + (1 : ℤ)) ^ 2) + (1 : ℤ)) :=
  cadd (e37_37 inputs) rfl

private theorem e39_39 (inputs : Fin 69 → ℕ) :
    node39 inputs = (inputs 47 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e40_40 (inputs : Fin 69 → ℕ) :
    node40 inputs = ((inputs 19 : ℤ) + (inputs 6 : ℤ)) :=
  cadd rfl rfl

private theorem e41_41 (inputs : Fin 69 → ℕ) :
    node41 inputs = ((inputs 6 : ℤ) * (inputs 26 : ℤ)) :=
  cmul rfl rfl

private theorem e42_42 (inputs : Fin 69 → ℕ) :
    node42 inputs = (((inputs 19 : ℤ) + (inputs 6 : ℤ)) + ((inputs 6 : ℤ) * (inputs 26 : ℤ))) :=
  cadd (e40_40 inputs) (e41_41 inputs)

private theorem e43_43 (inputs : Fin 69 → ℕ) :
    node43 inputs = (((inputs 6 : ℤ) * (inputs 26 : ℤ)) * (inputs 18 : ℤ)) :=
  cmul (e41_41 inputs) rfl

private theorem e44_44 (inputs : Fin 69 → ℕ) :
    node44 inputs = ((((inputs 19 : ℤ) + (inputs 6 : ℤ)) + ((inputs 6 : ℤ) * (inputs 26 : ℤ))) + (((inputs 6 : ℤ) * (inputs 26 : ℤ)) * (inputs 18 : ℤ))) :=
  cadd (e42_42 inputs) (e43_43 inputs)

private theorem e45_45 (inputs : Fin 69 → ℕ) :
    node45 inputs = ((inputs 16 : ℤ) * (inputs 44 : ℤ)) :=
  cmul rfl rfl

private theorem e46_46 (inputs : Fin 69 → ℕ) :
    node46 inputs = ((inputs 25 : ℤ) + ((inputs 16 : ℤ) * (inputs 44 : ℤ))) :=
  cadd rfl (e45_45 inputs)

private theorem e47_47 (inputs : Fin 69 → ℕ) :
    node47 inputs = ((inputs 15 : ℤ) + (inputs 3 : ℤ)) :=
  cadd rfl rfl

private theorem e48_48 (inputs : Fin 69 → ℕ) :
    node48 inputs = ((inputs 3 : ℤ) * (inputs 26 : ℤ)) :=
  cmul rfl rfl

private theorem e49_49 (inputs : Fin 69 → ℕ) :
    node49 inputs = (((inputs 15 : ℤ) + (inputs 3 : ℤ)) + ((inputs 3 : ℤ) * (inputs 26 : ℤ))) :=
  cadd (e47_47 inputs) (e48_48 inputs)

private theorem e50_50 (inputs : Fin 69 → ℕ) :
    node50 inputs = (((inputs 3 : ℤ) * (inputs 26 : ℤ)) * (inputs 22 : ℤ)) :=
  cmul (e48_48 inputs) rfl

private theorem e51_51 (inputs : Fin 69 → ℕ) :
    node51 inputs = ((((inputs 15 : ℤ) + (inputs 3 : ℤ)) + ((inputs 3 : ℤ) * (inputs 26 : ℤ))) + (((inputs 3 : ℤ) * (inputs 26 : ℤ)) * (inputs 22 : ℤ))) :=
  cadd (e49_49 inputs) (e50_50 inputs)

private theorem e52_52 (inputs : Fin 69 → ℕ) :
    node52 inputs = ((inputs 16 : ℤ) * (inputs 45 : ℤ)) :=
  cmul rfl rfl

private theorem e53_53 (inputs : Fin 69 → ℕ) :
    node53 inputs = ((inputs 25 : ℤ) + ((inputs 16 : ℤ) * (inputs 45 : ℤ))) :=
  cadd rfl (e52_52 inputs)

private theorem e54_54 (inputs : Fin 69 → ℕ) :
    node54 inputs = ((inputs 18 : ℤ) + (inputs 22 : ℤ)) :=
  cadd rfl rfl

private theorem e55_55 (inputs : Fin 69 → ℕ) :
    node55 inputs = ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e54_54 inputs)) (pw1 (e54_54 inputs))

private theorem e56_56 (inputs : Fin 69 → ℕ) :
    node56 inputs = ((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) :=
  cmul rfl (e55_55 inputs)

private theorem e57_57 (inputs : Fin 69 → ℕ) :
    node57 inputs = ((9 : ℤ) * (inputs 22 : ℤ)) :=
  cmul rfl rfl

private theorem e58_58 (inputs : Fin 69 → ℕ) :
    node58 inputs = (((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) :=
  cadd (e56_56 inputs) (e57_57 inputs)

private theorem e59_59 (inputs : Fin 69 → ℕ) :
    node59 inputs = ((3 : ℤ) * (inputs 18 : ℤ)) :=
  cmul rfl rfl

private theorem e60_60 (inputs : Fin 69 → ℕ) :
    node60 inputs = ((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) :=
  cadd (e58_58 inputs) (e59_59 inputs)

private theorem e61_61 (inputs : Fin 69 → ℕ) :
    node61 inputs = ((2 : ℤ) * (inputs 17 : ℤ)) :=
  cmul rfl rfl

private theorem e62_62 (inputs : Fin 69 → ℕ) :
    node62 inputs = (((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) - ((2 : ℤ) * (inputs 17 : ℤ))) :=
  csub (e60_60 inputs) (e61_61 inputs)

private theorem e63_63 (inputs : Fin 69 → ℕ) :
    node63 inputs = (((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 :=
  pw 1 1 (pw1 (e62_62 inputs)) (pw1 (e62_62 inputs))

private theorem e64_64 (inputs : Fin 69 → ℕ) :
    node64 inputs = ((1 : ℤ) + (inputs 26 : ℤ)) :=
  cadd rfl rfl

private theorem e65_65 (inputs : Fin 69 → ℕ) :
    node65 inputs = ((inputs 17 : ℤ) * (inputs 26 : ℤ)) :=
  cmul rfl rfl

private theorem e66_66 (inputs : Fin 69 → ℕ) :
    node66 inputs = (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) :=
  cadd (e64_64 inputs) (e65_65 inputs)

private theorem e67_67 (inputs : Fin 69 → ℕ) :
    node67 inputs = (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 :=
  pw 1 1 (pw1 (e66_66 inputs)) (pw1 (e66_66 inputs))

private theorem e68_68 (inputs : Fin 69 → ℕ) :
    node68 inputs = ((inputs 25 : ℤ) - (inputs 19 : ℤ)) :=
  csub rfl rfl

private theorem e69_69 (inputs : Fin 69 → ℕ) :
    node69 inputs = (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) :=
  csub (e68_68 inputs) rfl

private theorem e70_70 (inputs : Fin 69 → ℕ) :
    node70 inputs = (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e69_69 inputs)) (pw1 (e69_69 inputs))

private theorem e71_71 (inputs : Fin 69 → ℕ) :
    node71 inputs = ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2) :=
  cadd rfl (e70_70 inputs)

private theorem e72_72 (inputs : Fin 69 → ℕ) :
    node72 inputs = ((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) :=
  cmul (e67_67 inputs) (e71_71 inputs)

private theorem e73_73 (inputs : Fin 69 → ℕ) :
    node73 inputs = (inputs 19 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e74_74 (inputs : Fin 69 → ℕ) :
    node74 inputs = ((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) :=
  csub rfl (e73_73 inputs)

private theorem e75_75 (inputs : Fin 69 → ℕ) :
    node75 inputs = (inputs 15 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e76_76 (inputs : Fin 69 → ℕ) :
    node76 inputs = (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2) :=
  csub (e74_74 inputs) (e75_75 inputs)

private theorem e77_77 (inputs : Fin 69 → ℕ) :
    node77 inputs = (((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) :=
  cmul (e72_72 inputs) (e76_76 inputs)

private theorem e78_78 (inputs : Fin 69 → ℕ) :
    node78 inputs = ((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2) :=
  csub (e77_77 inputs) (e70_70 inputs)

private theorem e79_79 (inputs : Fin 69 → ℕ) :
    node79 inputs = ((inputs 8 : ℤ) + (1 : ℤ)) :=
  cadd rfl rfl

private theorem e80_80 (inputs : Fin 69 → ℕ) :
    node80 inputs = (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2) :=
  cmul (e79_79 inputs) (e67_67 inputs)

private theorem e81_81 (inputs : Fin 69 → ℕ) :
    node81 inputs = (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) :=
  csub (e78_78 inputs) (e80_80 inputs)

private theorem e82_82 (inputs : Fin 69 → ℕ) :
    node82 inputs = (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2 :=
  pw 1 1 (pw1 (e81_81 inputs)) (pw1 (e81_81 inputs))

private theorem e83_83 (inputs : Fin 69 → ℕ) :
    node83 inputs = ((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 + (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2) :=
  cadd (e63_63 inputs) (e82_82 inputs)

private theorem e84_84 (inputs : Fin 69 → ℕ) :
    node84 inputs = (((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) + (2 : ℤ)) :=
  cadd (e60_60 inputs) rfl

private theorem e85_85 (inputs : Fin 69 → ℕ) :
    node85 inputs = ((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) + (2 : ℤ)) - ((2 : ℤ) * (inputs 17 : ℤ))) :=
  csub (e84_84 inputs) (e61_61 inputs)

private theorem e86_86 (inputs : Fin 69 → ℕ) :
    node86 inputs = ((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) + (2 : ℤ)) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 :=
  pw 1 1 (pw1 (e85_85 inputs)) (pw1 (e85_85 inputs))

private theorem e87_87 (inputs : Fin 69 → ℕ) :
    node87 inputs = ((inputs 19 : ℤ) * (inputs 15 : ℤ)) :=
  cmul rfl rfl

private theorem e88_88 (inputs : Fin 69 → ℕ) :
    node88 inputs = ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) :=
  csub rfl (e87_87 inputs)

private theorem e89_89 (inputs : Fin 69 → ℕ) :
    node89 inputs = ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2 :=
  pw 1 1 (pw1 (e88_88 inputs)) (pw1 (e88_88 inputs))

private theorem e90_90 (inputs : Fin 69 → ℕ) :
    node90 inputs = ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2) :=
  cadd rfl (e89_89 inputs)

private theorem e91_91 (inputs : Fin 69 → ℕ) :
    node91 inputs = ((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) :=
  cmul (e67_67 inputs) (e90_90 inputs)

private theorem e92_92 (inputs : Fin 69 → ℕ) :
    node92 inputs = (((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) :=
  cmul (e91_91 inputs) (e76_76 inputs)

private theorem e93_93 (inputs : Fin 69 → ℕ) :
    node93 inputs = ((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2) :=
  csub (e92_92 inputs) (e89_89 inputs)

private theorem e94_94 (inputs : Fin 69 → ℕ) :
    node94 inputs = (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) :=
  csub (e93_93 inputs) (e80_80 inputs)

private theorem e95_95 (inputs : Fin 69 → ℕ) :
    node95 inputs = (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2 :=
  pw 1 1 (pw1 (e94_94 inputs)) (pw1 (e94_94 inputs))

private theorem e96_96 (inputs : Fin 69 → ℕ) :
    node96 inputs = (((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) + (2 : ℤ)) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 + (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2) :=
  cadd (e86_86 inputs) (e95_95 inputs)

private theorem e97_97 (inputs : Fin 69 → ℕ) :
    node97 inputs = (((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 + (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2) * (((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) + (2 : ℤ)) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 + (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2)) :=
  cmul (e83_83 inputs) (e96_96 inputs)

private theorem e98_98 (inputs : Fin 69 → ℕ) :
    node98 inputs = ((3 : ℤ) * (inputs 8 : ℤ)) :=
  cmul rfl rfl

private theorem e99_99 (inputs : Fin 69 → ℕ) :
    node99 inputs = (((3 : ℤ) * (inputs 8 : ℤ)) + (2 : ℤ)) :=
  cadd (e98_98 inputs) rfl

private theorem e100_100 (inputs : Fin 69 → ℕ) :
    node100 inputs = ((((3 : ℤ) * (inputs 8 : ℤ)) + (2 : ℤ)) - (inputs 17 : ℤ)) :=
  csub (e99_99 inputs) rfl

private theorem e101_101 (inputs : Fin 69 → ℕ) :
    node101 inputs = ((((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 + (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2) * (((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) + (2 : ℤ)) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 + (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2)) * ((((3 : ℤ) * (inputs 8 : ℤ)) + (2 : ℤ)) - (inputs 17 : ℤ))) :=
  cmul (e97_97 inputs) (e100_100 inputs)

private theorem e102_102 (inputs : Fin 69 → ℕ) :
    node102 inputs = (((3 : ℤ) * (inputs 0 : ℤ)) + (inputs 8 : ℤ)) :=
  cadd (e23_23 inputs) rfl

private theorem e103_103 (inputs : Fin 69 → ℕ) :
    node103 inputs = ((((3 : ℤ) * (inputs 0 : ℤ)) + (inputs 8 : ℤ)) - (inputs 17 : ℤ)) :=
  csub (e102_102 inputs) rfl

private theorem e104_104 (inputs : Fin 69 → ℕ) :
    node104 inputs = (((((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 + (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - (((inputs 25 : ℤ) - (inputs 19 : ℤ)) - (inputs 15 : ℤ)) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2) * (((((((3 : ℤ) * ((inputs 18 : ℤ) + (inputs 22 : ℤ)) ^ 2) + ((9 : ℤ) * (inputs 22 : ℤ))) + ((3 : ℤ) * (inputs 18 : ℤ))) + (2 : ℤ)) - ((2 : ℤ) * (inputs 17 : ℤ))) ^ 2 + (((((((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2 * ((1 : ℤ) + ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2)) * (((inputs 26 : ℤ) - (inputs 19 : ℤ) ^ 2) - (inputs 15 : ℤ) ^ 2)) - ((inputs 25 : ℤ) - ((inputs 19 : ℤ) * (inputs 15 : ℤ))) ^ 2) - (((inputs 8 : ℤ) + (1 : ℤ)) * (((1 : ℤ) + (inputs 26 : ℤ)) + ((inputs 17 : ℤ) * (inputs 26 : ℤ))) ^ 2)) ^ 2)) * ((((3 : ℤ) * (inputs 8 : ℤ)) + (2 : ℤ)) - (inputs 17 : ℤ))) * ((((3 : ℤ) * (inputs 0 : ℤ)) + (inputs 8 : ℤ)) - (inputs 17 : ℤ))) :=
  cmul (e101_101 inputs) (e103_103 inputs)

private theorem e105_105 (inputs : Fin 69 → ℕ) :
    node105 inputs = ((inputs 16 : ℤ) * (inputs 39 : ℤ)) :=
  cmul rfl rfl

private theorem e106_106 (inputs : Fin 69 → ℕ) :
    node106 inputs = ((inputs 17 : ℤ) + (inputs 16 : ℤ)) :=
  cadd rfl rfl

private theorem e107_107 (inputs : Fin 69 → ℕ) :
    node107 inputs = (((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) :=
  cadd (e106_106 inputs) rfl

private theorem e108_108 (inputs : Fin 69 → ℕ) :
    node108 inputs = ((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) :=
  cadd (e107_107 inputs) rfl

private theorem e109_109 (inputs : Fin 69 → ℕ) :
    node109 inputs = (((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) + (inputs 8 : ℤ)) :=
  cadd (e108_108 inputs) rfl

private theorem e110_110 (inputs : Fin 69 → ℕ) :
    node110 inputs = ((((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) + (inputs 8 : ℤ)) + (inputs 18 : ℤ)) :=
  cadd (e109_109 inputs) rfl

private theorem e111_111 (inputs : Fin 69 → ℕ) :
    node111 inputs = (((((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) + (inputs 8 : ℤ)) + (inputs 18 : ℤ)) + (inputs 22 : ℤ)) :=
  cadd (e110_110 inputs) rfl

private theorem e112_112 (inputs : Fin 69 → ℕ) :
    node112 inputs = ((((((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) + (inputs 8 : ℤ)) + (inputs 18 : ℤ)) + (inputs 22 : ℤ)) + (inputs 54 : ℤ)) :=
  cadd (e111_111 inputs) rfl

private theorem e113_113 (inputs : Fin 69 → ℕ) :
    node113 inputs = (((((((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) + (inputs 8 : ℤ)) + (inputs 18 : ℤ)) + (inputs 22 : ℤ)) + (inputs 54 : ℤ)) + (inputs 55 : ℤ)) :=
  cadd (e112_112 inputs) rfl

private theorem e114_114 (inputs : Fin 69 → ℕ) :
    node114 inputs = ((((((((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) + (inputs 8 : ℤ)) + (inputs 18 : ℤ)) + (inputs 22 : ℤ)) + (inputs 54 : ℤ)) + (inputs 55 : ℤ)) + (inputs 56 : ℤ)) :=
  cadd (e113_113 inputs) rfl

private theorem e115_115 (inputs : Fin 69 → ℕ) :
    node115 inputs = (((((((((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) + (inputs 8 : ℤ)) + (inputs 18 : ℤ)) + (inputs 22 : ℤ)) + (inputs 54 : ℤ)) + (inputs 55 : ℤ)) + (inputs 56 : ℤ)) + (inputs 57 : ℤ)) :=
  cadd (e114_114 inputs) rfl

private theorem e116_116 (inputs : Fin 69 → ℕ) :
    node116 inputs = ((((((((((((inputs 17 : ℤ) + (inputs 16 : ℤ)) + (inputs 3 : ℤ)) + (inputs 6 : ℤ)) + (inputs 8 : ℤ)) + (inputs 18 : ℤ)) + (inputs 22 : ℤ)) + (inputs 54 : ℤ)) + (inputs 55 : ℤ)) + (inputs 56 : ℤ)) + (inputs 57 : ℤ)) + (inputs 58 : ℤ)) :=
  cadd (e115_115 inputs) rfl

private theorem e117_117 (inputs : Fin 69 → ℕ) :
    node117 inputs = (inputs 48 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e118_118 (inputs : Fin 69 → ℕ) :
    node118 inputs = (inputs 48 : ℤ) ^ 3 :=
  pw 1 2 (pw1 rfl) (e117_117 inputs)

private theorem e119_119 (inputs : Fin 69 → ℕ) :
    node119 inputs = ((inputs 48 : ℤ) + (2 : ℤ)) :=
  cadd rfl rfl

private theorem e120_120 (inputs : Fin 69 → ℕ) :
    node120 inputs = ((inputs 48 : ℤ) ^ 3 * ((inputs 48 : ℤ) + (2 : ℤ))) :=
  cmul (e118_118 inputs) (e119_119 inputs)

private theorem e121_121 (inputs : Fin 69 → ℕ) :
    node121 inputs = ((inputs 41 : ℤ) + (1 : ℤ)) :=
  cadd rfl rfl

private theorem e122_122 (inputs : Fin 69 → ℕ) :
    node122 inputs = ((inputs 41 : ℤ) + (1 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e121_121 inputs)) (pw1 (e121_121 inputs))

private theorem e123_123 (inputs : Fin 69 → ℕ) :
    node123 inputs = (((inputs 48 : ℤ) ^ 3 * ((inputs 48 : ℤ) + (2 : ℤ))) * ((inputs 41 : ℤ) + (1 : ℤ)) ^ 2) :=
  cmul (e120_120 inputs) (e122_122 inputs)

private theorem e124_124 (inputs : Fin 69 → ℕ) :
    node124 inputs = ((((inputs 48 : ℤ) ^ 3 * ((inputs 48 : ℤ) + (2 : ℤ))) * ((inputs 41 : ℤ) + (1 : ℤ)) ^ 2) + (1 : ℤ)) :=
  cadd (e123_123 inputs) rfl

private theorem e125_125 (inputs : Fin 69 → ℕ) :
    node125 inputs = (inputs 28 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e126_126 (inputs : Fin 69 → ℕ) :
    node126 inputs = ((inputs 41 : ℤ) * (inputs 17 : ℤ)) :=
  cmul rfl rfl

private theorem e127_127 (inputs : Fin 69 → ℕ) :
    node127 inputs = (((inputs 41 : ℤ) * (inputs 17 : ℤ)) + (inputs 41 : ℤ)) :=
  cadd (e126_126 inputs) rfl

private theorem e128_128 (inputs : Fin 69 → ℕ) :
    node128 inputs = ((inputs 64 : ℤ) + (inputs 41 : ℤ)) :=
  cadd rfl rfl

private theorem e129_129 (inputs : Fin 69 → ℕ) :
    node129 inputs = (((inputs 64 : ℤ) + (inputs 41 : ℤ)) * (inputs 49 : ℤ)) :=
  cmul (e128_128 inputs) rfl

private theorem e130_130 (inputs : Fin 69 → ℕ) :
    node130 inputs = ((inputs 3 : ℤ) + (((inputs 64 : ℤ) + (inputs 41 : ℤ)) * (inputs 49 : ℤ))) :=
  cadd rfl (e129_129 inputs)

private theorem e131_131 (inputs : Fin 69 → ℕ) :
    node131 inputs = ((inputs 65 : ℤ) + (inputs 41 : ℤ)) :=
  cadd rfl rfl

private theorem e132_132 (inputs : Fin 69 → ℕ) :
    node132 inputs = (((inputs 65 : ℤ) + (inputs 41 : ℤ)) * (inputs 50 : ℤ)) :=
  cmul (e131_131 inputs) rfl

private theorem e133_133 (inputs : Fin 69 → ℕ) :
    node133 inputs = ((inputs 6 : ℤ) + (((inputs 65 : ℤ) + (inputs 41 : ℤ)) * (inputs 50 : ℤ))) :=
  cadd rfl (e132_132 inputs)

private theorem e134_134 (inputs : Fin 69 → ℕ) :
    node134 inputs = ((inputs 66 : ℤ) + (inputs 41 : ℤ)) :=
  cadd rfl rfl

private theorem e135_135 (inputs : Fin 69 → ℕ) :
    node135 inputs = (((inputs 66 : ℤ) + (inputs 41 : ℤ)) * (inputs 51 : ℤ)) :=
  cmul (e134_134 inputs) rfl

private theorem e136_136 (inputs : Fin 69 → ℕ) :
    node136 inputs = ((inputs 8 : ℤ) + (((inputs 66 : ℤ) + (inputs 41 : ℤ)) * (inputs 51 : ℤ))) :=
  cadd rfl (e135_135 inputs)

private theorem e137_137 (inputs : Fin 69 → ℕ) :
    node137 inputs = ((inputs 67 : ℤ) + (inputs 41 : ℤ)) :=
  cadd rfl rfl

private theorem e138_138 (inputs : Fin 69 → ℕ) :
    node138 inputs = (((inputs 67 : ℤ) + (inputs 41 : ℤ)) * (inputs 52 : ℤ)) :=
  cmul (e137_137 inputs) rfl

private theorem e139_139 (inputs : Fin 69 → ℕ) :
    node139 inputs = ((inputs 18 : ℤ) + (((inputs 67 : ℤ) + (inputs 41 : ℤ)) * (inputs 52 : ℤ))) :=
  cadd rfl (e138_138 inputs)

private theorem e140_140 (inputs : Fin 69 → ℕ) :
    node140 inputs = ((inputs 68 : ℤ) + (inputs 41 : ℤ)) :=
  cadd rfl rfl

private theorem e141_141 (inputs : Fin 69 → ℕ) :
    node141 inputs = (((inputs 68 : ℤ) + (inputs 41 : ℤ)) * (inputs 53 : ℤ)) :=
  cmul (e140_140 inputs) rfl

private theorem e142_142 (inputs : Fin 69 → ℕ) :
    node142 inputs = ((inputs 22 : ℤ) + (((inputs 68 : ℤ) + (inputs 41 : ℤ)) * (inputs 53 : ℤ))) :=
  cadd rfl (e141_141 inputs)

private theorem e143_143 (inputs : Fin 69 → ℕ) :
    node143 inputs = (inputs 31 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e144_144 (inputs : Fin 69 → ℕ) :
    node144 inputs = (inputs 31 : ℤ) ^ 3 :=
  pw 1 2 (pw1 rfl) (e143_143 inputs)

private theorem e145_145 (inputs : Fin 69 → ℕ) :
    node145 inputs = ((inputs 31 : ℤ) + (2 : ℤ)) :=
  cadd rfl rfl

private theorem e146_146 (inputs : Fin 69 → ℕ) :
    node146 inputs = ((inputs 31 : ℤ) ^ 3 * ((inputs 31 : ℤ) + (2 : ℤ))) :=
  cmul (e144_144 inputs) (e145_145 inputs)

private theorem e147_147 (inputs : Fin 69 → ℕ) :
    node147 inputs = ((inputs 30 : ℤ) + (1 : ℤ)) :=
  cadd rfl rfl

private theorem e148_148 (inputs : Fin 69 → ℕ) :
    node148 inputs = ((inputs 30 : ℤ) + (1 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e147_147 inputs)) (pw1 (e147_147 inputs))

private theorem e149_149 (inputs : Fin 69 → ℕ) :
    node149 inputs = (((inputs 31 : ℤ) ^ 3 * ((inputs 31 : ℤ) + (2 : ℤ))) * ((inputs 30 : ℤ) + (1 : ℤ)) ^ 2) :=
  cmul (e146_146 inputs) (e148_148 inputs)

private theorem e150_150 (inputs : Fin 69 → ℕ) :
    node150 inputs = ((((inputs 31 : ℤ) ^ 3 * ((inputs 31 : ℤ) + (2 : ℤ))) * ((inputs 30 : ℤ) + (1 : ℤ)) ^ 2) + (1 : ℤ)) :=
  cadd (e149_149 inputs) rfl

private theorem e151_151 (inputs : Fin 69 → ℕ) :
    node151 inputs = (inputs 29 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e152_152 (inputs : Fin 69 → ℕ) :
    node152 inputs = ((inputs 31 : ℤ) - (inputs 17 : ℤ)) :=
  csub rfl rfl

private theorem e153_153 (inputs : Fin 69 → ℕ) :
    node153 inputs = ((inputs 30 : ℤ) * ((inputs 31 : ℤ) - (inputs 17 : ℤ))) :=
  cmul rfl (e152_152 inputs)

private theorem e154_154 (inputs : Fin 69 → ℕ) :
    node154 inputs = (((inputs 30 : ℤ) * ((inputs 31 : ℤ) - (inputs 17 : ℤ))) * ((inputs 64 : ℤ) + (inputs 41 : ℤ))) :=
  cmul (e153_153 inputs) (e128_128 inputs)

private theorem e155_155 (inputs : Fin 69 → ℕ) :
    node155 inputs = ((((inputs 30 : ℤ) * ((inputs 31 : ℤ) - (inputs 17 : ℤ))) * ((inputs 64 : ℤ) + (inputs 41 : ℤ))) * ((inputs 65 : ℤ) + (inputs 41 : ℤ))) :=
  cmul (e154_154 inputs) (e131_131 inputs)

private theorem e156_156 (inputs : Fin 69 → ℕ) :
    node156 inputs = (((((inputs 30 : ℤ) * ((inputs 31 : ℤ) - (inputs 17 : ℤ))) * ((inputs 64 : ℤ) + (inputs 41 : ℤ))) * ((inputs 65 : ℤ) + (inputs 41 : ℤ))) * ((inputs 66 : ℤ) + (inputs 41 : ℤ))) :=
  cmul (e155_155 inputs) (e134_134 inputs)

private theorem e157_157 (inputs : Fin 69 → ℕ) :
    node157 inputs = ((((((inputs 30 : ℤ) * ((inputs 31 : ℤ) - (inputs 17 : ℤ))) * ((inputs 64 : ℤ) + (inputs 41 : ℤ))) * ((inputs 65 : ℤ) + (inputs 41 : ℤ))) * ((inputs 66 : ℤ) + (inputs 41 : ℤ))) * ((inputs 67 : ℤ) + (inputs 41 : ℤ))) :=
  cmul (e156_156 inputs) (e137_137 inputs)

private theorem e158_158 (inputs : Fin 69 → ℕ) :
    node158 inputs = (((((((inputs 30 : ℤ) * ((inputs 31 : ℤ) - (inputs 17 : ℤ))) * ((inputs 64 : ℤ) + (inputs 41 : ℤ))) * ((inputs 65 : ℤ) + (inputs 41 : ℤ))) * ((inputs 66 : ℤ) + (inputs 41 : ℤ))) * ((inputs 67 : ℤ) + (inputs 41 : ℤ))) * ((inputs 68 : ℤ) + (inputs 41 : ℤ))) :=
  cmul (e157_157 inputs) (e140_140 inputs)

private theorem e159_159 (inputs : Fin 69 → ℕ) :
    node159 inputs = ((1 : ℤ) + (inputs 38 : ℤ)) :=
  cadd rfl rfl

private theorem e160_160 (inputs : Fin 69 → ℕ) :
    node160 inputs = (((1 : ℤ) + (inputs 38 : ℤ)) * ((inputs 31 : ℤ) - (inputs 17 : ℤ))) :=
  cmul (e159_159 inputs) (e152_152 inputs)

private theorem e161_161 (inputs : Fin 69 → ℕ) :
    node161 inputs = ((inputs 16 : ℤ) + (((1 : ℤ) + (inputs 38 : ℤ)) * ((inputs 31 : ℤ) - (inputs 17 : ℤ)))) :=
  cadd rfl (e160_160 inputs)

private theorem e162_162 (inputs : Fin 69 → ℕ) :
    node162 inputs = ((inputs 16 : ℤ) * (inputs 54 : ℤ)) :=
  cmul rfl rfl

private theorem e163_163 (inputs : Fin 69 → ℕ) :
    node163 inputs = (((inputs 64 : ℤ) + (inputs 41 : ℤ)) * (inputs 59 : ℤ)) :=
  cmul (e128_128 inputs) rfl

private theorem e164_164 (inputs : Fin 69 → ℕ) :
    node164 inputs = (((inputs 16 : ℤ) * (inputs 54 : ℤ)) + (((inputs 64 : ℤ) + (inputs 41 : ℤ)) * (inputs 59 : ℤ))) :=
  cadd (e162_162 inputs) (e163_163 inputs)

private theorem e165_165 (inputs : Fin 69 → ℕ) :
    node165 inputs = ((inputs 16 : ℤ) * (inputs 55 : ℤ)) :=
  cmul rfl rfl

private theorem e166_166 (inputs : Fin 69 → ℕ) :
    node166 inputs = (((inputs 65 : ℤ) + (inputs 41 : ℤ)) * (inputs 60 : ℤ)) :=
  cmul (e131_131 inputs) rfl

private theorem e167_167 (inputs : Fin 69 → ℕ) :
    node167 inputs = (((inputs 16 : ℤ) * (inputs 55 : ℤ)) + (((inputs 65 : ℤ) + (inputs 41 : ℤ)) * (inputs 60 : ℤ))) :=
  cadd (e165_165 inputs) (e166_166 inputs)

private theorem e168_168 (inputs : Fin 69 → ℕ) :
    node168 inputs = ((inputs 16 : ℤ) * (inputs 56 : ℤ)) :=
  cmul rfl rfl

private theorem e169_169 (inputs : Fin 69 → ℕ) :
    node169 inputs = (((inputs 66 : ℤ) + (inputs 41 : ℤ)) * (inputs 61 : ℤ)) :=
  cmul (e134_134 inputs) rfl

private theorem e170_170 (inputs : Fin 69 → ℕ) :
    node170 inputs = (((inputs 16 : ℤ) * (inputs 56 : ℤ)) + (((inputs 66 : ℤ) + (inputs 41 : ℤ)) * (inputs 61 : ℤ))) :=
  cadd (e168_168 inputs) (e169_169 inputs)

private theorem e171_171 (inputs : Fin 69 → ℕ) :
    node171 inputs = ((inputs 16 : ℤ) * (inputs 57 : ℤ)) :=
  cmul rfl rfl

private theorem e172_172 (inputs : Fin 69 → ℕ) :
    node172 inputs = (((inputs 67 : ℤ) + (inputs 41 : ℤ)) * (inputs 62 : ℤ)) :=
  cmul (e137_137 inputs) rfl

private theorem e173_173 (inputs : Fin 69 → ℕ) :
    node173 inputs = (((inputs 16 : ℤ) * (inputs 57 : ℤ)) + (((inputs 67 : ℤ) + (inputs 41 : ℤ)) * (inputs 62 : ℤ))) :=
  cadd (e171_171 inputs) (e172_172 inputs)

private theorem e174_174 (inputs : Fin 69 → ℕ) :
    node174 inputs = ((inputs 16 : ℤ) * (inputs 58 : ℤ)) :=
  cmul rfl rfl

private theorem e175_175 (inputs : Fin 69 → ℕ) :
    node175 inputs = (((inputs 68 : ℤ) + (inputs 41 : ℤ)) * (inputs 63 : ℤ)) :=
  cmul (e140_140 inputs) rfl

private theorem e176_176 (inputs : Fin 69 → ℕ) :
    node176 inputs = (((inputs 16 : ℤ) * (inputs 58 : ℤ)) + (((inputs 68 : ℤ) + (inputs 41 : ℤ)) * (inputs 63 : ℤ))) :=
  cadd (e174_174 inputs) (e175_175 inputs)

private theorem e177_177 (inputs : Fin 69 → ℕ) :
    node177 inputs = (inputs 36 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e178_178 (inputs : Fin 69 → ℕ) :
    node178 inputs = ((inputs 36 : ℤ) ^ 2 - (1 : ℤ)) :=
  csub (e177_177 inputs) rfl

private theorem e179_179 (inputs : Fin 69 → ℕ) :
    node179 inputs = (inputs 34 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e180_180 (inputs : Fin 69 → ℕ) :
    node180 inputs = (((inputs 36 : ℤ) ^ 2 - (1 : ℤ)) * (inputs 34 : ℤ) ^ 2) :=
  cmul (e178_178 inputs) (e179_179 inputs)

private theorem e181_181 (inputs : Fin 69 → ℕ) :
    node181 inputs = ((((inputs 36 : ℤ) ^ 2 - (1 : ℤ)) * (inputs 34 : ℤ) ^ 2) + (1 : ℤ)) :=
  cadd (e180_180 inputs) rfl

private theorem e182_182 (inputs : Fin 69 → ℕ) :
    node182 inputs = (inputs 37 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e183_183 (inputs : Fin 69 → ℕ) :
    node183 inputs = (inputs 46 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e184_184 (inputs : Fin 69 → ℕ) :
    node184 inputs = ((inputs 36 : ℤ) ^ 2 * (inputs 46 : ℤ) ^ 2) :=
  cmul (e177_177 inputs) (e183_183 inputs)

private theorem e185_185 (inputs : Fin 69 → ℕ) :
    node185 inputs = (((inputs 36 : ℤ) ^ 2 * (inputs 46 : ℤ) ^ 2) - (1 : ℤ)) :=
  csub (e184_184 inputs) rfl

private theorem e186_186 (inputs : Fin 69 → ℕ) :
    node186 inputs = (inputs 35 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e187_187 (inputs : Fin 69 → ℕ) :
    node187 inputs = ((((inputs 36 : ℤ) ^ 2 * (inputs 46 : ℤ) ^ 2) - (1 : ℤ)) * (inputs 35 : ℤ) ^ 2) :=
  cmul (e185_185 inputs) (e186_186 inputs)

private theorem e188_188 (inputs : Fin 69 → ℕ) :
    node188 inputs = (((((inputs 36 : ℤ) ^ 2 * (inputs 46 : ℤ) ^ 2) - (1 : ℤ)) * (inputs 35 : ℤ) ^ 2) + (1 : ℤ)) :=
  cadd (e187_187 inputs) rfl

private theorem e189_189 (inputs : Fin 69 → ℕ) :
    node189 inputs = (inputs 43 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e190_190 (inputs : Fin 69 → ℕ) :
    node190 inputs = ((inputs 34 : ℤ) * (inputs 35 : ℤ)) :=
  cmul rfl rfl

private theorem e191_191 (inputs : Fin 69 → ℕ) :
    node191 inputs = (((inputs 34 : ℤ) * (inputs 35 : ℤ)) * (inputs 23 : ℤ)) :=
  cmul (e190_190 inputs) rfl

private theorem e192_192 (inputs : Fin 69 → ℕ) :
    node192 inputs = ((inputs 4 : ℤ) - (((inputs 34 : ℤ) * (inputs 35 : ℤ)) * (inputs 23 : ℤ))) :=
  csub rfl (e191_191 inputs)

private theorem e193_193 (inputs : Fin 69 → ℕ) :
    node193 inputs = ((inputs 4 : ℤ) - (((inputs 34 : ℤ) * (inputs 35 : ℤ)) * (inputs 23 : ℤ))) ^ 2 :=
  pw 1 1 (pw1 (e192_192 inputs)) (pw1 (e192_192 inputs))

private theorem e194_194 (inputs : Fin 69 → ℕ) :
    node194 inputs = ((5 : ℤ) * ((inputs 4 : ℤ) - (((inputs 34 : ℤ) * (inputs 35 : ℤ)) * (inputs 23 : ℤ))) ^ 2) :=
  cmul rfl (e193_193 inputs)

private theorem e195_195 (inputs : Fin 69 → ℕ) :
    node195 inputs = (((5 : ℤ) * ((inputs 4 : ℤ) - (((inputs 34 : ℤ) * (inputs 35 : ℤ)) * (inputs 23 : ℤ))) ^ 2) + (inputs 33 : ℤ)) :=
  cadd (e194_194 inputs) rfl

private theorem e196_196 (inputs : Fin 69 → ℕ) :
    node196 inputs = ((inputs 34 : ℤ) ^ 2 * (inputs 35 : ℤ) ^ 2) :=
  cmul (e179_179 inputs) (e186_186 inputs)

private theorem e197_197 (inputs : Fin 69 → ℕ) :
    node197 inputs = ((9 : ℤ) * (inputs 31 : ℤ)) :=
  cmul rfl rfl

private theorem e198_198 (inputs : Fin 69 → ℕ) :
    node198 inputs = (((9 : ℤ) * (inputs 31 : ℤ)) * (inputs 46 : ℤ)) :=
  cmul (e197_197 inputs) rfl

private theorem e199_199 (inputs : Fin 69 → ℕ) :
    node199 inputs = ((((9 : ℤ) * (inputs 31 : ℤ)) * (inputs 46 : ℤ)) * (inputs 23 : ℤ)) :=
  cmul (e198_198 inputs) rfl

private theorem e200_200 (inputs : Fin 69 → ℕ) :
    node200 inputs = ((inputs 31 : ℤ) - (inputs 24 : ℤ)) :=
  csub rfl rfl

private theorem e201_201 (inputs : Fin 69 → ℕ) :
    node201 inputs = (((inputs 31 : ℤ) - (inputs 24 : ℤ)) + (1 : ℤ)) :=
  cadd (e200_200 inputs) rfl

private theorem e202_202 (inputs : Fin 69 → ℕ) :
    node202 inputs = ((inputs 36 : ℤ) - (1 : ℤ)) :=
  csub rfl rfl

private theorem e203_203 (inputs : Fin 69 → ℕ) :
    node203 inputs = ((inputs 12 : ℤ) * ((inputs 36 : ℤ) - (1 : ℤ))) :=
  cmul rfl (e202_202 inputs)

private theorem e204_204 (inputs : Fin 69 → ℕ) :
    node204 inputs = ((((inputs 31 : ℤ) - (inputs 24 : ℤ)) + (1 : ℤ)) + ((inputs 12 : ℤ) * ((inputs 36 : ℤ) - (1 : ℤ)))) :=
  cadd (e201_201 inputs) (e203_203 inputs)

private theorem e205_205 (inputs : Fin 69 → ℕ) :
    node205 inputs = ((inputs 24 : ℤ) + (1 : ℤ)) :=
  cadd rfl rfl

private theorem e206_206 (inputs : Fin 69 → ℕ) :
    node206 inputs = ((inputs 36 : ℤ) * (inputs 46 : ℤ)) :=
  cmul rfl rfl

private theorem e207_207 (inputs : Fin 69 → ℕ) :
    node207 inputs = (((inputs 36 : ℤ) * (inputs 46 : ℤ)) - (1 : ℤ)) :=
  csub (e206_206 inputs) rfl

private theorem e208_208 (inputs : Fin 69 → ℕ) :
    node208 inputs = ((inputs 13 : ℤ) * (((inputs 36 : ℤ) * (inputs 46 : ℤ)) - (1 : ℤ))) :=
  cmul rfl (e207_207 inputs)

private theorem e209_209 (inputs : Fin 69 → ℕ) :
    node209 inputs = (((inputs 24 : ℤ) + (1 : ℤ)) + ((inputs 13 : ℤ) * (((inputs 36 : ℤ) * (inputs 46 : ℤ)) - (1 : ℤ)))) :=
  cadd (e205_205 inputs) (e208_208 inputs)

private theorem e210_210 (inputs : Fin 69 → ℕ) :
    node210 inputs = (((inputs 36 : ℤ) * (inputs 46 : ℤ)) + (inputs 36 : ℤ)) :=
  cadd (e206_206 inputs) rfl

private theorem e211_211 (inputs : Fin 69 → ℕ) :
    node211 inputs = ((inputs 14 : ℤ) + (inputs 31 : ℤ)) :=
  cadd rfl rfl

private theorem e212_212 (inputs : Fin 69 → ℕ) :
    node212 inputs = (((inputs 14 : ℤ) + (inputs 31 : ℤ)) + (1 : ℤ)) :=
  cadd (e211_211 inputs) rfl

private theorem e213_213 (inputs : Fin 69 → ℕ) :
    node213 inputs = (inputs 5 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e214_214 (inputs : Fin 69 → ℕ) :
    node214 inputs = (inputs 2 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e215_215 (inputs : Fin 69 → ℕ) :
    node215 inputs = ((inputs 2 : ℤ) ^ 2 - (1 : ℤ)) :=
  csub (e214_214 inputs) rfl

private theorem e216_216 (inputs : Fin 69 → ℕ) :
    node216 inputs = (inputs 4 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e217_217 (inputs : Fin 69 → ℕ) :
    node217 inputs = (((inputs 2 : ℤ) ^ 2 - (1 : ℤ)) * (inputs 4 : ℤ) ^ 2) :=
  cmul (e215_215 inputs) (e216_216 inputs)

private theorem e218_218 (inputs : Fin 69 → ℕ) :
    node218 inputs = ((((inputs 2 : ℤ) ^ 2 - (1 : ℤ)) * (inputs 4 : ℤ) ^ 2) + (1 : ℤ)) :=
  cadd (e217_217 inputs) rfl

private theorem e219_219 (inputs : Fin 69 → ℕ) :
    node219 inputs = (inputs 7 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e220_220 (inputs : Fin 69 → ℕ) :
    node220 inputs = ((4 : ℤ) * ((inputs 2 : ℤ) ^ 2 - (1 : ℤ))) :=
  cmul rfl (e215_215 inputs)

private theorem e221_221 (inputs : Fin 69 → ℕ) :
    node221 inputs = (inputs 10 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e222_222 (inputs : Fin 69 → ℕ) :
    node222 inputs = (((4 : ℤ) * ((inputs 2 : ℤ) ^ 2 - (1 : ℤ))) * (inputs 10 : ℤ) ^ 2) :=
  cmul (e220_220 inputs) (e221_221 inputs)

private theorem e223_223 (inputs : Fin 69 → ℕ) :
    node223 inputs = (inputs 4 : ℤ) ^ 4 :=
  pw 2 2 (e216_216 inputs) (e216_216 inputs)

private theorem e224_224 (inputs : Fin 69 → ℕ) :
    node224 inputs = ((((4 : ℤ) * ((inputs 2 : ℤ) ^ 2 - (1 : ℤ))) * (inputs 10 : ℤ) ^ 2) * (inputs 4 : ℤ) ^ 4) :=
  cmul (e222_222 inputs) (e223_223 inputs)

private theorem e225_225 (inputs : Fin 69 → ℕ) :
    node225 inputs = (((((4 : ℤ) * ((inputs 2 : ℤ) ^ 2 - (1 : ℤ))) * (inputs 10 : ℤ) ^ 2) * (inputs 4 : ℤ) ^ 4) + (1 : ℤ)) :=
  cadd (e224_224 inputs) rfl

private theorem e226_226 (inputs : Fin 69 → ℕ) :
    node226 inputs = ((inputs 42 : ℤ) * (inputs 7 : ℤ)) :=
  cmul rfl rfl

private theorem e227_227 (inputs : Fin 69 → ℕ) :
    node227 inputs = ((inputs 5 : ℤ) + ((inputs 42 : ℤ) * (inputs 7 : ℤ))) :=
  cadd rfl (e226_226 inputs)

private theorem e228_228 (inputs : Fin 69 → ℕ) :
    node228 inputs = ((inputs 5 : ℤ) + ((inputs 42 : ℤ) * (inputs 7 : ℤ))) ^ 2 :=
  pw 1 1 (pw1 (e227_227 inputs)) (pw1 (e227_227 inputs))

private theorem e229_229 (inputs : Fin 69 → ℕ) :
    node229 inputs = ((inputs 7 : ℤ) ^ 2 - (inputs 2 : ℤ)) :=
  csub (e219_219 inputs) rfl

private theorem e230_230 (inputs : Fin 69 → ℕ) :
    node230 inputs = ((inputs 7 : ℤ) ^ 2 * ((inputs 7 : ℤ) ^ 2 - (inputs 2 : ℤ))) :=
  cmul (e219_219 inputs) (e229_229 inputs)

private theorem e231_231 (inputs : Fin 69 → ℕ) :
    node231 inputs = ((inputs 2 : ℤ) + ((inputs 7 : ℤ) ^ 2 * ((inputs 7 : ℤ) ^ 2 - (inputs 2 : ℤ)))) :=
  cadd rfl (e230_230 inputs)

private theorem e232_232 (inputs : Fin 69 → ℕ) :
    node232 inputs = ((inputs 2 : ℤ) + ((inputs 7 : ℤ) ^ 2 * ((inputs 7 : ℤ) ^ 2 - (inputs 2 : ℤ)))) ^ 2 :=
  pw 1 1 (pw1 (e231_231 inputs)) (pw1 (e231_231 inputs))

private theorem e233_233 (inputs : Fin 69 → ℕ) :
    node233 inputs = (((inputs 2 : ℤ) + ((inputs 7 : ℤ) ^ 2 * ((inputs 7 : ℤ) ^ 2 - (inputs 2 : ℤ)))) ^ 2 - (1 : ℤ)) :=
  csub (e232_232 inputs) rfl

private theorem e234_234 (inputs : Fin 69 → ℕ) :
    node234 inputs = ((inputs 31 : ℤ) + (1 : ℤ)) :=
  cadd rfl rfl

private theorem e235_235 (inputs : Fin 69 → ℕ) :
    node235 inputs = ((2 : ℤ) * (inputs 11 : ℤ)) :=
  cmul rfl rfl

private theorem e236_236 (inputs : Fin 69 → ℕ) :
    node236 inputs = (((2 : ℤ) * (inputs 11 : ℤ)) * (inputs 4 : ℤ)) :=
  cmul (e235_235 inputs) rfl

private theorem e237_237 (inputs : Fin 69 → ℕ) :
    node237 inputs = (((inputs 31 : ℤ) + (1 : ℤ)) + (((2 : ℤ) * (inputs 11 : ℤ)) * (inputs 4 : ℤ))) :=
  cadd (e234_234 inputs) (e236_236 inputs)

private theorem e238_238 (inputs : Fin 69 → ℕ) :
    node238 inputs = (((inputs 31 : ℤ) + (1 : ℤ)) + (((2 : ℤ) * (inputs 11 : ℤ)) * (inputs 4 : ℤ))) ^ 2 :=
  pw 1 1 (pw1 (e237_237 inputs)) (pw1 (e237_237 inputs))

private theorem e239_239 (inputs : Fin 69 → ℕ) :
    node239 inputs = ((((inputs 2 : ℤ) + ((inputs 7 : ℤ) ^ 2 * ((inputs 7 : ℤ) ^ 2 - (inputs 2 : ℤ)))) ^ 2 - (1 : ℤ)) * (((inputs 31 : ℤ) + (1 : ℤ)) + (((2 : ℤ) * (inputs 11 : ℤ)) * (inputs 4 : ℤ))) ^ 2) :=
  cmul (e233_233 inputs) (e238_238 inputs)

private theorem e240_240 (inputs : Fin 69 → ℕ) :
    node240 inputs = (((((inputs 2 : ℤ) + ((inputs 7 : ℤ) ^ 2 * ((inputs 7 : ℤ) ^ 2 - (inputs 2 : ℤ)))) ^ 2 - (1 : ℤ)) * (((inputs 31 : ℤ) + (1 : ℤ)) + (((2 : ℤ) * (inputs 11 : ℤ)) * (inputs 4 : ℤ))) ^ 2) + (1 : ℤ)) :=
  cadd (e239_239 inputs) rfl

/-- The final comparisons of the evaluation are exactly the system (1.3). -/
theorem evaluation_final_iff_sys13 (inputs : Fin 69 → ℕ) :
    FinalEqualities inputs (evaluation inputs) ↔ Sys13 (inputs 0) (inputs 1) (inputs 2) (inputs 3) (inputs 4) (inputs 5) (inputs 6) (inputs 7) (inputs 8) (inputs 9) (inputs 10) (inputs 11) (inputs 12) (inputs 13) (inputs 14) (inputs 15) (inputs 16) (inputs 17) (inputs 18) (inputs 19) (inputs 20) (inputs 21) (inputs 22) (inputs 23) (inputs 24) (inputs 25) (inputs 26) (inputs 27) (inputs 28) (inputs 29) (inputs 30) (inputs 31) (inputs 32) (inputs 33) (inputs 34) (inputs 35) (inputs 36) (inputs 37) (inputs 38) (inputs 39) (inputs 40) (inputs 41) (inputs 42) (inputs 43) (inputs 44) (inputs 45) (inputs 46) (inputs 47) (inputs 48) (inputs 49) (inputs 50) (inputs 51) (inputs 52) (inputs 53) (inputs 54) (inputs 55) (inputs 56) (inputs 57) (inputs 58) (inputs 59) (inputs 60) (inputs 61) (inputs 62) (inputs 63) (inputs 64) (inputs 65) (inputs 66) (inputs 67) (inputs 68) := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩
    exact ⟨(e0_0 inputs).symm.trans (h0.trans (e5_5 inputs)),
      rfl.symm.trans (h1.trans (e7_7 inputs)),
      (e11_11 inputs).symm.trans (h2.trans (e16_16 inputs)),
      (e22_22 inputs).symm.trans (h3.trans rfl),
      rfl.symm.trans (h4.trans (e26_26 inputs)),
      (e38_38 inputs).symm.trans (h5.trans (e39_39 inputs)),
      (e44_44 inputs).symm.trans (h6.trans (e46_46 inputs)),
      (e51_51 inputs).symm.trans (h7.trans (e53_53 inputs)),
      (e104_104 inputs).symm.trans (h8.trans (e105_105 inputs)),
      rfl.symm.trans (h9.trans (e116_116 inputs)),
      (e124_124 inputs).symm.trans (h10.trans (e125_125 inputs)),
      rfl.symm.trans (h11.trans (e127_127 inputs)),
      rfl.symm.trans (h12.trans (e130_130 inputs)),
      rfl.symm.trans (h13.trans (e133_133 inputs)),
      rfl.symm.trans (h14.trans (e136_136 inputs)),
      rfl.symm.trans (h15.trans (e139_139 inputs)),
      rfl.symm.trans (h16.trans (e142_142 inputs)),
      (e150_150 inputs).symm.trans (h17.trans (e151_151 inputs)),
      rfl.symm.trans (h18.trans (e158_158 inputs)),
      rfl.symm.trans (h19.trans (e161_161 inputs)),
      rfl.symm.trans (h20.trans (e164_164 inputs)),
      rfl.symm.trans (h21.trans (e167_167 inputs)),
      rfl.symm.trans (h22.trans (e170_170 inputs)),
      rfl.symm.trans (h23.trans (e173_173 inputs)),
      rfl.symm.trans (h24.trans (e176_176 inputs)),
      (e181_181 inputs).symm.trans (h25.trans (e182_182 inputs)),
      (e188_188 inputs).symm.trans (h26.trans (e189_189 inputs)),
      (e195_195 inputs).symm.trans (h27.trans (e196_196 inputs)),
      rfl.symm.trans (h28.trans (e199_199 inputs)),
      rfl.symm.trans (h29.trans (e204_204 inputs)),
      rfl.symm.trans (h30.trans (e209_209 inputs)),
      rfl.symm.trans (h31.trans (e210_210 inputs)),
      rfl.symm.trans (h32.trans (e212_212 inputs)),
      (e213_213 inputs).symm.trans (h33.trans (e218_218 inputs)),
      (e219_219 inputs).symm.trans (h34.trans (e225_225 inputs)),
      (e228_228 inputs).symm.trans (h35.trans (e240_240 inputs))⟩
  · intro S
    exact ⟨(e0_0 inputs).trans (S.e01.trans (e5_5 inputs).symm),
      rfl.trans (S.e02.trans (e7_7 inputs).symm),
      (e11_11 inputs).trans (S.e03.trans (e16_16 inputs).symm),
      (e22_22 inputs).trans (S.e04.trans rfl.symm),
      rfl.trans (S.e05.trans (e26_26 inputs).symm),
      (e38_38 inputs).trans (S.e06.trans (e39_39 inputs).symm),
      (e44_44 inputs).trans (S.e07.trans (e46_46 inputs).symm),
      (e51_51 inputs).trans (S.e08.trans (e53_53 inputs).symm),
      (e104_104 inputs).trans (S.e09.trans (e105_105 inputs).symm),
      rfl.trans (S.e10.trans (e116_116 inputs).symm),
      (e124_124 inputs).trans (S.e11.trans (e125_125 inputs).symm),
      rfl.trans (S.e12.trans (e127_127 inputs).symm),
      rfl.trans (S.e13.trans (e130_130 inputs).symm),
      rfl.trans (S.e14.trans (e133_133 inputs).symm),
      rfl.trans (S.e15.trans (e136_136 inputs).symm),
      rfl.trans (S.e16.trans (e139_139 inputs).symm),
      rfl.trans (S.e17.trans (e142_142 inputs).symm),
      (e150_150 inputs).trans (S.e18.trans (e151_151 inputs).symm),
      rfl.trans (S.e19.trans (e158_158 inputs).symm),
      rfl.trans (S.e20.trans (e161_161 inputs).symm),
      rfl.trans (S.e21.trans (e164_164 inputs).symm),
      rfl.trans (S.e22.trans (e167_167 inputs).symm),
      rfl.trans (S.e23.trans (e170_170 inputs).symm),
      rfl.trans (S.e24.trans (e173_173 inputs).symm),
      rfl.trans (S.e25.trans (e176_176 inputs).symm),
      (e181_181 inputs).trans (S.e26.trans (e182_182 inputs).symm),
      (e188_188 inputs).trans (S.e27.trans (e189_189 inputs).symm),
      (e195_195 inputs).trans (S.e28.trans (e196_196 inputs).symm),
      rfl.trans (S.e29.trans (e199_199 inputs).symm),
      rfl.trans (S.e30.trans (e204_204 inputs).symm),
      rfl.trans (S.e31.trans (e209_209 inputs).symm),
      rfl.trans (S.e32.trans (e210_210 inputs).symm),
      rfl.trans (S.e33.trans (e212_212 inputs).symm),
      (e213_213 inputs).trans (S.e34.trans (e218_218 inputs).symm),
      (e219_219 inputs).trans (S.e35.trans (e225_225 inputs).symm),
      (e228_228 inputs).trans (S.e36.trans (e240_240 inputs).symm)⟩

/-- A certificate for `x ∈ Wₙ`: the inputs start with `n, x`, the trace is a valid run of the
schedule, and the 36 equality tests pass. -/
def Certificate (n x : ℕ) (inputs : Fin 69 → ℕ) (trace : Fin 241 → ℤ) : Prop :=
  inputs 0 = n ∧ inputs 1 = x ∧ Valid schedule inputs trace ∧ FinalEqualities inputs trace

/-- **Corollary 1 (certificate form).** For positive `n, x`, `x ∈ Wₙ` iff there is a
certificate checked by the fixed 241-instruction schedule. -/
theorem mem_W_iff_certificate {n x : ℕ} (hn : 0 < n) (hx : 0 < x) :
    x ∈ W n ↔ ∃ (inputs : Fin 69 → ℕ) (trace : Fin 241 → ℤ), Certificate n x inputs trace := by
  rw [theorem_3 hn hx]
  constructor
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, p, q, r, s, t, u, v, w, y, z, alpha, beta,
      gamma, delta, eps, zeta, eta, theta, iota, kappa, lam, mu, nu, xi, pi', rho, sigma, tau,
      ups, phi1, phi2, chi, psi, omega, a', b', c', d', e', f', g', h', i', j', k', l', m', n',
      p', q', r', s', t', u', S⟩
    let inputs : Fin 69 → ℕ := ![n, x, a, b, c, d, e, f, g, h, i, j, k, l, m, p, q, r, s, t, u,
      v, w, y, z, alpha, beta, gamma, delta, eps, zeta, eta, theta, iota, kappa, lam, mu, nu, xi,
      pi', rho, sigma, tau, ups, phi1, phi2, chi, psi, omega, a', b', c', d', e', f', g', h', i',
      j', k', l', m', n', p', q', r', s', t', u']
    exact ⟨inputs, evaluation inputs, rfl, rfl, evaluation_valid inputs,
      (evaluation_final_iff_sys13 inputs).mpr S⟩
  · rintro ⟨inputs, trace, rfl, rfl, hv, hf⟩
    rw [(valid_iff_eq_evaluation inputs trace).mp hv] at hf
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, (evaluation_final_iff_sys13 inputs).mp hf⟩

/-! ### The single equation -/

/-- The schedule extended by `∑ (Lᵢ − Rᵢ)²`, summed from the right. -/
def singleSchedule : Schedule 69 348
  | ⟨0, _⟩ => ⟨.mul, .constant (2), .input 0⟩
  | ⟨1, _⟩ => ⟨.add, .input 20, .input 21⟩
  | ⟨2, _⟩ => ⟨.mul, .previous ⟨1, by change 1 < 2; decide⟩, .previous ⟨1, by change 1 < 2; decide⟩⟩
  | ⟨3, _⟩ => ⟨.mul, .constant (3), .input 21⟩
  | ⟨4, _⟩ => ⟨.add, .previous ⟨2, by change 2 < 4; decide⟩, .previous ⟨3, by change 3 < 4; decide⟩⟩
  | ⟨5, _⟩ => ⟨.add, .previous ⟨4, by change 4 < 5; decide⟩, .input 20⟩
  | ⟨6, _⟩ => ⟨.mul, .input 32, .input 26⟩
  | ⟨7, _⟩ => ⟨.add, .previous ⟨6, by change 6 < 7; decide⟩, .input 32⟩
  | ⟨8, _⟩ => ⟨.mul, .input 9, .input 26⟩
  | ⟨9, _⟩ => ⟨.add, .input 9, .previous ⟨8, by change 8 < 9; decide⟩⟩
  | ⟨10, _⟩ => ⟨.mul, .previous ⟨8, by change 8 < 10; decide⟩, .input 21⟩
  | ⟨11, _⟩ => ⟨.add, .previous ⟨9, by change 9 < 11; decide⟩, .previous ⟨10, by change 10 < 11; decide⟩⟩
  | ⟨12, _⟩ => ⟨.add, .input 1, .input 40⟩
  | ⟨13, _⟩ => ⟨.mul, .input 40, .input 26⟩
  | ⟨14, _⟩ => ⟨.add, .previous ⟨12, by change 12 < 14; decide⟩, .previous ⟨13, by change 13 < 14; decide⟩⟩
  | ⟨15, _⟩ => ⟨.mul, .previous ⟨13, by change 13 < 15; decide⟩, .input 20⟩
  | ⟨16, _⟩ => ⟨.add, .previous ⟨14, by change 14 < 16; decide⟩, .previous ⟨15, by change 15 < 16; decide⟩⟩
  | ⟨17, _⟩ => ⟨.sub, .previous ⟨11, by change 11 < 17; decide⟩, .input 25⟩
  | ⟨18, _⟩ => ⟨.mul, .previous ⟨17, by change 17 < 18; decide⟩, .previous ⟨17, by change 17 < 18; decide⟩⟩
  | ⟨19, _⟩ => ⟨.mul, .input 1, .input 1⟩
  | ⟨20, _⟩ => ⟨.add, .previous ⟨18, by change 18 < 20; decide⟩, .previous ⟨19, by change 19 < 20; decide⟩⟩
  | ⟨21, _⟩ => ⟨.add, .previous ⟨20, by change 20 < 21; decide⟩, .input 27⟩
  | ⟨22, _⟩ => ⟨.add, .previous ⟨21, by change 21 < 22; decide⟩, .constant (1)⟩
  | ⟨23, _⟩ => ⟨.mul, .constant (3), .input 0⟩
  | ⟨24, _⟩ => ⟨.mul, .input 25, .input 25⟩
  | ⟨25, _⟩ => ⟨.mul, .input 25, .previous ⟨24, by change 24 < 25; decide⟩⟩
  | ⟨26, _⟩ => ⟨.add, .previous ⟨23, by change 23 < 26; decide⟩, .previous ⟨25, by change 25 < 26; decide⟩⟩
  | ⟨27, _⟩ => ⟨.mul, .input 24, .input 24⟩
  | ⟨28, _⟩ => ⟨.mul, .previous ⟨27, by change 27 < 28; decide⟩, .previous ⟨27, by change 27 < 28; decide⟩⟩
  | ⟨29, _⟩ => ⟨.mul, .input 24, .previous ⟨28, by change 28 < 29; decide⟩⟩
  | ⟨30, _⟩ => ⟨.mul, .previous ⟨28, by change 28 < 30; decide⟩, .previous ⟨29, by change 29 < 30; decide⟩⟩
  | ⟨31, _⟩ => ⟨.mul, .previous ⟨30, by change 30 < 31; decide⟩, .previous ⟨30, by change 30 < 31; decide⟩⟩
  | ⟨32, _⟩ => ⟨.mul, .input 24, .previous ⟨29, by change 29 < 32; decide⟩⟩
  | ⟨33, _⟩ => ⟨.add, .previous ⟨32, by change 32 < 33; decide⟩, .constant (2)⟩
  | ⟨34, _⟩ => ⟨.mul, .previous ⟨31, by change 31 < 34; decide⟩, .previous ⟨33, by change 33 < 34; decide⟩⟩
  | ⟨35, _⟩ => ⟨.add, .input 17, .constant (1)⟩
  | ⟨36, _⟩ => ⟨.mul, .previous ⟨35, by change 35 < 36; decide⟩, .previous ⟨35, by change 35 < 36; decide⟩⟩
  | ⟨37, _⟩ => ⟨.mul, .previous ⟨34, by change 34 < 37; decide⟩, .previous ⟨36, by change 36 < 37; decide⟩⟩
  | ⟨38, _⟩ => ⟨.add, .previous ⟨37, by change 37 < 38; decide⟩, .constant (1)⟩
  | ⟨39, _⟩ => ⟨.mul, .input 47, .input 47⟩
  | ⟨40, _⟩ => ⟨.add, .input 19, .input 6⟩
  | ⟨41, _⟩ => ⟨.mul, .input 6, .input 26⟩
  | ⟨42, _⟩ => ⟨.add, .previous ⟨40, by change 40 < 42; decide⟩, .previous ⟨41, by change 41 < 42; decide⟩⟩
  | ⟨43, _⟩ => ⟨.mul, .previous ⟨41, by change 41 < 43; decide⟩, .input 18⟩
  | ⟨44, _⟩ => ⟨.add, .previous ⟨42, by change 42 < 44; decide⟩, .previous ⟨43, by change 43 < 44; decide⟩⟩
  | ⟨45, _⟩ => ⟨.mul, .input 16, .input 44⟩
  | ⟨46, _⟩ => ⟨.add, .input 25, .previous ⟨45, by change 45 < 46; decide⟩⟩
  | ⟨47, _⟩ => ⟨.add, .input 15, .input 3⟩
  | ⟨48, _⟩ => ⟨.mul, .input 3, .input 26⟩
  | ⟨49, _⟩ => ⟨.add, .previous ⟨47, by change 47 < 49; decide⟩, .previous ⟨48, by change 48 < 49; decide⟩⟩
  | ⟨50, _⟩ => ⟨.mul, .previous ⟨48, by change 48 < 50; decide⟩, .input 22⟩
  | ⟨51, _⟩ => ⟨.add, .previous ⟨49, by change 49 < 51; decide⟩, .previous ⟨50, by change 50 < 51; decide⟩⟩
  | ⟨52, _⟩ => ⟨.mul, .input 16, .input 45⟩
  | ⟨53, _⟩ => ⟨.add, .input 25, .previous ⟨52, by change 52 < 53; decide⟩⟩
  | ⟨54, _⟩ => ⟨.add, .input 18, .input 22⟩
  | ⟨55, _⟩ => ⟨.mul, .previous ⟨54, by change 54 < 55; decide⟩, .previous ⟨54, by change 54 < 55; decide⟩⟩
  | ⟨56, _⟩ => ⟨.mul, .constant (3), .previous ⟨55, by change 55 < 56; decide⟩⟩
  | ⟨57, _⟩ => ⟨.mul, .constant (9), .input 22⟩
  | ⟨58, _⟩ => ⟨.add, .previous ⟨56, by change 56 < 58; decide⟩, .previous ⟨57, by change 57 < 58; decide⟩⟩
  | ⟨59, _⟩ => ⟨.mul, .constant (3), .input 18⟩
  | ⟨60, _⟩ => ⟨.add, .previous ⟨58, by change 58 < 60; decide⟩, .previous ⟨59, by change 59 < 60; decide⟩⟩
  | ⟨61, _⟩ => ⟨.mul, .constant (2), .input 17⟩
  | ⟨62, _⟩ => ⟨.sub, .previous ⟨60, by change 60 < 62; decide⟩, .previous ⟨61, by change 61 < 62; decide⟩⟩
  | ⟨63, _⟩ => ⟨.mul, .previous ⟨62, by change 62 < 63; decide⟩, .previous ⟨62, by change 62 < 63; decide⟩⟩
  | ⟨64, _⟩ => ⟨.add, .constant (1), .input 26⟩
  | ⟨65, _⟩ => ⟨.mul, .input 17, .input 26⟩
  | ⟨66, _⟩ => ⟨.add, .previous ⟨64, by change 64 < 66; decide⟩, .previous ⟨65, by change 65 < 66; decide⟩⟩
  | ⟨67, _⟩ => ⟨.mul, .previous ⟨66, by change 66 < 67; decide⟩, .previous ⟨66, by change 66 < 67; decide⟩⟩
  | ⟨68, _⟩ => ⟨.sub, .input 25, .input 19⟩
  | ⟨69, _⟩ => ⟨.sub, .previous ⟨68, by change 68 < 69; decide⟩, .input 15⟩
  | ⟨70, _⟩ => ⟨.mul, .previous ⟨69, by change 69 < 70; decide⟩, .previous ⟨69, by change 69 < 70; decide⟩⟩
  | ⟨71, _⟩ => ⟨.add, .constant (1), .previous ⟨70, by change 70 < 71; decide⟩⟩
  | ⟨72, _⟩ => ⟨.mul, .previous ⟨67, by change 67 < 72; decide⟩, .previous ⟨71, by change 71 < 72; decide⟩⟩
  | ⟨73, _⟩ => ⟨.mul, .input 19, .input 19⟩
  | ⟨74, _⟩ => ⟨.sub, .input 26, .previous ⟨73, by change 73 < 74; decide⟩⟩
  | ⟨75, _⟩ => ⟨.mul, .input 15, .input 15⟩
  | ⟨76, _⟩ => ⟨.sub, .previous ⟨74, by change 74 < 76; decide⟩, .previous ⟨75, by change 75 < 76; decide⟩⟩
  | ⟨77, _⟩ => ⟨.mul, .previous ⟨72, by change 72 < 77; decide⟩, .previous ⟨76, by change 76 < 77; decide⟩⟩
  | ⟨78, _⟩ => ⟨.sub, .previous ⟨77, by change 77 < 78; decide⟩, .previous ⟨70, by change 70 < 78; decide⟩⟩
  | ⟨79, _⟩ => ⟨.add, .input 8, .constant (1)⟩
  | ⟨80, _⟩ => ⟨.mul, .previous ⟨79, by change 79 < 80; decide⟩, .previous ⟨67, by change 67 < 80; decide⟩⟩
  | ⟨81, _⟩ => ⟨.sub, .previous ⟨78, by change 78 < 81; decide⟩, .previous ⟨80, by change 80 < 81; decide⟩⟩
  | ⟨82, _⟩ => ⟨.mul, .previous ⟨81, by change 81 < 82; decide⟩, .previous ⟨81, by change 81 < 82; decide⟩⟩
  | ⟨83, _⟩ => ⟨.add, .previous ⟨63, by change 63 < 83; decide⟩, .previous ⟨82, by change 82 < 83; decide⟩⟩
  | ⟨84, _⟩ => ⟨.add, .previous ⟨60, by change 60 < 84; decide⟩, .constant (2)⟩
  | ⟨85, _⟩ => ⟨.sub, .previous ⟨84, by change 84 < 85; decide⟩, .previous ⟨61, by change 61 < 85; decide⟩⟩
  | ⟨86, _⟩ => ⟨.mul, .previous ⟨85, by change 85 < 86; decide⟩, .previous ⟨85, by change 85 < 86; decide⟩⟩
  | ⟨87, _⟩ => ⟨.mul, .input 19, .input 15⟩
  | ⟨88, _⟩ => ⟨.sub, .input 25, .previous ⟨87, by change 87 < 88; decide⟩⟩
  | ⟨89, _⟩ => ⟨.mul, .previous ⟨88, by change 88 < 89; decide⟩, .previous ⟨88, by change 88 < 89; decide⟩⟩
  | ⟨90, _⟩ => ⟨.add, .constant (1), .previous ⟨89, by change 89 < 90; decide⟩⟩
  | ⟨91, _⟩ => ⟨.mul, .previous ⟨67, by change 67 < 91; decide⟩, .previous ⟨90, by change 90 < 91; decide⟩⟩
  | ⟨92, _⟩ => ⟨.mul, .previous ⟨91, by change 91 < 92; decide⟩, .previous ⟨76, by change 76 < 92; decide⟩⟩
  | ⟨93, _⟩ => ⟨.sub, .previous ⟨92, by change 92 < 93; decide⟩, .previous ⟨89, by change 89 < 93; decide⟩⟩
  | ⟨94, _⟩ => ⟨.sub, .previous ⟨93, by change 93 < 94; decide⟩, .previous ⟨80, by change 80 < 94; decide⟩⟩
  | ⟨95, _⟩ => ⟨.mul, .previous ⟨94, by change 94 < 95; decide⟩, .previous ⟨94, by change 94 < 95; decide⟩⟩
  | ⟨96, _⟩ => ⟨.add, .previous ⟨86, by change 86 < 96; decide⟩, .previous ⟨95, by change 95 < 96; decide⟩⟩
  | ⟨97, _⟩ => ⟨.mul, .previous ⟨83, by change 83 < 97; decide⟩, .previous ⟨96, by change 96 < 97; decide⟩⟩
  | ⟨98, _⟩ => ⟨.mul, .constant (3), .input 8⟩
  | ⟨99, _⟩ => ⟨.add, .previous ⟨98, by change 98 < 99; decide⟩, .constant (2)⟩
  | ⟨100, _⟩ => ⟨.sub, .previous ⟨99, by change 99 < 100; decide⟩, .input 17⟩
  | ⟨101, _⟩ => ⟨.mul, .previous ⟨97, by change 97 < 101; decide⟩, .previous ⟨100, by change 100 < 101; decide⟩⟩
  | ⟨102, _⟩ => ⟨.add, .previous ⟨23, by change 23 < 102; decide⟩, .input 8⟩
  | ⟨103, _⟩ => ⟨.sub, .previous ⟨102, by change 102 < 103; decide⟩, .input 17⟩
  | ⟨104, _⟩ => ⟨.mul, .previous ⟨101, by change 101 < 104; decide⟩, .previous ⟨103, by change 103 < 104; decide⟩⟩
  | ⟨105, _⟩ => ⟨.mul, .input 16, .input 39⟩
  | ⟨106, _⟩ => ⟨.add, .input 17, .input 16⟩
  | ⟨107, _⟩ => ⟨.add, .previous ⟨106, by change 106 < 107; decide⟩, .input 3⟩
  | ⟨108, _⟩ => ⟨.add, .previous ⟨107, by change 107 < 108; decide⟩, .input 6⟩
  | ⟨109, _⟩ => ⟨.add, .previous ⟨108, by change 108 < 109; decide⟩, .input 8⟩
  | ⟨110, _⟩ => ⟨.add, .previous ⟨109, by change 109 < 110; decide⟩, .input 18⟩
  | ⟨111, _⟩ => ⟨.add, .previous ⟨110, by change 110 < 111; decide⟩, .input 22⟩
  | ⟨112, _⟩ => ⟨.add, .previous ⟨111, by change 111 < 112; decide⟩, .input 54⟩
  | ⟨113, _⟩ => ⟨.add, .previous ⟨112, by change 112 < 113; decide⟩, .input 55⟩
  | ⟨114, _⟩ => ⟨.add, .previous ⟨113, by change 113 < 114; decide⟩, .input 56⟩
  | ⟨115, _⟩ => ⟨.add, .previous ⟨114, by change 114 < 115; decide⟩, .input 57⟩
  | ⟨116, _⟩ => ⟨.add, .previous ⟨115, by change 115 < 116; decide⟩, .input 58⟩
  | ⟨117, _⟩ => ⟨.mul, .input 48, .input 48⟩
  | ⟨118, _⟩ => ⟨.mul, .input 48, .previous ⟨117, by change 117 < 118; decide⟩⟩
  | ⟨119, _⟩ => ⟨.add, .input 48, .constant (2)⟩
  | ⟨120, _⟩ => ⟨.mul, .previous ⟨118, by change 118 < 120; decide⟩, .previous ⟨119, by change 119 < 120; decide⟩⟩
  | ⟨121, _⟩ => ⟨.add, .input 41, .constant (1)⟩
  | ⟨122, _⟩ => ⟨.mul, .previous ⟨121, by change 121 < 122; decide⟩, .previous ⟨121, by change 121 < 122; decide⟩⟩
  | ⟨123, _⟩ => ⟨.mul, .previous ⟨120, by change 120 < 123; decide⟩, .previous ⟨122, by change 122 < 123; decide⟩⟩
  | ⟨124, _⟩ => ⟨.add, .previous ⟨123, by change 123 < 124; decide⟩, .constant (1)⟩
  | ⟨125, _⟩ => ⟨.mul, .input 28, .input 28⟩
  | ⟨126, _⟩ => ⟨.mul, .input 41, .input 17⟩
  | ⟨127, _⟩ => ⟨.add, .previous ⟨126, by change 126 < 127; decide⟩, .input 41⟩
  | ⟨128, _⟩ => ⟨.add, .input 64, .input 41⟩
  | ⟨129, _⟩ => ⟨.mul, .previous ⟨128, by change 128 < 129; decide⟩, .input 49⟩
  | ⟨130, _⟩ => ⟨.add, .input 3, .previous ⟨129, by change 129 < 130; decide⟩⟩
  | ⟨131, _⟩ => ⟨.add, .input 65, .input 41⟩
  | ⟨132, _⟩ => ⟨.mul, .previous ⟨131, by change 131 < 132; decide⟩, .input 50⟩
  | ⟨133, _⟩ => ⟨.add, .input 6, .previous ⟨132, by change 132 < 133; decide⟩⟩
  | ⟨134, _⟩ => ⟨.add, .input 66, .input 41⟩
  | ⟨135, _⟩ => ⟨.mul, .previous ⟨134, by change 134 < 135; decide⟩, .input 51⟩
  | ⟨136, _⟩ => ⟨.add, .input 8, .previous ⟨135, by change 135 < 136; decide⟩⟩
  | ⟨137, _⟩ => ⟨.add, .input 67, .input 41⟩
  | ⟨138, _⟩ => ⟨.mul, .previous ⟨137, by change 137 < 138; decide⟩, .input 52⟩
  | ⟨139, _⟩ => ⟨.add, .input 18, .previous ⟨138, by change 138 < 139; decide⟩⟩
  | ⟨140, _⟩ => ⟨.add, .input 68, .input 41⟩
  | ⟨141, _⟩ => ⟨.mul, .previous ⟨140, by change 140 < 141; decide⟩, .input 53⟩
  | ⟨142, _⟩ => ⟨.add, .input 22, .previous ⟨141, by change 141 < 142; decide⟩⟩
  | ⟨143, _⟩ => ⟨.mul, .input 31, .input 31⟩
  | ⟨144, _⟩ => ⟨.mul, .input 31, .previous ⟨143, by change 143 < 144; decide⟩⟩
  | ⟨145, _⟩ => ⟨.add, .input 31, .constant (2)⟩
  | ⟨146, _⟩ => ⟨.mul, .previous ⟨144, by change 144 < 146; decide⟩, .previous ⟨145, by change 145 < 146; decide⟩⟩
  | ⟨147, _⟩ => ⟨.add, .input 30, .constant (1)⟩
  | ⟨148, _⟩ => ⟨.mul, .previous ⟨147, by change 147 < 148; decide⟩, .previous ⟨147, by change 147 < 148; decide⟩⟩
  | ⟨149, _⟩ => ⟨.mul, .previous ⟨146, by change 146 < 149; decide⟩, .previous ⟨148, by change 148 < 149; decide⟩⟩
  | ⟨150, _⟩ => ⟨.add, .previous ⟨149, by change 149 < 150; decide⟩, .constant (1)⟩
  | ⟨151, _⟩ => ⟨.mul, .input 29, .input 29⟩
  | ⟨152, _⟩ => ⟨.sub, .input 31, .input 17⟩
  | ⟨153, _⟩ => ⟨.mul, .input 30, .previous ⟨152, by change 152 < 153; decide⟩⟩
  | ⟨154, _⟩ => ⟨.mul, .previous ⟨153, by change 153 < 154; decide⟩, .previous ⟨128, by change 128 < 154; decide⟩⟩
  | ⟨155, _⟩ => ⟨.mul, .previous ⟨154, by change 154 < 155; decide⟩, .previous ⟨131, by change 131 < 155; decide⟩⟩
  | ⟨156, _⟩ => ⟨.mul, .previous ⟨155, by change 155 < 156; decide⟩, .previous ⟨134, by change 134 < 156; decide⟩⟩
  | ⟨157, _⟩ => ⟨.mul, .previous ⟨156, by change 156 < 157; decide⟩, .previous ⟨137, by change 137 < 157; decide⟩⟩
  | ⟨158, _⟩ => ⟨.mul, .previous ⟨157, by change 157 < 158; decide⟩, .previous ⟨140, by change 140 < 158; decide⟩⟩
  | ⟨159, _⟩ => ⟨.add, .constant (1), .input 38⟩
  | ⟨160, _⟩ => ⟨.mul, .previous ⟨159, by change 159 < 160; decide⟩, .previous ⟨152, by change 152 < 160; decide⟩⟩
  | ⟨161, _⟩ => ⟨.add, .input 16, .previous ⟨160, by change 160 < 161; decide⟩⟩
  | ⟨162, _⟩ => ⟨.mul, .input 16, .input 54⟩
  | ⟨163, _⟩ => ⟨.mul, .previous ⟨128, by change 128 < 163; decide⟩, .input 59⟩
  | ⟨164, _⟩ => ⟨.add, .previous ⟨162, by change 162 < 164; decide⟩, .previous ⟨163, by change 163 < 164; decide⟩⟩
  | ⟨165, _⟩ => ⟨.mul, .input 16, .input 55⟩
  | ⟨166, _⟩ => ⟨.mul, .previous ⟨131, by change 131 < 166; decide⟩, .input 60⟩
  | ⟨167, _⟩ => ⟨.add, .previous ⟨165, by change 165 < 167; decide⟩, .previous ⟨166, by change 166 < 167; decide⟩⟩
  | ⟨168, _⟩ => ⟨.mul, .input 16, .input 56⟩
  | ⟨169, _⟩ => ⟨.mul, .previous ⟨134, by change 134 < 169; decide⟩, .input 61⟩
  | ⟨170, _⟩ => ⟨.add, .previous ⟨168, by change 168 < 170; decide⟩, .previous ⟨169, by change 169 < 170; decide⟩⟩
  | ⟨171, _⟩ => ⟨.mul, .input 16, .input 57⟩
  | ⟨172, _⟩ => ⟨.mul, .previous ⟨137, by change 137 < 172; decide⟩, .input 62⟩
  | ⟨173, _⟩ => ⟨.add, .previous ⟨171, by change 171 < 173; decide⟩, .previous ⟨172, by change 172 < 173; decide⟩⟩
  | ⟨174, _⟩ => ⟨.mul, .input 16, .input 58⟩
  | ⟨175, _⟩ => ⟨.mul, .previous ⟨140, by change 140 < 175; decide⟩, .input 63⟩
  | ⟨176, _⟩ => ⟨.add, .previous ⟨174, by change 174 < 176; decide⟩, .previous ⟨175, by change 175 < 176; decide⟩⟩
  | ⟨177, _⟩ => ⟨.mul, .input 36, .input 36⟩
  | ⟨178, _⟩ => ⟨.sub, .previous ⟨177, by change 177 < 178; decide⟩, .constant (1)⟩
  | ⟨179, _⟩ => ⟨.mul, .input 34, .input 34⟩
  | ⟨180, _⟩ => ⟨.mul, .previous ⟨178, by change 178 < 180; decide⟩, .previous ⟨179, by change 179 < 180; decide⟩⟩
  | ⟨181, _⟩ => ⟨.add, .previous ⟨180, by change 180 < 181; decide⟩, .constant (1)⟩
  | ⟨182, _⟩ => ⟨.mul, .input 37, .input 37⟩
  | ⟨183, _⟩ => ⟨.mul, .input 46, .input 46⟩
  | ⟨184, _⟩ => ⟨.mul, .previous ⟨177, by change 177 < 184; decide⟩, .previous ⟨183, by change 183 < 184; decide⟩⟩
  | ⟨185, _⟩ => ⟨.sub, .previous ⟨184, by change 184 < 185; decide⟩, .constant (1)⟩
  | ⟨186, _⟩ => ⟨.mul, .input 35, .input 35⟩
  | ⟨187, _⟩ => ⟨.mul, .previous ⟨185, by change 185 < 187; decide⟩, .previous ⟨186, by change 186 < 187; decide⟩⟩
  | ⟨188, _⟩ => ⟨.add, .previous ⟨187, by change 187 < 188; decide⟩, .constant (1)⟩
  | ⟨189, _⟩ => ⟨.mul, .input 43, .input 43⟩
  | ⟨190, _⟩ => ⟨.mul, .input 34, .input 35⟩
  | ⟨191, _⟩ => ⟨.mul, .previous ⟨190, by change 190 < 191; decide⟩, .input 23⟩
  | ⟨192, _⟩ => ⟨.sub, .input 4, .previous ⟨191, by change 191 < 192; decide⟩⟩
  | ⟨193, _⟩ => ⟨.mul, .previous ⟨192, by change 192 < 193; decide⟩, .previous ⟨192, by change 192 < 193; decide⟩⟩
  | ⟨194, _⟩ => ⟨.mul, .constant (5), .previous ⟨193, by change 193 < 194; decide⟩⟩
  | ⟨195, _⟩ => ⟨.add, .previous ⟨194, by change 194 < 195; decide⟩, .input 33⟩
  | ⟨196, _⟩ => ⟨.mul, .previous ⟨179, by change 179 < 196; decide⟩, .previous ⟨186, by change 186 < 196; decide⟩⟩
  | ⟨197, _⟩ => ⟨.mul, .constant (9), .input 31⟩
  | ⟨198, _⟩ => ⟨.mul, .previous ⟨197, by change 197 < 198; decide⟩, .input 46⟩
  | ⟨199, _⟩ => ⟨.mul, .previous ⟨198, by change 198 < 199; decide⟩, .input 23⟩
  | ⟨200, _⟩ => ⟨.sub, .input 31, .input 24⟩
  | ⟨201, _⟩ => ⟨.add, .previous ⟨200, by change 200 < 201; decide⟩, .constant (1)⟩
  | ⟨202, _⟩ => ⟨.sub, .input 36, .constant (1)⟩
  | ⟨203, _⟩ => ⟨.mul, .input 12, .previous ⟨202, by change 202 < 203; decide⟩⟩
  | ⟨204, _⟩ => ⟨.add, .previous ⟨201, by change 201 < 204; decide⟩, .previous ⟨203, by change 203 < 204; decide⟩⟩
  | ⟨205, _⟩ => ⟨.add, .input 24, .constant (1)⟩
  | ⟨206, _⟩ => ⟨.mul, .input 36, .input 46⟩
  | ⟨207, _⟩ => ⟨.sub, .previous ⟨206, by change 206 < 207; decide⟩, .constant (1)⟩
  | ⟨208, _⟩ => ⟨.mul, .input 13, .previous ⟨207, by change 207 < 208; decide⟩⟩
  | ⟨209, _⟩ => ⟨.add, .previous ⟨205, by change 205 < 209; decide⟩, .previous ⟨208, by change 208 < 209; decide⟩⟩
  | ⟨210, _⟩ => ⟨.add, .previous ⟨206, by change 206 < 210; decide⟩, .input 36⟩
  | ⟨211, _⟩ => ⟨.add, .input 14, .input 31⟩
  | ⟨212, _⟩ => ⟨.add, .previous ⟨211, by change 211 < 212; decide⟩, .constant (1)⟩
  | ⟨213, _⟩ => ⟨.mul, .input 5, .input 5⟩
  | ⟨214, _⟩ => ⟨.mul, .input 2, .input 2⟩
  | ⟨215, _⟩ => ⟨.sub, .previous ⟨214, by change 214 < 215; decide⟩, .constant (1)⟩
  | ⟨216, _⟩ => ⟨.mul, .input 4, .input 4⟩
  | ⟨217, _⟩ => ⟨.mul, .previous ⟨215, by change 215 < 217; decide⟩, .previous ⟨216, by change 216 < 217; decide⟩⟩
  | ⟨218, _⟩ => ⟨.add, .previous ⟨217, by change 217 < 218; decide⟩, .constant (1)⟩
  | ⟨219, _⟩ => ⟨.mul, .input 7, .input 7⟩
  | ⟨220, _⟩ => ⟨.mul, .constant (4), .previous ⟨215, by change 215 < 220; decide⟩⟩
  | ⟨221, _⟩ => ⟨.mul, .input 10, .input 10⟩
  | ⟨222, _⟩ => ⟨.mul, .previous ⟨220, by change 220 < 222; decide⟩, .previous ⟨221, by change 221 < 222; decide⟩⟩
  | ⟨223, _⟩ => ⟨.mul, .previous ⟨216, by change 216 < 223; decide⟩, .previous ⟨216, by change 216 < 223; decide⟩⟩
  | ⟨224, _⟩ => ⟨.mul, .previous ⟨222, by change 222 < 224; decide⟩, .previous ⟨223, by change 223 < 224; decide⟩⟩
  | ⟨225, _⟩ => ⟨.add, .previous ⟨224, by change 224 < 225; decide⟩, .constant (1)⟩
  | ⟨226, _⟩ => ⟨.mul, .input 42, .input 7⟩
  | ⟨227, _⟩ => ⟨.add, .input 5, .previous ⟨226, by change 226 < 227; decide⟩⟩
  | ⟨228, _⟩ => ⟨.mul, .previous ⟨227, by change 227 < 228; decide⟩, .previous ⟨227, by change 227 < 228; decide⟩⟩
  | ⟨229, _⟩ => ⟨.sub, .previous ⟨219, by change 219 < 229; decide⟩, .input 2⟩
  | ⟨230, _⟩ => ⟨.mul, .previous ⟨219, by change 219 < 230; decide⟩, .previous ⟨229, by change 229 < 230; decide⟩⟩
  | ⟨231, _⟩ => ⟨.add, .input 2, .previous ⟨230, by change 230 < 231; decide⟩⟩
  | ⟨232, _⟩ => ⟨.mul, .previous ⟨231, by change 231 < 232; decide⟩, .previous ⟨231, by change 231 < 232; decide⟩⟩
  | ⟨233, _⟩ => ⟨.sub, .previous ⟨232, by change 232 < 233; decide⟩, .constant (1)⟩
  | ⟨234, _⟩ => ⟨.add, .input 31, .constant (1)⟩
  | ⟨235, _⟩ => ⟨.mul, .constant (2), .input 11⟩
  | ⟨236, _⟩ => ⟨.mul, .previous ⟨235, by change 235 < 236; decide⟩, .input 4⟩
  | ⟨237, _⟩ => ⟨.add, .previous ⟨234, by change 234 < 237; decide⟩, .previous ⟨236, by change 236 < 237; decide⟩⟩
  | ⟨238, _⟩ => ⟨.mul, .previous ⟨237, by change 237 < 238; decide⟩, .previous ⟨237, by change 237 < 238; decide⟩⟩
  | ⟨239, _⟩ => ⟨.mul, .previous ⟨233, by change 233 < 239; decide⟩, .previous ⟨238, by change 238 < 239; decide⟩⟩
  | ⟨240, _⟩ => ⟨.add, .previous ⟨239, by change 239 < 240; decide⟩, .constant (1)⟩
  | ⟨241, _⟩ => ⟨.sub, .previous ⟨0, by change 0 < 241; decide⟩, .previous ⟨5, by change 5 < 241; decide⟩⟩
  | ⟨242, _⟩ => ⟨.mul, .previous ⟨241, by change 241 < 242; decide⟩, .previous ⟨241, by change 241 < 242; decide⟩⟩
  | ⟨243, _⟩ => ⟨.sub, .input 25, .previous ⟨7, by change 7 < 243; decide⟩⟩
  | ⟨244, _⟩ => ⟨.mul, .previous ⟨243, by change 243 < 244; decide⟩, .previous ⟨243, by change 243 < 244; decide⟩⟩
  | ⟨245, _⟩ => ⟨.sub, .previous ⟨11, by change 11 < 245; decide⟩, .previous ⟨16, by change 16 < 245; decide⟩⟩
  | ⟨246, _⟩ => ⟨.mul, .previous ⟨245, by change 245 < 246; decide⟩, .previous ⟨245, by change 245 < 246; decide⟩⟩
  | ⟨247, _⟩ => ⟨.sub, .previous ⟨22, by change 22 < 247; decide⟩, .input 26⟩
  | ⟨248, _⟩ => ⟨.mul, .previous ⟨247, by change 247 < 248; decide⟩, .previous ⟨247, by change 247 < 248; decide⟩⟩
  | ⟨249, _⟩ => ⟨.sub, .input 24, .previous ⟨26, by change 26 < 249; decide⟩⟩
  | ⟨250, _⟩ => ⟨.mul, .previous ⟨249, by change 249 < 250; decide⟩, .previous ⟨249, by change 249 < 250; decide⟩⟩
  | ⟨251, _⟩ => ⟨.sub, .previous ⟨38, by change 38 < 251; decide⟩, .previous ⟨39, by change 39 < 251; decide⟩⟩
  | ⟨252, _⟩ => ⟨.mul, .previous ⟨251, by change 251 < 252; decide⟩, .previous ⟨251, by change 251 < 252; decide⟩⟩
  | ⟨253, _⟩ => ⟨.sub, .previous ⟨44, by change 44 < 253; decide⟩, .previous ⟨46, by change 46 < 253; decide⟩⟩
  | ⟨254, _⟩ => ⟨.mul, .previous ⟨253, by change 253 < 254; decide⟩, .previous ⟨253, by change 253 < 254; decide⟩⟩
  | ⟨255, _⟩ => ⟨.sub, .previous ⟨51, by change 51 < 255; decide⟩, .previous ⟨53, by change 53 < 255; decide⟩⟩
  | ⟨256, _⟩ => ⟨.mul, .previous ⟨255, by change 255 < 256; decide⟩, .previous ⟨255, by change 255 < 256; decide⟩⟩
  | ⟨257, _⟩ => ⟨.sub, .previous ⟨104, by change 104 < 257; decide⟩, .previous ⟨105, by change 105 < 257; decide⟩⟩
  | ⟨258, _⟩ => ⟨.mul, .previous ⟨257, by change 257 < 258; decide⟩, .previous ⟨257, by change 257 < 258; decide⟩⟩
  | ⟨259, _⟩ => ⟨.sub, .input 48, .previous ⟨116, by change 116 < 259; decide⟩⟩
  | ⟨260, _⟩ => ⟨.mul, .previous ⟨259, by change 259 < 260; decide⟩, .previous ⟨259, by change 259 < 260; decide⟩⟩
  | ⟨261, _⟩ => ⟨.sub, .previous ⟨124, by change 124 < 261; decide⟩, .previous ⟨125, by change 125 < 261; decide⟩⟩
  | ⟨262, _⟩ => ⟨.mul, .previous ⟨261, by change 261 < 262; decide⟩, .previous ⟨261, by change 261 < 262; decide⟩⟩
  | ⟨263, _⟩ => ⟨.sub, .input 31, .previous ⟨127, by change 127 < 263; decide⟩⟩
  | ⟨264, _⟩ => ⟨.mul, .previous ⟨263, by change 263 < 264; decide⟩, .previous ⟨263, by change 263 < 264; decide⟩⟩
  | ⟨265, _⟩ => ⟨.sub, .input 31, .previous ⟨130, by change 130 < 265; decide⟩⟩
  | ⟨266, _⟩ => ⟨.mul, .previous ⟨265, by change 265 < 266; decide⟩, .previous ⟨265, by change 265 < 266; decide⟩⟩
  | ⟨267, _⟩ => ⟨.sub, .input 31, .previous ⟨133, by change 133 < 267; decide⟩⟩
  | ⟨268, _⟩ => ⟨.mul, .previous ⟨267, by change 267 < 268; decide⟩, .previous ⟨267, by change 267 < 268; decide⟩⟩
  | ⟨269, _⟩ => ⟨.sub, .input 31, .previous ⟨136, by change 136 < 269; decide⟩⟩
  | ⟨270, _⟩ => ⟨.mul, .previous ⟨269, by change 269 < 270; decide⟩, .previous ⟨269, by change 269 < 270; decide⟩⟩
  | ⟨271, _⟩ => ⟨.sub, .input 31, .previous ⟨139, by change 139 < 271; decide⟩⟩
  | ⟨272, _⟩ => ⟨.mul, .previous ⟨271, by change 271 < 272; decide⟩, .previous ⟨271, by change 271 < 272; decide⟩⟩
  | ⟨273, _⟩ => ⟨.sub, .input 31, .previous ⟨142, by change 142 < 273; decide⟩⟩
  | ⟨274, _⟩ => ⟨.mul, .previous ⟨273, by change 273 < 274; decide⟩, .previous ⟨273, by change 273 < 274; decide⟩⟩
  | ⟨275, _⟩ => ⟨.sub, .previous ⟨150, by change 150 < 275; decide⟩, .previous ⟨151, by change 151 < 275; decide⟩⟩
  | ⟨276, _⟩ => ⟨.mul, .previous ⟨275, by change 275 < 276; decide⟩, .previous ⟨275, by change 275 < 276; decide⟩⟩
  | ⟨277, _⟩ => ⟨.sub, .input 46, .previous ⟨158, by change 158 < 277; decide⟩⟩
  | ⟨278, _⟩ => ⟨.mul, .previous ⟨277, by change 277 < 278; decide⟩, .previous ⟨277, by change 277 < 278; decide⟩⟩
  | ⟨279, _⟩ => ⟨.sub, .input 23, .previous ⟨161, by change 161 < 279; decide⟩⟩
  | ⟨280, _⟩ => ⟨.mul, .previous ⟨279, by change 279 < 280; decide⟩, .previous ⟨279, by change 279 < 280; decide⟩⟩
  | ⟨281, _⟩ => ⟨.sub, .input 23, .previous ⟨164, by change 164 < 281; decide⟩⟩
  | ⟨282, _⟩ => ⟨.mul, .previous ⟨281, by change 281 < 282; decide⟩, .previous ⟨281, by change 281 < 282; decide⟩⟩
  | ⟨283, _⟩ => ⟨.sub, .input 23, .previous ⟨167, by change 167 < 283; decide⟩⟩
  | ⟨284, _⟩ => ⟨.mul, .previous ⟨283, by change 283 < 284; decide⟩, .previous ⟨283, by change 283 < 284; decide⟩⟩
  | ⟨285, _⟩ => ⟨.sub, .input 23, .previous ⟨170, by change 170 < 285; decide⟩⟩
  | ⟨286, _⟩ => ⟨.mul, .previous ⟨285, by change 285 < 286; decide⟩, .previous ⟨285, by change 285 < 286; decide⟩⟩
  | ⟨287, _⟩ => ⟨.sub, .input 23, .previous ⟨173, by change 173 < 287; decide⟩⟩
  | ⟨288, _⟩ => ⟨.mul, .previous ⟨287, by change 287 < 288; decide⟩, .previous ⟨287, by change 287 < 288; decide⟩⟩
  | ⟨289, _⟩ => ⟨.sub, .input 23, .previous ⟨176, by change 176 < 289; decide⟩⟩
  | ⟨290, _⟩ => ⟨.mul, .previous ⟨289, by change 289 < 290; decide⟩, .previous ⟨289, by change 289 < 290; decide⟩⟩
  | ⟨291, _⟩ => ⟨.sub, .previous ⟨181, by change 181 < 291; decide⟩, .previous ⟨182, by change 182 < 291; decide⟩⟩
  | ⟨292, _⟩ => ⟨.mul, .previous ⟨291, by change 291 < 292; decide⟩, .previous ⟨291, by change 291 < 292; decide⟩⟩
  | ⟨293, _⟩ => ⟨.sub, .previous ⟨188, by change 188 < 293; decide⟩, .previous ⟨189, by change 189 < 293; decide⟩⟩
  | ⟨294, _⟩ => ⟨.mul, .previous ⟨293, by change 293 < 294; decide⟩, .previous ⟨293, by change 293 < 294; decide⟩⟩
  | ⟨295, _⟩ => ⟨.sub, .previous ⟨195, by change 195 < 295; decide⟩, .previous ⟨196, by change 196 < 295; decide⟩⟩
  | ⟨296, _⟩ => ⟨.mul, .previous ⟨295, by change 295 < 296; decide⟩, .previous ⟨295, by change 295 < 296; decide⟩⟩
  | ⟨297, _⟩ => ⟨.sub, .input 36, .previous ⟨199, by change 199 < 297; decide⟩⟩
  | ⟨298, _⟩ => ⟨.mul, .previous ⟨297, by change 297 < 298; decide⟩, .previous ⟨297, by change 297 < 298; decide⟩⟩
  | ⟨299, _⟩ => ⟨.sub, .input 34, .previous ⟨204, by change 204 < 299; decide⟩⟩
  | ⟨300, _⟩ => ⟨.mul, .previous ⟨299, by change 299 < 300; decide⟩, .previous ⟨299, by change 299 < 300; decide⟩⟩
  | ⟨301, _⟩ => ⟨.sub, .input 35, .previous ⟨209, by change 209 < 301; decide⟩⟩
  | ⟨302, _⟩ => ⟨.mul, .previous ⟨301, by change 301 < 302; decide⟩, .previous ⟨301, by change 301 < 302; decide⟩⟩
  | ⟨303, _⟩ => ⟨.sub, .input 2, .previous ⟨210, by change 210 < 303; decide⟩⟩
  | ⟨304, _⟩ => ⟨.mul, .previous ⟨303, by change 303 < 304; decide⟩, .previous ⟨303, by change 303 < 304; decide⟩⟩
  | ⟨305, _⟩ => ⟨.sub, .input 4, .previous ⟨212, by change 212 < 305; decide⟩⟩
  | ⟨306, _⟩ => ⟨.mul, .previous ⟨305, by change 305 < 306; decide⟩, .previous ⟨305, by change 305 < 306; decide⟩⟩
  | ⟨307, _⟩ => ⟨.sub, .previous ⟨213, by change 213 < 307; decide⟩, .previous ⟨218, by change 218 < 307; decide⟩⟩
  | ⟨308, _⟩ => ⟨.mul, .previous ⟨307, by change 307 < 308; decide⟩, .previous ⟨307, by change 307 < 308; decide⟩⟩
  | ⟨309, _⟩ => ⟨.sub, .previous ⟨219, by change 219 < 309; decide⟩, .previous ⟨225, by change 225 < 309; decide⟩⟩
  | ⟨310, _⟩ => ⟨.mul, .previous ⟨309, by change 309 < 310; decide⟩, .previous ⟨309, by change 309 < 310; decide⟩⟩
  | ⟨311, _⟩ => ⟨.sub, .previous ⟨228, by change 228 < 311; decide⟩, .previous ⟨240, by change 240 < 311; decide⟩⟩
  | ⟨312, _⟩ => ⟨.mul, .previous ⟨311, by change 311 < 312; decide⟩, .previous ⟨311, by change 311 < 312; decide⟩⟩
  | ⟨313, _⟩ => ⟨.add, .previous ⟨310, by change 310 < 313; decide⟩, .previous ⟨312, by change 312 < 313; decide⟩⟩
  | ⟨314, _⟩ => ⟨.add, .previous ⟨308, by change 308 < 314; decide⟩, .previous ⟨313, by change 313 < 314; decide⟩⟩
  | ⟨315, _⟩ => ⟨.add, .previous ⟨306, by change 306 < 315; decide⟩, .previous ⟨314, by change 314 < 315; decide⟩⟩
  | ⟨316, _⟩ => ⟨.add, .previous ⟨304, by change 304 < 316; decide⟩, .previous ⟨315, by change 315 < 316; decide⟩⟩
  | ⟨317, _⟩ => ⟨.add, .previous ⟨302, by change 302 < 317; decide⟩, .previous ⟨316, by change 316 < 317; decide⟩⟩
  | ⟨318, _⟩ => ⟨.add, .previous ⟨300, by change 300 < 318; decide⟩, .previous ⟨317, by change 317 < 318; decide⟩⟩
  | ⟨319, _⟩ => ⟨.add, .previous ⟨298, by change 298 < 319; decide⟩, .previous ⟨318, by change 318 < 319; decide⟩⟩
  | ⟨320, _⟩ => ⟨.add, .previous ⟨296, by change 296 < 320; decide⟩, .previous ⟨319, by change 319 < 320; decide⟩⟩
  | ⟨321, _⟩ => ⟨.add, .previous ⟨294, by change 294 < 321; decide⟩, .previous ⟨320, by change 320 < 321; decide⟩⟩
  | ⟨322, _⟩ => ⟨.add, .previous ⟨292, by change 292 < 322; decide⟩, .previous ⟨321, by change 321 < 322; decide⟩⟩
  | ⟨323, _⟩ => ⟨.add, .previous ⟨290, by change 290 < 323; decide⟩, .previous ⟨322, by change 322 < 323; decide⟩⟩
  | ⟨324, _⟩ => ⟨.add, .previous ⟨288, by change 288 < 324; decide⟩, .previous ⟨323, by change 323 < 324; decide⟩⟩
  | ⟨325, _⟩ => ⟨.add, .previous ⟨286, by change 286 < 325; decide⟩, .previous ⟨324, by change 324 < 325; decide⟩⟩
  | ⟨326, _⟩ => ⟨.add, .previous ⟨284, by change 284 < 326; decide⟩, .previous ⟨325, by change 325 < 326; decide⟩⟩
  | ⟨327, _⟩ => ⟨.add, .previous ⟨282, by change 282 < 327; decide⟩, .previous ⟨326, by change 326 < 327; decide⟩⟩
  | ⟨328, _⟩ => ⟨.add, .previous ⟨280, by change 280 < 328; decide⟩, .previous ⟨327, by change 327 < 328; decide⟩⟩
  | ⟨329, _⟩ => ⟨.add, .previous ⟨278, by change 278 < 329; decide⟩, .previous ⟨328, by change 328 < 329; decide⟩⟩
  | ⟨330, _⟩ => ⟨.add, .previous ⟨276, by change 276 < 330; decide⟩, .previous ⟨329, by change 329 < 330; decide⟩⟩
  | ⟨331, _⟩ => ⟨.add, .previous ⟨274, by change 274 < 331; decide⟩, .previous ⟨330, by change 330 < 331; decide⟩⟩
  | ⟨332, _⟩ => ⟨.add, .previous ⟨272, by change 272 < 332; decide⟩, .previous ⟨331, by change 331 < 332; decide⟩⟩
  | ⟨333, _⟩ => ⟨.add, .previous ⟨270, by change 270 < 333; decide⟩, .previous ⟨332, by change 332 < 333; decide⟩⟩
  | ⟨334, _⟩ => ⟨.add, .previous ⟨268, by change 268 < 334; decide⟩, .previous ⟨333, by change 333 < 334; decide⟩⟩
  | ⟨335, _⟩ => ⟨.add, .previous ⟨266, by change 266 < 335; decide⟩, .previous ⟨334, by change 334 < 335; decide⟩⟩
  | ⟨336, _⟩ => ⟨.add, .previous ⟨264, by change 264 < 336; decide⟩, .previous ⟨335, by change 335 < 336; decide⟩⟩
  | ⟨337, _⟩ => ⟨.add, .previous ⟨262, by change 262 < 337; decide⟩, .previous ⟨336, by change 336 < 337; decide⟩⟩
  | ⟨338, _⟩ => ⟨.add, .previous ⟨260, by change 260 < 338; decide⟩, .previous ⟨337, by change 337 < 338; decide⟩⟩
  | ⟨339, _⟩ => ⟨.add, .previous ⟨258, by change 258 < 339; decide⟩, .previous ⟨338, by change 338 < 339; decide⟩⟩
  | ⟨340, _⟩ => ⟨.add, .previous ⟨256, by change 256 < 340; decide⟩, .previous ⟨339, by change 339 < 340; decide⟩⟩
  | ⟨341, _⟩ => ⟨.add, .previous ⟨254, by change 254 < 341; decide⟩, .previous ⟨340, by change 340 < 341; decide⟩⟩
  | ⟨342, _⟩ => ⟨.add, .previous ⟨252, by change 252 < 342; decide⟩, .previous ⟨341, by change 341 < 342; decide⟩⟩
  | ⟨343, _⟩ => ⟨.add, .previous ⟨250, by change 250 < 343; decide⟩, .previous ⟨342, by change 342 < 343; decide⟩⟩
  | ⟨344, _⟩ => ⟨.add, .previous ⟨248, by change 248 < 344; decide⟩, .previous ⟨343, by change 343 < 344; decide⟩⟩
  | ⟨345, _⟩ => ⟨.add, .previous ⟨246, by change 246 < 345; decide⟩, .previous ⟨344, by change 344 < 345; decide⟩⟩
  | ⟨346, _⟩ => ⟨.add, .previous ⟨244, by change 244 < 346; decide⟩, .previous ⟨345, by change 345 < 346; decide⟩⟩
  | ⟨347, _⟩ => ⟨.add, .previous ⟨242, by change 242 < 347; decide⟩, .previous ⟨346, by change 346 < 347; decide⟩⟩
  | ⟨idx + 348, hidx⟩ => False.elim (by omega)

private def node241 (inputs : Fin 69 → ℕ) : ℤ :=
  node0 inputs - node5 inputs

private def node242 (inputs : Fin 69 → ℕ) : ℤ :=
  node241 inputs * node241 inputs

private def node243 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 25 : ℤ) - node7 inputs

private def node244 (inputs : Fin 69 → ℕ) : ℤ :=
  node243 inputs * node243 inputs

private def node245 (inputs : Fin 69 → ℕ) : ℤ :=
  node11 inputs - node16 inputs

private def node246 (inputs : Fin 69 → ℕ) : ℤ :=
  node245 inputs * node245 inputs

private def node247 (inputs : Fin 69 → ℕ) : ℤ :=
  node22 inputs - (inputs 26 : ℤ)

private def node248 (inputs : Fin 69 → ℕ) : ℤ :=
  node247 inputs * node247 inputs

private def node249 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 24 : ℤ) - node26 inputs

private def node250 (inputs : Fin 69 → ℕ) : ℤ :=
  node249 inputs * node249 inputs

private def node251 (inputs : Fin 69 → ℕ) : ℤ :=
  node38 inputs - node39 inputs

private def node252 (inputs : Fin 69 → ℕ) : ℤ :=
  node251 inputs * node251 inputs

private def node253 (inputs : Fin 69 → ℕ) : ℤ :=
  node44 inputs - node46 inputs

private def node254 (inputs : Fin 69 → ℕ) : ℤ :=
  node253 inputs * node253 inputs

private def node255 (inputs : Fin 69 → ℕ) : ℤ :=
  node51 inputs - node53 inputs

private def node256 (inputs : Fin 69 → ℕ) : ℤ :=
  node255 inputs * node255 inputs

private def node257 (inputs : Fin 69 → ℕ) : ℤ :=
  node104 inputs - node105 inputs

private def node258 (inputs : Fin 69 → ℕ) : ℤ :=
  node257 inputs * node257 inputs

private def node259 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 48 : ℤ) - node116 inputs

private def node260 (inputs : Fin 69 → ℕ) : ℤ :=
  node259 inputs * node259 inputs

private def node261 (inputs : Fin 69 → ℕ) : ℤ :=
  node124 inputs - node125 inputs

private def node262 (inputs : Fin 69 → ℕ) : ℤ :=
  node261 inputs * node261 inputs

private def node263 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) - node127 inputs

private def node264 (inputs : Fin 69 → ℕ) : ℤ :=
  node263 inputs * node263 inputs

private def node265 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) - node130 inputs

private def node266 (inputs : Fin 69 → ℕ) : ℤ :=
  node265 inputs * node265 inputs

private def node267 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) - node133 inputs

private def node268 (inputs : Fin 69 → ℕ) : ℤ :=
  node267 inputs * node267 inputs

private def node269 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) - node136 inputs

private def node270 (inputs : Fin 69 → ℕ) : ℤ :=
  node269 inputs * node269 inputs

private def node271 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) - node139 inputs

private def node272 (inputs : Fin 69 → ℕ) : ℤ :=
  node271 inputs * node271 inputs

private def node273 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 31 : ℤ) - node142 inputs

private def node274 (inputs : Fin 69 → ℕ) : ℤ :=
  node273 inputs * node273 inputs

private def node275 (inputs : Fin 69 → ℕ) : ℤ :=
  node150 inputs - node151 inputs

private def node276 (inputs : Fin 69 → ℕ) : ℤ :=
  node275 inputs * node275 inputs

private def node277 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 46 : ℤ) - node158 inputs

private def node278 (inputs : Fin 69 → ℕ) : ℤ :=
  node277 inputs * node277 inputs

private def node279 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 23 : ℤ) - node161 inputs

private def node280 (inputs : Fin 69 → ℕ) : ℤ :=
  node279 inputs * node279 inputs

private def node281 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 23 : ℤ) - node164 inputs

private def node282 (inputs : Fin 69 → ℕ) : ℤ :=
  node281 inputs * node281 inputs

private def node283 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 23 : ℤ) - node167 inputs

private def node284 (inputs : Fin 69 → ℕ) : ℤ :=
  node283 inputs * node283 inputs

private def node285 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 23 : ℤ) - node170 inputs

private def node286 (inputs : Fin 69 → ℕ) : ℤ :=
  node285 inputs * node285 inputs

private def node287 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 23 : ℤ) - node173 inputs

private def node288 (inputs : Fin 69 → ℕ) : ℤ :=
  node287 inputs * node287 inputs

private def node289 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 23 : ℤ) - node176 inputs

private def node290 (inputs : Fin 69 → ℕ) : ℤ :=
  node289 inputs * node289 inputs

private def node291 (inputs : Fin 69 → ℕ) : ℤ :=
  node181 inputs - node182 inputs

private def node292 (inputs : Fin 69 → ℕ) : ℤ :=
  node291 inputs * node291 inputs

private def node293 (inputs : Fin 69 → ℕ) : ℤ :=
  node188 inputs - node189 inputs

private def node294 (inputs : Fin 69 → ℕ) : ℤ :=
  node293 inputs * node293 inputs

private def node295 (inputs : Fin 69 → ℕ) : ℤ :=
  node195 inputs - node196 inputs

private def node296 (inputs : Fin 69 → ℕ) : ℤ :=
  node295 inputs * node295 inputs

private def node297 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 36 : ℤ) - node199 inputs

private def node298 (inputs : Fin 69 → ℕ) : ℤ :=
  node297 inputs * node297 inputs

private def node299 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 34 : ℤ) - node204 inputs

private def node300 (inputs : Fin 69 → ℕ) : ℤ :=
  node299 inputs * node299 inputs

private def node301 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 35 : ℤ) - node209 inputs

private def node302 (inputs : Fin 69 → ℕ) : ℤ :=
  node301 inputs * node301 inputs

private def node303 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 2 : ℤ) - node210 inputs

private def node304 (inputs : Fin 69 → ℕ) : ℤ :=
  node303 inputs * node303 inputs

private def node305 (inputs : Fin 69 → ℕ) : ℤ :=
  (inputs 4 : ℤ) - node212 inputs

private def node306 (inputs : Fin 69 → ℕ) : ℤ :=
  node305 inputs * node305 inputs

private def node307 (inputs : Fin 69 → ℕ) : ℤ :=
  node213 inputs - node218 inputs

private def node308 (inputs : Fin 69 → ℕ) : ℤ :=
  node307 inputs * node307 inputs

private def node309 (inputs : Fin 69 → ℕ) : ℤ :=
  node219 inputs - node225 inputs

private def node310 (inputs : Fin 69 → ℕ) : ℤ :=
  node309 inputs * node309 inputs

private def node311 (inputs : Fin 69 → ℕ) : ℤ :=
  node228 inputs - node240 inputs

private def node312 (inputs : Fin 69 → ℕ) : ℤ :=
  node311 inputs * node311 inputs

private def node313 (inputs : Fin 69 → ℕ) : ℤ :=
  node310 inputs + node312 inputs

private def node314 (inputs : Fin 69 → ℕ) : ℤ :=
  node308 inputs + node313 inputs

private def node315 (inputs : Fin 69 → ℕ) : ℤ :=
  node306 inputs + node314 inputs

private def node316 (inputs : Fin 69 → ℕ) : ℤ :=
  node304 inputs + node315 inputs

private def node317 (inputs : Fin 69 → ℕ) : ℤ :=
  node302 inputs + node316 inputs

private def node318 (inputs : Fin 69 → ℕ) : ℤ :=
  node300 inputs + node317 inputs

private def node319 (inputs : Fin 69 → ℕ) : ℤ :=
  node298 inputs + node318 inputs

private def node320 (inputs : Fin 69 → ℕ) : ℤ :=
  node296 inputs + node319 inputs

private def node321 (inputs : Fin 69 → ℕ) : ℤ :=
  node294 inputs + node320 inputs

private def node322 (inputs : Fin 69 → ℕ) : ℤ :=
  node292 inputs + node321 inputs

private def node323 (inputs : Fin 69 → ℕ) : ℤ :=
  node290 inputs + node322 inputs

private def node324 (inputs : Fin 69 → ℕ) : ℤ :=
  node288 inputs + node323 inputs

private def node325 (inputs : Fin 69 → ℕ) : ℤ :=
  node286 inputs + node324 inputs

private def node326 (inputs : Fin 69 → ℕ) : ℤ :=
  node284 inputs + node325 inputs

private def node327 (inputs : Fin 69 → ℕ) : ℤ :=
  node282 inputs + node326 inputs

private def node328 (inputs : Fin 69 → ℕ) : ℤ :=
  node280 inputs + node327 inputs

private def node329 (inputs : Fin 69 → ℕ) : ℤ :=
  node278 inputs + node328 inputs

private def node330 (inputs : Fin 69 → ℕ) : ℤ :=
  node276 inputs + node329 inputs

private def node331 (inputs : Fin 69 → ℕ) : ℤ :=
  node274 inputs + node330 inputs

private def node332 (inputs : Fin 69 → ℕ) : ℤ :=
  node272 inputs + node331 inputs

private def node333 (inputs : Fin 69 → ℕ) : ℤ :=
  node270 inputs + node332 inputs

private def node334 (inputs : Fin 69 → ℕ) : ℤ :=
  node268 inputs + node333 inputs

private def node335 (inputs : Fin 69 → ℕ) : ℤ :=
  node266 inputs + node334 inputs

private def node336 (inputs : Fin 69 → ℕ) : ℤ :=
  node264 inputs + node335 inputs

private def node337 (inputs : Fin 69 → ℕ) : ℤ :=
  node262 inputs + node336 inputs

private def node338 (inputs : Fin 69 → ℕ) : ℤ :=
  node260 inputs + node337 inputs

private def node339 (inputs : Fin 69 → ℕ) : ℤ :=
  node258 inputs + node338 inputs

private def node340 (inputs : Fin 69 → ℕ) : ℤ :=
  node256 inputs + node339 inputs

private def node341 (inputs : Fin 69 → ℕ) : ℤ :=
  node254 inputs + node340 inputs

private def node342 (inputs : Fin 69 → ℕ) : ℤ :=
  node252 inputs + node341 inputs

private def node343 (inputs : Fin 69 → ℕ) : ℤ :=
  node250 inputs + node342 inputs

private def node344 (inputs : Fin 69 → ℕ) : ℤ :=
  node248 inputs + node343 inputs

private def node345 (inputs : Fin 69 → ℕ) : ℤ :=
  node246 inputs + node344 inputs

private def node346 (inputs : Fin 69 → ℕ) : ℤ :=
  node244 inputs + node345 inputs

private def node347 (inputs : Fin 69 → ℕ) : ℤ :=
  node242 inputs + node346 inputs

/-- The canonical evaluation of the extended schedule. -/
def singleEvaluation (inputs : Fin 69 → ℕ) : Fin 348 → ℤ
  | ⟨0, _⟩ => node0 inputs
  | ⟨1, _⟩ => node1 inputs
  | ⟨2, _⟩ => node2 inputs
  | ⟨3, _⟩ => node3 inputs
  | ⟨4, _⟩ => node4 inputs
  | ⟨5, _⟩ => node5 inputs
  | ⟨6, _⟩ => node6 inputs
  | ⟨7, _⟩ => node7 inputs
  | ⟨8, _⟩ => node8 inputs
  | ⟨9, _⟩ => node9 inputs
  | ⟨10, _⟩ => node10 inputs
  | ⟨11, _⟩ => node11 inputs
  | ⟨12, _⟩ => node12 inputs
  | ⟨13, _⟩ => node13 inputs
  | ⟨14, _⟩ => node14 inputs
  | ⟨15, _⟩ => node15 inputs
  | ⟨16, _⟩ => node16 inputs
  | ⟨17, _⟩ => node17 inputs
  | ⟨18, _⟩ => node18 inputs
  | ⟨19, _⟩ => node19 inputs
  | ⟨20, _⟩ => node20 inputs
  | ⟨21, _⟩ => node21 inputs
  | ⟨22, _⟩ => node22 inputs
  | ⟨23, _⟩ => node23 inputs
  | ⟨24, _⟩ => node24 inputs
  | ⟨25, _⟩ => node25 inputs
  | ⟨26, _⟩ => node26 inputs
  | ⟨27, _⟩ => node27 inputs
  | ⟨28, _⟩ => node28 inputs
  | ⟨29, _⟩ => node29 inputs
  | ⟨30, _⟩ => node30 inputs
  | ⟨31, _⟩ => node31 inputs
  | ⟨32, _⟩ => node32 inputs
  | ⟨33, _⟩ => node33 inputs
  | ⟨34, _⟩ => node34 inputs
  | ⟨35, _⟩ => node35 inputs
  | ⟨36, _⟩ => node36 inputs
  | ⟨37, _⟩ => node37 inputs
  | ⟨38, _⟩ => node38 inputs
  | ⟨39, _⟩ => node39 inputs
  | ⟨40, _⟩ => node40 inputs
  | ⟨41, _⟩ => node41 inputs
  | ⟨42, _⟩ => node42 inputs
  | ⟨43, _⟩ => node43 inputs
  | ⟨44, _⟩ => node44 inputs
  | ⟨45, _⟩ => node45 inputs
  | ⟨46, _⟩ => node46 inputs
  | ⟨47, _⟩ => node47 inputs
  | ⟨48, _⟩ => node48 inputs
  | ⟨49, _⟩ => node49 inputs
  | ⟨50, _⟩ => node50 inputs
  | ⟨51, _⟩ => node51 inputs
  | ⟨52, _⟩ => node52 inputs
  | ⟨53, _⟩ => node53 inputs
  | ⟨54, _⟩ => node54 inputs
  | ⟨55, _⟩ => node55 inputs
  | ⟨56, _⟩ => node56 inputs
  | ⟨57, _⟩ => node57 inputs
  | ⟨58, _⟩ => node58 inputs
  | ⟨59, _⟩ => node59 inputs
  | ⟨60, _⟩ => node60 inputs
  | ⟨61, _⟩ => node61 inputs
  | ⟨62, _⟩ => node62 inputs
  | ⟨63, _⟩ => node63 inputs
  | ⟨64, _⟩ => node64 inputs
  | ⟨65, _⟩ => node65 inputs
  | ⟨66, _⟩ => node66 inputs
  | ⟨67, _⟩ => node67 inputs
  | ⟨68, _⟩ => node68 inputs
  | ⟨69, _⟩ => node69 inputs
  | ⟨70, _⟩ => node70 inputs
  | ⟨71, _⟩ => node71 inputs
  | ⟨72, _⟩ => node72 inputs
  | ⟨73, _⟩ => node73 inputs
  | ⟨74, _⟩ => node74 inputs
  | ⟨75, _⟩ => node75 inputs
  | ⟨76, _⟩ => node76 inputs
  | ⟨77, _⟩ => node77 inputs
  | ⟨78, _⟩ => node78 inputs
  | ⟨79, _⟩ => node79 inputs
  | ⟨80, _⟩ => node80 inputs
  | ⟨81, _⟩ => node81 inputs
  | ⟨82, _⟩ => node82 inputs
  | ⟨83, _⟩ => node83 inputs
  | ⟨84, _⟩ => node84 inputs
  | ⟨85, _⟩ => node85 inputs
  | ⟨86, _⟩ => node86 inputs
  | ⟨87, _⟩ => node87 inputs
  | ⟨88, _⟩ => node88 inputs
  | ⟨89, _⟩ => node89 inputs
  | ⟨90, _⟩ => node90 inputs
  | ⟨91, _⟩ => node91 inputs
  | ⟨92, _⟩ => node92 inputs
  | ⟨93, _⟩ => node93 inputs
  | ⟨94, _⟩ => node94 inputs
  | ⟨95, _⟩ => node95 inputs
  | ⟨96, _⟩ => node96 inputs
  | ⟨97, _⟩ => node97 inputs
  | ⟨98, _⟩ => node98 inputs
  | ⟨99, _⟩ => node99 inputs
  | ⟨100, _⟩ => node100 inputs
  | ⟨101, _⟩ => node101 inputs
  | ⟨102, _⟩ => node102 inputs
  | ⟨103, _⟩ => node103 inputs
  | ⟨104, _⟩ => node104 inputs
  | ⟨105, _⟩ => node105 inputs
  | ⟨106, _⟩ => node106 inputs
  | ⟨107, _⟩ => node107 inputs
  | ⟨108, _⟩ => node108 inputs
  | ⟨109, _⟩ => node109 inputs
  | ⟨110, _⟩ => node110 inputs
  | ⟨111, _⟩ => node111 inputs
  | ⟨112, _⟩ => node112 inputs
  | ⟨113, _⟩ => node113 inputs
  | ⟨114, _⟩ => node114 inputs
  | ⟨115, _⟩ => node115 inputs
  | ⟨116, _⟩ => node116 inputs
  | ⟨117, _⟩ => node117 inputs
  | ⟨118, _⟩ => node118 inputs
  | ⟨119, _⟩ => node119 inputs
  | ⟨120, _⟩ => node120 inputs
  | ⟨121, _⟩ => node121 inputs
  | ⟨122, _⟩ => node122 inputs
  | ⟨123, _⟩ => node123 inputs
  | ⟨124, _⟩ => node124 inputs
  | ⟨125, _⟩ => node125 inputs
  | ⟨126, _⟩ => node126 inputs
  | ⟨127, _⟩ => node127 inputs
  | ⟨128, _⟩ => node128 inputs
  | ⟨129, _⟩ => node129 inputs
  | ⟨130, _⟩ => node130 inputs
  | ⟨131, _⟩ => node131 inputs
  | ⟨132, _⟩ => node132 inputs
  | ⟨133, _⟩ => node133 inputs
  | ⟨134, _⟩ => node134 inputs
  | ⟨135, _⟩ => node135 inputs
  | ⟨136, _⟩ => node136 inputs
  | ⟨137, _⟩ => node137 inputs
  | ⟨138, _⟩ => node138 inputs
  | ⟨139, _⟩ => node139 inputs
  | ⟨140, _⟩ => node140 inputs
  | ⟨141, _⟩ => node141 inputs
  | ⟨142, _⟩ => node142 inputs
  | ⟨143, _⟩ => node143 inputs
  | ⟨144, _⟩ => node144 inputs
  | ⟨145, _⟩ => node145 inputs
  | ⟨146, _⟩ => node146 inputs
  | ⟨147, _⟩ => node147 inputs
  | ⟨148, _⟩ => node148 inputs
  | ⟨149, _⟩ => node149 inputs
  | ⟨150, _⟩ => node150 inputs
  | ⟨151, _⟩ => node151 inputs
  | ⟨152, _⟩ => node152 inputs
  | ⟨153, _⟩ => node153 inputs
  | ⟨154, _⟩ => node154 inputs
  | ⟨155, _⟩ => node155 inputs
  | ⟨156, _⟩ => node156 inputs
  | ⟨157, _⟩ => node157 inputs
  | ⟨158, _⟩ => node158 inputs
  | ⟨159, _⟩ => node159 inputs
  | ⟨160, _⟩ => node160 inputs
  | ⟨161, _⟩ => node161 inputs
  | ⟨162, _⟩ => node162 inputs
  | ⟨163, _⟩ => node163 inputs
  | ⟨164, _⟩ => node164 inputs
  | ⟨165, _⟩ => node165 inputs
  | ⟨166, _⟩ => node166 inputs
  | ⟨167, _⟩ => node167 inputs
  | ⟨168, _⟩ => node168 inputs
  | ⟨169, _⟩ => node169 inputs
  | ⟨170, _⟩ => node170 inputs
  | ⟨171, _⟩ => node171 inputs
  | ⟨172, _⟩ => node172 inputs
  | ⟨173, _⟩ => node173 inputs
  | ⟨174, _⟩ => node174 inputs
  | ⟨175, _⟩ => node175 inputs
  | ⟨176, _⟩ => node176 inputs
  | ⟨177, _⟩ => node177 inputs
  | ⟨178, _⟩ => node178 inputs
  | ⟨179, _⟩ => node179 inputs
  | ⟨180, _⟩ => node180 inputs
  | ⟨181, _⟩ => node181 inputs
  | ⟨182, _⟩ => node182 inputs
  | ⟨183, _⟩ => node183 inputs
  | ⟨184, _⟩ => node184 inputs
  | ⟨185, _⟩ => node185 inputs
  | ⟨186, _⟩ => node186 inputs
  | ⟨187, _⟩ => node187 inputs
  | ⟨188, _⟩ => node188 inputs
  | ⟨189, _⟩ => node189 inputs
  | ⟨190, _⟩ => node190 inputs
  | ⟨191, _⟩ => node191 inputs
  | ⟨192, _⟩ => node192 inputs
  | ⟨193, _⟩ => node193 inputs
  | ⟨194, _⟩ => node194 inputs
  | ⟨195, _⟩ => node195 inputs
  | ⟨196, _⟩ => node196 inputs
  | ⟨197, _⟩ => node197 inputs
  | ⟨198, _⟩ => node198 inputs
  | ⟨199, _⟩ => node199 inputs
  | ⟨200, _⟩ => node200 inputs
  | ⟨201, _⟩ => node201 inputs
  | ⟨202, _⟩ => node202 inputs
  | ⟨203, _⟩ => node203 inputs
  | ⟨204, _⟩ => node204 inputs
  | ⟨205, _⟩ => node205 inputs
  | ⟨206, _⟩ => node206 inputs
  | ⟨207, _⟩ => node207 inputs
  | ⟨208, _⟩ => node208 inputs
  | ⟨209, _⟩ => node209 inputs
  | ⟨210, _⟩ => node210 inputs
  | ⟨211, _⟩ => node211 inputs
  | ⟨212, _⟩ => node212 inputs
  | ⟨213, _⟩ => node213 inputs
  | ⟨214, _⟩ => node214 inputs
  | ⟨215, _⟩ => node215 inputs
  | ⟨216, _⟩ => node216 inputs
  | ⟨217, _⟩ => node217 inputs
  | ⟨218, _⟩ => node218 inputs
  | ⟨219, _⟩ => node219 inputs
  | ⟨220, _⟩ => node220 inputs
  | ⟨221, _⟩ => node221 inputs
  | ⟨222, _⟩ => node222 inputs
  | ⟨223, _⟩ => node223 inputs
  | ⟨224, _⟩ => node224 inputs
  | ⟨225, _⟩ => node225 inputs
  | ⟨226, _⟩ => node226 inputs
  | ⟨227, _⟩ => node227 inputs
  | ⟨228, _⟩ => node228 inputs
  | ⟨229, _⟩ => node229 inputs
  | ⟨230, _⟩ => node230 inputs
  | ⟨231, _⟩ => node231 inputs
  | ⟨232, _⟩ => node232 inputs
  | ⟨233, _⟩ => node233 inputs
  | ⟨234, _⟩ => node234 inputs
  | ⟨235, _⟩ => node235 inputs
  | ⟨236, _⟩ => node236 inputs
  | ⟨237, _⟩ => node237 inputs
  | ⟨238, _⟩ => node238 inputs
  | ⟨239, _⟩ => node239 inputs
  | ⟨240, _⟩ => node240 inputs
  | ⟨241, _⟩ => node241 inputs
  | ⟨242, _⟩ => node242 inputs
  | ⟨243, _⟩ => node243 inputs
  | ⟨244, _⟩ => node244 inputs
  | ⟨245, _⟩ => node245 inputs
  | ⟨246, _⟩ => node246 inputs
  | ⟨247, _⟩ => node247 inputs
  | ⟨248, _⟩ => node248 inputs
  | ⟨249, _⟩ => node249 inputs
  | ⟨250, _⟩ => node250 inputs
  | ⟨251, _⟩ => node251 inputs
  | ⟨252, _⟩ => node252 inputs
  | ⟨253, _⟩ => node253 inputs
  | ⟨254, _⟩ => node254 inputs
  | ⟨255, _⟩ => node255 inputs
  | ⟨256, _⟩ => node256 inputs
  | ⟨257, _⟩ => node257 inputs
  | ⟨258, _⟩ => node258 inputs
  | ⟨259, _⟩ => node259 inputs
  | ⟨260, _⟩ => node260 inputs
  | ⟨261, _⟩ => node261 inputs
  | ⟨262, _⟩ => node262 inputs
  | ⟨263, _⟩ => node263 inputs
  | ⟨264, _⟩ => node264 inputs
  | ⟨265, _⟩ => node265 inputs
  | ⟨266, _⟩ => node266 inputs
  | ⟨267, _⟩ => node267 inputs
  | ⟨268, _⟩ => node268 inputs
  | ⟨269, _⟩ => node269 inputs
  | ⟨270, _⟩ => node270 inputs
  | ⟨271, _⟩ => node271 inputs
  | ⟨272, _⟩ => node272 inputs
  | ⟨273, _⟩ => node273 inputs
  | ⟨274, _⟩ => node274 inputs
  | ⟨275, _⟩ => node275 inputs
  | ⟨276, _⟩ => node276 inputs
  | ⟨277, _⟩ => node277 inputs
  | ⟨278, _⟩ => node278 inputs
  | ⟨279, _⟩ => node279 inputs
  | ⟨280, _⟩ => node280 inputs
  | ⟨281, _⟩ => node281 inputs
  | ⟨282, _⟩ => node282 inputs
  | ⟨283, _⟩ => node283 inputs
  | ⟨284, _⟩ => node284 inputs
  | ⟨285, _⟩ => node285 inputs
  | ⟨286, _⟩ => node286 inputs
  | ⟨287, _⟩ => node287 inputs
  | ⟨288, _⟩ => node288 inputs
  | ⟨289, _⟩ => node289 inputs
  | ⟨290, _⟩ => node290 inputs
  | ⟨291, _⟩ => node291 inputs
  | ⟨292, _⟩ => node292 inputs
  | ⟨293, _⟩ => node293 inputs
  | ⟨294, _⟩ => node294 inputs
  | ⟨295, _⟩ => node295 inputs
  | ⟨296, _⟩ => node296 inputs
  | ⟨297, _⟩ => node297 inputs
  | ⟨298, _⟩ => node298 inputs
  | ⟨299, _⟩ => node299 inputs
  | ⟨300, _⟩ => node300 inputs
  | ⟨301, _⟩ => node301 inputs
  | ⟨302, _⟩ => node302 inputs
  | ⟨303, _⟩ => node303 inputs
  | ⟨304, _⟩ => node304 inputs
  | ⟨305, _⟩ => node305 inputs
  | ⟨306, _⟩ => node306 inputs
  | ⟨307, _⟩ => node307 inputs
  | ⟨308, _⟩ => node308 inputs
  | ⟨309, _⟩ => node309 inputs
  | ⟨310, _⟩ => node310 inputs
  | ⟨311, _⟩ => node311 inputs
  | ⟨312, _⟩ => node312 inputs
  | ⟨313, _⟩ => node313 inputs
  | ⟨314, _⟩ => node314 inputs
  | ⟨315, _⟩ => node315 inputs
  | ⟨316, _⟩ => node316 inputs
  | ⟨317, _⟩ => node317 inputs
  | ⟨318, _⟩ => node318 inputs
  | ⟨319, _⟩ => node319 inputs
  | ⟨320, _⟩ => node320 inputs
  | ⟨321, _⟩ => node321 inputs
  | ⟨322, _⟩ => node322 inputs
  | ⟨323, _⟩ => node323 inputs
  | ⟨324, _⟩ => node324 inputs
  | ⟨325, _⟩ => node325 inputs
  | ⟨326, _⟩ => node326 inputs
  | ⟨327, _⟩ => node327 inputs
  | ⟨328, _⟩ => node328 inputs
  | ⟨329, _⟩ => node329 inputs
  | ⟨330, _⟩ => node330 inputs
  | ⟨331, _⟩ => node331 inputs
  | ⟨332, _⟩ => node332 inputs
  | ⟨333, _⟩ => node333 inputs
  | ⟨334, _⟩ => node334 inputs
  | ⟨335, _⟩ => node335 inputs
  | ⟨336, _⟩ => node336 inputs
  | ⟨337, _⟩ => node337 inputs
  | ⟨338, _⟩ => node338 inputs
  | ⟨339, _⟩ => node339 inputs
  | ⟨340, _⟩ => node340 inputs
  | ⟨341, _⟩ => node341 inputs
  | ⟨342, _⟩ => node342 inputs
  | ⟨343, _⟩ => node343 inputs
  | ⟨344, _⟩ => node344 inputs
  | ⟨345, _⟩ => node345 inputs
  | ⟨346, _⟩ => node346 inputs
  | ⟨347, _⟩ => node347 inputs
  | ⟨idx + 348, hidx⟩ => False.elim (by omega)

theorem singleEvaluation_valid (inputs : Fin 69 → ℕ) :
    Valid singleSchedule inputs (singleEvaluation inputs) := by
  intro idx
  apply ((singleSchedule idx).check_iff inputs _ _).mpr
  fin_cases idx <;> rfl

theorem single_assignment_counts :
    operationCount singleSchedule .add = 124 ∧ operationCount singleSchedule .sub = 60 ∧
      operationCount singleSchedule .mul = 164 := by
  decide +kernel

theorem single_check_counts :
    additionChecks singleSchedule + multiplicationChecks singleSchedule = 348 := by
  rcases single_assignment_counts with ⟨ha, hs, hm⟩
  norm_num [additionChecks, multiplicationChecks, ha, hs, hm]

private theorem sq_add {a b R : ℤ} (hR : 0 ≤ R) : (a - b) * (a - b) + R = 0 ↔ a = b ∧ R = 0 := by
  constructor
  · intro h
    have h1 : (a - b) * (a - b) = 0 := by nlinarith [mul_self_nonneg (a - b)]
    exact ⟨by simpa [sub_eq_zero] using h1, by nlinarith [mul_self_nonneg (a - b)]⟩
  · rintro ⟨rfl, rfl⟩; ring

private theorem sq_add_sq {a b c d : ℤ} :
    (a - b) * (a - b) + (c - d) * (c - d) = 0 ↔ a = b ∧ c = d := by
  rw [sq_add (mul_self_nonneg _), mul_self_eq_zero, sub_eq_zero]

/-- The last intermediate vanishes iff all 36 equality tests pass. -/
theorem singleEvaluation_last_eq_zero_iff (inputs : Fin 69 → ℕ) :
    singleEvaluation inputs 347 = 0 ↔ FinalEqualities inputs (evaluation inputs) := by
  show (node0 inputs - node5 inputs) * (node0 inputs - node5 inputs) + (((inputs 25 : ℤ) - node7 inputs) * ((inputs 25 : ℤ) - node7 inputs) + ((node11 inputs - node16 inputs) * (node11 inputs - node16 inputs) + ((node22 inputs - (inputs 26 : ℤ)) * (node22 inputs - (inputs 26 : ℤ)) + (((inputs 24 : ℤ) - node26 inputs) * ((inputs 24 : ℤ) - node26 inputs) + ((node38 inputs - node39 inputs) * (node38 inputs - node39 inputs) + ((node44 inputs - node46 inputs) * (node44 inputs - node46 inputs) + ((node51 inputs - node53 inputs) * (node51 inputs - node53 inputs) + ((node104 inputs - node105 inputs) * (node104 inputs - node105 inputs) + (((inputs 48 : ℤ) - node116 inputs) * ((inputs 48 : ℤ) - node116 inputs) + ((node124 inputs - node125 inputs) * (node124 inputs - node125 inputs) + (((inputs 31 : ℤ) - node127 inputs) * ((inputs 31 : ℤ) - node127 inputs) + (((inputs 31 : ℤ) - node130 inputs) * ((inputs 31 : ℤ) - node130 inputs) + (((inputs 31 : ℤ) - node133 inputs) * ((inputs 31 : ℤ) - node133 inputs) + (((inputs 31 : ℤ) - node136 inputs) * ((inputs 31 : ℤ) - node136 inputs) + (((inputs 31 : ℤ) - node139 inputs) * ((inputs 31 : ℤ) - node139 inputs) + (((inputs 31 : ℤ) - node142 inputs) * ((inputs 31 : ℤ) - node142 inputs) + ((node150 inputs - node151 inputs) * (node150 inputs - node151 inputs) + (((inputs 46 : ℤ) - node158 inputs) * ((inputs 46 : ℤ) - node158 inputs) + (((inputs 23 : ℤ) - node161 inputs) * ((inputs 23 : ℤ) - node161 inputs) + (((inputs 23 : ℤ) - node164 inputs) * ((inputs 23 : ℤ) - node164 inputs) + (((inputs 23 : ℤ) - node167 inputs) * ((inputs 23 : ℤ) - node167 inputs) + (((inputs 23 : ℤ) - node170 inputs) * ((inputs 23 : ℤ) - node170 inputs) + (((inputs 23 : ℤ) - node173 inputs) * ((inputs 23 : ℤ) - node173 inputs) + (((inputs 23 : ℤ) - node176 inputs) * ((inputs 23 : ℤ) - node176 inputs) + ((node181 inputs - node182 inputs) * (node181 inputs - node182 inputs) + ((node188 inputs - node189 inputs) * (node188 inputs - node189 inputs) + ((node195 inputs - node196 inputs) * (node195 inputs - node196 inputs) + (((inputs 36 : ℤ) - node199 inputs) * ((inputs 36 : ℤ) - node199 inputs) + (((inputs 34 : ℤ) - node204 inputs) * ((inputs 34 : ℤ) - node204 inputs) + (((inputs 35 : ℤ) - node209 inputs) * ((inputs 35 : ℤ) - node209 inputs) + (((inputs 2 : ℤ) - node210 inputs) * ((inputs 2 : ℤ) - node210 inputs) + (((inputs 4 : ℤ) - node212 inputs) * ((inputs 4 : ℤ) - node212 inputs) + ((node213 inputs - node218 inputs) * (node213 inputs - node218 inputs) + ((node219 inputs - node225 inputs) * (node219 inputs - node225 inputs) + ((node228 inputs - node240 inputs) * (node228 inputs - node240 inputs)))))))))))))))))))))))))))))))))))) = 0 ↔ _
  rw [sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add ?_, sq_add_sq]
  · exact Iff.rfl
  all_goals repeat' first | exact mul_self_nonneg _ | apply add_nonneg

/-- A single-equation certificate: a valid run of the extended schedule whose last value
is zero. -/
def SingleCertificate (n x : ℕ) (inputs : Fin 69 → ℕ) (trace : Fin 348 → ℤ) : Prop :=
  inputs 0 = n ∧ inputs 1 = x ∧ Valid singleSchedule inputs trace ∧ trace 347 = 0

theorem certificate_iff_single (n x : ℕ) :
    (∃ (inputs : Fin 69 → ℕ) (trace : Fin 241 → ℤ), Certificate n x inputs trace) ↔
      ∃ (inputs : Fin 69 → ℕ) (trace : Fin 348 → ℤ), SingleCertificate n x inputs trace := by
  constructor
  · rintro ⟨inputs, trace, h0, h1, hv, hf⟩
    rw [(valid_iff_eq_evaluation inputs trace).mp hv] at hf
    exact ⟨inputs, singleEvaluation inputs, h0, h1, singleEvaluation_valid inputs,
      (singleEvaluation_last_eq_zero_iff inputs).mpr hf⟩
  · rintro ⟨inputs, trace, h0, h1, hv, hz⟩
    rw [hv.unique (singleEvaluation_valid inputs)] at hz
    exact ⟨inputs, evaluation inputs, h0, h1, evaluation_valid inputs,
      (singleEvaluation_last_eq_zero_iff inputs).mp hz⟩

end Jones1978.OperationCount

namespace Jones1978

open Diophantine.ArithmeticCertificate in
/-- **Corollary 1**, with the operation counts: for positive `n, x`, membership `x ∈ Wₙ` is
certified by a fixed schedule of at most 243 additions and multiplications (here 113 + 128),
and, combining the 36 equations into one, by a fixed schedule of at most 350 (here 348) whose
last value must vanish. -/
theorem corollary_1 :
    additionChecks OperationCount.schedule +
        multiplicationChecks OperationCount.schedule ≤ 243 ∧
      additionChecks OperationCount.singleSchedule +
        multiplicationChecks OperationCount.singleSchedule ≤ 350 ∧
      ∀ {n x : ℕ}, 0 < n → 0 < x →
        (x ∈ W n ↔ ∃ inputs trace, OperationCount.Certificate n x inputs trace) ∧
        (x ∈ W n ↔ ∃ inputs trace, OperationCount.SingleCertificate n x inputs trace) := by
  refine ⟨by rw [OperationCount.check_counts.2.2]; norm_num,
    by rw [OperationCount.single_check_counts]; norm_num, fun hn hx => ?_⟩
  have h := OperationCount.mem_W_iff_certificate hn hx
  exact ⟨h, h.trans (OperationCount.certificate_iff_single _ _)⟩

end Jones1978
