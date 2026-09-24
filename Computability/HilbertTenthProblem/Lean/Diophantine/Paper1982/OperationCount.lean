import Diophantine.Common.ArithmeticCertificate
import Diophantine.Paper1980.Universal90

/-!
# Jones 1982, Theorem 5: at most 100 operations check a membership certificate

The article counts `o = 100` arithmetical operations (additions and multiplications,
subtraction being a signed addition) for its Theorem 3 system with `q = b^(5^60)` done away
with, and reads this as: 100 operations suffice to check a supplied Diophantine certificate of
membership in any r.e. set.  Here the count is made literal in the calculator model of
`Diophantine.ArithmeticCertificate` (numerals free, intermediates reusable, equality and
positivity tests uncharged), for the 90-operation universal system `Jones1980.Sys90`.

The schedule has 90 instructions: 33 additions, 9 subtractions and 48 multiplications, i.e.
42 addition checks and 48 multiplication checks, followed by 22 equality tests.  Its inputs are
`x, V, H, Tindex` and the 34 unknowns of `Sys90` in its argument order.  Some equations are
evaluated in a form that reuses earlier intermediates (`θ` for `H + b`, the computed
`(e − l)(x + g)²` for `σ`, `(i c²)²` for `(A² − 1)(f² − 1)`); the equality tests are shown to be
equivalent to the whole system, not equation by equation.

This is the straight-line certificate of `Papers/verification/round37_1980_binary_product_certificate.json`
up to the order of instructions.  It bounds the operations of checking a certificate; it says
nothing about the size of the witnesses or the work of finding them.
-/

namespace Jones1982.OperationCount

open Diophantine.ArithmeticCertificate Jones1980

/-- The literal schedule. -/
def schedule : Schedule 38 90
  | ⟨0, _⟩ => ⟨.add, .input 15, .input 36⟩
  | ⟨1, _⟩ => ⟨.add, .previous ⟨0, by change 0 < 1; decide⟩, .input 23⟩
  | ⟨2, _⟩ => ⟨.add, .input 0, .input 34⟩
  | ⟨3, _⟩ => ⟨.mul, .input 18, .input 18⟩
  | ⟨4, _⟩ => ⟨.mul, .input 26, .input 27⟩
  | ⟨5, _⟩ => ⟨.add, .previous ⟨4, by change 4 < 5; decide⟩, .constant (1)⟩
  | ⟨6, _⟩ => ⟨.add, .previous ⟨5, by change 5 < 6; decide⟩, .input 27⟩
  | ⟨7, _⟩ => ⟨.add, .input 2, .input 5⟩
  | ⟨8, _⟩ => ⟨.mul, .input 8, .input 18⟩
  | ⟨9, _⟩ => ⟨.add, .input 15, .previous ⟨8, by change 8 < 9; decide⟩⟩
  | ⟨10, _⟩ => ⟨.mul, .input 21, .input 26⟩
  | ⟨11, _⟩ => ⟨.add, .input 1, .previous ⟨10, by change 10 < 11; decide⟩⟩
  | ⟨12, _⟩ => ⟨.mul, .previous ⟨3, by change 3 < 12; decide⟩, .previous ⟨3, by change 3 < 12; decide⟩⟩
  | ⟨13, _⟩ => ⟨.mul, .previous ⟨12, by change 12 < 13; decide⟩, .previous ⟨12, by change 12 < 13; decide⟩⟩
  | ⟨14, _⟩ => ⟨.sub, .input 8, .input 15⟩
  | ⟨15, _⟩ => ⟨.add, .input 0, .input 10⟩
  | ⟨16, _⟩ => ⟨.mul, .previous ⟨15, by change 15 < 16; decide⟩, .previous ⟨15, by change 15 < 16; decide⟩⟩
  | ⟨17, _⟩ => ⟨.mul, .previous ⟨14, by change 14 < 17; decide⟩, .previous ⟨16, by change 16 < 17; decide⟩⟩
  | ⟨18, _⟩ => ⟨.mul, .previous ⟨17, by change 17 < 18; decide⟩, .previous ⟨3, by change 3 < 18; decide⟩⟩
  | ⟨19, _⟩ => ⟨.add, .previous ⟨9, by change 9 < 19; decide⟩, .previous ⟨18, by change 18 < 19; decide⟩⟩
  | ⟨20, _⟩ => ⟨.mul, .previous ⟨19, by change 19 < 20; decide⟩, .previous ⟨3, by change 3 < 20; decide⟩⟩
  | ⟨21, _⟩ => ⟨.add, .input 10, .previous ⟨20, by change 20 < 21; decide⟩⟩
  | ⟨22, _⟩ => ⟨.mul, .input 16, .input 16⟩
  | ⟨23, _⟩ => ⟨.sub, .previous ⟨22, by change 22 < 23; decide⟩, .input 16⟩
  | ⟨24, _⟩ => ⟨.mul, .previous ⟨21, by change 21 < 24; decide⟩, .previous ⟨23, by change 23 < 24; decide⟩⟩
  | ⟨25, _⟩ => ⟨.mul, .previous ⟨5, by change 5 < 25; decide⟩, .previous ⟨3, by change 3 < 25; decide⟩⟩
  | ⟨26, _⟩ => ⟨.mul, .input 26, .previous ⟨12, by change 12 < 26; decide⟩⟩
  | ⟨27, _⟩ => ⟨.sub, .previous ⟨26, by change 26 < 27; decide⟩, .input 5⟩
  | ⟨28, _⟩ => ⟨.mul, .input 15, .previous ⟨27, by change 27 < 28; decide⟩⟩
  | ⟨29, _⟩ => ⟨.add, .previous ⟨25, by change 25 < 29; decide⟩, .previous ⟨28, by change 28 < 29; decide⟩⟩
  | ⟨30, _⟩ => ⟨.sub, .previous ⟨22, by change 22 < 30; decide⟩, .constant (1)⟩
  | ⟨31, _⟩ => ⟨.mul, .previous ⟨29, by change 29 < 31; decide⟩, .previous ⟨30, by change 30 < 31; decide⟩⟩
  | ⟨32, _⟩ => ⟨.add, .previous ⟨24, by change 24 < 32; decide⟩, .previous ⟨31, by change 31 < 32; decide⟩⟩
  | ⟨33, _⟩ => ⟨.add, .input 28, .constant (1)⟩
  | ⟨34, _⟩ => ⟨.mul, .input 28, .previous ⟨33, by change 33 < 34; decide⟩⟩
  | ⟨35, _⟩ => ⟨.mul, .input 22, .previous ⟨22, by change 22 < 35; decide⟩⟩
  | ⟨36, _⟩ => ⟨.mul, .input 20, .previous ⟨22, by change 22 < 36; decide⟩⟩
  | ⟨37, _⟩ => ⟨.mul, .previous ⟨35, by change 35 < 37; decide⟩, .previous ⟨36, by change 36 < 37; decide⟩⟩
  | ⟨38, _⟩ => ⟨.mul, .previous ⟨37, by change 37 < 38; decide⟩, .previous ⟨37, by change 37 < 38; decide⟩⟩
  | ⟨39, _⟩ => ⟨.add, .previous ⟨38, by change 38 < 39; decide⟩, .previous ⟨35, by change 35 < 39; decide⟩⟩
  | ⟨40, _⟩ => ⟨.mul, .input 14, .previous ⟨36, by change 36 < 40; decide⟩⟩
  | ⟨41, _⟩ => ⟨.mul, .previous ⟨40, by change 40 < 41; decide⟩, .previous ⟨40, by change 40 < 41; decide⟩⟩
  | ⟨42, _⟩ => ⟨.mul, .previous ⟨39, by change 39 < 42; decide⟩, .previous ⟨41, by change 41 < 42; decide⟩⟩
  | ⟨43, _⟩ => ⟨.add, .previous ⟨40, by change 40 < 43; decide⟩, .input 25⟩
  | ⟨44, _⟩ => ⟨.add, .input 25, .input 35⟩
  | ⟨45, _⟩ => ⟨.add, .input 19, .constant (1)⟩
  | ⟨46, _⟩ => ⟨.mul, .input 11, .previous ⟨37, by change 37 < 46; decide⟩⟩
  | ⟨47, _⟩ => ⟨.add, .previous ⟨45, by change 45 < 47; decide⟩, .previous ⟨46, by change 46 < 47; decide⟩⟩
  | ⟨48, _⟩ => ⟨.add, .previous ⟨37, by change 37 < 48; decide⟩, .previous ⟨36, by change 36 < 48; decide⟩⟩
  | ⟨49, _⟩ => ⟨.add, .input 30, .input 29⟩
  | ⟨50, _⟩ => ⟨.mul, .input 6, .input 4⟩
  | ⟨51, _⟩ => ⟨.add, .previous ⟨35, by change 35 < 51; decide⟩, .previous ⟨50, by change 50 < 51; decide⟩⟩
  | ⟨52, _⟩ => ⟨.mul, .constant (4), .input 4⟩
  | ⟨53, _⟩ => ⟨.add, .previous ⟨52, by change 52 < 53; decide⟩, .constant (3)⟩
  | ⟨54, _⟩ => ⟨.mul, .input 24, .previous ⟨53, by change 53 < 54; decide⟩⟩
  | ⟨55, _⟩ => ⟨.add, .previous ⟨51, by change 51 < 55; decide⟩, .previous ⟨54, by change 54 < 55; decide⟩⟩
  | ⟨56, _⟩ => ⟨.mul, .input 7, .input 7⟩
  | ⟨57, _⟩ => ⟨.mul, .input 4, .input 4⟩
  | ⟨58, _⟩ => ⟨.add, .previous ⟨57, by change 57 < 58; decide⟩, .previous ⟨53, by change 53 < 58; decide⟩⟩
  | ⟨59, _⟩ => ⟨.mul, .input 6, .input 6⟩
  | ⟨60, _⟩ => ⟨.mul, .previous ⟨58, by change 58 < 60; decide⟩, .previous ⟨59, by change 59 < 60; decide⟩⟩
  | ⟨61, _⟩ => ⟨.add, .previous ⟨60, by change 60 < 61; decide⟩, .constant (1)⟩
  | ⟨62, _⟩ => ⟨.mul, .input 12, .previous ⟨59, by change 59 < 62; decide⟩⟩
  | ⟨63, _⟩ => ⟨.mul, .previous ⟨62, by change 62 < 63; decide⟩, .previous ⟨62, by change 62 < 63; decide⟩⟩
  | ⟨64, _⟩ => ⟨.mul, .input 9, .input 9⟩
  | ⟨65, _⟩ => ⟨.sub, .previous ⟨64, by change 64 < 65; decide⟩, .constant (1)⟩
  | ⟨66, _⟩ => ⟨.mul, .previous ⟨58, by change 58 < 66; decide⟩, .previous ⟨65, by change 65 < 66; decide⟩⟩
  | ⟨67, _⟩ => ⟨.add, .previous ⟨45, by change 45 < 67; decide⟩, .input 19⟩
  | ⟨68, _⟩ => ⟨.mul, .input 13, .input 6⟩
  | ⟨69, _⟩ => ⟨.add, .previous ⟨67, by change 67 < 69; decide⟩, .previous ⟨68, by change 68 < 69; decide⟩⟩
  | ⟨70, _⟩ => ⟨.mul, .previous ⟨69, by change 69 < 70; decide⟩, .previous ⟨69, by change 69 < 70; decide⟩⟩
  | ⟨71, _⟩ => ⟨.mul, .input 37, .input 37⟩
  | ⟨72, _⟩ => ⟨.sub, .previous ⟨70, by change 70 < 72; decide⟩, .previous ⟨71, by change 71 < 72; decide⟩⟩
  | ⟨73, _⟩ => ⟨.mul, .previous ⟨63, by change 63 < 73; decide⟩, .previous ⟨72, by change 72 < 73; decide⟩⟩
  | ⟨74, _⟩ => ⟨.sub, .constant (1), .previous ⟨71, by change 71 < 74; decide⟩⟩
  | ⟨75, _⟩ => ⟨.mul, .input 17, .input 9⟩
  | ⟨76, _⟩ => ⟨.add, .input 6, .previous ⟨75, by change 75 < 76; decide⟩⟩
  | ⟨77, _⟩ => ⟨.sub, .input 4, .input 26⟩
  | ⟨78, _⟩ => ⟨.mul, .input 30, .previous ⟨77, by change 77 < 78; decide⟩⟩
  | ⟨79, _⟩ => ⟨.add, .input 18, .previous ⟨78, by change 78 < 79; decide⟩⟩
  | ⟨80, _⟩ => ⟨.mul, .previous ⟨77, by change 77 < 80; decide⟩, .previous ⟨77, by change 77 < 80; decide⟩⟩
  | ⟨81, _⟩ => ⟨.sub, .previous ⟨58, by change 58 < 81; decide⟩, .previous ⟨80, by change 80 < 81; decide⟩⟩
  | ⟨82, _⟩ => ⟨.mul, .input 32, .previous ⟨81, by change 81 < 82; decide⟩⟩
  | ⟨83, _⟩ => ⟨.add, .previous ⟨79, by change 79 < 83; decide⟩, .previous ⟨82, by change 82 < 83; decide⟩⟩
  | ⟨84, _⟩ => ⟨.mul, .input 31, .input 31⟩
  | ⟨85, _⟩ => ⟨.mul, .input 30, .input 30⟩
  | ⟨86, _⟩ => ⟨.mul, .previous ⟨58, by change 58 < 86; decide⟩, .previous ⟨85, by change 85 < 86; decide⟩⟩
  | ⟨87, _⟩ => ⟨.add, .previous ⟨86, by change 86 < 87; decide⟩, .constant (1)⟩
  | ⟨88, _⟩ => ⟨.mul, .input 33, .input 4⟩
  | ⟨89, _⟩ => ⟨.add, .previous ⟨88, by change 88 < 89; decide⟩, .input 3⟩
  | ⟨idx + 90, hidx⟩ => False.elim (by omega)

private def node0 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 15 : ℤ) + (inputs 36 : ℤ)

private def node1 (inputs : Fin 38 → ℕ) : ℤ :=
  node0 inputs + (inputs 23 : ℤ)

private def node2 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 0 : ℤ) + (inputs 34 : ℤ)

private def node3 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 18 : ℤ) * (inputs 18 : ℤ)

private def node4 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 26 : ℤ) * (inputs 27 : ℤ)

private def node5 (inputs : Fin 38 → ℕ) : ℤ :=
  node4 inputs + (1 : ℤ)

private def node6 (inputs : Fin 38 → ℕ) : ℤ :=
  node5 inputs + (inputs 27 : ℤ)

private def node7 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 2 : ℤ) + (inputs 5 : ℤ)

private def node8 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 8 : ℤ) * (inputs 18 : ℤ)

private def node9 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 15 : ℤ) + node8 inputs

private def node10 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 21 : ℤ) * (inputs 26 : ℤ)

private def node11 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 1 : ℤ) + node10 inputs

private def node12 (inputs : Fin 38 → ℕ) : ℤ :=
  node3 inputs * node3 inputs

private def node13 (inputs : Fin 38 → ℕ) : ℤ :=
  node12 inputs * node12 inputs

private def node14 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 8 : ℤ) - (inputs 15 : ℤ)

private def node15 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 0 : ℤ) + (inputs 10 : ℤ)

private def node16 (inputs : Fin 38 → ℕ) : ℤ :=
  node15 inputs * node15 inputs

private def node17 (inputs : Fin 38 → ℕ) : ℤ :=
  node14 inputs * node16 inputs

private def node18 (inputs : Fin 38 → ℕ) : ℤ :=
  node17 inputs * node3 inputs

private def node19 (inputs : Fin 38 → ℕ) : ℤ :=
  node9 inputs + node18 inputs

private def node20 (inputs : Fin 38 → ℕ) : ℤ :=
  node19 inputs * node3 inputs

private def node21 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 10 : ℤ) + node20 inputs

private def node22 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 16 : ℤ) * (inputs 16 : ℤ)

private def node23 (inputs : Fin 38 → ℕ) : ℤ :=
  node22 inputs - (inputs 16 : ℤ)

private def node24 (inputs : Fin 38 → ℕ) : ℤ :=
  node21 inputs * node23 inputs

private def node25 (inputs : Fin 38 → ℕ) : ℤ :=
  node5 inputs * node3 inputs

private def node26 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 26 : ℤ) * node12 inputs

private def node27 (inputs : Fin 38 → ℕ) : ℤ :=
  node26 inputs - (inputs 5 : ℤ)

private def node28 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 15 : ℤ) * node27 inputs

private def node29 (inputs : Fin 38 → ℕ) : ℤ :=
  node25 inputs + node28 inputs

private def node30 (inputs : Fin 38 → ℕ) : ℤ :=
  node22 inputs - (1 : ℤ)

private def node31 (inputs : Fin 38 → ℕ) : ℤ :=
  node29 inputs * node30 inputs

private def node32 (inputs : Fin 38 → ℕ) : ℤ :=
  node24 inputs + node31 inputs

private def node33 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 28 : ℤ) + (1 : ℤ)

private def node34 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 28 : ℤ) * node33 inputs

private def node35 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 22 : ℤ) * node22 inputs

private def node36 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 20 : ℤ) * node22 inputs

private def node37 (inputs : Fin 38 → ℕ) : ℤ :=
  node35 inputs * node36 inputs

private def node38 (inputs : Fin 38 → ℕ) : ℤ :=
  node37 inputs * node37 inputs

private def node39 (inputs : Fin 38 → ℕ) : ℤ :=
  node38 inputs + node35 inputs

private def node40 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 14 : ℤ) * node36 inputs

private def node41 (inputs : Fin 38 → ℕ) : ℤ :=
  node40 inputs * node40 inputs

private def node42 (inputs : Fin 38 → ℕ) : ℤ :=
  node39 inputs * node41 inputs

private def node43 (inputs : Fin 38 → ℕ) : ℤ :=
  node40 inputs + (inputs 25 : ℤ)

private def node44 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 25 : ℤ) + (inputs 35 : ℤ)

private def node45 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 19 : ℤ) + (1 : ℤ)

private def node46 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 11 : ℤ) * node37 inputs

private def node47 (inputs : Fin 38 → ℕ) : ℤ :=
  node45 inputs + node46 inputs

private def node48 (inputs : Fin 38 → ℕ) : ℤ :=
  node37 inputs + node36 inputs

private def node49 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 30 : ℤ) + (inputs 29 : ℤ)

private def node50 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 6 : ℤ) * (inputs 4 : ℤ)

private def node51 (inputs : Fin 38 → ℕ) : ℤ :=
  node35 inputs + node50 inputs

private def node52 (inputs : Fin 38 → ℕ) : ℤ :=
  (4 : ℤ) * (inputs 4 : ℤ)

private def node53 (inputs : Fin 38 → ℕ) : ℤ :=
  node52 inputs + (3 : ℤ)

private def node54 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 24 : ℤ) * node53 inputs

private def node55 (inputs : Fin 38 → ℕ) : ℤ :=
  node51 inputs + node54 inputs

private def node56 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 7 : ℤ) * (inputs 7 : ℤ)

private def node57 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 4 : ℤ) * (inputs 4 : ℤ)

private def node58 (inputs : Fin 38 → ℕ) : ℤ :=
  node57 inputs + node53 inputs

private def node59 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 6 : ℤ) * (inputs 6 : ℤ)

private def node60 (inputs : Fin 38 → ℕ) : ℤ :=
  node58 inputs * node59 inputs

private def node61 (inputs : Fin 38 → ℕ) : ℤ :=
  node60 inputs + (1 : ℤ)

private def node62 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 12 : ℤ) * node59 inputs

private def node63 (inputs : Fin 38 → ℕ) : ℤ :=
  node62 inputs * node62 inputs

private def node64 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 9 : ℤ) * (inputs 9 : ℤ)

private def node65 (inputs : Fin 38 → ℕ) : ℤ :=
  node64 inputs - (1 : ℤ)

private def node66 (inputs : Fin 38 → ℕ) : ℤ :=
  node58 inputs * node65 inputs

private def node67 (inputs : Fin 38 → ℕ) : ℤ :=
  node45 inputs + (inputs 19 : ℤ)

private def node68 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 13 : ℤ) * (inputs 6 : ℤ)

private def node69 (inputs : Fin 38 → ℕ) : ℤ :=
  node67 inputs + node68 inputs

private def node70 (inputs : Fin 38 → ℕ) : ℤ :=
  node69 inputs * node69 inputs

private def node71 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 37 : ℤ) * (inputs 37 : ℤ)

private def node72 (inputs : Fin 38 → ℕ) : ℤ :=
  node70 inputs - node71 inputs

private def node73 (inputs : Fin 38 → ℕ) : ℤ :=
  node63 inputs * node72 inputs

private def node74 (inputs : Fin 38 → ℕ) : ℤ :=
  (1 : ℤ) - node71 inputs

private def node75 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 17 : ℤ) * (inputs 9 : ℤ)

private def node76 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 6 : ℤ) + node75 inputs

private def node77 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 4 : ℤ) - (inputs 26 : ℤ)

private def node78 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 30 : ℤ) * node77 inputs

private def node79 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 18 : ℤ) + node78 inputs

private def node80 (inputs : Fin 38 → ℕ) : ℤ :=
  node77 inputs * node77 inputs

private def node81 (inputs : Fin 38 → ℕ) : ℤ :=
  node58 inputs - node80 inputs

private def node82 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 32 : ℤ) * node81 inputs

private def node83 (inputs : Fin 38 → ℕ) : ℤ :=
  node79 inputs + node82 inputs

private def node84 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 31 : ℤ) * (inputs 31 : ℤ)

private def node85 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 30 : ℤ) * (inputs 30 : ℤ)

private def node86 (inputs : Fin 38 → ℕ) : ℤ :=
  node58 inputs * node85 inputs

private def node87 (inputs : Fin 38 → ℕ) : ℤ :=
  node86 inputs + (1 : ℤ)

private def node88 (inputs : Fin 38 → ℕ) : ℤ :=
  (inputs 33 : ℤ) * (inputs 4 : ℤ)

private def node89 (inputs : Fin 38 → ℕ) : ℤ :=
  node88 inputs + (inputs 3 : ℤ)

/-- The canonical signed evaluation of the schedule. -/
def evaluation (inputs : Fin 38 → ℕ) : Fin 90 → ℤ
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
  | ⟨idx + 90, hidx⟩ => False.elim (by omega)

theorem evaluation_valid (inputs : Fin 38 → ℕ) :
    Valid schedule inputs (evaluation inputs) := by
  intro idx
  apply ((schedule idx).check_iff inputs _ _).mpr
  fin_cases idx <;> rfl

/-- Every valid supplied trace is the canonical evaluation. -/
theorem valid_iff_eq_evaluation (inputs : Fin 38 → ℕ) (trace : Fin 90 → ℤ) :
    Valid schedule inputs trace ↔ trace = evaluation inputs :=
  ⟨fun h => h.unique (evaluation_valid inputs), fun h => h ▸ evaluation_valid inputs⟩

theorem assignment_counts :
    operationCount schedule .add = 33 ∧ operationCount schedule .sub = 9 ∧
      operationCount schedule .mul = 48 := by
  decide +kernel

theorem check_counts :
    additionChecks schedule = 42 ∧ multiplicationChecks schedule = 48 ∧
      additionChecks schedule + multiplicationChecks schedule = 90 := by
  rcases assignment_counts with ⟨ha, hs, hm⟩
  norm_num [additionChecks, multiplicationChecks, ha, hs, hm]

/-- The twenty-two equality tests. -/
def FinalEqualities (inputs : Fin 38 → ℕ) (trace : Fin 90 → ℤ) : Prop :=
  trace 1 = (inputs 18 : ℤ) ∧
  (inputs 5 : ℤ) = trace 2 ∧
  trace 3 = trace 6 ∧
  (inputs 26 : ℤ) = trace 7 ∧
  trace 9 = trace 11 ∧
  (inputs 16 : ℤ) = trace 13 ∧
  (inputs 19 : ℤ) = trace 32 ∧
  trace 34 = trace 42 ∧
  (inputs 6 : ℤ) = trace 43 ∧
  (inputs 14 : ℤ) = trace 44 ∧
  (inputs 14 : ℤ) = trace 47 ∧
  (inputs 4 : ℤ) = trace 48 ∧
  (inputs 6 : ℤ) = trace 49 ∧
  (inputs 7 : ℤ) = trace 55 ∧
  trace 56 = trace 61 ∧
  trace 63 = trace 66 ∧
  trace 73 = trace 74 ∧
  trace 69 = trace 76 ∧
  (inputs 31 : ℤ) = trace 83 ∧
  trace 84 = trace 87 ∧
  (inputs 30 : ℤ) = trace 89 ∧
  trace 17 = (inputs 36 : ℤ)

/-! ### Reading each intermediate as a subterm of the system -/

private theorem cadd {a b a' b' : ℤ} (ha : a = a') (hb : b = b') : a + b = a' + b' := by rw [ha, hb]
private theorem csub {a b a' b' : ℤ} (ha : a = a') (hb : b = b') : a - b = a' - b' := by rw [ha, hb]
private theorem cmul {a b a' b' : ℤ} (ha : a = a') (hb : b = b') : a * b = a' * b' := by rw [ha, hb]
private theorem pw1 {u x : ℤ} (hu : u = x) : u = x ^ 1 := by rw [hu, pow_one]
private theorem pw {u v x : ℤ} (a b : ℕ) (hu : u = x ^ a) (hv : v = x ^ b) : u * v = x ^ (a + b) := by
  rw [hu, hv, pow_add]

private theorem e0_0 (inputs : Fin 38 → ℕ) :
    node0 inputs = ((inputs 15 : ℤ) + (inputs 36 : ℤ)) :=
  cadd rfl rfl

private theorem e1_1 (inputs : Fin 38 → ℕ) :
    node1 inputs = (((inputs 15 : ℤ) + (inputs 36 : ℤ)) + (inputs 23 : ℤ)) :=
  cadd (e0_0 inputs) rfl

private theorem e2_2 (inputs : Fin 38 → ℕ) :
    node2 inputs = ((inputs 0 : ℤ) + (inputs 34 : ℤ)) :=
  cadd rfl rfl

private theorem e3_3 (inputs : Fin 38 → ℕ) :
    node3 inputs = (inputs 18 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e4_4 (inputs : Fin 38 → ℕ) :
    node4 inputs = ((inputs 26 : ℤ) * (inputs 27 : ℤ)) :=
  cmul rfl rfl

private theorem e5_5 (inputs : Fin 38 → ℕ) :
    node5 inputs = (((inputs 26 : ℤ) * (inputs 27 : ℤ)) + (1 : ℤ)) :=
  cadd (e4_4 inputs) rfl

private theorem e6_6 (inputs : Fin 38 → ℕ) :
    node6 inputs = ((((inputs 26 : ℤ) * (inputs 27 : ℤ)) + (1 : ℤ)) + (inputs 27 : ℤ)) :=
  cadd (e5_5 inputs) rfl

private theorem e7_7 (inputs : Fin 38 → ℕ) :
    node7 inputs = ((inputs 2 : ℤ) + (inputs 5 : ℤ)) :=
  cadd rfl rfl

private theorem e8_8 (inputs : Fin 38 → ℕ) :
    node8 inputs = ((inputs 8 : ℤ) * (inputs 18 : ℤ)) :=
  cmul rfl rfl

private theorem e9_9 (inputs : Fin 38 → ℕ) :
    node9 inputs = ((inputs 15 : ℤ) + ((inputs 8 : ℤ) * (inputs 18 : ℤ))) :=
  cadd rfl (e8_8 inputs)

private theorem e10_10 (inputs : Fin 38 → ℕ) :
    node10 inputs = ((inputs 21 : ℤ) * (inputs 26 : ℤ)) :=
  cmul rfl rfl

private theorem e11_11 (inputs : Fin 38 → ℕ) :
    node11 inputs = ((inputs 1 : ℤ) + ((inputs 21 : ℤ) * (inputs 26 : ℤ))) :=
  cadd rfl (e10_10 inputs)

private theorem e12_12 (inputs : Fin 38 → ℕ) :
    node12 inputs = (inputs 18 : ℤ) ^ 4 :=
  pw 2 2 (e3_3 inputs) (e3_3 inputs)

private theorem e13_13 (inputs : Fin 38 → ℕ) :
    node13 inputs = (inputs 18 : ℤ) ^ 8 :=
  pw 4 4 (e12_12 inputs) (e12_12 inputs)

private theorem e14_14 (inputs : Fin 38 → ℕ) :
    node14 inputs = ((inputs 8 : ℤ) - (inputs 15 : ℤ)) :=
  csub rfl rfl

private theorem e15_15 (inputs : Fin 38 → ℕ) :
    node15 inputs = ((inputs 0 : ℤ) + (inputs 10 : ℤ)) :=
  cadd rfl rfl

private theorem e16_16 (inputs : Fin 38 → ℕ) :
    node16 inputs = ((inputs 0 : ℤ) + (inputs 10 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e15_15 inputs)) (pw1 (e15_15 inputs))

private theorem e17_17 (inputs : Fin 38 → ℕ) :
    node17 inputs = (((inputs 8 : ℤ) - (inputs 15 : ℤ)) * ((inputs 0 : ℤ) + (inputs 10 : ℤ)) ^ 2) :=
  cmul (e14_14 inputs) (e16_16 inputs)

private theorem e18_18 (inputs : Fin 38 → ℕ) :
    node18 inputs = ((((inputs 8 : ℤ) - (inputs 15 : ℤ)) * ((inputs 0 : ℤ) + (inputs 10 : ℤ)) ^ 2) * (inputs 18 : ℤ) ^ 2) :=
  cmul (e17_17 inputs) (e3_3 inputs)

private theorem e19_19 (inputs : Fin 38 → ℕ) :
    node19 inputs = (((inputs 15 : ℤ) + ((inputs 8 : ℤ) * (inputs 18 : ℤ))) + ((((inputs 8 : ℤ) - (inputs 15 : ℤ)) * ((inputs 0 : ℤ) + (inputs 10 : ℤ)) ^ 2) * (inputs 18 : ℤ) ^ 2)) :=
  cadd (e9_9 inputs) (e18_18 inputs)

private theorem e20_20 (inputs : Fin 38 → ℕ) :
    node20 inputs = ((((inputs 15 : ℤ) + ((inputs 8 : ℤ) * (inputs 18 : ℤ))) + ((((inputs 8 : ℤ) - (inputs 15 : ℤ)) * ((inputs 0 : ℤ) + (inputs 10 : ℤ)) ^ 2) * (inputs 18 : ℤ) ^ 2)) * (inputs 18 : ℤ) ^ 2) :=
  cmul (e19_19 inputs) (e3_3 inputs)

private theorem e21_21 (inputs : Fin 38 → ℕ) :
    node21 inputs = ((inputs 10 : ℤ) + ((((inputs 15 : ℤ) + ((inputs 8 : ℤ) * (inputs 18 : ℤ))) + ((((inputs 8 : ℤ) - (inputs 15 : ℤ)) * ((inputs 0 : ℤ) + (inputs 10 : ℤ)) ^ 2) * (inputs 18 : ℤ) ^ 2)) * (inputs 18 : ℤ) ^ 2)) :=
  cadd rfl (e20_20 inputs)

private theorem e22_22 (inputs : Fin 38 → ℕ) :
    node22 inputs = (inputs 16 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e23_23 (inputs : Fin 38 → ℕ) :
    node23 inputs = ((inputs 16 : ℤ) ^ 2 - (inputs 16 : ℤ)) :=
  csub (e22_22 inputs) rfl

private theorem e24_24 (inputs : Fin 38 → ℕ) :
    node24 inputs = (((inputs 10 : ℤ) + ((((inputs 15 : ℤ) + ((inputs 8 : ℤ) * (inputs 18 : ℤ))) + ((((inputs 8 : ℤ) - (inputs 15 : ℤ)) * ((inputs 0 : ℤ) + (inputs 10 : ℤ)) ^ 2) * (inputs 18 : ℤ) ^ 2)) * (inputs 18 : ℤ) ^ 2)) * ((inputs 16 : ℤ) ^ 2 - (inputs 16 : ℤ))) :=
  cmul (e21_21 inputs) (e23_23 inputs)

private theorem e25_25 (inputs : Fin 38 → ℕ) :
    node25 inputs = ((((inputs 26 : ℤ) * (inputs 27 : ℤ)) + (1 : ℤ)) * (inputs 18 : ℤ) ^ 2) :=
  cmul (e5_5 inputs) (e3_3 inputs)

private theorem e26_26 (inputs : Fin 38 → ℕ) :
    node26 inputs = ((inputs 26 : ℤ) * (inputs 18 : ℤ) ^ 4) :=
  cmul rfl (e12_12 inputs)

private theorem e27_27 (inputs : Fin 38 → ℕ) :
    node27 inputs = (((inputs 26 : ℤ) * (inputs 18 : ℤ) ^ 4) - (inputs 5 : ℤ)) :=
  csub (e26_26 inputs) rfl

private theorem e28_28 (inputs : Fin 38 → ℕ) :
    node28 inputs = ((inputs 15 : ℤ) * (((inputs 26 : ℤ) * (inputs 18 : ℤ) ^ 4) - (inputs 5 : ℤ))) :=
  cmul rfl (e27_27 inputs)

private theorem e29_29 (inputs : Fin 38 → ℕ) :
    node29 inputs = (((((inputs 26 : ℤ) * (inputs 27 : ℤ)) + (1 : ℤ)) * (inputs 18 : ℤ) ^ 2) + ((inputs 15 : ℤ) * (((inputs 26 : ℤ) * (inputs 18 : ℤ) ^ 4) - (inputs 5 : ℤ)))) :=
  cadd (e25_25 inputs) (e28_28 inputs)

private theorem e30_30 (inputs : Fin 38 → ℕ) :
    node30 inputs = ((inputs 16 : ℤ) ^ 2 - (1 : ℤ)) :=
  csub (e22_22 inputs) rfl

private theorem e31_31 (inputs : Fin 38 → ℕ) :
    node31 inputs = ((((((inputs 26 : ℤ) * (inputs 27 : ℤ)) + (1 : ℤ)) * (inputs 18 : ℤ) ^ 2) + ((inputs 15 : ℤ) * (((inputs 26 : ℤ) * (inputs 18 : ℤ) ^ 4) - (inputs 5 : ℤ)))) * ((inputs 16 : ℤ) ^ 2 - (1 : ℤ))) :=
  cmul (e29_29 inputs) (e30_30 inputs)

private theorem e32_32 (inputs : Fin 38 → ℕ) :
    node32 inputs = ((((inputs 10 : ℤ) + ((((inputs 15 : ℤ) + ((inputs 8 : ℤ) * (inputs 18 : ℤ))) + ((((inputs 8 : ℤ) - (inputs 15 : ℤ)) * ((inputs 0 : ℤ) + (inputs 10 : ℤ)) ^ 2) * (inputs 18 : ℤ) ^ 2)) * (inputs 18 : ℤ) ^ 2)) * ((inputs 16 : ℤ) ^ 2 - (inputs 16 : ℤ))) + ((((((inputs 26 : ℤ) * (inputs 27 : ℤ)) + (1 : ℤ)) * (inputs 18 : ℤ) ^ 2) + ((inputs 15 : ℤ) * (((inputs 26 : ℤ) * (inputs 18 : ℤ) ^ 4) - (inputs 5 : ℤ)))) * ((inputs 16 : ℤ) ^ 2 - (1 : ℤ)))) :=
  cadd (e24_24 inputs) (e31_31 inputs)

private theorem e33_33 (inputs : Fin 38 → ℕ) :
    node33 inputs = ((inputs 28 : ℤ) + (1 : ℤ)) :=
  cadd rfl rfl

private theorem e34_34 (inputs : Fin 38 → ℕ) :
    node34 inputs = ((inputs 28 : ℤ) * ((inputs 28 : ℤ) + (1 : ℤ))) :=
  cmul rfl (e33_33 inputs)

private theorem e35_35 (inputs : Fin 38 → ℕ) :
    node35 inputs = ((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) :=
  cmul rfl (e22_22 inputs)

private theorem e36_36 (inputs : Fin 38 → ℕ) :
    node36 inputs = ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2) :=
  cmul rfl (e22_22 inputs)

private theorem e37_37 (inputs : Fin 38 → ℕ) :
    node37 inputs = (((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) :=
  cmul (e35_35 inputs) (e36_36 inputs)

private theorem e38_38 (inputs : Fin 38 → ℕ) :
    node38 inputs = (((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) ^ 2 :=
  pw 1 1 (pw1 (e37_37 inputs)) (pw1 (e37_37 inputs))

private theorem e39_39 (inputs : Fin 38 → ℕ) :
    node39 inputs = ((((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) ^ 2 + ((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2)) :=
  cadd (e38_38 inputs) (e35_35 inputs)

private theorem e40_40 (inputs : Fin 38 → ℕ) :
    node40 inputs = ((inputs 14 : ℤ) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) :=
  cmul rfl (e36_36 inputs)

private theorem e41_41 (inputs : Fin 38 → ℕ) :
    node41 inputs = ((inputs 14 : ℤ) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) ^ 2 :=
  pw 1 1 (pw1 (e40_40 inputs)) (pw1 (e40_40 inputs))

private theorem e42_42 (inputs : Fin 38 → ℕ) :
    node42 inputs = (((((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) ^ 2 + ((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2)) * ((inputs 14 : ℤ) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) ^ 2) :=
  cmul (e39_39 inputs) (e41_41 inputs)

private theorem e43_43 (inputs : Fin 38 → ℕ) :
    node43 inputs = (((inputs 14 : ℤ) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) + (inputs 25 : ℤ)) :=
  cadd (e40_40 inputs) rfl

private theorem e44_44 (inputs : Fin 38 → ℕ) :
    node44 inputs = ((inputs 25 : ℤ) + (inputs 35 : ℤ)) :=
  cadd rfl rfl

private theorem e45_45 (inputs : Fin 38 → ℕ) :
    node45 inputs = ((inputs 19 : ℤ) + (1 : ℤ)) :=
  cadd rfl rfl

private theorem e46_46 (inputs : Fin 38 → ℕ) :
    node46 inputs = ((inputs 11 : ℤ) * (((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2))) :=
  cmul rfl (e37_37 inputs)

private theorem e47_47 (inputs : Fin 38 → ℕ) :
    node47 inputs = (((inputs 19 : ℤ) + (1 : ℤ)) + ((inputs 11 : ℤ) * (((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)))) :=
  cadd (e45_45 inputs) (e46_46 inputs)

private theorem e48_48 (inputs : Fin 38 → ℕ) :
    node48 inputs = ((((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) * ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) + ((inputs 20 : ℤ) * (inputs 16 : ℤ) ^ 2)) :=
  cadd (e37_37 inputs) (e36_36 inputs)

private theorem e49_49 (inputs : Fin 38 → ℕ) :
    node49 inputs = ((inputs 30 : ℤ) + (inputs 29 : ℤ)) :=
  cadd rfl rfl

private theorem e50_50 (inputs : Fin 38 → ℕ) :
    node50 inputs = ((inputs 6 : ℤ) * (inputs 4 : ℤ)) :=
  cmul rfl rfl

private theorem e51_51 (inputs : Fin 38 → ℕ) :
    node51 inputs = (((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) + ((inputs 6 : ℤ) * (inputs 4 : ℤ))) :=
  cadd (e35_35 inputs) (e50_50 inputs)

private theorem e52_52 (inputs : Fin 38 → ℕ) :
    node52 inputs = ((4 : ℤ) * (inputs 4 : ℤ)) :=
  cmul rfl rfl

private theorem e53_53 (inputs : Fin 38 → ℕ) :
    node53 inputs = (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ)) :=
  cadd (e52_52 inputs) rfl

private theorem e54_54 (inputs : Fin 38 → ℕ) :
    node54 inputs = ((inputs 24 : ℤ) * (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) :=
  cmul rfl (e53_53 inputs)

private theorem e55_55 (inputs : Fin 38 → ℕ) :
    node55 inputs = ((((inputs 22 : ℤ) * (inputs 16 : ℤ) ^ 2) + ((inputs 6 : ℤ) * (inputs 4 : ℤ))) + ((inputs 24 : ℤ) * (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ)))) :=
  cadd (e51_51 inputs) (e54_54 inputs)

private theorem e56_56 (inputs : Fin 38 → ℕ) :
    node56 inputs = (inputs 7 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e57_57 (inputs : Fin 38 → ℕ) :
    node57 inputs = (inputs 4 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e58_58 (inputs : Fin 38 → ℕ) :
    node58 inputs = ((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) :=
  cadd (e57_57 inputs) (e53_53 inputs)

private theorem e59_59 (inputs : Fin 38 → ℕ) :
    node59 inputs = (inputs 6 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e60_60 (inputs : Fin 38 → ℕ) :
    node60 inputs = (((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) * (inputs 6 : ℤ) ^ 2) :=
  cmul (e58_58 inputs) (e59_59 inputs)

private theorem e61_61 (inputs : Fin 38 → ℕ) :
    node61 inputs = ((((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) * (inputs 6 : ℤ) ^ 2) + (1 : ℤ)) :=
  cadd (e60_60 inputs) rfl

private theorem e62_62 (inputs : Fin 38 → ℕ) :
    node62 inputs = ((inputs 12 : ℤ) * (inputs 6 : ℤ) ^ 2) :=
  cmul rfl (e59_59 inputs)

private theorem e63_63 (inputs : Fin 38 → ℕ) :
    node63 inputs = ((inputs 12 : ℤ) * (inputs 6 : ℤ) ^ 2) ^ 2 :=
  pw 1 1 (pw1 (e62_62 inputs)) (pw1 (e62_62 inputs))

private theorem e64_64 (inputs : Fin 38 → ℕ) :
    node64 inputs = (inputs 9 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e65_65 (inputs : Fin 38 → ℕ) :
    node65 inputs = ((inputs 9 : ℤ) ^ 2 - (1 : ℤ)) :=
  csub (e64_64 inputs) rfl

private theorem e66_66 (inputs : Fin 38 → ℕ) :
    node66 inputs = (((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) * ((inputs 9 : ℤ) ^ 2 - (1 : ℤ))) :=
  cmul (e58_58 inputs) (e65_65 inputs)

private theorem e67_67 (inputs : Fin 38 → ℕ) :
    node67 inputs = (((inputs 19 : ℤ) + (1 : ℤ)) + (inputs 19 : ℤ)) :=
  cadd (e45_45 inputs) rfl

private theorem e68_68 (inputs : Fin 38 → ℕ) :
    node68 inputs = ((inputs 13 : ℤ) * (inputs 6 : ℤ)) :=
  cmul rfl rfl

private theorem e69_69 (inputs : Fin 38 → ℕ) :
    node69 inputs = ((((inputs 19 : ℤ) + (1 : ℤ)) + (inputs 19 : ℤ)) + ((inputs 13 : ℤ) * (inputs 6 : ℤ))) :=
  cadd (e67_67 inputs) (e68_68 inputs)

private theorem e70_70 (inputs : Fin 38 → ℕ) :
    node70 inputs = ((((inputs 19 : ℤ) + (1 : ℤ)) + (inputs 19 : ℤ)) + ((inputs 13 : ℤ) * (inputs 6 : ℤ))) ^ 2 :=
  pw 1 1 (pw1 (e69_69 inputs)) (pw1 (e69_69 inputs))

private theorem e71_71 (inputs : Fin 38 → ℕ) :
    node71 inputs = (inputs 37 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e72_72 (inputs : Fin 38 → ℕ) :
    node72 inputs = (((((inputs 19 : ℤ) + (1 : ℤ)) + (inputs 19 : ℤ)) + ((inputs 13 : ℤ) * (inputs 6 : ℤ))) ^ 2 - (inputs 37 : ℤ) ^ 2) :=
  csub (e70_70 inputs) (e71_71 inputs)

private theorem e73_73 (inputs : Fin 38 → ℕ) :
    node73 inputs = (((inputs 12 : ℤ) * (inputs 6 : ℤ) ^ 2) ^ 2 * (((((inputs 19 : ℤ) + (1 : ℤ)) + (inputs 19 : ℤ)) + ((inputs 13 : ℤ) * (inputs 6 : ℤ))) ^ 2 - (inputs 37 : ℤ) ^ 2)) :=
  cmul (e63_63 inputs) (e72_72 inputs)

private theorem e74_74 (inputs : Fin 38 → ℕ) :
    node74 inputs = ((1 : ℤ) - (inputs 37 : ℤ) ^ 2) :=
  csub rfl (e71_71 inputs)

private theorem e75_75 (inputs : Fin 38 → ℕ) :
    node75 inputs = ((inputs 17 : ℤ) * (inputs 9 : ℤ)) :=
  cmul rfl rfl

private theorem e76_76 (inputs : Fin 38 → ℕ) :
    node76 inputs = ((inputs 6 : ℤ) + ((inputs 17 : ℤ) * (inputs 9 : ℤ))) :=
  cadd rfl (e75_75 inputs)

private theorem e77_77 (inputs : Fin 38 → ℕ) :
    node77 inputs = ((inputs 4 : ℤ) - (inputs 26 : ℤ)) :=
  csub rfl rfl

private theorem e78_78 (inputs : Fin 38 → ℕ) :
    node78 inputs = ((inputs 30 : ℤ) * ((inputs 4 : ℤ) - (inputs 26 : ℤ))) :=
  cmul rfl (e77_77 inputs)

private theorem e79_79 (inputs : Fin 38 → ℕ) :
    node79 inputs = ((inputs 18 : ℤ) + ((inputs 30 : ℤ) * ((inputs 4 : ℤ) - (inputs 26 : ℤ)))) :=
  cadd rfl (e78_78 inputs)

private theorem e80_80 (inputs : Fin 38 → ℕ) :
    node80 inputs = ((inputs 4 : ℤ) - (inputs 26 : ℤ)) ^ 2 :=
  pw 1 1 (pw1 (e77_77 inputs)) (pw1 (e77_77 inputs))

private theorem e81_81 (inputs : Fin 38 → ℕ) :
    node81 inputs = (((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) - ((inputs 4 : ℤ) - (inputs 26 : ℤ)) ^ 2) :=
  csub (e58_58 inputs) (e80_80 inputs)

private theorem e82_82 (inputs : Fin 38 → ℕ) :
    node82 inputs = ((inputs 32 : ℤ) * (((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) - ((inputs 4 : ℤ) - (inputs 26 : ℤ)) ^ 2)) :=
  cmul rfl (e81_81 inputs)

private theorem e83_83 (inputs : Fin 38 → ℕ) :
    node83 inputs = (((inputs 18 : ℤ) + ((inputs 30 : ℤ) * ((inputs 4 : ℤ) - (inputs 26 : ℤ)))) + ((inputs 32 : ℤ) * (((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) - ((inputs 4 : ℤ) - (inputs 26 : ℤ)) ^ 2))) :=
  cadd (e79_79 inputs) (e82_82 inputs)

private theorem e84_84 (inputs : Fin 38 → ℕ) :
    node84 inputs = (inputs 31 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e85_85 (inputs : Fin 38 → ℕ) :
    node85 inputs = (inputs 30 : ℤ) ^ 2 :=
  pw 1 1 (pw1 rfl) (pw1 rfl)

private theorem e86_86 (inputs : Fin 38 → ℕ) :
    node86 inputs = (((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) * (inputs 30 : ℤ) ^ 2) :=
  cmul (e58_58 inputs) (e85_85 inputs)

private theorem e87_87 (inputs : Fin 38 → ℕ) :
    node87 inputs = ((((inputs 4 : ℤ) ^ 2 + (((4 : ℤ) * (inputs 4 : ℤ)) + (3 : ℤ))) * (inputs 30 : ℤ) ^ 2) + (1 : ℤ)) :=
  cadd (e86_86 inputs) rfl

private theorem e88_88 (inputs : Fin 38 → ℕ) :
    node88 inputs = ((inputs 33 : ℤ) * (inputs 4 : ℤ)) :=
  cmul rfl rfl

private theorem e89_89 (inputs : Fin 38 → ℕ) :
    node89 inputs = (((inputs 33 : ℤ) * (inputs 4 : ℤ)) + (inputs 3 : ℤ)) :=
  cadd (e88_88 inputs) rfl

/-- The equations as evaluated by the schedule. -/
def Printed (x V H T a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y : ℕ) : Prop :=
  (((l : ℤ) + (σ : ℤ)) + (α : ℤ)) = (q : ℤ) ∧
  (b : ℤ) = ((x : ℤ) + (β : ℤ)) ∧
  (q : ℤ) ^ 2 = ((((θ : ℤ) * (lam : ℤ)) + (1 : ℤ)) + (lam : ℤ)) ∧
  (θ : ℤ) = ((H : ℤ) + (b : ℤ)) ∧
  ((l : ℤ) + ((e : ℤ) * (q : ℤ))) = ((V : ℤ) + ((t : ℤ) * (θ : ℤ))) ∧
  (n : ℤ) = (q : ℤ) ^ 8 ∧
  (r : ℤ) = ((((g : ℤ) + ((((l : ℤ) + ((e : ℤ) * (q : ℤ))) + ((((e : ℤ) - (l : ℤ)) * ((x : ℤ) + (g : ℤ)) ^ 2) * (q : ℤ) ^ 2)) * (q : ℤ) ^ 2)) * ((n : ℤ) ^ 2 - (n : ℤ))) + ((((((θ : ℤ) * (lam : ℤ)) + (1 : ℤ)) * (q : ℤ) ^ 2) + ((l : ℤ) * (((θ : ℤ) * (q : ℤ) ^ 4) - (b : ℤ)))) * ((n : ℤ) ^ 2 - (1 : ℤ)))) ∧
  ((τ : ℤ) * ((τ : ℤ) + (1 : ℤ))) = (((((w : ℤ) * (n : ℤ) ^ 2) * ((s : ℤ) * (n : ℤ) ^ 2)) ^ 2 + ((w : ℤ) * (n : ℤ) ^ 2)) * ((k : ℤ) * ((s : ℤ) * (n : ℤ) ^ 2)) ^ 2) ∧
  (c : ℤ) = (((k : ℤ) * ((s : ℤ) * (n : ℤ) ^ 2)) + (η : ℤ)) ∧
  (k : ℤ) = ((η : ℤ) + (ζ : ℤ)) ∧
  (k : ℤ) = (((r : ℤ) + (1 : ℤ)) + ((h : ℤ) * (((w : ℤ) * (n : ℤ) ^ 2) * ((s : ℤ) * (n : ℤ) ^ 2)))) ∧
  (a : ℤ) = ((((w : ℤ) * (n : ℤ) ^ 2) * ((s : ℤ) * (n : ℤ) ^ 2)) + ((s : ℤ) * (n : ℤ) ^ 2)) ∧
  (c : ℤ) = ((κ : ℤ) + (φ : ℤ)) ∧
  (d : ℤ) = ((((w : ℤ) * (n : ℤ) ^ 2) + ((c : ℤ) * (a : ℤ))) + ((γ : ℤ) * (((4 : ℤ) * (a : ℤ)) + (3 : ℤ)))) ∧
  (d : ℤ) ^ 2 = ((((a : ℤ) ^ 2 + (((4 : ℤ) * (a : ℤ)) + (3 : ℤ))) * (c : ℤ) ^ 2) + (1 : ℤ)) ∧
  ((i : ℤ) * (c : ℤ) ^ 2) ^ 2 = (((a : ℤ) ^ 2 + (((4 : ℤ) * (a : ℤ)) + (3 : ℤ))) * ((f : ℤ) ^ 2 - (1 : ℤ))) ∧
  (((i : ℤ) * (c : ℤ) ^ 2) ^ 2 * (((((r : ℤ) + (1 : ℤ)) + (r : ℤ)) + ((j : ℤ) * (c : ℤ))) ^ 2 - (y : ℤ) ^ 2)) = ((1 : ℤ) - (y : ℤ) ^ 2) ∧
  ((((r : ℤ) + (1 : ℤ)) + (r : ℤ)) + ((j : ℤ) * (c : ℤ))) = ((c : ℤ) + ((o : ℤ) * (f : ℤ))) ∧
  (μ : ℤ) = (((q : ℤ) + ((κ : ℤ) * ((a : ℤ) - (θ : ℤ)))) + ((ρ : ℤ) * (((a : ℤ) ^ 2 + (((4 : ℤ) * (a : ℤ)) + (3 : ℤ))) - ((a : ℤ) - (θ : ℤ)) ^ 2))) ∧
  (μ : ℤ) ^ 2 = ((((a : ℤ) ^ 2 + (((4 : ℤ) * (a : ℤ)) + (3 : ℤ))) * (κ : ℤ) ^ 2) + (1 : ℤ)) ∧
  (κ : ℤ) = (((Δ : ℤ) * (a : ℤ)) + (T : ℤ)) ∧
  (((e : ℤ) - (l : ℤ)) * ((x : ℤ) + (g : ℤ)) ^ 2) = (σ : ℤ)

theorem evaluation_final_iff_printed (inputs : Fin 38 → ℕ) :
    FinalEqualities inputs (evaluation inputs) ↔ Printed (inputs 0) (inputs 1) (inputs 2) (inputs 3) (inputs 4) (inputs 5) (inputs 6) (inputs 7) (inputs 8) (inputs 9) (inputs 10) (inputs 11) (inputs 12) (inputs 13) (inputs 14) (inputs 15) (inputs 16) (inputs 17) (inputs 18) (inputs 19) (inputs 20) (inputs 21) (inputs 22) (inputs 23) (inputs 24) (inputs 25) (inputs 26) (inputs 27) (inputs 28) (inputs 29) (inputs 30) (inputs 31) (inputs 32) (inputs 33) (inputs 34) (inputs 35) (inputs 36) (inputs 37) := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
    exact ⟨(e1_1 inputs).symm.trans (h0.trans rfl),
      rfl.symm.trans (h1.trans (e2_2 inputs)),
      (e3_3 inputs).symm.trans (h2.trans (e6_6 inputs)),
      rfl.symm.trans (h3.trans (e7_7 inputs)),
      (e9_9 inputs).symm.trans (h4.trans (e11_11 inputs)),
      rfl.symm.trans (h5.trans (e13_13 inputs)),
      rfl.symm.trans (h6.trans (e32_32 inputs)),
      (e34_34 inputs).symm.trans (h7.trans (e42_42 inputs)),
      rfl.symm.trans (h8.trans (e43_43 inputs)),
      rfl.symm.trans (h9.trans (e44_44 inputs)),
      rfl.symm.trans (h10.trans (e47_47 inputs)),
      rfl.symm.trans (h11.trans (e48_48 inputs)),
      rfl.symm.trans (h12.trans (e49_49 inputs)),
      rfl.symm.trans (h13.trans (e55_55 inputs)),
      (e56_56 inputs).symm.trans (h14.trans (e61_61 inputs)),
      (e63_63 inputs).symm.trans (h15.trans (e66_66 inputs)),
      (e73_73 inputs).symm.trans (h16.trans (e74_74 inputs)),
      (e69_69 inputs).symm.trans (h17.trans (e76_76 inputs)),
      rfl.symm.trans (h18.trans (e83_83 inputs)),
      (e84_84 inputs).symm.trans (h19.trans (e87_87 inputs)),
      rfl.symm.trans (h20.trans (e89_89 inputs)),
      (e17_17 inputs).symm.trans (h21.trans rfl)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
    exact ⟨(e1_1 inputs).trans (h0.trans rfl.symm),
      rfl.trans (h1.trans (e2_2 inputs).symm),
      (e3_3 inputs).trans (h2.trans (e6_6 inputs).symm),
      rfl.trans (h3.trans (e7_7 inputs).symm),
      (e9_9 inputs).trans (h4.trans (e11_11 inputs).symm),
      rfl.trans (h5.trans (e13_13 inputs).symm),
      rfl.trans (h6.trans (e32_32 inputs).symm),
      (e34_34 inputs).trans (h7.trans (e42_42 inputs).symm),
      rfl.trans (h8.trans (e43_43 inputs).symm),
      rfl.trans (h9.trans (e44_44 inputs).symm),
      rfl.trans (h10.trans (e47_47 inputs).symm),
      rfl.trans (h11.trans (e48_48 inputs).symm),
      rfl.trans (h12.trans (e49_49 inputs).symm),
      rfl.trans (h13.trans (e55_55 inputs).symm),
      (e56_56 inputs).trans (h14.trans (e61_61 inputs).symm),
      (e63_63 inputs).trans (h15.trans (e66_66 inputs).symm),
      (e73_73 inputs).trans (h16.trans (e74_74 inputs).symm),
      (e69_69 inputs).trans (h17.trans (e76_76 inputs).symm),
      rfl.trans (h18.trans (e83_83 inputs).symm),
      (e84_84 inputs).trans (h19.trans (e87_87 inputs).symm),
      rfl.trans (h20.trans (e89_89 inputs).symm),
      (e17_17 inputs).trans (h21.trans rfl.symm)⟩

/-- The evaluated forms are equivalent to the system `Sys90` (for positive `f`, which makes the
natural subtraction `f² − 1` exact). -/
theorem printed_iff_sys90 {x V H T a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β
    ζ σ y : ℕ} (hf : 0 < f) :
    Printed x V H T a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y ↔
      Sys90 x V H T a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y := by
  have h1f : 1 ≤ f ^ 2 := Nat.one_le_pow _ _ hf
  constructor
  · rintro ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19,
      p20, p21, p22⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · zify; linear_combination p1
    · zify; linear_combination p2
    · zify; linear_combination p3 + (lam : ℤ) * p4
    · zify; linear_combination p4
    · zify; linear_combination p5
    · zify; linear_combination p6
    · linear_combination p7 + (q : ℤ) ^ 4 * ((n : ℤ) ^ 2 - n) * p22
    · zify; linear_combination p8
    · zify; linear_combination p9
    · zify; linear_combination p10
    · zify; linear_combination p11
    · zify; linear_combination p12
    · zify; linear_combination p13
    · zify; linear_combination p14
    · zify; linear_combination p15
    · zify [h1f]; linear_combination p16
    · linear_combination p17 - ((2 * (r : ℤ) + 1 + j * c) ^ 2 - (y : ℤ) ^ 2) * p16
    · zify; linear_combination p18
    · linear_combination p19 + ((ρ : ℤ) * (2 * a - θ - H - b) - κ) * p4
    · zify; linear_combination p20
    · zify; linear_combination p21
    · linear_combination -p22
  · rintro ⟨E1, E1b, E2, E3, E45, E6, E7, E9, E10a, E10b, E11, E12, E13, E14, E15, E16, E17, E17b,
      E18, E19, E20, ES⟩
    zify [h1f] at E1 E1b E2 E3 E45 E6 E9 E10a E10b E11 E12 E13 E14 E15 E16 E17b E19 E20
    exact ⟨by linear_combination E1, by linear_combination E1b,
      by linear_combination E2 - (lam : ℤ) * E3, by linear_combination E3,
      by linear_combination E45, by linear_combination E6,
      by linear_combination E7 + (q : ℤ) ^ 4 * ((n : ℤ) ^ 2 - n) * ES,
      by linear_combination E9, by linear_combination E10a, by linear_combination E10b,
      by linear_combination E11, by linear_combination E12, by linear_combination E13,
      by linear_combination E14, by linear_combination E15, by linear_combination E16,
      by linear_combination E17 + ((2 * (r : ℤ) + 1 + j * c) ^ 2 - (y : ℤ) ^ 2) * E16,
      by linear_combination E17b,
      by linear_combination E18 - ((ρ : ℤ) * (2 * a - θ - H - b) - κ) * E3,
      by linear_combination E19, by linear_combination E20, by linear_combination -ES⟩

/-- A certificate for `Solvable90 x V H Tindex`: the inputs start with `x, V, H, Tindex`, the
other 34 inputs are positive, the trace is a valid run of the schedule, and the 22 equality
tests pass. -/
def Certificate (x V H Tindex : ℕ) (inputs : Fin 38 → ℕ) (trace : Fin 90 → ℤ) : Prop :=
  inputs 0 = x ∧ inputs 1 = V ∧ inputs 2 = H ∧ inputs 3 = Tindex ∧
    (∀ idx : Fin 38, 4 ≤ idx.val → 0 < inputs idx) ∧
    Valid schedule inputs trace ∧ FinalEqualities inputs trace

theorem solvable90_iff_certificate (x V H Tindex : ℕ) :
    Solvable90 x V H Tindex ↔
      ∃ (inputs : Fin 38 → ℕ) (trace : Fin 90 → ℤ), Certificate x V H Tindex inputs trace := by
  constructor
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, k, l, n, o, q, r, s, t, w, α, γ, η, θ, lam, τ, φ, κ, μ,
      ρ, Δ, β, ζ, σ, y, ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl, hn, ho, hq, hr, hs, ht,
      hw, hα, hγ, hη, hθ, hlam, hτ, hφ, hκ, hμ, hρ, hΔ, hβ, hζ, hσ, hy, S⟩
    let inputs : Fin 38 → ℕ := ![x, V, H, Tindex, a, b, c, d, e, f, g, h, i, j, k, l, n, o, q, r,
      s, t, w, α, γ, η, θ, lam, τ, φ, κ, μ, ρ, Δ, β, ζ, σ, y]
    refine ⟨inputs, evaluation inputs, rfl, rfl, rfl, rfl, ?_, evaluation_valid inputs,
      (evaluation_final_iff_printed inputs).mpr ((printed_iff_sys90 hf).mpr S)⟩
    intro idx hidx
    fin_cases idx <;> first | exact absurd hidx (by decide) | assumption
  · rintro ⟨inputs, trace, rfl, rfl, rfl, rfl, hpos, hv, hfin⟩
    rw [(valid_iff_eq_evaluation inputs trace).mp hv] at hfin
    have hp := fun k (hk : k < 38) (h4 : 4 ≤ k) => hpos ⟨k, hk⟩ h4
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, hp 4 (by decide) (by decide), hp 5 (by decide) (by decide),
      hp 6 (by decide) (by decide), hp 7 (by decide) (by decide), hp 8 (by decide) (by decide),
      hp 9 (by decide) (by decide), hp 10 (by decide) (by decide),
      hp 11 (by decide) (by decide), hp 12 (by decide) (by decide),
      hp 13 (by decide) (by decide), hp 14 (by decide) (by decide),
      hp 15 (by decide) (by decide), hp 16 (by decide) (by decide),
      hp 17 (by decide) (by decide), hp 18 (by decide) (by decide),
      hp 19 (by decide) (by decide), hp 20 (by decide) (by decide),
      hp 21 (by decide) (by decide), hp 22 (by decide) (by decide),
      hp 23 (by decide) (by decide), hp 24 (by decide) (by decide),
      hp 25 (by decide) (by decide), hp 26 (by decide) (by decide),
      hp 27 (by decide) (by decide), hp 28 (by decide) (by decide),
      hp 29 (by decide) (by decide), hp 30 (by decide) (by decide),
      hp 31 (by decide) (by decide), hp 32 (by decide) (by decide),
      hp 33 (by decide) (by decide), hp 34 (by decide) (by decide),
      hp 35 (by decide) (by decide), hp 36 (by decide) (by decide),
      hp 37 (by decide) (by decide),
      (printed_iff_sys90 (hp 9 (by decide) (by decide))).mp
        ((evaluation_final_iff_printed inputs).mp hfin)⟩

end Jones1982.OperationCount

namespace Jones1982

open Diophantine.ArithmeticCertificate in
/-- **Theorem 5**, with the operation count: one fixed schedule of at most 100 additions and
multiplications (here 42 + 48 = 90) checks membership certificates for every recursively
enumerable set.  For each such `S` there is an index `(V, H, Tindex)` so that a positive `x` is
in `S` iff there is a certificate: natural inputs `x, V, H, Tindex` and 34 positive unknowns, a
valid trace, and 22 passing equality tests. -/
theorem theorem_5_operations :
    additionChecks OperationCount.schedule + multiplicationChecks OperationCount.schedule ≤ 100 ∧
      ∀ {S : Set ℕ}, REPred S → ∃ V H Tindex : ℕ, ∀ x : ℕ, 0 < x →
        (x ∈ S ↔ ∃ inputs trace, OperationCount.Certificate x V H Tindex inputs trace) := by
  refine ⟨by rw [OperationCount.check_counts.2.2]; norm_num, fun hS => ?_⟩
  obtain ⟨V, H, Tindex, h⟩ := Jones1980.universal90_re hS
  exact ⟨V, H, Tindex, fun x hx =>
    (h x hx).trans (OperationCount.solvable90_iff_certificate x V H Tindex)⟩

end Jones1982
