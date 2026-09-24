import Diophantine.Common.ArithmeticCertificate
import Diophantine.Paper1976.Theorem212

/-!
# JSWW 1976, Theorem 5: an explicit 87-operation primality certificate

The schedule is the independently reconstructed certificate in
`Papers/verification/jones1976_primality87.json`, with inputs `a, …, z` in that order.
The 87 intermediate values are signed integers. Each instruction is checked
by one addition or multiplication; subtraction uses `out + rhs = lhs`.
The fourteen source equations and the candidate comparison are equality
tests. The latter reads the existing intermediate `kp1 = k + 1`.

This proves an arithmetic certificate bound. It makes no claim about bit
complexity, finding witnesses, optimality, or the authors' evaluation order.
-/

namespace JSWW1976.PrimalityCertificate

open Diophantine.ArithmeticCertificate

/-- The literal schedule: a previous-result operand is bounded by its step index. -/
def schedule : Schedule 26 87
  | ⟨0, _⟩ => ⟨.add, .input 7, .input 9⟩ -- hj
  | ⟨1, _⟩ => ⟨.mul, .input 22, .input 25⟩ -- wz
  | ⟨2, _⟩ => ⟨.add, .previous ⟨1, by change 1 < 2; decide⟩, .previous ⟨0, by change 0 < 2; decide⟩⟩ -- rhs1
  | ⟨3, _⟩ => ⟨.mul, .input 6, .input 10⟩ -- gk
  | ⟨4, _⟩ => ⟨.add, .previous ⟨3, by change 3 < 4; decide⟩, .input 6⟩ -- gkg
  | ⟨5, _⟩ => ⟨.add, .previous ⟨4, by change 4 < 5; decide⟩, .input 10⟩ -- gkgk
  | ⟨6, _⟩ => ⟨.mul, .previous ⟨5, by change 5 < 6; decide⟩, .previous ⟨0, by change 0 < 6; decide⟩⟩ -- zprod
  | ⟨7, _⟩ => ⟨.add, .previous ⟨6, by change 6 < 7; decide⟩, .input 7⟩ -- rhs2
  | ⟨8, _⟩ => ⟨.add, .input 10, .constant 1⟩ -- kp1
  | ⟨9, _⟩ => ⟨.add, .input 13, .constant 1⟩ -- np1
  | ⟨10, _⟩ => ⟨.mul, .constant 4, .input 10⟩ -- fourk
  | ⟨11, _⟩ => ⟨.mul, .previous ⟨10, by change 10 < 11; decide⟩, .previous ⟨9, by change 9 < 11; decide⟩⟩ -- fourkn
  | ⟨12, _⟩ => ⟨.mul, .previous ⟨11, by change 11 < 12; decide⟩, .previous ⟨11, by change 11 < 12; decide⟩⟩ -- fourkn2
  | ⟨13, _⟩ => ⟨.mul, .input 10, .previous ⟨8, by change 8 < 13; decide⟩⟩ -- kkp1
  | ⟨14, _⟩ => ⟨.mul, .previous ⟨13, by change 13 < 14; decide⟩, .previous ⟨12, by change 12 < 14; decide⟩⟩ -- fprod
  | ⟨15, _⟩ => ⟨.add, .previous ⟨14, by change 14 < 15; decide⟩, .constant 1⟩ -- rhs3
  | ⟨16, _⟩ => ⟨.mul, .input 5, .input 5⟩ -- lhs3
  | ⟨17, _⟩ => ⟨.mul, .constant 2, .input 13⟩ -- twon
  | ⟨18, _⟩ => ⟨.add, .input 15, .input 16⟩ -- pq
  | ⟨19, _⟩ => ⟨.add, .previous ⟨18, by change 18 < 19; decide⟩, .input 25⟩ -- pqz
  | ⟨20, _⟩ => ⟨.add, .previous ⟨19, by change 19 < 20; decide⟩, .previous ⟨17, by change 17 < 20; decide⟩⟩ -- rhs4
  | ⟨21, _⟩ => ⟨.add, .input 0, .constant 1⟩ -- ap1
  | ⟨22, _⟩ => ⟨.add, .input 4, .constant 2⟩ -- ep2
  | ⟨23, _⟩ => ⟨.mul, .input 4, .previous ⟨21, by change 21 < 23; decide⟩⟩ -- eap1
  | ⟨24, _⟩ => ⟨.mul, .previous ⟨23, by change 23 < 24; decide⟩, .previous ⟨23, by change 23 < 24; decide⟩⟩ -- eap12
  | ⟨25, _⟩ => ⟨.mul, .input 4, .previous ⟨22, by change 22 < 25; decide⟩⟩ -- eep2
  | ⟨26, _⟩ => ⟨.mul, .previous ⟨25, by change 25 < 26; decide⟩, .previous ⟨24, by change 24 < 26; decide⟩⟩ -- oprod
  | ⟨27, _⟩ => ⟨.add, .previous ⟨26, by change 26 < 27; decide⟩, .constant 1⟩ -- rhs5
  | ⟨28, _⟩ => ⟨.mul, .input 14, .input 14⟩ -- lhs5
  | ⟨29, _⟩ => ⟨.mul, .input 0, .input 0⟩ -- a2
  | ⟨30, _⟩ => ⟨.sub, .previous ⟨29, by change 29 < 30; decide⟩, .constant 1⟩ -- A
  | ⟨31, _⟩ => ⟨.mul, .input 24, .input 24⟩ -- y2
  | ⟨32, _⟩ => ⟨.mul, .previous ⟨30, by change 30 < 32; decide⟩, .previous ⟨31, by change 31 < 32; decide⟩⟩ -- xprod
  | ⟨33, _⟩ => ⟨.add, .previous ⟨32, by change 32 < 33; decide⟩, .constant 1⟩ -- rhs6
  | ⟨34, _⟩ => ⟨.mul, .input 23, .input 23⟩ -- lhs6
  | ⟨35, _⟩ => ⟨.mul, .input 17, .previous ⟨31, by change 31 < 35; decide⟩⟩ -- ry2
  | ⟨36, _⟩ => ⟨.mul, .constant 4, .previous ⟨35, by change 35 < 36; decide⟩⟩ -- fourry2
  | ⟨37, _⟩ => ⟨.mul, .previous ⟨36, by change 36 < 37; decide⟩, .previous ⟨36, by change 36 < 37; decide⟩⟩ -- fourry22
  | ⟨38, _⟩ => ⟨.mul, .previous ⟨30, by change 30 < 38; decide⟩, .previous ⟨37, by change 37 < 38; decide⟩⟩ -- uprod
  | ⟨39, _⟩ => ⟨.add, .previous ⟨38, by change 38 < 39; decide⟩, .constant 1⟩ -- rhs7
  | ⟨40, _⟩ => ⟨.mul, .input 20, .input 20⟩ -- u2
  | ⟨41, _⟩ => ⟨.mul, .input 2, .input 20⟩ -- cu
  | ⟨42, _⟩ => ⟨.add, .input 23, .previous ⟨41, by change 41 < 42; decide⟩⟩ -- xcu
  | ⟨43, _⟩ => ⟨.mul, .previous ⟨42, by change 42 < 43; decide⟩, .previous ⟨42, by change 42 < 43; decide⟩⟩ -- lhs8
  | ⟨44, _⟩ => ⟨.sub, .previous ⟨40, by change 40 < 44; decide⟩, .input 0⟩ -- u2a
  | ⟨45, _⟩ => ⟨.mul, .previous ⟨40, by change 40 < 45; decide⟩, .previous ⟨44, by change 44 < 45; decide⟩⟩ -- u2u2a
  | ⟨46, _⟩ => ⟨.add, .input 0, .previous ⟨45, by change 45 < 46; decide⟩⟩ -- G
  | ⟨47, _⟩ => ⟨.mul, .previous ⟨46, by change 46 < 47; decide⟩, .previous ⟨46, by change 46 < 47; decide⟩⟩ -- G2
  | ⟨48, _⟩ => ⟨.sub, .previous ⟨47, by change 47 < 48; decide⟩, .constant 1⟩ -- G2m1
  | ⟨49, _⟩ => ⟨.mul, .input 3, .input 24⟩ -- dy
  | ⟨50, _⟩ => ⟨.mul, .constant 4, .previous ⟨49, by change 49 < 50; decide⟩⟩ -- fourdy
  | ⟨51, _⟩ => ⟨.add, .input 13, .previous ⟨50, by change 50 < 51; decide⟩⟩ -- nfourdy
  | ⟨52, _⟩ => ⟨.mul, .previous ⟨51, by change 51 < 52; decide⟩, .previous ⟨51, by change 51 < 52; decide⟩⟩ -- nfourdy2
  | ⟨53, _⟩ => ⟨.mul, .previous ⟨48, by change 48 < 53; decide⟩, .previous ⟨52, by change 52 < 53; decide⟩⟩ -- gprod
  | ⟨54, _⟩ => ⟨.add, .previous ⟨53, by change 53 < 54; decide⟩, .constant 1⟩ -- rhs8
  | ⟨55, _⟩ => ⟨.mul, .input 11, .input 11⟩ -- l2
  | ⟨56, _⟩ => ⟨.mul, .previous ⟨30, by change 30 < 56; decide⟩, .previous ⟨55, by change 55 < 56; decide⟩⟩ -- mprod
  | ⟨57, _⟩ => ⟨.add, .previous ⟨56, by change 56 < 57; decide⟩, .constant 1⟩ -- rhs9
  | ⟨58, _⟩ => ⟨.mul, .input 12, .input 12⟩ -- lhs9
  | ⟨59, _⟩ => ⟨.sub, .input 0, .constant 1⟩ -- am1
  | ⟨60, _⟩ => ⟨.mul, .input 8, .previous ⟨59, by change 59 < 60; decide⟩⟩ -- iam1
  | ⟨61, _⟩ => ⟨.add, .input 10, .previous ⟨60, by change 60 < 61; decide⟩⟩ -- rhs10
  | ⟨62, _⟩ => ⟨.add, .input 13, .input 11⟩ -- nl
  | ⟨63, _⟩ => ⟨.add, .previous ⟨62, by change 62 < 63; decide⟩, .input 21⟩ -- rhs11
  | ⟨64, _⟩ => ⟨.sub, .input 0, .previous ⟨9, by change 9 < 64; decide⟩⟩ -- an
  | ⟨65, _⟩ => ⟨.mul, .previous ⟨64, by change 64 < 65; decide⟩, .previous ⟨64, by change 64 < 65; decide⟩⟩ -- an2
  | ⟨66, _⟩ => ⟨.sub, .previous ⟨30, by change 30 < 66; decide⟩, .previous ⟨65, by change 65 < 66; decide⟩⟩ -- Dn
  | ⟨67, _⟩ => ⟨.mul, .input 1, .previous ⟨66, by change 66 < 67; decide⟩⟩ -- bDn
  | ⟨68, _⟩ => ⟨.mul, .input 11, .previous ⟨64, by change 64 < 68; decide⟩⟩ -- lan
  | ⟨69, _⟩ => ⟨.add, .input 15, .previous ⟨68, by change 68 < 69; decide⟩⟩ -- pla
  | ⟨70, _⟩ => ⟨.add, .previous ⟨69, by change 69 < 70; decide⟩, .previous ⟨67, by change 67 < 70; decide⟩⟩ -- rhs12
  | ⟨71, _⟩ => ⟨.sub, .input 0, .input 15⟩ -- ap
  | ⟨72, _⟩ => ⟨.sub, .previous ⟨71, by change 71 < 72; decide⟩, .constant 1⟩ -- app
  | ⟨73, _⟩ => ⟨.mul, .previous ⟨72, by change 72 < 73; decide⟩, .previous ⟨72, by change 72 < 73; decide⟩⟩ -- app2
  | ⟨74, _⟩ => ⟨.sub, .previous ⟨30, by change 30 < 74; decide⟩, .previous ⟨73, by change 73 < 74; decide⟩⟩ -- Dpp
  | ⟨75, _⟩ => ⟨.mul, .input 18, .previous ⟨74, by change 74 < 75; decide⟩⟩ -- sDpp
  | ⟨76, _⟩ => ⟨.mul, .input 24, .previous ⟨72, by change 72 < 76; decide⟩⟩ -- yapp
  | ⟨77, _⟩ => ⟨.add, .input 16, .previous ⟨76, by change 76 < 77; decide⟩⟩ -- qyapp
  | ⟨78, _⟩ => ⟨.add, .previous ⟨77, by change 77 < 78; decide⟩, .previous ⟨75, by change 75 < 78; decide⟩⟩ -- rhs13
  | ⟨79, _⟩ => ⟨.mul, .previous ⟨71, by change 71 < 79; decide⟩, .previous ⟨71, by change 71 < 79; decide⟩⟩ -- ap2
  | ⟨80, _⟩ => ⟨.sub, .previous ⟨30, by change 30 < 80; decide⟩, .previous ⟨79, by change 79 < 80; decide⟩⟩ -- Dp
  | ⟨81, _⟩ => ⟨.mul, .input 19, .previous ⟨80, by change 80 < 81; decide⟩⟩ -- tDp
  | ⟨82, _⟩ => ⟨.mul, .input 15, .input 11⟩ -- pl
  | ⟨83, _⟩ => ⟨.mul, .previous ⟨82, by change 82 < 83; decide⟩, .previous ⟨71, by change 71 < 83; decide⟩⟩ -- plap
  | ⟨84, _⟩ => ⟨.add, .input 25, .previous ⟨83, by change 83 < 84; decide⟩⟩ -- zplap
  | ⟨85, _⟩ => ⟨.add, .previous ⟨84, by change 84 < 85; decide⟩, .previous ⟨81, by change 81 < 85; decide⟩⟩ -- rhs14
  | ⟨86, _⟩ => ⟨.mul, .input 15, .input 12⟩ -- lhs14
  | ⟨idx + 87, hidx⟩ => False.elim (by omega)

private def node1 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 7 : ℤ) + (inputs 9 : ℤ) -- hj

private def node2 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 22 : ℤ) * (inputs 25 : ℤ) -- wz

private def node3 (inputs : Fin 26 → ℕ) : ℤ :=
  node2 inputs + node1 inputs -- rhs1

private def node4 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 6 : ℤ) * (inputs 10 : ℤ) -- gk

private def node5 (inputs : Fin 26 → ℕ) : ℤ :=
  node4 inputs + (inputs 6 : ℤ) -- gkg

private def node6 (inputs : Fin 26 → ℕ) : ℤ :=
  node5 inputs + (inputs 10 : ℤ) -- gkgk

private def node7 (inputs : Fin 26 → ℕ) : ℤ :=
  node6 inputs * node1 inputs -- zprod

private def node8 (inputs : Fin 26 → ℕ) : ℤ :=
  node7 inputs + (inputs 7 : ℤ) -- rhs2

private def node9 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 10 : ℤ) + 1 -- kp1

private def node10 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 13 : ℤ) + 1 -- np1

private def node11 (inputs : Fin 26 → ℕ) : ℤ :=
  4 * (inputs 10 : ℤ) -- fourk

private def node12 (inputs : Fin 26 → ℕ) : ℤ :=
  node11 inputs * node10 inputs -- fourkn

private def node13 (inputs : Fin 26 → ℕ) : ℤ :=
  node12 inputs * node12 inputs -- fourkn2

private def node14 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 10 : ℤ) * node9 inputs -- kkp1

private def node15 (inputs : Fin 26 → ℕ) : ℤ :=
  node14 inputs * node13 inputs -- fprod

private def node16 (inputs : Fin 26 → ℕ) : ℤ :=
  node15 inputs + 1 -- rhs3

private def node17 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 5 : ℤ) * (inputs 5 : ℤ) -- lhs3

private def node18 (inputs : Fin 26 → ℕ) : ℤ :=
  2 * (inputs 13 : ℤ) -- twon

private def node19 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 15 : ℤ) + (inputs 16 : ℤ) -- pq

private def node20 (inputs : Fin 26 → ℕ) : ℤ :=
  node19 inputs + (inputs 25 : ℤ) -- pqz

private def node21 (inputs : Fin 26 → ℕ) : ℤ :=
  node20 inputs + node18 inputs -- rhs4

private def node22 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 0 : ℤ) + 1 -- ap1

private def node23 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 4 : ℤ) + 2 -- ep2

private def node24 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 4 : ℤ) * node22 inputs -- eap1

private def node25 (inputs : Fin 26 → ℕ) : ℤ :=
  node24 inputs * node24 inputs -- eap12

private def node26 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 4 : ℤ) * node23 inputs -- eep2

private def node27 (inputs : Fin 26 → ℕ) : ℤ :=
  node26 inputs * node25 inputs -- oprod

private def node28 (inputs : Fin 26 → ℕ) : ℤ :=
  node27 inputs + 1 -- rhs5

private def node29 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 14 : ℤ) * (inputs 14 : ℤ) -- lhs5

private def node30 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 0 : ℤ) * (inputs 0 : ℤ) -- a2

private def node31 (inputs : Fin 26 → ℕ) : ℤ :=
  node30 inputs - 1 -- A

private def node32 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 24 : ℤ) * (inputs 24 : ℤ) -- y2

private def node33 (inputs : Fin 26 → ℕ) : ℤ :=
  node31 inputs * node32 inputs -- xprod

private def node34 (inputs : Fin 26 → ℕ) : ℤ :=
  node33 inputs + 1 -- rhs6

private def node35 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 23 : ℤ) * (inputs 23 : ℤ) -- lhs6

private def node36 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 17 : ℤ) * node32 inputs -- ry2

private def node37 (inputs : Fin 26 → ℕ) : ℤ :=
  4 * node36 inputs -- fourry2

private def node38 (inputs : Fin 26 → ℕ) : ℤ :=
  node37 inputs * node37 inputs -- fourry22

private def node39 (inputs : Fin 26 → ℕ) : ℤ :=
  node31 inputs * node38 inputs -- uprod

private def node40 (inputs : Fin 26 → ℕ) : ℤ :=
  node39 inputs + 1 -- rhs7

private def node41 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 20 : ℤ) * (inputs 20 : ℤ) -- u2

private def node42 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 2 : ℤ) * (inputs 20 : ℤ) -- cu

private def node43 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 23 : ℤ) + node42 inputs -- xcu

private def node44 (inputs : Fin 26 → ℕ) : ℤ :=
  node43 inputs * node43 inputs -- lhs8

private def node45 (inputs : Fin 26 → ℕ) : ℤ :=
  node41 inputs - (inputs 0 : ℤ) -- u2a

private def node46 (inputs : Fin 26 → ℕ) : ℤ :=
  node41 inputs * node45 inputs -- u2u2a

private def node47 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 0 : ℤ) + node46 inputs -- G

private def node48 (inputs : Fin 26 → ℕ) : ℤ :=
  node47 inputs * node47 inputs -- G2

private def node49 (inputs : Fin 26 → ℕ) : ℤ :=
  node48 inputs - 1 -- G2m1

private def node50 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 3 : ℤ) * (inputs 24 : ℤ) -- dy

private def node51 (inputs : Fin 26 → ℕ) : ℤ :=
  4 * node50 inputs -- fourdy

private def node52 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 13 : ℤ) + node51 inputs -- nfourdy

private def node53 (inputs : Fin 26 → ℕ) : ℤ :=
  node52 inputs * node52 inputs -- nfourdy2

private def node54 (inputs : Fin 26 → ℕ) : ℤ :=
  node49 inputs * node53 inputs -- gprod

private def node55 (inputs : Fin 26 → ℕ) : ℤ :=
  node54 inputs + 1 -- rhs8

private def node56 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 11 : ℤ) * (inputs 11 : ℤ) -- l2

private def node57 (inputs : Fin 26 → ℕ) : ℤ :=
  node31 inputs * node56 inputs -- mprod

private def node58 (inputs : Fin 26 → ℕ) : ℤ :=
  node57 inputs + 1 -- rhs9

private def node59 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 12 : ℤ) * (inputs 12 : ℤ) -- lhs9

private def node60 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 0 : ℤ) - 1 -- am1

private def node61 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 8 : ℤ) * node60 inputs -- iam1

private def node62 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 10 : ℤ) + node61 inputs -- rhs10

private def node63 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 13 : ℤ) + (inputs 11 : ℤ) -- nl

private def node64 (inputs : Fin 26 → ℕ) : ℤ :=
  node63 inputs + (inputs 21 : ℤ) -- rhs11

private def node65 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 0 : ℤ) - node10 inputs -- an

private def node66 (inputs : Fin 26 → ℕ) : ℤ :=
  node65 inputs * node65 inputs -- an2

private def node67 (inputs : Fin 26 → ℕ) : ℤ :=
  node31 inputs - node66 inputs -- Dn

private def node68 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 1 : ℤ) * node67 inputs -- bDn

private def node69 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 11 : ℤ) * node65 inputs -- lan

private def node70 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 15 : ℤ) + node69 inputs -- pla

private def node71 (inputs : Fin 26 → ℕ) : ℤ :=
  node70 inputs + node68 inputs -- rhs12

private def node72 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 0 : ℤ) - (inputs 15 : ℤ) -- ap

private def node73 (inputs : Fin 26 → ℕ) : ℤ :=
  node72 inputs - 1 -- app

private def node74 (inputs : Fin 26 → ℕ) : ℤ :=
  node73 inputs * node73 inputs -- app2

private def node75 (inputs : Fin 26 → ℕ) : ℤ :=
  node31 inputs - node74 inputs -- Dpp

private def node76 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 18 : ℤ) * node75 inputs -- sDpp

private def node77 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 24 : ℤ) * node73 inputs -- yapp

private def node78 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 16 : ℤ) + node77 inputs -- qyapp

private def node79 (inputs : Fin 26 → ℕ) : ℤ :=
  node78 inputs + node76 inputs -- rhs13

private def node80 (inputs : Fin 26 → ℕ) : ℤ :=
  node72 inputs * node72 inputs -- ap2

private def node81 (inputs : Fin 26 → ℕ) : ℤ :=
  node31 inputs - node80 inputs -- Dp

private def node82 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 19 : ℤ) * node81 inputs -- tDp

private def node83 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 15 : ℤ) * (inputs 11 : ℤ) -- pl

private def node84 (inputs : Fin 26 → ℕ) : ℤ :=
  node83 inputs * node72 inputs -- plap

private def node85 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 25 : ℤ) + node84 inputs -- zplap

private def node86 (inputs : Fin 26 → ℕ) : ℤ :=
  node85 inputs + node82 inputs -- rhs14

private def node87 (inputs : Fin 26 → ℕ) : ℤ :=
  (inputs 15 : ℤ) * (inputs 12 : ℤ) -- lhs14

/-- Canonical signed evaluation, with one coordinate for each schedule instruction. -/
def evaluation (inputs : Fin 26 → ℕ) : Fin 87 → ℤ
  | ⟨0, _⟩ => node1 inputs
  | ⟨1, _⟩ => node2 inputs
  | ⟨2, _⟩ => node3 inputs
  | ⟨3, _⟩ => node4 inputs
  | ⟨4, _⟩ => node5 inputs
  | ⟨5, _⟩ => node6 inputs
  | ⟨6, _⟩ => node7 inputs
  | ⟨7, _⟩ => node8 inputs
  | ⟨8, _⟩ => node9 inputs
  | ⟨9, _⟩ => node10 inputs
  | ⟨10, _⟩ => node11 inputs
  | ⟨11, _⟩ => node12 inputs
  | ⟨12, _⟩ => node13 inputs
  | ⟨13, _⟩ => node14 inputs
  | ⟨14, _⟩ => node15 inputs
  | ⟨15, _⟩ => node16 inputs
  | ⟨16, _⟩ => node17 inputs
  | ⟨17, _⟩ => node18 inputs
  | ⟨18, _⟩ => node19 inputs
  | ⟨19, _⟩ => node20 inputs
  | ⟨20, _⟩ => node21 inputs
  | ⟨21, _⟩ => node22 inputs
  | ⟨22, _⟩ => node23 inputs
  | ⟨23, _⟩ => node24 inputs
  | ⟨24, _⟩ => node25 inputs
  | ⟨25, _⟩ => node26 inputs
  | ⟨26, _⟩ => node27 inputs
  | ⟨27, _⟩ => node28 inputs
  | ⟨28, _⟩ => node29 inputs
  | ⟨29, _⟩ => node30 inputs
  | ⟨30, _⟩ => node31 inputs
  | ⟨31, _⟩ => node32 inputs
  | ⟨32, _⟩ => node33 inputs
  | ⟨33, _⟩ => node34 inputs
  | ⟨34, _⟩ => node35 inputs
  | ⟨35, _⟩ => node36 inputs
  | ⟨36, _⟩ => node37 inputs
  | ⟨37, _⟩ => node38 inputs
  | ⟨38, _⟩ => node39 inputs
  | ⟨39, _⟩ => node40 inputs
  | ⟨40, _⟩ => node41 inputs
  | ⟨41, _⟩ => node42 inputs
  | ⟨42, _⟩ => node43 inputs
  | ⟨43, _⟩ => node44 inputs
  | ⟨44, _⟩ => node45 inputs
  | ⟨45, _⟩ => node46 inputs
  | ⟨46, _⟩ => node47 inputs
  | ⟨47, _⟩ => node48 inputs
  | ⟨48, _⟩ => node49 inputs
  | ⟨49, _⟩ => node50 inputs
  | ⟨50, _⟩ => node51 inputs
  | ⟨51, _⟩ => node52 inputs
  | ⟨52, _⟩ => node53 inputs
  | ⟨53, _⟩ => node54 inputs
  | ⟨54, _⟩ => node55 inputs
  | ⟨55, _⟩ => node56 inputs
  | ⟨56, _⟩ => node57 inputs
  | ⟨57, _⟩ => node58 inputs
  | ⟨58, _⟩ => node59 inputs
  | ⟨59, _⟩ => node60 inputs
  | ⟨60, _⟩ => node61 inputs
  | ⟨61, _⟩ => node62 inputs
  | ⟨62, _⟩ => node63 inputs
  | ⟨63, _⟩ => node64 inputs
  | ⟨64, _⟩ => node65 inputs
  | ⟨65, _⟩ => node66 inputs
  | ⟨66, _⟩ => node67 inputs
  | ⟨67, _⟩ => node68 inputs
  | ⟨68, _⟩ => node69 inputs
  | ⟨69, _⟩ => node70 inputs
  | ⟨70, _⟩ => node71 inputs
  | ⟨71, _⟩ => node72 inputs
  | ⟨72, _⟩ => node73 inputs
  | ⟨73, _⟩ => node74 inputs
  | ⟨74, _⟩ => node75 inputs
  | ⟨75, _⟩ => node76 inputs
  | ⟨76, _⟩ => node77 inputs
  | ⟨77, _⟩ => node78 inputs
  | ⟨78, _⟩ => node79 inputs
  | ⟨79, _⟩ => node80 inputs
  | ⟨80, _⟩ => node81 inputs
  | ⟨81, _⟩ => node82 inputs
  | ⟨82, _⟩ => node83 inputs
  | ⟨83, _⟩ => node84 inputs
  | ⟨84, _⟩ => node85 inputs
  | ⟨85, _⟩ => node86 inputs
  | ⟨86, _⟩ => node87 inputs
  | ⟨idx + 87, hidx⟩ => False.elim (by omega)

theorem evaluation_valid (inputs : Fin 26 → ℕ) :
    Valid schedule inputs (evaluation inputs) := by
  intro idx
  apply ((schedule idx).check_iff inputs _ _).mpr
  fin_cases idx <;> rfl

/-- Every valid supplied trace equals the canonical evaluation, including subtraction nodes. -/
theorem valid_iff_eq_evaluation (inputs : Fin 26 → ℕ) (trace : Fin 87 → ℤ) :
    Valid schedule inputs trace ↔ trace = evaluation inputs := by
  constructor
  · intro htrace
    exact htrace.unique (evaluation_valid inputs)
  · rintro rfl
    exact evaluation_valid inputs

theorem assignment_counts :
    operationCount schedule .add = 30 ∧ operationCount schedule .sub = 10 ∧
      operationCount schedule .mul = 47 := by
  decide

theorem check_counts :
    additionChecks schedule = 40 ∧ multiplicationChecks schedule = 47 ∧
      additionChecks schedule + multiplicationChecks schedule = 87 := by
  rcases assignment_counts with ⟨ha, hs, hm⟩
  norm_num [additionChecks, multiplicationChecks, ha, hs, hm]

/-- The fourteen equality comparisons, with the candidate comparison kept separate. -/
def FinalEqualities (inputs : Fin 26 → ℕ) (trace : Fin 87 → ℤ) : Prop :=
  (inputs 16 : ℤ) = trace 2 ∧
  (inputs 25 : ℤ) = trace 7 ∧
  trace 16 = trace 15 ∧
  (inputs 4 : ℤ) = trace 20 ∧
  trace 28 = trace 27 ∧
  trace 34 = trace 33 ∧
  trace 40 = trace 39 ∧
  trace 43 = trace 54 ∧
  trace 58 = trace 57 ∧
  (inputs 11 : ℤ) = trace 61 ∧
  (inputs 24 : ℤ) = trace 63 ∧
  (inputs 12 : ℤ) = trace 70 ∧
  (inputs 23 : ℤ) = trace 78 ∧
  trace 86 = trace 85

/-- The existing natural-input system of Theorem 2.12. -/
def System (inputs : Fin 26 → ℕ) : Prop :=
  Thm212System (inputs 10) (inputs 0) (inputs 1) (inputs 2) (inputs 3) (inputs 4) (inputs 5) (inputs 6) (inputs 7) (inputs 8) (inputs 9) (inputs 11) (inputs 12) (inputs 13) (inputs 14) (inputs 15) (inputs 16) (inputs 17) (inputs 18) (inputs 19) (inputs 20) (inputs 21) (inputs 22) (inputs 23) (inputs 24) (inputs 25)

/-- Integer residuals of the fourteen source equations; only orientations may differ. -/
private def sourceResidual (inputs : Fin 26 → ℕ) : Fin 14 → ℤ :=
  ![(inputs 16 : ℤ) - ((inputs 22 : ℤ) * (inputs 25 : ℤ) + (inputs 7 : ℤ) + (inputs 9 : ℤ)),
    (inputs 25 : ℤ) - (((inputs 6 : ℤ) * (inputs 10 : ℤ) + (inputs 6 : ℤ) + (inputs 10 : ℤ)) * ((inputs 7 : ℤ) + (inputs 9 : ℤ)) + (inputs 7 : ℤ)),
    (inputs 5 : ℤ) * (inputs 5 : ℤ) - ((2 * (inputs 10 : ℤ)) ^ 3 * (2 * (inputs 10 : ℤ) + 2) * ((inputs 13 : ℤ) + 1) ^ 2 + 1),
    (inputs 4 : ℤ) - ((inputs 15 : ℤ) + (inputs 16 : ℤ) + (inputs 25 : ℤ) + 2 * (inputs 13 : ℤ)),
    (inputs 14 : ℤ) * (inputs 14 : ℤ) - ((inputs 4 : ℤ) ^ 3 * ((inputs 4 : ℤ) + 2) * ((inputs 0 : ℤ) + 1) ^ 2 + 1),
    (inputs 23 : ℤ) * (inputs 23 : ℤ) - (((inputs 0 : ℤ) * (inputs 0 : ℤ) - 1) * (inputs 24 : ℤ) * (inputs 24 : ℤ) + 1),
    (inputs 20 : ℤ) * (inputs 20 : ℤ) - (16 * ((inputs 0 : ℤ) * (inputs 0 : ℤ) - 1) * (inputs 17 : ℤ) * (inputs 17 : ℤ) * (inputs 24 : ℤ) ^ 4 + 1),
    ((inputs 23 : ℤ) + (inputs 2 : ℤ) * (inputs 20 : ℤ)) * ((inputs 23 : ℤ) + (inputs 2 : ℤ) * (inputs 20 : ℤ)) - ((((inputs 0 : ℤ) + (inputs 20 : ℤ) * (inputs 20 : ℤ) * ((inputs 20 : ℤ) * (inputs 20 : ℤ) - (inputs 0 : ℤ))) * ((inputs 0 : ℤ) + (inputs 20 : ℤ) * (inputs 20 : ℤ) * ((inputs 20 : ℤ) * (inputs 20 : ℤ) - (inputs 0 : ℤ))) - 1) * ((inputs 13 : ℤ) + 4 * (inputs 3 : ℤ) * (inputs 24 : ℤ)) * ((inputs 13 : ℤ) + 4 * (inputs 3 : ℤ) * (inputs 24 : ℤ)) + 1),
    (inputs 12 : ℤ) * (inputs 12 : ℤ) - (((inputs 0 : ℤ) * (inputs 0 : ℤ) - 1) * (inputs 11 : ℤ) * (inputs 11 : ℤ) + 1),
    (inputs 11 : ℤ) - ((inputs 10 : ℤ) + (inputs 8 : ℤ) * ((inputs 0 : ℤ) - 1)),
    (inputs 24 : ℤ) - ((inputs 13 : ℤ) + (inputs 11 : ℤ) + (inputs 21 : ℤ)),
    (inputs 12 : ℤ) - ((inputs 15 : ℤ) + (inputs 11 : ℤ) * ((inputs 0 : ℤ) - (inputs 13 : ℤ) - 1) + (inputs 1 : ℤ) * (2 * (inputs 0 : ℤ) * ((inputs 13 : ℤ) + 1) - ((inputs 13 : ℤ) + 1) * ((inputs 13 : ℤ) + 1) - 1)),
    (inputs 23 : ℤ) - ((inputs 16 : ℤ) + (inputs 24 : ℤ) * ((inputs 0 : ℤ) - (inputs 15 : ℤ) - 1) + (inputs 18 : ℤ) * (2 * (inputs 0 : ℤ) * ((inputs 15 : ℤ) + 1) - ((inputs 15 : ℤ) + 1) * ((inputs 15 : ℤ) + 1) - 1)),
    (inputs 15 : ℤ) * (inputs 12 : ℤ) - ((inputs 25 : ℤ) + (inputs 15 : ℤ) * (inputs 11 : ℤ) * ((inputs 0 : ℤ) - (inputs 15 : ℤ)) + (inputs 19 : ℤ) * (2 * (inputs 0 : ℤ) * (inputs 15 : ℤ) - (inputs 15 : ℤ) * (inputs 15 : ℤ) - 1))]

private theorem comparison_1 (inputs : Fin 26 → ℕ) :
    ((inputs 16 : ℤ) = evaluation inputs 2) ↔ sourceResidual inputs 0 = 0 := by
  have heq : (inputs 16 : ℤ) - (evaluation inputs 2) = sourceResidual inputs 0 := by
    change (inputs 16 : ℤ) - ((((inputs 22 : ℤ) * (inputs 25 : ℤ)) + ((inputs 7 : ℤ) + (inputs 9 : ℤ)))) = (inputs 16 : ℤ) - ((inputs 22 : ℤ) * (inputs 25 : ℤ) + (inputs 7 : ℤ) + (inputs 9 : ℤ))
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_2 (inputs : Fin 26 → ℕ) :
    ((inputs 25 : ℤ) = evaluation inputs 7) ↔ sourceResidual inputs 1 = 0 := by
  have heq : (inputs 25 : ℤ) - (evaluation inputs 7) = sourceResidual inputs 1 := by
    change (inputs 25 : ℤ) - (((((((inputs 6 : ℤ) * (inputs 10 : ℤ)) + (inputs 6 : ℤ)) + (inputs 10 : ℤ)) * ((inputs 7 : ℤ) + (inputs 9 : ℤ))) + (inputs 7 : ℤ))) = (inputs 25 : ℤ) - (((inputs 6 : ℤ) * (inputs 10 : ℤ) + (inputs 6 : ℤ) + (inputs 10 : ℤ)) * ((inputs 7 : ℤ) + (inputs 9 : ℤ)) + (inputs 7 : ℤ))
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_3 (inputs : Fin 26 → ℕ) :
    (evaluation inputs 16 = evaluation inputs 15) ↔ sourceResidual inputs 2 = 0 := by
  have heq : evaluation inputs 16 - (evaluation inputs 15) = sourceResidual inputs 2 := by
    change ((inputs 5 : ℤ) * (inputs 5 : ℤ)) - (((((inputs 10 : ℤ) * ((inputs 10 : ℤ) + 1)) * (((4 * (inputs 10 : ℤ)) * ((inputs 13 : ℤ) + 1)) * ((4 * (inputs 10 : ℤ)) * ((inputs 13 : ℤ) + 1)))) + 1)) = (inputs 5 : ℤ) * (inputs 5 : ℤ) - ((2 * (inputs 10 : ℤ)) ^ 3 * (2 * (inputs 10 : ℤ) + 2) * ((inputs 13 : ℤ) + 1) ^ 2 + 1)
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_4 (inputs : Fin 26 → ℕ) :
    ((inputs 4 : ℤ) = evaluation inputs 20) ↔ sourceResidual inputs 3 = 0 := by
  have heq : (inputs 4 : ℤ) - (evaluation inputs 20) = sourceResidual inputs 3 := by
    change (inputs 4 : ℤ) - (((((inputs 15 : ℤ) + (inputs 16 : ℤ)) + (inputs 25 : ℤ)) + (2 * (inputs 13 : ℤ)))) = (inputs 4 : ℤ) - ((inputs 15 : ℤ) + (inputs 16 : ℤ) + (inputs 25 : ℤ) + 2 * (inputs 13 : ℤ))
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_5 (inputs : Fin 26 → ℕ) :
    (evaluation inputs 28 = evaluation inputs 27) ↔ sourceResidual inputs 4 = 0 := by
  have heq : evaluation inputs 28 - (evaluation inputs 27) = sourceResidual inputs 4 := by
    change ((inputs 14 : ℤ) * (inputs 14 : ℤ)) - (((((inputs 4 : ℤ) * ((inputs 4 : ℤ) + 2)) * (((inputs 4 : ℤ) * ((inputs 0 : ℤ) + 1)) * ((inputs 4 : ℤ) * ((inputs 0 : ℤ) + 1)))) + 1)) = (inputs 14 : ℤ) * (inputs 14 : ℤ) - ((inputs 4 : ℤ) ^ 3 * ((inputs 4 : ℤ) + 2) * ((inputs 0 : ℤ) + 1) ^ 2 + 1)
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_6 (inputs : Fin 26 → ℕ) :
    (evaluation inputs 34 = evaluation inputs 33) ↔ sourceResidual inputs 5 = 0 := by
  have heq : evaluation inputs 34 - (evaluation inputs 33) = sourceResidual inputs 5 := by
    change ((inputs 23 : ℤ) * (inputs 23 : ℤ)) - ((((((inputs 0 : ℤ) * (inputs 0 : ℤ)) - 1) * ((inputs 24 : ℤ) * (inputs 24 : ℤ))) + 1)) = (inputs 23 : ℤ) * (inputs 23 : ℤ) - (((inputs 0 : ℤ) * (inputs 0 : ℤ) - 1) * (inputs 24 : ℤ) * (inputs 24 : ℤ) + 1)
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_7 (inputs : Fin 26 → ℕ) :
    (evaluation inputs 40 = evaluation inputs 39) ↔ sourceResidual inputs 6 = 0 := by
  have heq : evaluation inputs 40 - (evaluation inputs 39) = sourceResidual inputs 6 := by
    change ((inputs 20 : ℤ) * (inputs 20 : ℤ)) - ((((((inputs 0 : ℤ) * (inputs 0 : ℤ)) - 1) * ((4 * ((inputs 17 : ℤ) * ((inputs 24 : ℤ) * (inputs 24 : ℤ)))) * (4 * ((inputs 17 : ℤ) * ((inputs 24 : ℤ) * (inputs 24 : ℤ)))))) + 1)) = (inputs 20 : ℤ) * (inputs 20 : ℤ) - (16 * ((inputs 0 : ℤ) * (inputs 0 : ℤ) - 1) * (inputs 17 : ℤ) * (inputs 17 : ℤ) * (inputs 24 : ℤ) ^ 4 + 1)
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_8 (inputs : Fin 26 → ℕ) :
    (evaluation inputs 43 = evaluation inputs 54) ↔ sourceResidual inputs 7 = 0 := by
  have heq : evaluation inputs 43 - (evaluation inputs 54) = sourceResidual inputs 7 := by
    change (((inputs 23 : ℤ) + ((inputs 2 : ℤ) * (inputs 20 : ℤ))) * ((inputs 23 : ℤ) + ((inputs 2 : ℤ) * (inputs 20 : ℤ)))) - (((((((inputs 0 : ℤ) + (((inputs 20 : ℤ) * (inputs 20 : ℤ)) * (((inputs 20 : ℤ) * (inputs 20 : ℤ)) - (inputs 0 : ℤ)))) * ((inputs 0 : ℤ) + (((inputs 20 : ℤ) * (inputs 20 : ℤ)) * (((inputs 20 : ℤ) * (inputs 20 : ℤ)) - (inputs 0 : ℤ))))) - 1) * (((inputs 13 : ℤ) + (4 * ((inputs 3 : ℤ) * (inputs 24 : ℤ)))) * ((inputs 13 : ℤ) + (4 * ((inputs 3 : ℤ) * (inputs 24 : ℤ)))))) + 1)) = ((inputs 23 : ℤ) + (inputs 2 : ℤ) * (inputs 20 : ℤ)) * ((inputs 23 : ℤ) + (inputs 2 : ℤ) * (inputs 20 : ℤ)) - ((((inputs 0 : ℤ) + (inputs 20 : ℤ) * (inputs 20 : ℤ) * ((inputs 20 : ℤ) * (inputs 20 : ℤ) - (inputs 0 : ℤ))) * ((inputs 0 : ℤ) + (inputs 20 : ℤ) * (inputs 20 : ℤ) * ((inputs 20 : ℤ) * (inputs 20 : ℤ) - (inputs 0 : ℤ))) - 1) * ((inputs 13 : ℤ) + 4 * (inputs 3 : ℤ) * (inputs 24 : ℤ)) * ((inputs 13 : ℤ) + 4 * (inputs 3 : ℤ) * (inputs 24 : ℤ)) + 1)
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_9 (inputs : Fin 26 → ℕ) :
    (evaluation inputs 58 = evaluation inputs 57) ↔ sourceResidual inputs 8 = 0 := by
  have heq : evaluation inputs 58 - (evaluation inputs 57) = sourceResidual inputs 8 := by
    change ((inputs 12 : ℤ) * (inputs 12 : ℤ)) - ((((((inputs 0 : ℤ) * (inputs 0 : ℤ)) - 1) * ((inputs 11 : ℤ) * (inputs 11 : ℤ))) + 1)) = (inputs 12 : ℤ) * (inputs 12 : ℤ) - (((inputs 0 : ℤ) * (inputs 0 : ℤ) - 1) * (inputs 11 : ℤ) * (inputs 11 : ℤ) + 1)
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_10 (inputs : Fin 26 → ℕ) :
    ((inputs 11 : ℤ) = evaluation inputs 61) ↔ sourceResidual inputs 9 = 0 := by
  have heq : (inputs 11 : ℤ) - (evaluation inputs 61) = sourceResidual inputs 9 := by
    change (inputs 11 : ℤ) - (((inputs 10 : ℤ) + ((inputs 8 : ℤ) * ((inputs 0 : ℤ) - 1)))) = (inputs 11 : ℤ) - ((inputs 10 : ℤ) + (inputs 8 : ℤ) * ((inputs 0 : ℤ) - 1))
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_11 (inputs : Fin 26 → ℕ) :
    ((inputs 24 : ℤ) = evaluation inputs 63) ↔ sourceResidual inputs 10 = 0 := by
  have heq : (inputs 24 : ℤ) - (evaluation inputs 63) = sourceResidual inputs 10 := by
    change (inputs 24 : ℤ) - ((((inputs 13 : ℤ) + (inputs 11 : ℤ)) + (inputs 21 : ℤ))) = (inputs 24 : ℤ) - ((inputs 13 : ℤ) + (inputs 11 : ℤ) + (inputs 21 : ℤ))
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_12 (inputs : Fin 26 → ℕ) :
    ((inputs 12 : ℤ) = evaluation inputs 70) ↔ sourceResidual inputs 11 = 0 := by
  have heq : (inputs 12 : ℤ) - (evaluation inputs 70) = sourceResidual inputs 11 := by
    change (inputs 12 : ℤ) - ((((inputs 15 : ℤ) + ((inputs 11 : ℤ) * ((inputs 0 : ℤ) - ((inputs 13 : ℤ) + 1)))) + ((inputs 1 : ℤ) * ((((inputs 0 : ℤ) * (inputs 0 : ℤ)) - 1) - (((inputs 0 : ℤ) - ((inputs 13 : ℤ) + 1)) * ((inputs 0 : ℤ) - ((inputs 13 : ℤ) + 1))))))) = (inputs 12 : ℤ) - ((inputs 15 : ℤ) + (inputs 11 : ℤ) * ((inputs 0 : ℤ) - (inputs 13 : ℤ) - 1) + (inputs 1 : ℤ) * (2 * (inputs 0 : ℤ) * ((inputs 13 : ℤ) + 1) - ((inputs 13 : ℤ) + 1) * ((inputs 13 : ℤ) + 1) - 1))
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_13 (inputs : Fin 26 → ℕ) :
    ((inputs 23 : ℤ) = evaluation inputs 78) ↔ sourceResidual inputs 12 = 0 := by
  have heq : (inputs 23 : ℤ) - (evaluation inputs 78) = sourceResidual inputs 12 := by
    change (inputs 23 : ℤ) - ((((inputs 16 : ℤ) + ((inputs 24 : ℤ) * (((inputs 0 : ℤ) - (inputs 15 : ℤ)) - 1))) + ((inputs 18 : ℤ) * ((((inputs 0 : ℤ) * (inputs 0 : ℤ)) - 1) - ((((inputs 0 : ℤ) - (inputs 15 : ℤ)) - 1) * (((inputs 0 : ℤ) - (inputs 15 : ℤ)) - 1)))))) = (inputs 23 : ℤ) - ((inputs 16 : ℤ) + (inputs 24 : ℤ) * ((inputs 0 : ℤ) - (inputs 15 : ℤ) - 1) + (inputs 18 : ℤ) * (2 * (inputs 0 : ℤ) * ((inputs 15 : ℤ) + 1) - ((inputs 15 : ℤ) + 1) * ((inputs 15 : ℤ) + 1) - 1))
    ring
  rw [← heq, sub_eq_zero]

private theorem comparison_14 (inputs : Fin 26 → ℕ) :
    (evaluation inputs 86 = evaluation inputs 85) ↔ sourceResidual inputs 13 = 0 := by
  have heq : evaluation inputs 86 - (evaluation inputs 85) = sourceResidual inputs 13 := by
    change ((inputs 15 : ℤ) * (inputs 12 : ℤ)) - ((((inputs 25 : ℤ) + (((inputs 15 : ℤ) * (inputs 11 : ℤ)) * ((inputs 0 : ℤ) - (inputs 15 : ℤ)))) + ((inputs 19 : ℤ) * ((((inputs 0 : ℤ) * (inputs 0 : ℤ)) - 1) - (((inputs 0 : ℤ) - (inputs 15 : ℤ)) * ((inputs 0 : ℤ) - (inputs 15 : ℤ))))))) = (inputs 15 : ℤ) * (inputs 12 : ℤ) - ((inputs 25 : ℤ) + (inputs 15 : ℤ) * (inputs 11 : ℤ) * ((inputs 0 : ℤ) - (inputs 15 : ℤ)) + (inputs 19 : ℤ) * (2 * (inputs 0 : ℤ) * (inputs 15 : ℤ) - (inputs 15 : ℤ) * (inputs 15 : ℤ) - 1))
    ring
  rw [← heq, sub_eq_zero]

private theorem finalEqualities_iff_residuals (inputs : Fin 26 → ℕ) :
    FinalEqualities inputs (evaluation inputs) ↔ ∀ idx, sourceResidual inputs idx = 0 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    intro idx
    fin_cases idx
    · exact (comparison_1 inputs).mp h1
    · exact (comparison_2 inputs).mp h2
    · exact (comparison_3 inputs).mp h3
    · exact (comparison_4 inputs).mp h4
    · exact (comparison_5 inputs).mp h5
    · exact (comparison_6 inputs).mp h6
    · exact (comparison_7 inputs).mp h7
    · exact (comparison_8 inputs).mp h8
    · exact (comparison_9 inputs).mp h9
    · exact (comparison_10 inputs).mp h10
    · exact (comparison_11 inputs).mp h11
    · exact (comparison_12 inputs).mp h12
    · exact (comparison_13 inputs).mp h13
    · exact (comparison_14 inputs).mp h14
  · intro hres
    exact ⟨(comparison_1 inputs).mpr (hres 0),
      (comparison_2 inputs).mpr (hres 1),
      (comparison_3 inputs).mpr (hres 2),
      (comparison_4 inputs).mpr (hres 3),
      (comparison_5 inputs).mpr (hres 4),
      (comparison_6 inputs).mpr (hres 5),
      (comparison_7 inputs).mpr (hres 6),
      (comparison_8 inputs).mpr (hres 7),
      (comparison_9 inputs).mpr (hres 8),
      (comparison_10 inputs).mpr (hres 9),
      (comparison_11 inputs).mpr (hres 10),
      (comparison_12 inputs).mpr (hres 11),
      (comparison_13 inputs).mpr (hres 12),
      (comparison_14 inputs).mpr (hres 13)⟩

private theorem sourceResiduals_iff_system (inputs : Fin 26 → ℕ) :
    (∀ idx, sourceResidual inputs idx = 0) ↔ System inputs := by
  simp only [sourceResidual, Fin.forall_fin_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, System, Thm212System]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, by linear_combination h6,
      by linear_combination h7, by linear_combination h8, by linear_combination h9,
      by linear_combination h10, ?_, by linear_combination h12,
      by linear_combination h13, by linear_combination h14⟩
    · exact_mod_cast (show (inputs 16 : ℤ) = (inputs 22 : ℤ) * (inputs 25 : ℤ) + (inputs 7 : ℤ) + (inputs 9 : ℤ) by linear_combination h1)
    · exact_mod_cast (show (inputs 25 : ℤ) = ((inputs 6 : ℤ) * (inputs 10 : ℤ) + (inputs 6 : ℤ) + (inputs 10 : ℤ)) * ((inputs 7 : ℤ) + (inputs 9 : ℤ)) + (inputs 7 : ℤ) by linear_combination h2)
    · exact_mod_cast (show (2 * (inputs 10 : ℤ)) ^ 3 * (2 * (inputs 10 : ℤ) + 2) * ((inputs 13 : ℤ) + 1) ^ 2 + 1 = (inputs 5 : ℤ) * (inputs 5 : ℤ) by linear_combination -h3)
    · exact_mod_cast (show (inputs 4 : ℤ) = (inputs 15 : ℤ) + (inputs 16 : ℤ) + (inputs 25 : ℤ) + 2 * (inputs 13 : ℤ) by linear_combination h4)
    · exact_mod_cast (show (inputs 4 : ℤ) ^ 3 * ((inputs 4 : ℤ) + 2) * ((inputs 0 : ℤ) + 1) ^ 2 + 1 = (inputs 14 : ℤ) * (inputs 14 : ℤ) by linear_combination -h5)
    · exact_mod_cast (show (inputs 13 : ℤ) + (inputs 11 : ℤ) + (inputs 21 : ℤ) = (inputs 24 : ℤ) by linear_combination -h11)
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have h1' : (inputs 16 : ℤ) = (inputs 22 : ℤ) * (inputs 25 : ℤ) + (inputs 7 : ℤ) + (inputs 9 : ℤ) := by exact_mod_cast h1
    have h2' : (inputs 25 : ℤ) = ((inputs 6 : ℤ) * (inputs 10 : ℤ) + (inputs 6 : ℤ) + (inputs 10 : ℤ)) * ((inputs 7 : ℤ) + (inputs 9 : ℤ)) + (inputs 7 : ℤ) := by exact_mod_cast h2
    have h3' : (2 * (inputs 10 : ℤ)) ^ 3 * (2 * (inputs 10 : ℤ) + 2) * ((inputs 13 : ℤ) + 1) ^ 2 + 1 = (inputs 5 : ℤ) * (inputs 5 : ℤ) := by exact_mod_cast h3
    have h4' : (inputs 4 : ℤ) = (inputs 15 : ℤ) + (inputs 16 : ℤ) + (inputs 25 : ℤ) + 2 * (inputs 13 : ℤ) := by exact_mod_cast h4
    have h5' : (inputs 4 : ℤ) ^ 3 * ((inputs 4 : ℤ) + 2) * ((inputs 0 : ℤ) + 1) ^ 2 + 1 = (inputs 14 : ℤ) * (inputs 14 : ℤ) := by exact_mod_cast h5
    have h11' : (inputs 13 : ℤ) + (inputs 11 : ℤ) + (inputs 21 : ℤ) = (inputs 24 : ℤ) := by exact_mod_cast h11
    refine ⟨by linear_combination h1', by linear_combination h2',
      by linear_combination -h3', by linear_combination h4',
      by linear_combination -h5', by linear_combination h6,
      by linear_combination h7, by linear_combination h8,
      by linear_combination h9, by linear_combination h10,
      by linear_combination -h11', by linear_combination h12,
      by linear_combination h13, ⟨by linear_combination h14, fun idx => idx.elim0⟩⟩

/-- The schedule's final comparisons are exactly the established primality system. -/
theorem evaluation_final_iff_system (inputs : Fin 26 → ℕ) :
    FinalEqualities inputs (evaluation inputs) ↔ System inputs :=
  (finalEqualities_iff_residuals inputs).trans (sourceResiduals_iff_system inputs)

theorem evaluation_candidate (inputs : Fin 26 → ℕ) :
    evaluation inputs 8 = (inputs 10 : ℤ) + 1 := rfl

/-- Natural inputs, signed intermediates, and equality-only final checks.
The candidate is compared to an intermediate already computed at step nine. -/
def Certificate (N : ℕ) (inputs : Fin 26 → ℕ) (trace : Fin 87 → ℤ) : Prop :=
  1 ≤ inputs 10 ∧ Valid schedule inputs trace ∧ FinalEqualities inputs trace ∧
    (N : ℤ) = trace 8

theorem certificate_iff (N : ℕ) (inputs : Fin 26 → ℕ) (trace : Fin 87 → ℤ) :
    Certificate N inputs trace ↔
      1 ≤ inputs 10 ∧ trace = evaluation inputs ∧ System inputs ∧ N = inputs 10 + 1 := by
  constructor
  · rintro ⟨hk, ht, hf, hN⟩
    have heq := (valid_iff_eq_evaluation inputs trace).mp ht
    subst trace
    refine ⟨hk, rfl, (evaluation_final_iff_system inputs).mp hf, ?_⟩
    rw [evaluation_candidate] at hN
    exact_mod_cast hN
  · rintro ⟨hk, rfl, hs, hN⟩
    refine ⟨hk, evaluation_valid inputs, (evaluation_final_iff_system inputs).mpr hs, ?_⟩
    simp only [evaluation_candidate, hN, Nat.cast_add, Nat.cast_one]

/-- A prime has such a certificate, and every checked certificate certifies a prime. -/
theorem prime_iff_certificate (N : ℕ) :
    Nat.Prime N ↔ ∃ inputs : Fin 26 → ℕ, ∃ trace : Fin 87 → ℤ,
      Certificate N inputs trace := by
  constructor
  · intro hN
    obtain ⟨k, hkN⟩ : ∃ k, N = k + 1 := ⟨N - 1, by have := hN.two_le; omega⟩
    have hk : 1 ≤ k := by have := hN.two_le; omega
    have hprime : Nat.Prime (k + 1) := hkN ▸ hN
    obtain ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, hs⟩ :=
      theorem_2_12_exists hk hprime
    let inputs : Fin 26 → ℕ := ![a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z]
    refine ⟨inputs, evaluation inputs, (certificate_iff N inputs _).mpr ⟨?_, rfl, ?_, ?_⟩⟩
    · exact hk
    · exact hs
    · exact hkN
  · rintro ⟨inputs, trace, hcert⟩
    obtain ⟨hk, _, hs, hN⟩ := (certificate_iff N inputs trace).mp hcert
    rw [hN]
    exact theorem_2_12_of hk hs

end JSWW1976.PrimalityCertificate

namespace JSWW1976

/-- Theorem 5, explicit arithmetic-certificate reading: primality is equivalent
to a certificate checked with 40 additions and 47 multiplications. Fixed
numerals, equality/domain checks, and reading the certificate are uncharged. -/
theorem theorem_5 (N : ℕ) :
    Nat.Prime N ↔ ∃ inputs : Fin 26 → ℕ, ∃ trace : Fin 87 → ℤ,
      PrimalityCertificate.Certificate N inputs trace :=
  PrimalityCertificate.prime_iff_certificate N

end JSWW1976
