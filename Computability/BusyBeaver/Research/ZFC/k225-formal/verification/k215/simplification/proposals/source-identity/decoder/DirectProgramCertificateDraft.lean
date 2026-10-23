import BusyBeaver.ZFC.K215Decoder
import BusyBeaver.ZFC.KSource215Program

/-!
UNCOMPILED PILOT, pinned to cbf94cb552a3b49509e0eee80e7455d4eb5974c6.
This file proposes a finite checker and retargeted role data only.
No direct-program semantic soundness theorem is supplied here.
The old K215Decoder import is a migration convenience for its formal table and
281 checked blocks. Production must split those into an independent block-data
module before this pilot removes anything from the dependency closure.
-/
namespace SetTheory.BusyBeaver.ZFC.DirectProgramCertificateDraft
open FramedWindow DecoderCertificate

inductive Link where
  | internal (target block : Nat)
  | primitive (action : Action)
  deriving DecidableEq, Repr

structure Role where
  node : Nat
  state : Nat
  suffix : List Bool
  zero : Link
  one : Link
  deriving DecidableEq, Repr

def branch (p : RegisterPath.Program) (n : Nat) (bit : Bool) : RegisterPath.Edge :=
  if bit then (p.nodes n).2 else (p.nodes n).1

def edgeCheck (M : Table) (p : RegisterPath.Program) (rs : Array Role)
    (bs : Array Block) (r : Role) (bit : Bool) : Bool :=
  match (if bit then r.one else r.zero), branch p r.node bit with
  | .primitive action, .node _ => false
  | .primitive action, _ => decide (M r.state bit = some action)
  | .internal k j, .node child =>
    match rs[k]?, bs[j]? with
    | some s, some b =>
      let w := r.suffix ++ [bit]
      decide (child < r.node ∧ s.node = child ∧ s.suffix = tail2 w ∧
        b.entry = r.state ∧ b.exit = s.state ∧ b.word.length ≤ w.length ∧
        b.word = w.drop (w.length - b.word.length))
    | _, _ => false
  | .internal _ _, _ => false

def roleCheck (M : Table) (p : RegisterPath.Program) (rs : Array Role)
    (bs : Array Block) (r : Role) : Bool :=
  decide (r.node < p.nnodes ∧ 0 < r.suffix.length ∧ r.suffix.length ≤ 2) &&
    edgeCheck M p rs bs r false && edgeCheck M p rs bs r true

def structuralCheck (M : Table) (p : RegisterPath.Program)
    (rs : Array Role) (bs : Array Block) : Bool :=
  match rs[0]? with
  | none => false
  | some r => decide (r.node = p.root ∧ r.state = 84 ∧ r.suffix = [true]) &&
      rs.toList.all (roleCheck M p rs bs)

-- The role order, physical states, suffixes, and internal block references
-- are unchanged. Only source labels are retargeted; primitive leaf IDs vanish.
def roles : Array Role := #[
  ⟨178, 84, [true], (.internal 1 0), (.internal 9 1)⟩,
  ⟨7, 95, [true, false], (.internal 2 2), (.internal 3 3)⟩,
  ⟨0, 27, [false, false], (.primitive ⟨false, 1, 39⟩), (.primitive ⟨false, (-1), 40⟩)⟩,
  ⟨6, 110, [false, true], (.internal 4 4), (.internal 7 5)⟩,
  ⟨3, 127, [true, false], (.primitive ⟨false, 1, 14⟩), (.internal 5 6)⟩,
  ⟨2, 138, [false, true], (.primitive ⟨false, 1, 39⟩), (.internal 6 7)⟩,
  ⟨1, 62, [true, true], (.primitive ⟨false, (-1), 28⟩), (.primitive ⟨true, (-1), 73⟩)⟩,
  ⟨5, 8, [true, true], (.primitive ⟨false, 1, 14⟩), (.internal 8 8)⟩,
  ⟨4, 13, [true, true], (.primitive ⟨false, (-1), 91⟩), (.primitive ⟨true, (-1), 31⟩)⟩,
  ⟨177, 214, [true, true], (.internal 10 9), (.internal 23 10)⟩,
  ⟨20, 111, [true, false], (.internal 11 11), (.internal 21 12)⟩,
  ⟨17, 104, [false, false], (.internal 12 13), (.internal 19 14)⟩,
  ⟨14, 123, [false, false], (.primitive ⟨false, 1, 39⟩), (.internal 13 15)⟩,
  ⟨13, 73, [false, true], (.primitive ⟨false, 1, 82⟩), (.internal 14 16)⟩,
  ⟨12, 83, [true, true], (.internal 15 17), (.primitive ⟨false, (-1), 42⟩)⟩,
  ⟨11, 93, [true, false], (.internal 16 18), (.internal 17 19)⟩,
  ⟨8, 108, [false, false], (.primitive ⟨false, 1, 21⟩), (.primitive ⟨false, (-1), 10⟩)⟩,
  ⟨10, 109, [false, true], (.primitive ⟨false, 1, 62⟩), (.internal 18 20)⟩,
  ⟨9, 42, [true, true], (.primitive ⟨false, 1, 13⟩), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨16, 124, [false, true], (.primitive ⟨false, 1, 62⟩), (.internal 20 21)⟩,
  ⟨15, 138, [true, true], (.primitive ⟨false, 1, 39⟩), (.primitive ⟨true, (-1), 130⟩)⟩,
  ⟨19, 128, [false, true], (.primitive ⟨false, 1, 21⟩), (.internal 22 22)⟩,
  ⟨18, 141, [true, true], (.primitive ⟨false, 1, 161⟩), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨176, 26, [true, true], (.internal 24 23), (.internal 230 24)⟩,
  ⟨171, 37, [true, false], (.primitive ⟨false, 1, 17⟩), (.internal 25 25)⟩,
  ⟨170, 117, [false, true], (.internal 26 26), (.primitive ⟨false, (-1), 120⟩)⟩,
  ⟨169, 134, [true, false], (.internal 27 27), (.internal 57 28)⟩,
  ⟨168, 163, [false, false], (.primitive ⟨false, 1, 17⟩), (.internal 28 29)⟩,
  ⟨167, 162, [false, true], (.internal 29 30), (.primitive ⟨false, (-1), 120⟩)⟩,
  ⟨166, 174, [true, false], (.internal 30 31), (.internal 225 32)⟩,
  ⟨162, 11, [false, false], (.primitive ⟨false, (-1), 26⟩), (.internal 31 33)⟩,
  ⟨161, 115, [false, true], (.internal 32 34), (.internal 75 35)⟩,
  ⟨57, 76, [true, false], (.internal 33 36), (.internal 63 37)⟩,
  ⟨47, 85, [false, false], (.internal 34 38), (.internal 57 39)⟩,
  ⟨41, 98, [false, false], (.internal 35 40), (.internal 52 41)⟩,
  ⟨35, 19, [false, false], (.internal 36 42), (.internal 38 43)⟩,
  ⟨21, 28, [false, false], (.primitive ⟨false, 1, 41⟩), (.internal 37 44)⟩,
  ⟨9, 42, [false, true], (.primitive ⟨false, 1, 13⟩), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨34, 29, [false, true], (.internal 39 45), (.internal 41 46)⟩,
  ⟨23, 43, [true, false], (.primitive ⟨false, 1, 56⟩), (.internal 40 47)⟩,
  ⟨22, 57, [false, true], (.primitive ⟨false, 1, 61⟩), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨33, 44, [true, true], (.internal 42 48), (.internal 50 49)⟩,
  ⟨30, 58, [true, false], (.internal 43 50), (.internal 45 51)⟩,
  ⟨25, 70, [false, false], (.primitive ⟨false, 1, 41⟩), (.internal 44 52)⟩,
  ⟨24, 63, [false, true], (.primitive ⟨false, (-1), 123⟩), (.internal 6 53)⟩,
  ⟨29, 71, [false, true], (.primitive ⟨false, (-1), 91⟩), (.internal 46 54)⟩,
  ⟨28, 80, [true, true], (.internal 47 55), (.primitive ⟨true, (-1), 138⟩)⟩,
  ⟨27, 91, [true, false], (.primitive ⟨false, 1, 82⟩), (.internal 48 56)⟩,
  ⟨26, 81, [false, true], (.primitive ⟨false, (-1), 111⟩), (.internal 49 57)⟩,
  ⟨22, 57, [true, true], (.primitive ⟨false, 1, 61⟩), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨32, 59, [true, true], (.primitive ⟨false, 1, 62⟩), (.internal 51 58)⟩,
  ⟨31, 72, [true, true], (.primitive ⟨false, 1, 56⟩), (.primitive ⟨true, (-1), 81⟩)⟩,
  ⟨40, 114, [false, true], (.internal 53 59), (.internal 55 60)⟩,
  ⟨37, 130, [true, false], (.primitive ⟨false, 1, 144⟩), (.internal 54 61)⟩,
  ⟨36, 46, [false, true], (.primitive ⟨false, 1, 61⟩), (.internal 6 62)⟩,
  ⟨39, 107, [true, true], (.primitive ⟨false, 1, 21⟩), (.internal 56 63)⟩,
  ⟨38, 126, [true, true], (.primitive ⟨false, 1, 71⟩), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨46, 12, [false, true], (.internal 58 64), (.internal 59 65)⟩,
  ⟨35, 19, [true, false], (.internal 36 42), (.internal 38 43)⟩,
  ⟨45, 20, [true, true], (.internal 60 66), (.internal 61 67)⟩,
  ⟨42, 30, [true, false], (.primitive ⟨false, 1, 45⟩), (.internal 54 68)⟩,
  ⟨44, 31, [true, true], (.primitive ⟨false, 1, 21⟩), (.internal 62 69)⟩,
  ⟨43, 47, [true, true], (.primitive ⟨false, 1, 63⟩), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨56, 86, [false, true], (.internal 64 70), (.internal 74 71)⟩,
  ⟨55, 90, [true, false], (.internal 65 72), (.internal 68 73)⟩,
  ⟨49, 105, [false, false], (.internal 66 74), (.internal 67 75)⟩,
  ⟨48, 72, [false, false], (.primitive ⟨false, 1, 56⟩), (.internal 13 76)⟩,
  ⟨32, 59, [false, true], (.primitive ⟨false, 1, 62⟩), (.internal 51 58)⟩,
  ⟨54, 106, [false, true], (.internal 42 77), (.internal 69 78)⟩,
  ⟨53, 125, [true, true], (.primitive ⟨false, 1, 62⟩), (.internal 70 79)⟩,
  ⟨52, 139, [true, true], (.internal 71 80), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨51, 160, [true, false], (.internal 72 81), (.internal 73 82)⟩,
  ⟨50, 99, [false, false], (.primitive ⟨false, 1, 61⟩), (.primitive ⟨true, 1, 61⟩)⟩,
  ⟨50, 99, [false, true], (.primitive ⟨false, 1, 61⟩), (.primitive ⟨true, 1, 61⟩)⟩,
  ⟨50, 99, [true, true], (.primitive ⟨false, 1, 61⟩), (.primitive ⟨true, 1, 61⟩)⟩,
  ⟨160, 185, [true, true], (.internal 76 83), (.internal 83 84)⟩,
  ⟨61, 168, [true, false], (.internal 77 85), (.internal 81 86)⟩,
  ⟨60, 166, [false, false], (.internal 35 87), (.internal 78 88)⟩,
  ⟨59, 179, [false, true], (.internal 79 89), (.internal 80 90)⟩,
  ⟨58, 194, [true, false], (.primitive ⟨false, 1, 17⟩), (.internal 54 91)⟩,
  ⟨19, 128, [true, true], (.primitive ⟨false, 1, 21⟩), (.internal 22 22)⟩,
  ⟨41, 98, [false, true], (.internal 58 40), (.internal 82 41)⟩,
  ⟨40, 114, [true, true], (.internal 53 59), (.internal 55 60)⟩,
  ⟨159, 146, [true, true], (.internal 84 92), (.internal 221 93)⟩,
  ⟨157, 78, [true, false], (.internal 85 94), (.internal 103 95)⟩,
  ⟨69, 100, [false, false], (.internal 86 96), (.internal 88 97)⟩,
  ⟨62, 69, [false, false], (.internal 11 98), (.internal 87 99)⟩,
  ⟨44, 31, [false, true], (.primitive ⟨false, 1, 21⟩), (.internal 62 69)⟩,
  ⟨68, 142, [false, true], (.internal 64 100), (.internal 89 101)⟩,
  ⟨67, 143, [true, true], (.internal 90 102), (.internal 99 103)⟩,
  ⟨65, 213, [true, false], (.internal 91 104), (.internal 96 105)⟩,
  ⟨64, 92, [false, false], (.internal 11 106), (.internal 92 107)⟩,
  ⟨63, 212, [false, true], (.internal 93 108), (.internal 95 109)⟩,
  ⟨39, 107, [true, false], (.primitive ⟨false, 1, 21⟩), (.internal 94 63)⟩,
  ⟨38, 126, [false, true], (.primitive ⟨false, 1, 71⟩), (.primitive ⟨false, (-1), 16⟩)⟩,
  ⟨41, 98, [true, true], (.internal 58 40), (.internal 82 41)⟩,
  ⟨55, 90, [false, true], (.internal 97 72), (.internal 98 73)⟩,
  ⟨49, 105, [true, false], (.internal 66 74), (.internal 67 75)⟩,
  ⟨54, 106, [true, true], (.internal 42 77), (.internal 69 78)⟩,
  ⟨66, 147, [true, true], (.internal 100 110), (.internal 101 111)⟩,
  ⟨41, 98, [true, false], (.internal 35 40), (.internal 52 41)⟩,
  ⟨60, 166, [true, true], (.internal 58 87), (.internal 102 88)⟩,
  ⟨59, 179, [true, true], (.internal 79 89), (.internal 80 90)⟩,
  ⟨156, 225, [false, true], (.internal 104 112), (.internal 218 113)⟩,
  ⟨153, 210, [true, false], (.internal 105 114), (.internal 110 115)⟩,
  ⟨71, 171, [false, false], (.internal 106 116), (.internal 107 117)⟩,
  ⟨55, 90, [false, false], (.internal 65 72), (.internal 68 73)⟩,
  ⟨70, 149, [false, true], (.internal 108 118), (.internal 101 119)⟩,
  ⟨46, 12, [true, false], (.internal 35 64), (.internal 109 65)⟩,
  ⟨45, 20, [false, true], (.internal 60 66), (.internal 61 67)⟩,
  ⟨152, 201, [false, true], (.internal 111 120), (.internal 208 121)⟩,
  ⟨143, 195, [true, false], (.internal 112 122), (.internal 113 123)⟩,
  ⟨72, 150, [false, false], (.internal 106 124), (.internal 96 125)⟩,
  ⟨142, 188, [false, true], (.internal 114 126), (.internal 124 127)⟩,
  ⟨79, 151, [true, false], (.internal 106 128), (.internal 115 129)⟩,
  ⟨78, 165, [false, true], (.internal 116 130), (.internal 119 131)⟩,
  ⟨74, 176, [true, false], (.internal 117 132), (.internal 118 133)⟩,
  ⟨61, 168, [false, false], (.internal 77 85), (.internal 81 86)⟩,
  ⟨73, 150, [false, true], (.internal 64 124), (.primitive ⟨true, (-1), 173⟩)⟩,
  ⟨77, 190, [true, true], (.internal 120 134), (.internal 121 135)⟩,
  ⟨50, 99, [true, false], (.primitive ⟨false, 1, 61⟩), (.primitive ⟨true, 1, 61⟩)⟩,
  ⟨76, 52, [true, true], (.internal 122 136), (.internal 123 137)⟩,
  ⟨75, 154, [true, false], (.internal 77 138), (.internal 57 139)⟩,
  ⟨73, 150, [true, true], (.internal 64 124), (.primitive ⟨true, (-1), 173⟩)⟩,
  ⟨141, 181, [true, true], (.internal 125 140), (.internal 202 141)⟩,
  ⟨136, 177, [true, false], (.internal 126 142), (.internal 143 143)⟩,
  ⟨135, 203, [false, false], (.internal 127 144), (.internal 148 145)⟩,
  ⟨95, 207, [false, false], (.internal 128 146), (.internal 132 147)⟩,
  ⟨83, 65, [false, false], (.internal 72 148), (.internal 129 149)⟩,
  ⟨82, 157, [false, true], (.internal 130 150), (.internal 131 151)⟩,
  ⟨80, 155, [true, false], (.internal 33 152), (.internal 118 153)⟩,
  ⟨81, 182, [true, true], (.internal 32 154), (.primitive ⟨true, 1, 61⟩)⟩,
  ⟨94, 7, [false, true], (.internal 133 155), (.internal 134 156)⟩,
  ⟨56, 86, [true, false], (.internal 106 70), (.internal 73 71)⟩,
  ⟨93, 205, [true, true], (.internal 135 157), (.internal 136 158)⟩,
  ⟨84, 164, [true, false], (.internal 112 159), (.internal 81 160)⟩,
  ⟨92, 206, [true, true], (.internal 137 161), (.internal 140 162)⟩,
  ⟨85, 186, [true, false], (.internal 138 163), (.internal 63 164)⟩,
  ⟨66, 147, [false, false], (.internal 34 110), (.internal 139 111)⟩,
  ⟨60, 166, [false, true], (.internal 58 87), (.internal 102 88)⟩,
  ⟨91, 199, [true, true], (.internal 141 165), (.internal 101 166)⟩,
  ⟨90, 180, [true, false], (.internal 142 167), (.internal 143 168)⟩,
  ⟨86, 152, [false, false], (.internal 35 169), (.primitive ⟨true, (-1), 170⟩)⟩,
  ⟨89, 172, [false, true], (.internal 144 170), (.internal 145 171)⟩,
  ⟨87, 157, [true, false], (.internal 106 172), (.internal 63 173)⟩,
  ⟨88, 184, [true, true], (.internal 146 174), (.internal 147 175)⟩,
  ⟨86, 152, [true, false], (.internal 35 169), (.primitive ⟨true, (-1), 170⟩)⟩,
  ⟨55, 90, [true, true], (.internal 97 72), (.internal 98 73)⟩,
  ⟨134, 101, [false, true], (.internal 149 176), (.internal 154 177)⟩,
  ⟨98, 67, [true, false], (.internal 150 178), (.internal 151 179)⟩,
  ⟨79, 151, [false, false], (.internal 106 128), (.internal 115 129)⟩,
  ⟨97, 152, [false, true], (.internal 130 180), (.internal 152 181)⟩,
  ⟨96, 171, [true, true], (.internal 135 182), (.internal 153 117)⟩,
  ⟨70, 149, [true, true], (.internal 108 118), (.internal 101 119)⟩,
  ⟨133, 204, [true, true], (.internal 155 183), (.internal 157 184)⟩,
  ⟨99, 153, [true, false], (.internal 156 185), (.internal 96 186)⟩,
  ⟨56, 86, [false, false], (.internal 106 70), (.internal 73 71)⟩,
  ⟨132, 215, [true, true], (.internal 158 187), (.internal 197 188)⟩,
  ⟨128, 223, [true, false], (.internal 159 189), (.internal 175 190)⟩,
  ⟨112, 132, [false, false], (.internal 160 191), (.internal 173 192)⟩,
  ⟨111, 222, [false, false], (.internal 161 193), (.internal 169 194)⟩,
  ⟨106, 170, [false, false], (.internal 72 195), (.internal 162 196)⟩,
  ⟨105, 169, [false, true], (.internal 163 197), (.internal 152 198)⟩,
  ⟨104, 131, [true, false], (.internal 164 199), (.internal 168 200)⟩,
  ⟨102, 136, [false, false], (.internal 165 201), (.internal 166 202)⟩,
  ⟨46, 12, [false, false], (.internal 35 64), (.internal 109 65)⟩,
  ⟨101, 148, [false, true], (.internal 137 203), (.internal 167 204)⟩,
  ⟨100, 173, [true, true], (.internal 155 205), (.internal 131 206)⟩,
  ⟨103, 193, [false, true], (.internal 116 207), (.internal 121 208)⟩,
  ⟨110, 209, [false, true], (.internal 144 209), (.internal 170 210)⟩,
  ⟨109, 133, [true, true], (.internal 32 211), (.internal 171 212)⟩,
  ⟨108, 187, [true, true], (.internal 137 213), (.internal 172 214)⟩,
  ⟨107, 76, [true, true], (.internal 135 215), (.internal 131 216)⟩,
  ⟨90, 180, [false, true], (.internal 146 167), (.internal 174 168)⟩,
  ⟨89, 172, [true, true], (.internal 144 170), (.internal 145 171)⟩,
  ⟨127, 158, [false, true], (.internal 130 217), (.internal 176 218)⟩,
  ⟨126, 220, [true, true], (.internal 177 219), (.internal 184 220)⟩,
  ⟨117, 211, [true, false], (.internal 178 221), (.internal 181 222)⟩,
  ⟨114, 159, [false, false], (.internal 77 223), (.internal 179 224)⟩,
  ⟨113, 118, [false, true], (.internal 130 225), (.internal 180 226)⟩,
  ⟨99, 153, [true, true], (.internal 133 185), (.internal 147 186)⟩,
  ⟨116, 129, [false, true], (.internal 122 227), (.internal 182 228)⟩,
  ⟨115, 189, [true, true], (.internal 183 229), (.internal 123 230)⟩,
  ⟨70, 149, [true, false], (.internal 165 118), (.internal 139 119)⟩,
  ⟨125, 18, [true, true], (.internal 185 231), (.internal 189 232)⟩,
  ⟨119, 218, [true, false], (.internal 138 233), (.internal 186 234)⟩,
  ⟨118, 145, [false, true], (.internal 187 235), (.internal 188 236)⟩,
  ⟨66, 147, [true, false], (.internal 34 110), (.internal 139 111)⟩,
  ⟨103, 193, [true, true], (.internal 116 207), (.internal 121 208)⟩,
  ⟨124, 217, [true, true], (.internal 190 237), (.internal 195 238)⟩,
  ⟨122, 216, [true, false], (.internal 191 239), (.internal 192 240)⟩,
  ⟨87, 157, [false, false], (.internal 106 172), (.internal 63 173)⟩,
  ⟨121, 178, [false, true], (.internal 193 241), (.internal 182 242)⟩,
  ⟨120, 189, [true, false], (.internal 194 229), (.internal 107 243)⟩,
  ⟨70, 149, [false, false], (.internal 165 118), (.internal 139 119)⟩,
  ⟨123, 167, [true, true], (.internal 196 244), (.internal 174 245)⟩,
  ⟨88, 184, [true, false], (.internal 142 174), (.internal 96 175)⟩,
  ⟨131, 112, [true, true], (.internal 144 246), (.internal 198 247)⟩,
  ⟨130, 200, [true, true], (.internal 144 248), (.internal 199 249)⟩,
  ⟨129, 119, [true, true], (.internal 200 250), (.internal 189 251)⟩,
  ⟨123, 167, [true, false], (.internal 201 244), (.internal 143 245)⟩,
  ⟨88, 184, [false, false], (.internal 142 174), (.internal 96 175)⟩,
  ⟨140, 89, [true, true], (.internal 144 252), (.internal 203 253)⟩,
  ⟨139, 116, [true, true], (.internal 204 254), (.internal 206 255)⟩,
  ⟨137, 172, [true, false], (.internal 106 256), (.internal 205 171)⟩,
  ⟨88, 184, [false, true], (.internal 146 174), (.internal 147 175)⟩,
  ⟨138, 194, [true, true], (.primitive ⟨false, 1, 17⟩), (.internal 207 257)⟩,
  ⟨24, 63, [true, true], (.primitive ⟨false, (-1), 123⟩), (.internal 6 53)⟩,
  ⟨151, 196, [true, true], (.internal 209 258), (.internal 217 259)⟩,
  ⟨149, 77, [true, false], (.internal 210 260), (.internal 214 261)⟩,
  ⟨146, 87, [false, false], (.internal 211 262), (.primitive ⟨true, 1, 21⟩)⟩,
  ⟨145, 102, [false, false], (.primitive ⟨false, 1, 45⟩), (.internal 212 263)⟩,
  ⟨144, 103, [false, true], (.internal 213 264), (.primitive ⟨false, (-1), 120⟩)⟩,
  ⟨4, 108, [true, false], (.primitive ⟨false, 1, 21⟩), (.primitive ⟨false, (-1), 10⟩)⟩,
  ⟨148, 88, [false, true], (.internal 215 265), (.internal 216 266)⟩,
  ⟨147, 122, [true, false], (.primitive ⟨false, (-1), 137⟩), (.primitive ⟨false, (-1), 1⟩)⟩,
  ⟨144, 103, [true, true], (.internal 213 264), (.primitive ⟨false, (-1), 120⟩)⟩,
  ⟨150, 122, [true, true], (.primitive ⟨false, (-1), 137⟩), (.primitive ⟨false, (-1), 1⟩)⟩,
  ⟨155, 197, [true, true], (.internal 219 267), (.internal 220 268)⟩,
  ⟨10, 109, [true, false], (.primitive ⟨false, 1, 62⟩), (.internal 37 20)⟩,
  ⟨154, 130, [true, true], (.primitive ⟨false, 1, 144⟩), (.internal 62 269)⟩,
  ⟨158, 96, [true, true], (.internal 222 270), (.primitive ⟨false, (-1), 120⟩)⟩,
  ⟨151, 196, [true, false], (.internal 223 258), (.internal 224 259)⟩,
  ⟨149, 77, [false, false], (.internal 210 260), (.internal 214 261)⟩,
  ⟨150, 122, [false, true], (.primitive ⟨false, (-1), 137⟩), (.primitive ⟨false, (-1), 1⟩)⟩,
  ⟨165, 135, [false, true], (.internal 226 271), (.internal 229 272)⟩,
  ⟨163, 221, [true, false], (.internal 227 273), (.internal 228 274)⟩,
  ⟨65, 213, [false, false], (.internal 91 104), (.internal 96 105)⟩,
  ⟨21, 28, [false, true], (.primitive ⟨false, 1, 41⟩), (.internal 18 44)⟩,
  ⟨164, 164, [true, true], (.internal 209 275), (.internal 95 160)⟩,
  ⟨175, 38, [true, true], (.primitive ⟨false, 1, 13⟩), (.internal 231 276)⟩,
  ⟨174, 53, [true, true], (.internal 232 277), (.internal 233 278)⟩,
  ⟨172, 68, [true, false], (.internal 223 279), (.primitive ⟨true, 1, 230⟩)⟩,
  ⟨173, 69, [true, true], (.internal 97 280), (.internal 61 99)⟩
]

-- Proposed proof-assistant checks. These declarations have NOT been compiled.
theorem counts : roles.size = 234 ∧ K215Decoder.blocks.size = 281 := by
  decide +kernel

theorem structure_checked :
    structuralCheck K215Decoder.formal KSource215.p215 roles K215Decoder.blocks = true := by
  rw [← K215Decoder.fast_eq]
  decide +kernel

#print axioms counts
#print axioms structure_checked
end SetTheory.BusyBeaver.ZFC.DirectProgramCertificateDraft
