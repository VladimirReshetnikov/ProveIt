import DiophantineConsistency.SharingNormTrace

/-! UNCOMPILED DRAFT. Concrete 60-gate final assignment environment for the
38-witness candidate. Data definitions and conditional predicates only;
none of the required model/seed/source equivalences is proved here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.NormAssignment38
open SharingGateModel

/-- Inputs, four natural port values, constants 1/3/4, then 60 gate values. -/
def assignment {S : Type*} [CommSemiring S]
    (ports : Fin 4 → S) (w : Fin 38 → S) : Fin 81 → SignedPair S :=
  let a0 : SignedPair S := ⟨w 0 + 1, 0⟩
  let a1 : SignedPair S := ⟨w 1 + 1, 0⟩
  let a2 : SignedPair S := ⟨w 2 + 1, 0⟩
  let a3 : SignedPair S := ⟨w 3 + 1, 0⟩
  let a4 : SignedPair S := ⟨w 4 + 1, 0⟩
  let a5 : SignedPair S := ⟨w 5 + 1, 0⟩
  let a6 : SignedPair S := ⟨w 6 + 1, 0⟩
  let a7 : SignedPair S := ⟨w 7 + 1, 0⟩
  let a8 : SignedPair S := ⟨w 8 + 1, 0⟩
  let a9 : SignedPair S := ⟨w 9 + 1, 0⟩
  let a10 : SignedPair S := ⟨w 10 + 1, 0⟩
  let a11 : SignedPair S := ⟨w 11 + 1, 0⟩
  let a12 : SignedPair S := ⟨w 12 + 1, 0⟩
  let a13 : SignedPair S := ⟨w 13 + 1, 0⟩
  let a14 : SignedPair S := ⟨ports 0, 0⟩
  let a15 : SignedPair S := ⟨ports 1, 0⟩
  let a16 : SignedPair S := ⟨ports 2, 0⟩
  let a17 : SignedPair S := ⟨ports 3, 0⟩
  let a18 : SignedPair S := ⟨1, 0⟩
  let a19 : SignedPair S := ⟨3, 0⟩
  let a20 : SignedPair S := ⟨4, 0⟩
  let a21 : SignedPair S := pairCompute GateOp.mul a14 a0
  let a22 : SignedPair S := pairCompute GateOp.add a21 a18
  let a23 : SignedPair S := ⟨w 14, 0⟩
  let a24 : SignedPair S := ⟨w 15, 0⟩
  let a25 : SignedPair S := ⟨w 16, 0⟩
  let a26 : SignedPair S := ⟨w 17, 0⟩
  let a27 : SignedPair S := ⟨w 18, 0⟩
  let a28 : SignedPair S := pairCompute GateOp.add a10 a11
  let a29 : SignedPair S := ⟨w 19, 0⟩
  let a30 : SignedPair S := ⟨w 20, 0⟩
  let a31 : SignedPair S := pairCompute GateOp.add a29 a10
  let a32 : SignedPair S := pairCompute GateOp.add a27 a26
  let a33 : SignedPair S := pairCompute GateOp.mul a20 a32
  let a34 : SignedPair S := pairCompute GateOp.add a33 a19
  let a35 : SignedPair S := pairCompute GateOp.mul a32 a32
  let a36 : SignedPair S := ⟨w 21, 0⟩
  let a37 : SignedPair S := pairCompute GateOp.mul a32 a31
  let a38 : SignedPair S := pairCompute GateOp.add a25 a37
  let a39 : SignedPair S := pairCompute GateOp.mul a13 a34
  let a40 : SignedPair S := ⟨w 22, 0⟩
  let a41 : SignedPair S := ⟨w 23, 0⟩
  let a42 : SignedPair S := ⟨w 24, 0⟩
  let a43 : SignedPair S := pairCompute GateOp.mul a40 a40
  let a44 : SignedPair S := pairCompute GateOp.sub a43 a42
  let a45 : SignedPair S := pairCompute GateOp.sub a22 a1
  let a46 : SignedPair S := pairCompute GateOp.sub a45 a2
  let a47 : SignedPair S := pairCompute GateOp.mul a21 a45
  let a48 : SignedPair S := ⟨w 25, w 26⟩
  let a49 : SignedPair S := pairCompute GateOp.sub a23 a18
  let a50 : SignedPair S := pairCompute GateOp.mul a48 a49
  let a51 : SignedPair S := pairCompute GateOp.mul a22 a17
  let a52 : SignedPair S := pairCompute GateOp.add a16 a51
  let a53 : SignedPair S := pairCompute GateOp.mul a52 a0
  let a54 : SignedPair S := pairCompute GateOp.add a50 a53
  let a55 : SignedPair S := pairCompute GateOp.mul a27 a9
  let a56 : SignedPair S := pairCompute GateOp.add a55 a28
  let a57 : SignedPair S := ⟨w 27, w 28⟩
  let a58 : SignedPair S := pairCompute GateOp.mul a57 a57
  let a59 : SignedPair S := pairCompute GateOp.add a30 a28
  let a60 : SignedPair S := pairCompute GateOp.mul a30 a59
  let a61 : SignedPair S := pairCompute GateOp.sub a58 a60
  let a62 : SignedPair S := pairCompute GateOp.add a15 a8
  let a63 : SignedPair S := pairCompute GateOp.mul a62 a46
  let a64 : SignedPair S := pairCompute GateOp.add a63 a45
  let a65 : SignedPair S := pairCompute GateOp.mul a3 a21
  let a66 : SignedPair S := pairCompute GateOp.sub a64 a65
  let a67 : SignedPair S := ⟨w 29, 0⟩
  let a68 : SignedPair S := pairCompute GateOp.mul a31 a6
  let a69 : SignedPair S := ⟨w 30, w 31⟩
  let a70 : SignedPair S := pairCompute GateOp.mul a67 a69
  let a71 : SignedPair S := ⟨w 32, w 33⟩
  let a72 : SignedPair S := ⟨w 34, 0⟩
  let a73 : SignedPair S := ⟨w 35, 0⟩
  let a74 : SignedPair S := pairCompute GateOp.mul a71 a71
  let a75 : SignedPair S := pairCompute GateOp.mul a12 a12
  let a76 : SignedPair S := ⟨w 36, w 37⟩
  let a77 : SignedPair S := pairCompute GateOp.mul a73 a76
  let a78 : SignedPair S := pairCompute GateOp.add a77 a75
  let a79 : SignedPair S := pairCompute GateOp.mul a36 a67
  let a80 : SignedPair S := pairCompute GateOp.sub a79 a73
  ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77, a78, a79, a80]

/-- The checked external candidate's 60 source gates, in their original order. -/
def gates : List (Gate (Fin 81)) :=
  [
    ⟨21, 14, 0, GateOp.mul⟩,
    ⟨22, 21, 18, GateOp.add⟩,
    ⟨23, 22, 22, GateOp.mul⟩,
    ⟨24, 23, 22, GateOp.mul⟩,
    ⟨25, 8, 22, GateOp.mul⟩,
    ⟨26, 7, 24, GateOp.mul⟩,
    ⟨27, 25, 26, GateOp.mul⟩,
    ⟨28, 10, 11, GateOp.add⟩,
    ⟨29, 28, 26, GateOp.mul⟩,
    ⟨30, 27, 29, GateOp.mul⟩,
    ⟨31, 29, 10, GateOp.add⟩,
    ⟨32, 27, 26, GateOp.add⟩,
    ⟨33, 20, 32, GateOp.mul⟩,
    ⟨34, 33, 19, GateOp.add⟩,
    ⟨35, 32, 32, GateOp.mul⟩,
    ⟨36, 35, 34, GateOp.add⟩,
    ⟨37, 32, 31, GateOp.mul⟩,
    ⟨38, 25, 37, GateOp.add⟩,
    ⟨39, 13, 34, GateOp.mul⟩,
    ⟨40, 38, 39, GateOp.add⟩,
    ⟨41, 31, 31, GateOp.mul⟩,
    ⟨42, 36, 41, GateOp.mul⟩,
    ⟨43, 40, 40, GateOp.mul⟩,
    ⟨44, 43, 42, GateOp.sub⟩,
    ⟨45, 22, 1, GateOp.sub⟩,
    ⟨46, 45, 2, GateOp.sub⟩,
    ⟨47, 21, 45, GateOp.mul⟩,
    ⟨48, 47, 2, GateOp.add⟩,
    ⟨49, 23, 18, GateOp.sub⟩,
    ⟨50, 48, 49, GateOp.mul⟩,
    ⟨51, 22, 17, GateOp.mul⟩,
    ⟨52, 16, 51, GateOp.add⟩,
    ⟨53, 52, 0, GateOp.mul⟩,
    ⟨54, 50, 53, GateOp.add⟩,
    ⟨55, 27, 9, GateOp.mul⟩,
    ⟨56, 55, 28, GateOp.add⟩,
    ⟨57, 56, 54, GateOp.sub⟩,
    ⟨58, 57, 57, GateOp.mul⟩,
    ⟨59, 30, 28, GateOp.add⟩,
    ⟨60, 30, 59, GateOp.mul⟩,
    ⟨61, 58, 60, GateOp.sub⟩,
    ⟨62, 15, 8, GateOp.add⟩,
    ⟨63, 62, 46, GateOp.mul⟩,
    ⟨64, 63, 45, GateOp.add⟩,
    ⟨65, 3, 21, GateOp.mul⟩,
    ⟨66, 64, 65, GateOp.sub⟩,
    ⟨67, 4, 4, GateOp.mul⟩,
    ⟨68, 31, 6, GateOp.mul⟩,
    ⟨69, 68, 54, GateOp.sub⟩,
    ⟨70, 67, 69, GateOp.mul⟩,
    ⟨71, 70, 31, GateOp.sub⟩,
    ⟨72, 5, 42, GateOp.mul⟩,
    ⟨73, 72, 72, GateOp.mul⟩,
    ⟨74, 71, 71, GateOp.mul⟩,
    ⟨75, 12, 12, GateOp.mul⟩,
    ⟨76, 74, 75, GateOp.sub⟩,
    ⟨77, 73, 76, GateOp.mul⟩,
    ⟨78, 77, 75, GateOp.add⟩,
    ⟨79, 36, 67, GateOp.mul⟩,
    ⟨80, 79, 73, GateOp.sub⟩
  ]

/-- Proposed reverse-side gate constraints for one final assignment. -/
def gatesHold {S R : Type*} [CommSemiring S] [CommRing R]
    (embed : S →+* R) (ports : Fin 4 → S) (w : Fin 38 → S) : Prop :=
  let v := assignment ports w
  ∀ g ∈ gates,
    positiveResidual embed g.op (v g.left) (v g.right) (v g.target) = 0 ∧
    negativeResidual embed g.op (v g.left) (v g.right) (v g.target) = 0

/-- The five proposed graph norm targets, in the model difference ring. -/
def fiveNorms {S R : Type*} [CommSemiring S] [CommRing R]
    (embed : S →+* R) (ports : Fin 4 → S) (w : Fin 38 → S) : Prop :=
  let v := assignment ports w
  pairValue embed (v 61) = 1 ∧
  pairValue embed (v 44) = 1 ∧
  pairValue embed (v 78) = 1 ∧
  pairValue embed (v 66) = 1 ∧
  pairValue embed (v 80) = pairValue embed (v 36)

-- Unresolved: derive gatesHold and fiveNorms from the 29 seed residuals;
-- construct the final assignment trace; identify these values with the
-- Carrier65 core under actual port casts and positive shifted inputs.
end DiophantineConsistency.NormAssignment38
