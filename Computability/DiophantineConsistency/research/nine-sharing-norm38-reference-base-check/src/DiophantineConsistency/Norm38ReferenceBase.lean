import DiophantineConsistency.SharingTopology38

/-! UNCOMPILED DRAFT. Concrete source-DAG reference and extraction direction.
Imported topology and slot modules, tactics, provider routing and all
declarations here require Lean checking. No equivalence or endpoint is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38

/-- The first 60 source rows interpreted directly in a commutative ring. -/
def reference {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) : Fin 81 → R :=
  let a0 : R := x 0
  let a1 : R := x 1
  let a2 : R := x 2
  let a3 : R := x 3
  let a4 : R := x 4
  let a5 : R := x 5
  let a6 : R := x 6
  let a7 : R := x 7
  let a8 : R := x 8
  let a9 : R := x 9
  let a10 : R := x 10
  let a11 : R := x 11
  let a12 : R := x 12
  let a13 : R := x 13
  let a14 : R := p 0
  let a15 : R := p 1
  let a16 : R := p 2
  let a17 : R := p 3
  let a18 : R := 1
  let a19 : R := 3
  let a20 : R := 4
  let a21 : R := a14 * a0
  let a22 : R := a21 + a18
  let a23 : R := a22 * a22
  let a24 : R := a23 * a22
  let a25 : R := a8 * a22
  let a26 : R := a7 * a24
  let a27 : R := a25 * a26
  let a28 : R := a10 + a11
  let a29 : R := a28 * a26
  let a30 : R := a27 * a29
  let a31 : R := a29 + a10
  let a32 : R := a27 + a26
  let a33 : R := a20 * a32
  let a34 : R := a33 + a19
  let a35 : R := a32 * a32
  let a36 : R := a35 + a34
  let a37 : R := a32 * a31
  let a38 : R := a25 + a37
  let a39 : R := a13 * a34
  let a40 : R := a38 + a39
  let a41 : R := a31 * a31
  let a42 : R := a36 * a41
  let a43 : R := a40 * a40
  let a44 : R := a43 - a42
  let a45 : R := a22 - a1
  let a46 : R := a45 - a2
  let a47 : R := a21 * a45
  let a48 : R := a47 + a2
  let a49 : R := a23 - a18
  let a50 : R := a48 * a49
  let a51 : R := a22 * a17
  let a52 : R := a16 + a51
  let a53 : R := a52 * a0
  let a54 : R := a50 + a53
  let a55 : R := a27 * a9
  let a56 : R := a55 + a28
  let a57 : R := a56 - a54
  let a58 : R := a57 * a57
  let a59 : R := a30 + a28
  let a60 : R := a30 * a59
  let a61 : R := a58 - a60
  let a62 : R := a15 + a8
  let a63 : R := a62 * a46
  let a64 : R := a63 + a45
  let a65 : R := a3 * a21
  let a66 : R := a64 - a65
  let a67 : R := a4 * a4
  let a68 : R := a31 * a6
  let a69 : R := a68 - a54
  let a70 : R := a67 * a69
  let a71 : R := a70 - a31
  let a72 : R := a5 * a42
  let a73 : R := a72 * a72
  let a74 : R := a71 * a71
  let a75 : R := a12 * a12
  let a76 : R := a74 - a75
  let a77 : R := a73 * a76
  let a78 : R := a77 + a75
  let a79 : R := a36 * a67
  let a80 : R := a79 - a73
  ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77, a78, a79, a80]

/-- The exact initially defined node indices. -/
def initialNodes : List (Fin 81) :=
  (List.finRange 21).map fun i => Fin.castLE (by decide : 21 ≤ 81) i

/-- Candidate decidable check for the actual 60-row topological ordering. -/
theorem graph_topological : Topological NormAssignment38.gates initialNodes := by
  decide

end DiophantineConsistency.Norm38Reference

#print axioms DiophantineConsistency.Norm38Reference.graph_topological
