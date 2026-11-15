import GeometryCore

/-!
# General-conic Pascal implication

STATUS: Uncompiled candidate source, for Lean/mathlib v4.32.0.
This file deliberately uses the explicit fixed determinant from GeometryCore,
so there is no dependency on guessed names for Mathlib matrix lemmas.
The six column-replacement identities are ordinary commutative-ring identities.
They can be checked by the kernel after the `ring` tactic produces proof terms.

This remains an ambient Lean proof, not a reified iPRA derivation.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace DesarguesPascal

variable {R : Type*} [CommRing R]

def dot6 (a q : V6 R) : R :=
  a.c0 * q.c0 + a.c1 * q.c1 + a.c2 * q.c2 +
  a.c3 * q.c3 + a.c4 * q.c4 + a.c5 * q.c5

def Apart6 (q : V6 R) : Prop :=
  q.c0 ≠ 0 ∨ q.c1 ≠ 0 ∨ q.c2 ≠ 0 ∨
  q.c3 ≠ 0 ∨ q.c4 ≠ 0 ∨ q.c5 ≠ 0

/-- Replace column 0 by the linear combination of all columns with coefficients q. -/
def replaceCol0 (q a : V6 R) : V6 R :=
  { a with c0 := dot6 a q }

theorem column_identity0 (q a b c d e f : V6 R) :
    det6 (replaceCol0 q a) (replaceCol0 q b) (replaceCol0 q c)
      (replaceCol0 q d) (replaceCol0 q e) (replaceCol0 q f) =
        q.c0 * det6 a b c d e f := by
  dsimp [replaceCol0, dot6, det6, minor3, get6, det, dot, cross]
  ring

/-- Replace column 1 by the linear combination of all columns with coefficients q. -/
def replaceCol1 (q a : V6 R) : V6 R :=
  { a with c1 := dot6 a q }

theorem column_identity1 (q a b c d e f : V6 R) :
    det6 (replaceCol1 q a) (replaceCol1 q b) (replaceCol1 q c)
      (replaceCol1 q d) (replaceCol1 q e) (replaceCol1 q f) =
        q.c1 * det6 a b c d e f := by
  dsimp [replaceCol1, dot6, det6, minor3, get6, det, dot, cross]
  ring

/-- Replace column 2 by the linear combination of all columns with coefficients q. -/
def replaceCol2 (q a : V6 R) : V6 R :=
  { a with c2 := dot6 a q }

theorem column_identity2 (q a b c d e f : V6 R) :
    det6 (replaceCol2 q a) (replaceCol2 q b) (replaceCol2 q c)
      (replaceCol2 q d) (replaceCol2 q e) (replaceCol2 q f) =
        q.c2 * det6 a b c d e f := by
  dsimp [replaceCol2, dot6, det6, minor3, get6, det, dot, cross]
  ring

/-- Replace column 3 by the linear combination of all columns with coefficients q. -/
def replaceCol3 (q a : V6 R) : V6 R :=
  { a with c3 := dot6 a q }

theorem column_identity3 (q a b c d e f : V6 R) :
    det6 (replaceCol3 q a) (replaceCol3 q b) (replaceCol3 q c)
      (replaceCol3 q d) (replaceCol3 q e) (replaceCol3 q f) =
        q.c3 * det6 a b c d e f := by
  dsimp [replaceCol3, dot6, det6, minor3, get6, det, dot, cross]
  ring

/-- Replace column 4 by the linear combination of all columns with coefficients q. -/
def replaceCol4 (q a : V6 R) : V6 R :=
  { a with c4 := dot6 a q }

theorem column_identity4 (q a b c d e f : V6 R) :
    det6 (replaceCol4 q a) (replaceCol4 q b) (replaceCol4 q c)
      (replaceCol4 q d) (replaceCol4 q e) (replaceCol4 q f) =
        q.c4 * det6 a b c d e f := by
  dsimp [replaceCol4, dot6, det6, minor3, get6, det, dot, cross]
  ring

/-- Replace column 5 by the linear combination of all columns with coefficients q. -/
def replaceCol5 (q a : V6 R) : V6 R :=
  { a with c5 := dot6 a q }

theorem column_identity5 (q a b c d e f : V6 R) :
    det6 (replaceCol5 q a) (replaceCol5 q b) (replaceCol5 q c)
      (replaceCol5 q d) (replaceCol5 q e) (replaceCol5 q f) =
        q.c5 * det6 a b c d e f := by
  dsimp [replaceCol5, dot6, det6, minor3, get6, det, dot, cross]
  ring

/-- The fixed-size adjugate argument, expressed by column replacement. -/
theorem det6_zero_of_kernel [NoZeroDivisors R]
    (a b c d e f q : V6 R) (hq : Apart6 q)
    (ha : dot6 a q = 0) (hb : dot6 b q = 0) (hc : dot6 c q = 0)
    (hd : dot6 d q = 0) (he : dot6 e q = 0) (hf : dot6 f q = 0) :
    det6 a b c d e f = 0 := by
  rcases hq with h0 | h1 | h2 | h3 | h4 | h5
  · have hz : q.c0 * det6 a b c d e f = 0 := by
      rw [← column_identity0]
      dsimp only [replaceCol0, det6, minor3, get6, det, dot, cross]
      simp [ha, hb, hc, hd, he, hf]
    exact (mul_eq_zero.mp hz).resolve_left h0
  · have hz : q.c1 * det6 a b c d e f = 0 := by
      rw [← column_identity1]
      dsimp only [replaceCol1, det6, minor3, get6, det, dot, cross]
      simp [ha, hb, hc, hd, he, hf]
    exact (mul_eq_zero.mp hz).resolve_left h1
  · have hz : q.c2 * det6 a b c d e f = 0 := by
      rw [← column_identity2]
      dsimp only [replaceCol2, det6, minor3, get6, det, dot, cross]
      simp [ha, hb, hc, hd, he, hf]
    exact (mul_eq_zero.mp hz).resolve_left h2
  · have hz : q.c3 * det6 a b c d e f = 0 := by
      rw [← column_identity3]
      dsimp only [replaceCol3, det6, minor3, get6, det, dot, cross]
      simp [ha, hb, hc, hd, he, hf]
    exact (mul_eq_zero.mp hz).resolve_left h3
  · have hz : q.c4 * det6 a b c d e f = 0 := by
      rw [← column_identity4]
      dsimp only [replaceCol4, det6, minor3, get6, det, dot, cross]
      simp [ha, hb, hc, hd, he, hf]
    exact (mul_eq_zero.mp hz).resolve_left h4
  · have hz : q.c5 * det6 a b c d e f = 0 := by
      rw [← column_identity5]
      dsimp only [replaceCol5, det6, minor3, get6, det, dot, cross]
      simp [ha, hb, hc, hd, he, hf]
    exact (mul_eq_zero.mp hz).resolve_left h5

/-- A homogeneous quadratic with the coefficient order x²,y²,z²,xy,xz,yz. -/
def quadratic (q : V6 R) (a : V3 R) : R := dot6 (veronese a) q

/-- Pascal over every commutative ring without zero divisors, with an explicit
nonzero coefficient witness. No smoothness, factorization, parametrization,
coordinate normalization or division is used. Zero meets are permitted here;
`explicit_axis` adds a geometric line witness when a pair of meets is apart. -/
theorem pascal_of_conic [NoZeroDivisors R]
    (a b c d e f : V3 R) (q : V6 R) (hq : Apart6 q)
    (ha : quadratic q a = 0) (hb : quadratic q b = 0)
    (hc : quadratic q c = 0) (hd : quadratic q d = 0)
    (he : quadratic q e = 0) (hf : quadratic q f = 0) :
    pascalDet a b c d e f = 0 := by
  apply pascal_of_veronese_det_zero
  exact det6_zero_of_kernel
    (veronese a) (veronese b) (veronese c)
    (veronese d) (veronese e) (veronese f) q hq ha hb hc hd he hf

end DesarguesPascal
