import Mathlib

/-!
# Coordinate certificates for Desargues and Pascal

STATUS: Candidate Lean source. This file has NOT been compiled in the
authoring environment, which had no Lean executable. Target: Lean/mathlib
v4.32.0, matching the inspected ProveIt revision. There are no proof holes
or additional axiom declarations. The explicit `ring` proofs are intended
to be checked by Lean; their mathematical identities are independently
checked by the exact-arithmetic verifier in this package.

This is an AMBIENT Lean algebra layer. It does not yet construct
`LeanProofs.ConciseIPRA.Prf` objects. See FORMALIZATION.txt for that separate
obligation and for the general-conic adjugate step.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace DesarguesPascal

structure V3 (R : Type*) where
  x : R
  y : R
  z : R

structure V6 (R : Type*) where
  c0 : R
  c1 : R
  c2 : R
  c3 : R
  c4 : R
  c5 : R

variable {R : Type*} [CommRing R]

def dot (a b : V3 R) : R := a.x * b.x + a.y * b.y + a.z * b.z

def cross (a b : V3 R) : V3 R :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

def det (a b c : V3 R) : R := dot a (cross b c)

/-- Intersection of the two joins; allowed to be the zero vector. -/
def meet (a b c d : V3 R) : V3 R := cross (cross a b) (cross c d)

/-- Positive finite data for a nonzero homogeneous representative. -/
def Apart (v : V3 R) : Prop := v.x ≠ 0 ∨ v.y ≠ 0 ∨ v.z ≠ 0

theorem join_left (a b : V3 R) : dot (cross a b) a = 0 := by
  dsimp [dot, cross]
  ring

theorem join_right (a b : V3 R) : dot (cross a b) b = 0 := by
  dsimp [dot, cross]
  ring

theorem cyclic_det (a b c : V3 R) : dot (cross a b) c = det a b c := by
  dsimp [dot, cross, det]
  ring

/-- The three scalar components of the adjugate identity. -/
theorem adjugate_x (u v w o : V3 R) :
    det u v w * o.x =
      dot u o * (cross v w).x + dot v o * (cross w u).x +
        dot w o * (cross u v).x := by
  dsimp [dot, cross, det]
  ring

theorem adjugate_y (u v w o : V3 R) :
    det u v w * o.y =
      dot u o * (cross v w).y + dot v o * (cross w u).y +
        dot w o * (cross u v).y := by
  dsimp [dot, cross, det]
  ring

theorem adjugate_z (u v w o : V3 R) :
    det u v w * o.z =
      dot u o * (cross v w).z + dot v o * (cross w u).z +
        dot w o * (cross u v).z := by
  dsimp [dot, cross, det]
  ring

/-- Universal division-free Desargues polynomial. -/
theorem desargues_identity (a b c a' b' c' : V3 R) :
    det (meet a b a' b') (meet b c b' c') (meet c a c' a') =
      det a b c * det a' b' c' *
        det (cross a a') (cross b b') (cross c c') := by
  dsimp [meet, dot, cross, det]
  ring

theorem desargues_of_join_det_zero (a b c a' b' c' : V3 R)
    (h : det (cross a a') (cross b b') (cross c c') = 0) :
    det (meet a b a' b') (meet b c b' c') (meet c a c' a') = 0 := by
  rw [desargues_identity, h]
  ring

section IntegralDomain

variable [NoZeroDivisors R]

/-- A nonzero common kernel vector forces a 3 by 3 determinant to vanish. -/
theorem det_zero_of_kernel (u v w o : V3 R) (ho : Apart o)
    (hu : dot u o = 0) (hv : dot v o = 0) (hw : dot w o = 0) :
    det u v w = 0 := by
  rcases ho with hx | hy | hz
  · have h : det u v w * o.x = 0 := by
      simpa [hu, hv, hw] using adjugate_x u v w o
    exact (mul_eq_zero.mp h).resolve_right hx
  · have h : det u v w * o.y = 0 := by
      simpa [hu, hv, hw] using adjugate_y u v w o
    exact (mul_eq_zero.mp h).resolve_right hy
  · have h : det u v w * o.z = 0 := by
      simpa [hu, hv, hw] using adjugate_z u v w o
    exact (mul_eq_zero.mp h).resolve_right hz

theorem desargues_of_center (a b c a' b' c' o : V3 R)
    (ho : Apart o)
    (ha : dot (cross a a') o = 0)
    (hb : dot (cross b b') o = 0)
    (hc : dot (cross c c') o = 0) :
    det (meet a b a' b') (meet b c b' c') (meet c a c' a') = 0 := by
  apply desargues_of_join_det_zero
  exact det_zero_of_kernel (cross a a') (cross b b') (cross c c') o ho ha hb hc

theorem desargues_converse_det (a b c a' b' c' : V3 R)
    (h₁ : det a b c ≠ 0) (h₂ : det a' b' c' ≠ 0)
    (h : det (meet a b a' b') (meet b c b' c') (meet c a c' a') = 0) :
    det (cross a a') (cross b b') (cross c c') = 0 := by
  have h' : det a b c * det a' b' c' *
      det (cross a a') (cross b b') (cross c c') = 0 := by
    rw [← desargues_identity]
    exact h
  exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero h₁ h₂)

end IntegralDomain

/-- When two output points are apart, their cross product is an explicit axis. -/
theorem explicit_axis (x y z : V3 R) (ha : Apart (cross x y))
    (h : det x y z = 0) :
    Apart (cross x y) ∧ dot (cross x y) x = 0 ∧
      dot (cross x y) y = 0 ∧ dot (cross x y) z = 0 := by
  refine ⟨ha, join_left x y, join_right x y, ?_⟩
  rw [cyclic_det, h]

def pascalDet (a b c d e f : V3 R) : R :=
  det (meet a b d e) (meet b c e f) (meet c d f a)

/-- The compact bracket form of the Pascal polynomial. -/
theorem pascal_bracket_identity (a b c d e f : V3 R) :
    pascalDet a b c d e f =
      det a b e * det a c d * det b c f * det d e f -
        det a b c * det a d e * det b e f * det c d f := by
  dsimp [pascalDet, meet, dot, cross, det]
  ring

def veronese (a : V3 R) : V6 R :=
  ⟨a.x * a.x, a.y * a.y, a.z * a.z,
   a.x * a.y, a.x * a.z, a.y * a.z⟩

def get6 (a : V6 R) : Nat → R
  | 0 => a.c0
  | 1 => a.c1
  | 2 => a.c2
  | 3 => a.c3
  | 4 => a.c4
  | 5 => a.c5
  | _ => 0

def minor3 (a b c : V6 R) (i j k : Nat) : R :=
  det ⟨get6 a i, get6 a j, get6 a k⟩
      ⟨get6 b i, get6 b j, get6 b k⟩
      ⟨get6 c i, get6 c j, get6 c k⟩

/-- Laplace expansion of a 6 by 6 row determinant along the first three rows.
The 20 summands correspond to the increasing triples of columns. -/
def det6 (a b c d e f : V6 R) : R :=
    minor3 a b c 0 1 2 * minor3 d e f 3 4 5
  - minor3 a b c 0 1 3 * minor3 d e f 2 4 5
  + minor3 a b c 0 1 4 * minor3 d e f 2 3 5
  - minor3 a b c 0 1 5 * minor3 d e f 2 3 4
  + minor3 a b c 0 2 3 * minor3 d e f 1 4 5
  - minor3 a b c 0 2 4 * minor3 d e f 1 3 5
  + minor3 a b c 0 2 5 * minor3 d e f 1 3 4
  + minor3 a b c 0 3 4 * minor3 d e f 1 2 5
  - minor3 a b c 0 3 5 * minor3 d e f 1 2 4
  + minor3 a b c 0 4 5 * minor3 d e f 1 2 3
  - minor3 a b c 1 2 3 * minor3 d e f 0 4 5
  + minor3 a b c 1 2 4 * minor3 d e f 0 3 5
  - minor3 a b c 1 2 5 * minor3 d e f 0 3 4
  - minor3 a b c 1 3 4 * minor3 d e f 0 2 5
  + minor3 a b c 1 3 5 * minor3 d e f 0 2 4
  - minor3 a b c 1 4 5 * minor3 d e f 0 2 3
  + minor3 a b c 2 3 4 * minor3 d e f 0 1 5
  - minor3 a b c 2 3 5 * minor3 d e f 0 1 4
  + minor3 a b c 2 4 5 * minor3 d e f 0 1 3
  - minor3 a b c 3 4 5 * minor3 d e f 0 1 2

/-- Universal Pascal identity, including degenerate configurations. -/
theorem pascal_veronese_identity (a b c d e f : V3 R) :
    pascalDet a b c d e f =
      det6 (veronese a) (veronese b) (veronese c)
        (veronese d) (veronese e) (veronese f) := by
  dsimp [pascalDet, meet, det6, minor3, get6, veronese, dot, cross, det]
  ring

theorem pascal_of_veronese_det_zero (a b c d e f : V3 R)
    (h : det6 (veronese a) (veronese b) (veronese c)
      (veronese d) (veronese e) (veronese f) = 0) :
    pascalDet a b c d e f = 0 := by
  rw [pascal_veronese_identity, h]

def e1 : V3 R := ⟨1, 0, 0⟩
def e2 : V3 R := ⟨0, 1, 0⟩
def e3 : V3 R := ⟨0, 0, 1⟩

def mixed (a : V3 R) : V3 R := ⟨a.x * a.y, a.x * a.z, a.y * a.z⟩

theorem pascal_normalized_identity (d e f : V3 R) :
    pascalDet e1 e2 e3 d e f = det (mixed d) (mixed e) (mixed f) := by
  dsimp [pascalDet, e1, e2, e3, mixed, meet, dot, cross, det]
  ring

/-- Pascal for a conic through the coordinate triangle:
`q.x*x*y + q.y*x*z + q.z*y*z = 0`.
There is no smoothness or irreducibility hypothesis. -/
theorem pascal_normalized [NoZeroDivisors R] (d e f q : V3 R)
    (hq : Apart q)
    (hd : dot (mixed d) q = 0)
    (he : dot (mixed e) q = 0)
    (hf : dot (mixed f) q = 0) :
    pascalDet e1 e2 e3 d e f = 0 := by
  rw [pascal_normalized_identity]
  exact det_zero_of_kernel (mixed d) (mixed e) (mixed f) q hq hd he hf

end DesarguesPascal
