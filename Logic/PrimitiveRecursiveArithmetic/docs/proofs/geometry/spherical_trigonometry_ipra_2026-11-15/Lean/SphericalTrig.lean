import Mathlib
import SphericalKernel

/-!
# Abstract spherical-trigonometry layer

This file records the algebraic interfaces intended for a complete Lean
formalization.  It proves representative core consequences and specifies the
remaining analytic/branch data without identifying host-level real theorems
with object-language iPRA derivations.

STATUS: uncompiled prototype; no `sorry` and no custom axioms.
-/

namespace SphericalIPRA

class TrigSystem (Angle R : Type*) [AddCommGroup Angle] [CommRing R] where
  sin : Angle → R
  cos : Angle → R
  q : Angle
  sin_zero : sin 0 = 0
  cos_zero : cos 0 = 1
  sin_add : ∀ x y, sin (x+y) = sin x * cos y + cos x * sin y
  cos_add : ∀ x y, cos (x+y) = cos x * cos y - sin x * sin y
  pythagorean : ∀ x, sin x ^ 2 + cos x ^ 2 = 1
  sin_q : sin q = 1
  cos_q : cos q = 0

/-- Division-free algebraic certificate from the report, equation (4.16). -/
structure SphericalCore (R : Type*) [CommRing R] where
  x y z : R
  sa sb sc : R
  tau : R
  cA sA cB sB cC sC : R
  sa_sq : sa^2 + x^2 = 1
  sb_sq : sb^2 + y^2 = 1
  sc_sq : sc^2 + z^2 = 1
  gram : tau^2 = 1 + 2*x*y*z - x^2 - y^2 - z^2
  cA_num : sb*sc*cA = x - y*z
  cB_num : sc*sa*cB = y - z*x
  cC_num : sa*sb*cC = z - x*y
  sA_num : sb*sc*sA = tau
  sB_num : sc*sa*sB = tau
  sC_num : sa*sb*sC = tau

namespace SphericalCore

variable {R : Type*} [CommRing R] (T : SphericalCore R)

theorem side_cosine_A : T.x = T.y*T.z + T.sb*T.sc*T.cA := by
  linear_combination T.cA_num

theorem side_cosine_B : T.y = T.z*T.x + T.sc*T.sa*T.cB := by
  linear_combination T.cB_num

theorem side_cosine_C : T.z = T.x*T.y + T.sa*T.sb*T.cC := by
  linear_combination T.cC_num

theorem angle_pair_A_numerator :
    (T.x - T.y*T.z)^2 + T.tau^2 =
      (1-T.y^2)*(1-T.z^2) :=
  angle_pair_numerator T.x T.y T.z T.tau T.gram

theorem supplemental_A_numerator :
    -(T.y-T.z*T.x)*(T.z-T.x*T.y) + T.x*T.tau^2 =
      (1-T.x^2)*(T.x-T.y*T.z) :=
  supplemental_cosine_numerator T.x T.y T.z T.tau T.gram

theorem solid_angle_normalization :
    (1+T.x+T.y+T.z)^2 + T.tau^2 =
      2*(1+T.x)*(1+T.y)*(1+T.z) :=
  solid_angle_norm T.x T.y T.z T.tau T.gram

end SphericalCore

/-- Ordered information required only for cancellation and branch selection. -/
structure ProperCore (R : Type*) [LinearOrderedField R]
    extends SphericalCore R where
  sa_pos : 0 < sa
  sb_pos : 0 < sb
  sc_pos : 0 < sc
  tau_pos : 0 < tau

namespace ProperCore

variable {R : Type*} [LinearOrderedField R] (T : ProperCore R)

theorem sine_cross_AB : T.sA*T.sb = T.sB*T.sa := by
  have hsc : T.sc ≠ 0 := ne_of_gt T.sc_pos
  have hp : T.sc * (T.sA*T.sb - T.sB*T.sa) = 0 := by
    calc
      T.sc * (T.sA*T.sb - T.sB*T.sa)
          = T.sb*T.sc*T.sA - T.sc*T.sa*T.sB := by ring
      _ = 0 := by rw [T.sA_num, T.sB_num]; ring
  have hz : T.sA*T.sb - T.sB*T.sa = 0 :=
    (mul_eq_zero.mp hp).resolve_left hsc
  exact sub_eq_zero.mp hz

theorem sine_cross_BC : T.sB*T.sc = T.sC*T.sb := by
  have hsa : T.sa ≠ 0 := ne_of_gt T.sa_pos
  have hp : T.sa * (T.sB*T.sc - T.sC*T.sb) = 0 := by
    calc
      T.sa * (T.sB*T.sc - T.sC*T.sb)
          = T.sc*T.sa*T.sB - T.sa*T.sb*T.sC := by ring
      _ = 0 := by rw [T.sB_num, T.sC_num]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hsa)

end ProperCore

/-- Presentation layer: actual angle terms realizing a proper core. -/
structure NamedSphericalTriangle
    (Angle R : Type*) [AddCommGroup Angle] [LinearOrderedField R]
    [TrigSystem Angle R] where
  a b c A B C : Angle
  core : ProperCore R
  cos_a : TrigSystem.cos a = core.x
  sin_a : TrigSystem.sin a = core.sa
  cos_b : TrigSystem.cos b = core.y
  sin_b : TrigSystem.sin b = core.sb
  cos_c : TrigSystem.cos c = core.z
  sin_c : TrigSystem.sin c = core.sc
  cos_A : TrigSystem.cos A = core.cA
  sin_A : TrigSystem.sin A = core.sA
  cos_B : TrigSystem.cos B = core.cB
  sin_B : TrigSystem.sin B = core.sB
  cos_C : TrigSystem.cos C = core.cC
  sin_C : TrigSystem.sin C = core.sC

/-!
Completion modules should add, in this order:

1. integer-angle syntax and a Gaussian Laurent polynomial normalizer;
2. polar-triangle data and involution;
3. explicit half-angle witnesses (`hA+hA=A`, etc.) plus positivity intervals;
4. cross-multiplied Delambre identities, then guarded Napier/tangent forms;
5. cotangent, five-part, Cagnoli, right and quadrantal families;
6. constructive derivative names and the differential variation equations;
7. equal-area chart names and the finite lune/triangle dissection;
8. a separate tetrahedral structure built from `V3.face_area_closure`.

The object-language bridge is in `IPRABridge.lean`; none of the declarations in
this file by itself establishes `Prf PRAAx` derivability.
-/

end SphericalIPRA
