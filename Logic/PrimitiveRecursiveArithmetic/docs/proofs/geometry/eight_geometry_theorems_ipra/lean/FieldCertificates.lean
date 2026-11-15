import Mathlib

/-!
# Field-level polynomial certificates for eight constructive geometry theorems

This file records compact scalar identities intended for the generic-field
layer of the full formalization.  It deliberately avoids division.  The
geometric wrappers (triples, nonzero hypotheses, projective equivalence, and
coded iPRA formulas) belong in later modules.

The delivery environment did not contain Lean, so this source is supplied as a
Mathlib-oriented starting point and is not claimed to have been build-tested.
-/

namespace ConstructiveGeometryIPRA

section CommRing

variable {K : Type*} [CommRing K]

/-- The bracket equality expressing cross-ratio `-1` in the normalized
Pappus-harmonic configuration. -/
theorem pappusHarmonic_bracket (t : K) :
    (-t) * (1 - t) + (-t) * (t - 1) = 0 := by
  ring

/-- The two automatic incidences of the explicit Ceva point. -/
theorem ceva_witness_AD (dB dC eC : K) :
    (-dC) * (dB * eC) + dB * (dC * eC) = 0 := by
  ring

theorem ceva_witness_BE (dC eA eC : K) :
    eC * (eA * dC) - eA * (dC * eC) = 0 := by
  ring

/-- The third Ceva incidence is exactly the product hypothesis. -/
theorem ceva_witness_CF
    (dB dC eA eC fA fB : K)
    (h : dC * eA * fB = dB * eC * fA) :
    (-fB) * (eA * dC) + fA * (dB * eC) = 0 := by
  calc
    (-fB) * (eA * dC) + fA * (dB * eC)
        = -(dC * eA * fB) + dB * eC * fA := by ring
    _ = 0 := by rw [h]; ring

/-- The Menelaus line through the first two side points evaluates to the
cross-multiplied Menelaus expression at the third point. -/
theorem menelaus_line_residue (dB dC eA eC fA fB : K) :
    (dB * eC) * fA + (dC * eA) * fB + (-dB * eA) * 0
      = dB * eC * fA + dC * eA * fB := by
  ring

/-- Division-free binary quadratic root-product factorization. -/
theorem binaryQuadratic_subtraction
    (v p w y1 z1 y2 z2 : K) :
    y2 * z2 * (v*y1^2 + p*y1*z1 + w*z1^2)
      - y1 * z1 * (v*y2^2 + p*y2*z2 + w*z2^2)
      = (y1*z2 - y2*z1) * (v*y1*y2 - w*z1*z2) := by
  ring

/-- First explicit factorization in the converse to Carnot's conic theorem. -/
theorem carnotConic_BC_factor
    (d1 d2 e1 e2 Ex Fy y z : K) :
    (e1*e2*Ex*Fy) * y^2
      - Ex*Fy*(e1*d2 + d1*e2) * y*z
      + (d1*d2*Ex*Fy) * z^2
      = Ex*Fy*(e1*y - d1*z)*(e2*y - d2*z) := by
  ring

/-- Second explicit factorization in the converse to Carnot's conic theorem. -/
theorem carnotConic_CA_factor
    (a1 a2 c1 c2 Dy Fy x z : K) :
    (c1*c2*Dy*Fy) * x^2
      - Dy*Fy*(c1*a2 + a1*c2) * z*x
      + (a1*a2*Dy*Fy) * z^2
      = Dy*Fy*(c1*x - a1*z)*(c2*x - a2*z) := by
  ring

/-- Third explicit factorization, after rewriting its `y^2` coefficient by
Carnot's product hypothesis. -/
theorem carnotConic_AB_factor
    (p1 p2 q1 q2 Dy Ez x y : K) :
    (q1*q2*Dy*Ez) * x^2
      - Dy*Ez*(q1*p2 + p1*q2) * x*y
      + (p1*p2*Dy*Ez) * y^2
      = Dy*Ez*(q1*x - p1*y)*(q2*x - p2*y) := by
  ring

/-- Representative endpoint identity behind Carnot's polygon theorem.  The
full theorem is an induction over lists. -/
theorem carnotSide_threeRoots (c t1 t2 t3 : K) :
    (c * ((1-t1)*(1-t2)*(1-t3))) * (t1*t2*t3)
      = (-1 : K)^3 * (c * ((-t1)*(-t2)*(-t3)))
          * ((1-t1)*(1-t2)*(1-t3)) := by
  ring

/-- The first five-factor cancellation in Hoehn after the determinant
relabellings have been established. -/
theorem hoehn_first_cycle
    (A0 A1 A2 A3 A4 S0 S1 S2 S3 S4 : K) :
    (A0*(-S1))*(A1*(-S2))*(A2*(-S3))*(A3*(-S4))*(A4*(-S0))
      = (S0*(-A2))*(S1*(-A3))*(S2*(-A4))*(S3*(-A0))*(S4*(-A1)) := by
  ring

/-- The second five-factor cancellation in Hoehn. -/
theorem hoehn_second_cycle
    (B0 B1 B2 B3 B4 S0 S1 S2 S3 S4 : K) :
    ((-B4)*S0)*((-B0)*S1)*((-B1)*S2)*((-B2)*S3)*((-B3)*S4)
      = ((-S1)*B0)*((-S2)*B1)*((-S3)*B2)*((-S4)*B3)*((-S0)*B4) := by
  ring

/-- The three scalar coordinates of `X - Y + Z = 0` in Pappus's hexagon
certificate. -/
theorem pappusHexagon_x (a b c d e f : K) :
    (a*d - b*e) - (a*d - c*f) + (b*e - c*f) = 0 := by
  ring

theorem pappusHexagon_y (a b c d e f : K) :
    (d-e) - (d-f) + (e-f) = 0 := by
  ring

theorem pappusHexagon_z (a b c d e f : K) :
    (a-b) - (a-c) + (b-c) = 0 := by
  ring

/-- First coordinate of Pascal's weighted vector certificate. -/
theorem pascal_x (a b c d e f : K) :
    (c-f) * (a*b*(d+e) - d*e*(a+b))
      + (d-a) * (b*c*(e+f) - e*f*(b+c))
      + (e-b) * (c*d*(f+a) - f*a*(c+d)) = 0 := by
  ring

/-- Second coordinate of Pascal's weighted vector certificate. -/
theorem pascal_y (a b c d e f : K) :
    (c-f) * (a*b - d*e)
      + (d-a) * (b*c - e*f)
      + (e-b) * (c*d - f*a) = 0 := by
  ring

/-- Third coordinate of Pascal's weighted vector certificate. -/
theorem pascal_z (a b c d e f : K) :
    (c-f) * (a+b-d-e)
      + (d-a) * (b+c-e-f)
      + (e-b) * (c+d-f-a) = 0 := by
  ring

/-- A point of the standard conic and its tangent are incident. -/
theorem standardConic_tangent (t : K) :
    (1 : K) * t^2 + (-2*t) * t + t^2 * 1 = 0 := by
  ring

end CommRing

end ConstructiveGeometryIPRA
