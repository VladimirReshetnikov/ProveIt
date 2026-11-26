import IPRADerivations.Geometry.PlatonicSurface.Intrinsic

/-!
# The dodecahedral weighted gap

Packet: `geometry/platonic_surface_diameters_2026-11-19`, the dodecahedron (diameter `√((17 + 7√5)/2)`).
Imported from the packet's `lean/DodecahedronIPRA.lean`: `dodecaGap`, the two-strip averaged chamber estimate
with the positive `3/10` loss on nonvertex corner pairs, with `φ` replaced by `(s + r)/s`.
-/

namespace LeanProofs.IPRA.Geometry.PlatonicSurface.Dodecahedron

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (num)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Weighted 100M for the four-face strip. The formal parameter replacing φ
is (s+r)/s; keeping rational s,r symbolic needs only nonnegative terms. -/
def weighted (s r a b c d e f : PTm n) : PTm n :=
  let entry (u v : Nat) := num u*s + num v*(s+r)
  a*(entry 500 700*d + entry 475 750*e + entry 340 520*f) +
  b*(entry 475 600*d + entry 450 675*e + entry 315 470*f) +
  c*(entry 640 820*d + entry 615 920*e + entry 460 680*f)

def offCorner (a b c d e f : PTm n) : PTm n :=
  a*(e+f) + (b+c)*(d+e+f)

/-- The (0,0) entry is excluded. Remaining coefficients give the rational-
part excess of the nine gaps over 60, after substituting φ=1+r/s. -/
def excessAtOne (a b c d e f : PTm n) : PTm n :=
  a*(num 40*e + num 20*f) +
  b*(num 40*d + num 90*e + num 20*f) +
  c*(num 20*d + num 20*e + num 60*f)

def gapSlope (a b c d e f : PTm n) : PTm n :=
  a*(num 50*e + num 60*f) +
  b*(num 50*d + num 50*e + num 10*f) +
  c*(num 60*d + num 10*e + num 40*f)

/-- Two-strip averaged chamber estimate with the positive 3/10 loss on
all nonvertex corner pairs. Divide by 200sAB for positive totals A,B and
s, then approximate φ by rationals ≥1. -/
theorem dodecaGap (s r a b c d e f : PTm n) :
    Γ ⊢[PRAAx] le
      (weighted s r a b c d e f + weighted s r d e f a b c +
       num 60*s*offCorner a b c d e f)
      (num 200*(num 5*s+num 7*(s+r))*((a+b+c)*(d+e+f))) := by
  refine le_of_eq_add (d := s*excessAtOne a b c d e f + r*gapSlope a b c d e f) ?_
  unfold weighted offCorner excessAtOne gapSlope
  ipra_ring

end LeanProofs.IPRA.Geometry.PlatonicSurface.Dodecahedron
