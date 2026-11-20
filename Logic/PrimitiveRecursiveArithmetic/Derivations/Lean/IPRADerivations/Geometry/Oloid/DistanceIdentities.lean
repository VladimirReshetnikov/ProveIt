import IPRADerivations.Core.Tactic

/-!
Packet: `geometry/oloid_surface_distance_audit_2026-11-19` (surface distances on the oloid). Imported from the
packet's `lean/ObjectIdentities.lean`, adapted to the library's namespace: `support_identity` (the Lagrange
identity for the support function), `tangent_identity` (the unit boundary tangent), `ruling_identity` (the
cleared squared ruling), `sylvester_identity` (the two-variable strong-convexity remainder),
`residual_identity` (completion of squares for a gradient residual), each also closed over signed variables.

Geometric identities as actual sequents of ordinary iPRA, for use
at arbitrary signed terms in an arbitrary open context. The public closed
endpoints quantify the natural-number pairs encoding signed variables.
-/
namespace LeanProofs.IPRA.Geometry.Oloid.DistanceIdentities
open LeanProofs LeanProofs.IPRA LeanProofs.ConciseIPRA
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def supportEquation (x y a b : ZT n) : Fm PTm n :=
  ZT.eq (ZT.sq (x*a+y*b) + ZT.sq (x*b-y*a))
    ((ZT.sq x + ZT.sq y) * (ZT.sq a + ZT.sq b))

theorem support_identity (x y a b : ZT n) :
    Γ ⊢[PRAAx] supportEquation x y a b := by
  unfold supportEquation
  ipra_ring

/-- The numerator identity for the unit boundary tangent. -/
def tangentEquation (u : ZT n) : Fm PTm n :=
  let s := ZT.sq u
  let d := ZT.natLit 1 - s
  ZT.eq (d*d*d + s * ZT.sq (ZT.natLit 3 + s)) (ZT.sq (ZT.natLit 1 + ZT.natLit 3 * s))

theorem tangent_identity (u : ZT n) : Γ ⊢[PRAAx] tangentEquation u := by
  unfold tangentEquation
  ipra_ring

/-- Squaring the spatial ruling after clearing the denominator (1+c).
The two circular square roots have already been replaced by their squares. -/
def rulingEquation (c : ZT n) : Fm PTm n :=
  let one := ZT.natLit 1
  let d := one+c
  let z := one+ZT.natLit 2*c
  let x := one+c+ZT.sq c
  ZT.eq (ZT.sq x + (one-ZT.sq c)*ZT.sq d + z) (ZT.natLit 3*ZT.sq d)

theorem ruling_identity (c : ZT n) : Γ ⊢[PRAAx] rulingEquation c := by
  unfold rulingEquation
  ipra_ring

theorem support_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 8 (supportEquation (ZT.var2 0 1) (ZT.var2 2 3) (ZT.var2 4 5) (ZT.var2 6 7)) :=
  closeUniv 8 (support_identity _ _ _ _)

theorem tangent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 2 (tangentEquation (ZT.var2 0 1)) := closeUniv 2 (tangent_identity _)

theorem ruling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 2 (rulingEquation (ZT.var2 0 1)) := closeUniv 2 (ruling_identity _)

/-- Positive-square remainder for the 2-variable strong-convexity test. -/
def sylvesterEquation (a b c x y : ZT n) : Fm PTm n :=
  ZT.eq (a*(a*ZT.sq x+ZT.natLit 2*b*x*y+c*ZT.sq y))
    (ZT.sq (a*x+b*y)+(a*c-ZT.sq b)*ZT.sq y)

theorem sylvester_identity (a b c x y : ZT n) :
    Γ ⊢[PRAAx] sylvesterEquation a b c x y := by
  unfold sylvesterEquation
  ipra_ring

/-- Cleared-denominator completion of squares for a gradient residual. -/
def residualEquation (x y a b k : ZT n) : Fm PTm n :=
  ZT.eq (ZT.sq (x+k*a)+ZT.sq (y+k*b))
    ((ZT.sq x+ZT.sq y)+ZT.natLit 2*k*(x*a+y*b)+ZT.sq k*(ZT.sq a+ZT.sq b))

theorem residual_identity (x y a b k : ZT n) :
    Γ ⊢[PRAAx] residualEquation x y a b k := by
  unfold residualEquation
  ipra_ring

theorem sylvester_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 10 (sylvesterEquation (ZT.var2 0 1) (ZT.var2 2 3) (ZT.var2 4 5)
      (ZT.var2 6 7) (ZT.var2 8 9)) := closeUniv 10 (sylvester_identity _ _ _ _ _)

theorem residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 10 (residualEquation (ZT.var2 0 1) (ZT.var2 2 3) (ZT.var2 4 5)
      (ZT.var2 6 7) (ZT.var2 8 9)) := closeUniv 10 (residual_identity _ _ _ _ _)

end LeanProofs.IPRA.Geometry.Oloid.DistanceIdentities
