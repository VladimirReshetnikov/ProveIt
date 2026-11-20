import IPRADerivations.Geometry.PlatonicSurface.Intrinsic
import IPRADerivations.Core.Tactic

/-!
# The tetrahedral lattice and Voronoi inequalities

Packet: `geometry/platonic_surface_diameters_2026-11-19`, the tetrahedron (diameter `2/√3`, farthest point the
opposite face center). Imported from the packet's `lean/TetrahedronIPRA.lean`: `voronoiUpper` (the Voronoi
subtriangle bound), `sixMod`, `sixModZ` (a natural number congruent to `6` modulo `18` is at least `6`) and
`holeLower` (the lattice hole lower bound).
-/

namespace LeanProofs.IPRA.Geometry.PlatonicSurface.Tetrahedron

open LeanProofs.ConciseIPRA LeanProofs.IPRA LeanProofs.IPRA.Geometry.PlatonicSurface
open LeanProofs.IPRA.PTm (num monus)
open LeanProofs.ConciseIPRA.PTm (succ zero)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Barycentric counts a,b,c in the Voronoi subtriangle with corners
0, e, 2(e+f)/3. Squared norm is cleared by 9(a+b+c)². -/
theorem voronoiUpper (a b c : PTm n) :
    Γ ⊢[PRAAx] le
      ((num 3*b+num 2*c)*(num 3*b+num 2*c) +
       (num 3*b+num 2*c)*(num 2*c) + (num 2*c)*(num 2*c))
      (num 12*((a+b+c)*(a+b+c))) := by
  refine le_of_eq_add (d := num 12*a*a + num 24*a*b + num 24*a*c +
                            num 3*b*b + num 6*b*c) ?_
  ipra_ring

/-- A natural number congruent to 6 modulo 18 is at least 6. -/
theorem sixMod (X U V : PTm n)
    (e : Γ ⊢[PRAAx] X + num 18 * V ≐ num 6 + num 18 * U) :
    Γ ⊢[PRAAx] le (num 6) X := by
  refine .orE (lt_or_le U V) ?_ ?_
  · have h := natEq (eq_add_of_le
      (Prf.hyp0 : (lt U V :: Γ) ⊢[PRAAx] le (succ U) V))
    have h' := natEq (e.wk : (lt U V :: Γ) ⊢[PRAAx] _)
    apply succ_ne_zero' _ (a := X + num 18 * monus V (succ U) + num 11)
    apply deriveNat
    ipra_simps
    linear_combination h' - 18*h
  · have h := natEq (eq_add_of_le
      (Prf.hyp0 : (le V U :: Γ) ⊢[PRAAx] le V U))
    have h' := natEq (e.wk : (le V U :: Γ) ⊢[PRAAx] _)
    refine le_of_eq_add (d := num 18*monus U V) ?_
    apply deriveNat
    ipra_simps
    linear_combination h' + 18*h

theorem sixModZ (X : PTm n) (K : ZT n)
    (h : Γ ⊢[PRAAx] ZT.eq (z X) (z (num 6)+z (num 18)*K)) :
    Γ ⊢[PRAAx] le (num 6) X := by
  apply sixMod X K.pos K.neg
  have e := ZT.toZ_eq h
  ipra_simps
  simp only [ZT.toZ] at e
  apply deriveNat
  ipra_simps
  linear_combination e

/-- Twice Q(1−3m,1−3n), with the signed coordinates m=mp−mn, n=np−nn.
This is (9/2) times the geometric squared distance from h to 2(m e+n f). -/
def holeCost (mp mn np nn : PTm n) : PTm n :=
  twiceSq (num 1+num 3*mn) (num 1+num 3*nn) (num 3*mp) (num 3*np)

theorem holeLower (mp mn np nn : PTm n) :
    Γ ⊢[PRAAx] le (num 6) (holeCost mp mn np nn) := by
  let m := z mp-z mn
  let k := z np-z nn
  apply sixModZ _ (triQ m k-m-k)
  have e := ZT.toZ_eq (twiceSq_correct (Γ := Γ)
    (num 1+num 3*mn) (num 1+num 3*nn) (num 3*mp) (num 3*np))
  unfold holeCost
  dsimp only [m,k,triQ] at *
  apply ZT.derive
  ipra_simps
  linear_combination e

end LeanProofs.IPRA.Geometry.PlatonicSurface.Tetrahedron
