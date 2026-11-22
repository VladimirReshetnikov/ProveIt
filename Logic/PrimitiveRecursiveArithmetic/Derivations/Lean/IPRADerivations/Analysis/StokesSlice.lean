import IPRADerivations.Analysis.FiniteFTC
import IPRADerivations.Core.Integers

/-!
# Constructive Stokes: a grid slice and two polynomial certificates

Packet: `analysis/constructive_stokes_ipra_2026-11-21`, `report/03_cube.tex`, `report/05_geometry.tex` and
`lean/RepositorySlice.lean` (the packet's object-level adapter, adapted here and compiled against this workspace).

* `slice_upper`, `slice_lower`: along one grid line, cell inequalities between increments of a sampled potential `G`
  and a width-weighted derivative `Fpos − Fneg`, with a cell error `E`, telescope to the endpoint estimate
  (`FiniteFTC.ftc_upper`, `ftc_lower`); all other parameters are packed into `x`;
* `boundary_squared_square`: the four corner coefficients of the oriented boundary of a square cancel
  (`∂∂ = 0` on one cell);
* `curl_pullback_polynomial`: the polynomial identity behind the surface formula: the antisymmetrized derivative of
  the pullback of `P dx + Q dy + R dz` along a parameterization with tangent vectors `u`, `v` and common mixed second
  derivatives `m` is `curl F · (u × v)`.

These are the finite algebraic steps only. The rational mesh terms, the sum over transverse grid points, the error
schedule and the equality of the two regular names (the Stokes theorem of the packet) are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.StokesSlice
open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem slice_upper (G Fpos Fneg : PTm 2) (x N E : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 G (succ (var 0)) (Syn.shift x) +
            inst2 Fneg (var 0) (Syn.shift x))
        (inst2 G (var 0) (Syn.shift x) +
            inst2 Fpos (var 0) (Syn.shift x) + Syn.shift E))) :
    Γ ⊢[PRAAx] FiniteFTC.UpInv G Fpos Fneg N x E :=
  FiniteFTC.ftc_upper G Fpos Fneg x N E h

theorem slice_lower (G Fpos Fneg : PTm 2) (x N E : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 G (var 0) (Syn.shift x) +
            inst2 Fpos (var 0) (Syn.shift x))
        (inst2 G (succ (var 0)) (Syn.shift x) +
            inst2 Fneg (var 0) (Syn.shift x) + Syn.shift E))) :
    Γ ⊢[PRAAx] FiniteFTC.DnInv G Fpos Fneg N x E :=
  FiniteFTC.ftc_lower G Fpos Fneg x N E h

/-- The four corner coefficients of the oriented boundary cancel internally. -/
theorem boundary_squared_square (a00 a01 a10 a11 : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      ((a11 - a10) - (a01 - a00) - (a11 - a01) + (a10 - a00))
      (ZT.natLit 0) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_natLit]
    push_cast
    ring)

/-!
The next certificate is the algebra behind the classical surface formula.
`P,Q,R` are field components; `px,...,rz` their first derivatives;
`ux,uy,uz` and `vx,vy,vz` the two tangent vectors; and `mx,my,mz`
the common mixed second derivatives of a C2 parameterization.

This theorem proves only a polynomial identity.  Interpreting the symbols as
derivatives still requires the effective product/chain rules and the mixed-jet
certificate described in the report.  In particular, this code does not
silently assume that a name for a function also contains its derivative.
-/

theorem curl_pullback_polynomial
    (P Q R px py pz qx qy qz rx ry rz
      ux uy uz vx vy vz mx my mz : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (((px * ux + py * uy + pz * uz) * vx + P * mx) +
       ((qx * ux + qy * uy + qz * uz) * vy + Q * my) +
       ((rx * ux + ry * uy + rz * uz) * vz + R * mz) -
       (((px * vx + py * vy + pz * vz) * ux + P * mx) +
        ((qx * vx + qy * vy + qz * vz) * uy + Q * my) +
        ((rx * vx + ry * vy + rz * vz) * uz + R * mz)))
      ((ry - qz) * (uy * vz - uz * vy) +
       (pz - rx) * (uz * vx - ux * vz) +
       (qx - py) * (ux * vy - uy * vx)) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub]
    ring)

end LeanProofs.IPRA.Analysis.StokesSlice
