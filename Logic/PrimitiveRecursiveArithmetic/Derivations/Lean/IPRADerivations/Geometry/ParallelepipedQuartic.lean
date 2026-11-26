import IPRADerivations.Geometry.PlatonicSections

/-!
# The isolating certificate of the skew parallelepiped quartic

Packet: `geometry/parallelepiped_surface_2026-11-19`, Section 7 (the skew `(1,1,2)` example, Gram data
`1, 1, 4, 0, 80/401, 0`): "Section 7 of the paper specifies the squared diameter by its irreducible quartic,
isolating interval ..."; the packet's Lean scaffold checks the bracket `rootBracket` and the derivative sign
`derivativeUpperNegative` by `decide`. Here they are derived in iPRA, with
`F(t) = c_0 + c_1 t + c_2 t² + c_3 t³ + c_4 t⁴`,
`c = (613884455156800, −209597886831520, 26061786638084, −1382740019876, 25856961601)`:

* `bracket_pos`: `d⁴ F(n/d) > 0` at `n/d = 457633/50000`;
* `bracket_neg`: `d⁴ F(n/d) < 0` at `n/d = 228817/25000`;
* `derivative_negative`: for every `x` with `915266 ≤ x ≤ 915268` (`d = 100000`), `d³ F'(x/d) < 0`, from the
  monomial-sign bound of the packet's `derivativeUpper` and its negative value.

Hence `F` changes sign and is strictly decreasing on `[9.15266, 9.15268]`: the interval isolates its root, the
squared diameter.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.ParallelepipedQuartic

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `d⁴ F(n/d)` over integer terms. -/
abbrev FS (x d : ZT n) : ZT n :=
  ZT.natLit 613884455156800 * (d * d * d * d) - ZT.natLit 209597886831520 * (x * (d * d * d)) +
    ZT.natLit 26061786638084 * (x * x * (d * d)) - ZT.natLit 1382740019876 * (x * x * x * d) +
    ZT.natLit 25856961601 * (x * x * x * x)

/-- The bracket, positive end. -/
theorem bracket_pos : Γ ⊢[PRAAx] zle (ZT.natLit 1) (FS (ZT.natLit 457633) (ZT.natLit 50000)) := by
  refine zle_of_toZ (num 46885618157909150270824320) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Q.mk_num, map_natCast]
  push_cast; norm_num

/-- The bracket, negative end. -/
theorem bracket_neg : Γ ⊢[PRAAx] zle (FS (ZT.natLit 228817) (ZT.natLit 25000) + ZT.natLit 1) (ZT.natLit 0) := by
  refine zle_of_toZ (num 2762491491834606562325278) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Q.mk_num, map_natCast]
  push_cast; norm_num

/-- `d³ F'(x/d) < 0` on `[915266, 915268]/100000`, with `d³F'(x/d) = 4c_4x³ + 3c_3x²d + 2c_2xd² + c_1d³`. -/
theorem derivative_negative {x : PTm n} (hl : Γ ⊢[PRAAx] le (num 915266) x) (hh : Γ ⊢[PRAAx] le x (num 915268)) :
    Γ ⊢[PRAAx] le (succ (num 4 * num 25856961601 * (x * x * x) + num 2 * num 26061786638084 * x *
      (num 100000 * num 100000)))
      (num 3 * num 1382740019876 * (x * x) * num 100000 +
        num 209597886831520 * (num 100000 * num 100000 * num 100000)) := by
  ipra_le 3 * 1382740019876 * 100000 * sl hl * (𝔟 x + 915266) + 727143346020821100864879871 +
    4 * 25856961601 * sl hh * (915268 ^ 2 + 915268 * 𝔟 x + 𝔟 x ^ 2) +
    2 * 26061786638084 * 100000 ^ 2 * sl hh

end LeanProofs.IPRA.Geometry.ParallelepipedQuartic
