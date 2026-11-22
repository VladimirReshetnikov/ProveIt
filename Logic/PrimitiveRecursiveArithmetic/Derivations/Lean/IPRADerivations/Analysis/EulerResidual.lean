import IPRADerivations.Core.LinearAlgebra

/-!
# The exact coarse residual of the refined Euler polygon

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Theorem
`thm:ode-produced-refinement`, the identity `eq:ode-residual-identity`, as an iPRA derivation about integer-term
vectors and matrices (`Vec`, `Mat` of `Core/LinearAlgebra`, the rational data cleared of a common denominator):

For a coarse node value `x = X_{n,i}`, the slope matrices `B' = B(t_{j-1})`, `B = B(t_j)` and the fine step
`δ = 1/(2n)`, the fine-mesh values of the coarse polygon are `V_j = x + δ B' x` (the midpoint of the coarse step,
by interpolation) and `V_{j+1} = x + 2δ B' x`. Then "Substitution, with no approximation, gives"

  `r_j = V_{j+1} − V_j − δ B V_j = δ ((B' − B) x − δ B B' x)`

(`residual_identity`), and at an even fine index the residual vanishes (`residual_even`: `V_{j+1} = V_j + δ B V_j`
is the coarse step itself, stated as equality with the zero multiple `0 · x`).
-/

namespace LeanProofs.IPRA.Analysis.EulerResidual

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-- `eq:ode-residual-identity`: `(x + 2δB'x) − (x + δB'x) − δB(x + δB'x) = δ((B' − B)x − δB(B'x))`. -/
theorem residual_identity (B B' : Mat k n) (x : Vec k n) (δ : ZT n) :
    Γ ⊢[PRAAx] Vec.eqFm
      (Vec.sub (Vec.sub (Vec.add x (Vec.smul (ZT.natLit 2 * δ) (Mat.mulVec B' x)))
          (Vec.add x (Vec.smul δ (Mat.mulVec B' x))))
        (Vec.smul δ (Mat.mulVec B (Vec.add x (Vec.smul δ (Mat.mulVec B' x))))))
      (Vec.smul δ (Vec.sub (Mat.mulVec (Mat.sub B' B) x) (Vec.smul δ (Mat.mulVec B (Mat.mulVec B' x))))) := by
  apply Vec.derive
  funext i
  simp only [Vec.toZ_sub, Vec.toZ_add, Vec.toZ_smul, Mat.toZ_mulVec, Mat.toZ_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.sub_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat]
  ring

/-- At an even fine index the coarse polygon takes the coarse Euler step, so its residual vanishes:
`(x + 2δBx) − x − 2δBx = 0` (the step `2δ = 1/n` from the node `t_j = i/n`). -/
theorem residual_even (B : Mat k n) (x : Vec k n) (δ : ZT n) :
    Γ ⊢[PRAAx] Vec.eqFm
      (Vec.sub (Vec.sub (Vec.add x (Vec.smul (ZT.natLit 2 * δ) (Mat.mulVec B x))) x)
        (Vec.smul (ZT.natLit 2 * δ) (Mat.mulVec B x)))
      (Vec.smul (ZT.natLit 0) x) := by
  apply Vec.derive
  funext i
  simp only [Vec.toZ_sub, Vec.toZ_add, Vec.toZ_smul, Mat.toZ_mulVec, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero]
  ring

end LeanProofs.IPRA.Analysis.EulerResidual
