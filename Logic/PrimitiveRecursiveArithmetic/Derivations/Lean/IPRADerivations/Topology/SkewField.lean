import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Core.IntCancel
import IPRADerivations.Algebra.QuinticPrincipal

/-!
# Linear tangent fields on even spheres vanish

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/07_spheres.tex`, Theorem
`thm:linear-hairy` (S08): "Let `n` be even and `A` a rational `(n+1) × (n+1)` matrix satisfying `Aᵀ = −A`.
... Since `d = n + 1` is odd, `det A = det Aᵀ = det(−A) = (−1)^d det A = −det A`. Rational arithmetic gives
`det A = 0`."

For every odd size `k` and every `k × k` matrix of integer terms (rational data cleared of a common
denominator) whose skew symmetry `A_{ji} = −A_{ij}` is derivable:

* `skew_det_double`: `2 det A = 0`, from the transpose and the sign `(−1)^k = −1` evaluated in the ring of the
  context;
* `skew_det_zero`: `det A = 0`, cancelling the nonzero factor `2` (`Core/IntCancel`), so that the kernel is
  nontrivial and bounded elimination yields the zero of the field.
-/

namespace LeanProofs.IPRA.Topology.SkewField

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.QuinticPrincipal (two_ne_zero)
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-- `2 det A = 0` for an odd skew-symmetric matrix. -/
theorem skew_det_double {M : Mat k n} (hk : Odd k) (h : ∀ i j, Γ ⊢[PRAAx] ZT.eq (M j i) (-(M i j))) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * Mat.det M) (ZT.natLit 0) := by
  apply ZT.derive
  have hT : Matrix.transpose (Mat.toZ Γ M) = -(Mat.toZ Γ M) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Mat.toZ_apply]
    rw [ZT.toZ_eq (h i j), ZT.toZ_neg]
  have hd := Matrix.det_transpose (Mat.toZ Γ M)
  rw [hT, Matrix.det_neg, Fintype.card_fin, hk.neg_one_pow] at hd
  rw [ZT.toZ_mul, Mat.toZ_det, ZT.toZ_natLit, ZT.toZ_natLit]
  push_cast
  linear_combination -hd

/-- S08: an odd skew-symmetric matrix has determinant zero. -/
theorem skew_det_zero {M : Mat k n} (hk : Odd k) (h : ∀ i j, Γ ⊢[PRAAx] ZT.eq (M j i) (-(M i j))) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det M) (ZT.natLit 0) :=
  zt_mul_cancel_left two_ne_zero (skew_det_double hk h)

end LeanProofs.IPRA.Topology.SkewField
