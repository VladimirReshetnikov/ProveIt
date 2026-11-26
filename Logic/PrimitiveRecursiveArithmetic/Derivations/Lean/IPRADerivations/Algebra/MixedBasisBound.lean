import IPRADerivations.Algebra.StableRootBounds
import IPRADerivations.Probability.Expectation
import IPRADerivations.Analysis.RationalArithmetic.PowerSums

/-!
# Square-root certificate stability in mixed bases

Packet: `algebra/ipra_stable_observables`, `paper/sections/06_square_roots.tex`, Theorem `thm:sqrtstable`
("Square-root certificate stability"): for `S = Q diag(s) Qᵀ`, `T = R diag(t) Rᵀ` with rational orthogonal
`Q, R` and `s_i, t_j ≥ 0`, "the entirely rational inequality `F(S − T)² ≤ n F(S² − T²)` holds", where
`F` is the squared Frobenius norm. In the mixed bases, with `V = Qᵀ R`,
`(Qᵀ (S − T) R)_{ij} = (s_i − t_j) V_{ij}` and `(Qᵀ (S² − T²) R)_{ij} = (s_i² − t_j²) V_{ij}`, so
`F(S − T) = ∑ V_{ij}² (s_i − t_j)²` and `F(S² − T²) = ∑ V_{ij}² (s_i² − t_j²)²`, and `∑ V_{ij}² = n`.

Over the flattened index set of the pairs `(i, j)`, with weights `w = V_{ij}²` and the values `s_i`, `t_j`
given by bodies `s(k, x)`, `t(k, x)` (natural numerators):

* `dB`, `eB`: the bodies `|s − t|` and `|s² − t²|` (truncated-subtraction form);
* `entry_bound`: `∑ w |s − t|² ≤ ∑ w |s² − t²|`, from `sqrt_scalar` of `Algebra/StableRootBounds`;
* `mixed_basis_bound`: `(∑ w |s − t|²)² ≤ (∑ w |s² − t²|²) · ∑ w`, i.e. `F(S − T)² ≤ F(S² − T²) · n`
  when `∑ w = n`, by the weighted Cauchy–Schwarz inequality of `Probability/Expectation`.

The mixed-basis expansions themselves (orthogonality of `Q`, `R`, `∑ V_{ij}² = n`) are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.MixedBasisBound

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' second_moment)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open LeanProofs.IPRA.Algebra.StableRootBounds (sqrt_scalar)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Bound

variable (w s t : PTm 2)

/-- `|s − t|`. -/
def dB : PTm 2 := monus s t + monus t s
/-- `|s² − t²|`. -/
def eB : PTm 2 := monus (s * s) (t * t) + monus (t * t) (s * s)

theorem inst2_dB (k x : PTm n) : inst2 (dB s t) k x = ad (inst2 s k x) (inst2 t k x) := by
  simp [inst2, dB]

theorem inst2_eB (k x : PTm n) :
    inst2 (eB s t) k x = ad (inst2 s k x * inst2 s k x) (inst2 t k x * inst2 t k x) := by
  simp [inst2, eB]

/-- `∑ w |s − t|² ≤ ∑ w |s² − t²|`. -/
theorem entry_bound (N x : PTm n) :
    Γ ⊢[PRAAx] le (Ew w (dB s t * dB s t) N x) (Ew w (eB s t) N x) := by
  refine sum_le (w * (dB s t * dB s t)) (w * eB s t) x N (.allI (.impI ?_))
  rw [inst2_mul', inst2_mul', inst2_mul', inst2_dB, inst2_eB]
  exact le_congr (mul_comm _ _) (mul_comm _ _)
    (mul_le_mul_right _ (sqrt_scalar (inst2 s (var 0) (Syn.shift x)) (inst2 t (var 0) (Syn.shift x))))

/-- `thm:sqrtstable`: `(∑ w |s − t|²)² ≤ (∑ w |s² − t²|²) · ∑ w`. -/
theorem mixed_basis_bound (N x : PTm n) :
    Γ ⊢[PRAAx] le (Ew w (dB s t * dB s t) N x * Ew w (dB s t * dB s t) N x)
      (Ew w (eB s t * eB s t) N x * Wt w N x) :=
  le_trans (sq_le_sq (entry_bound w s t N x)) (second_moment w (eB s t) N x)

end Bound

end LeanProofs.IPRA.Algebra.MixedBasisBound
