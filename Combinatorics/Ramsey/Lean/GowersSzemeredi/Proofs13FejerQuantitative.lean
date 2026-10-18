import GowersSzemeredi.Proofs13FejerArrangementSelection
import GowersSzemeredi.Proofs13FejerNumerics
import GowersSzemeredi.Proofs13PreparedFrequencyGraph

/-! Quantitative purification with an even kernel length. The two explicit
scale inequalities pay for baseline survival and exceptional arrangements.
The signal uses the elementary shifted-pair estimate, not a sharp integral. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_purification_even {N M : Nat} [NeZero N] [Fact N.Prime]
    (hM : 0 < M) (hMN : 2 * M ≤ N)
    (U : Finset (Pair N)) (phi : Pair N → ZMod N)
    (beta rho eta : Real) (hbeta : 0 < beta) (hrho : 0 < rho) (heta : 0 < eta)
    (hcard : (U.card : Real) = beta * (N : Real) ^ 2)
    (habundance : rho * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 U phi)
    (hkernel : (2 : Real) ^ 34 ≤ rho * eta * (M : Real))
    (hmodulus : (2 : Real) ^ 131 * (M : Real) ^ 63 ≤ rho * eta * beta ^ 15 * (N : Real)) :
    ∃ S ⊆ U,
      ((2 : Real) ^ 65)⁻¹ * rho * ((M : Real) ^ 31)⁻¹ * beta ^ 15 * (N : Real) ^ 32 ≤
        (respectedArrangementCount 8 S phi : Real) ∧
      (arrangementCount 8 S : Real) ≤ (1 + eta) * (respectedArrangementCount 8 S phi : Real) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hs := fejer_signal_32_even hM
  have hbase := fejer_baseline_32_le_signal hM (rho * eta / 4) (by linarith)
  rw [hs] at hbase
  have htotal : (arrangementCount 8 U : Real) ≤ (U.card : Real) ^ 15 * (N : Real) ^ 2 := by
    exact_mod_cast context_arrangementCount_le_card_pow U
  rw [hcard] at htotal
  have hexc : (2 * ((2 * M : Nat) : Real)) ^ 32 * (2 * (N : Real) ^ 31) ≤
      rho * eta * beta ^ 15 * (N : Real) ^ 32 * ((M : Real) ^ 31)⁻¹ / 2 ^ 66 := by
    rw [← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
    push_cast
    linarith [mul_le_mul_of_nonneg_right hmodulus (pow_nonneg hn.le 31)]
  refine section13_fejer_purification_score (by omega) le_rfl hMN U phi eta _ heta
    (by positivity) ?_
  rw [hs]
  have hX : (0 : Real) ≤ eta * (((2 : Real) ^ 64)⁻¹ * ((M : Real) ^ 31)⁻¹) := by positivity
  linarith [mul_le_mul_of_nonneg_right habundance hX,
    mul_le_mul htotal hbase (by positivity) (by positivity)]

end LeanProofs.GowersSzemeredi
