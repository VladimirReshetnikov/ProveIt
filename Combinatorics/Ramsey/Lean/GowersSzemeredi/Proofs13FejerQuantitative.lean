import GowersSzemeredi.Proofs13FejerArrangementSelection
import GowersSzemeredi.Proofs13FejerNumerics
import GowersSzemeredi.Proofs13ContextExtraction

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
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hm0 : (M : Real) ≠ 0 := ne_of_gt hm
  let signal : Real := ((((2 * M : Nat) : Real) ^ 2)⁻¹) ^ 32 * (M : Real) ^ 33
  let baseline : Real := ((((2 * M : Nat) : Real))⁻¹) ^ 32
  let q : Real := beta ^ 15 * (N : Real) ^ 32
  let mass : Real := rho * q * signal / 2
  have hs : signal = ((2 : Real) ^ 64)⁻¹ * ((M : Real) ^ 31)⁻¹ := fejer_signal_32_even hM
  have hspos : 0 < signal := by rw [hs]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hmass : 0 < mass := by dsimp [mass]; positivity
  have hbase : baseline ≤ (rho * eta / 4) * signal := by
    apply fejer_baseline_32_le_signal hM
    norm_num only [pow_succ, pow_zero, mul_one] at hkernel ⊢
    nlinarith only [hkernel]
  have hexc : (2 * ((2 * M : Nat) : Real)) ^ 32 * (2 * (N : Real) ^ 31) ≤
      rho * eta * q * signal / 4 := by
    let w : Real := (N : Real) ^ 31 / ((2 : Real) ^ 66 * (M : Real) ^ 31)
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have ht := mul_le_mul_of_nonneg_right hmodulus hw
    have hl : ((2 : Real) ^ 131 * (M : Real) ^ 63) * w =
        (2 * ((2 * M : Nat) : Real)) ^ 32 * (2 * (N : Real) ^ 31) := by
      dsimp [w]
      push_cast
      field_simp
    have hr : (rho * eta * beta ^ 15 * (N : Real)) * w = rho * eta * q * signal / 4 := by
      rw [hs]
      dsimp [w, q]
      field_simp
      ring
    rw [hl, hr] at ht
    exact ht
  have htotal : (arrangementCount 8 U : Real) ≤ q := by
    calc
      _ ≤ (U.card : Real) ^ 15 * (N : Real) ^ 2 := by
        exact_mod_cast context_arrangementCount_le_card_pow U
      _ = q := by rw [hcard]; dsimp [q]; ring
  have hg : rho * q ≤ (respectedArrangementCount 8 U phi : Real) := by
    simpa only [q, mul_assoc] using habundance
  have hg' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg heta.le) hspos.le
  have hb' : (arrangementCount 8 U : Real) * baseline ≤ q * ((rho * eta / 4) * signal) :=
    (mul_le_mul_of_nonneg_right htotal (by dsimp [baseline]; positivity)).trans
      (mul_le_mul_of_nonneg_left hbase hq.le)
  have hbudget : eta * mass ≤ eta * (respectedArrangementCount 8 U phi : Real) * signal -
      (arrangementCount 8 U : Real) * baseline -
      (2 * ((2 * M : Nat) : Real)) ^ 32 * (2 * (N : Real) ^ 31) := by
    dsimp [mass]
    nlinarith only [hg', hb', hexc]
  obtain ⟨S, hS, hmS, hratio⟩ := section13_fejer_purification_score (by omega : 2 ≤ 2 * M)
    (le_refl (2 * M)) hMN U phi eta mass heta hmass hbudget
  refine ⟨S, hS, ?_, hratio⟩
  have hmass_eq : mass = ((2 : Real) ^ 65)⁻¹ * rho * ((M : Real) ^ 31)⁻¹ * beta ^ 15 * (N : Real) ^ 32 := by
    dsimp [mass]
    rw [hs]
    dsimp [q]
    ring
  rwa [hmass_eq] at hmS

end LeanProofs.GowersSzemeredi
