import GowersSzemeredi.Proofs13GeometricThresholdEnvelope
import GowersSzemeredi.Proofs13FejerOddSquare

/-! The complete cubic Fourier inverse theorem at a conventional explicit
double-exponential modulus threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem real_le_double_exp (x : Real) : x ≤ Real.exp (Real.exp x) := by
  have h : x ≤ Real.exp x := by have h := Real.add_one_le_exp x; linarith only [h]
  exact h.trans (Real.exp_le_exp.mpr h)

theorem section13FourierThreshold_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section13FourierThreshold alpha ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) := by
  have ht : 1 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  unfold section13FourierThreshold
  apply max_le
  · exact (section13FrequencyGraphThreshold_le_power hα hαone).trans
      ((pow_le_pow_right₀ ht (by norm_num : (2 : Nat) ^ 37 ≤ (2 : Nat) ^ 54)).trans
        (real_le_double_exp _))
  · exact section13_fejer_geometric_threshold_le_double_exp hα hαone

/-- The proper common-step bilinear Fourier square with improved size and
density exists whenever N exceeds the displayed double exponential. -/
theorem theorem_13_12_fejer_double_exponential (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime]
    (hN : Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) ≤ N)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
      (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))) ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ :=
  theorem_13_12_fejer_explicit_threshold alpha hα hαone N
    ((section13FourierThreshold_le_double_exp hα hαone).trans hN) f hf hnot

/-- The same modulus bound suffices for the odd-square localization input. -/
theorem section13FejerOddSquareThreshold_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section13FejerOddSquareThreshold alpha ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) := by
  let x := 2 / alpha
  let A := x ^ ((2 : Nat) ^ 53)
  let e := (1 / 2 : Real) ^ A
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hA4 : 4 ≤ A := by
    calc
      _ = (2 : Real) ^ (2 : Nat) := by norm_num
      _ ≤ x ^ (2 : Nat) := pow_le_pow_left₀ (by norm_num) hx _
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num : (2 : Nat) ≤ (2 : Nat) ^ 53)
  have hA0 : 0 ≤ A := by linarith only [hA4]
  have he : 0 < e := Real.rpow_pos_of_pos (by norm_num) _
  have heI : e⁻¹ ≤ Real.exp A := by
    dsimp [e]
    rw [← Real.inv_rpow (by norm_num : (0 : Real) ≤ 1 / 2)]
    norm_num only [one_div, inv_inv]
    exact two_rpow_le_exp hA0
  have h1 : (1 : Real) ≤ Real.exp (1 * A) := by rw [one_mul]; exact Real.one_le_exp_iff.mpr hA0
  have h4 : (4 : Real) ≤ Real.exp (1 * A) := by
    rw [one_mul]
    exact (by norm_num : (4 : Real) ≤ 8).trans (eight_le_exp_of_four_le hA4)
  have hpower := positivePowerThreshold_le_double_exp (C := 4) (r := 1) zero_lt_one he.le hA0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 1) h4
    (by simpa only [inv_one] using h1) (by simpa only [one_mul] using heI)
  have hinner : 3 * A ≤ x ^ ((2 : Nat) ^ 54) := by
    have hx2 : (3 : Real) ≤ x ^ (2 : Nat) := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hx 2
      norm_num at hh
      linarith only [hh]
    calc
      _ ≤ x ^ (2 : Nat) * x ^ ((2 : Nat) ^ 53) := mul_le_mul_of_nonneg_right hx2 (by positivity)
      _ = x ^ (2 + (2 : Nat) ^ 53) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num)
  unfold section13FejerOddSquareThreshold
  refine max_le (section13FourierThreshold_le_double_exp hα hαone) ?_
  have hp : positivePowerThreshold 4 1 e ≤ Real.exp (Real.exp (3 * A)) := by
    norm_num only [show (1 + 1 + 1 : Real) = 3 by norm_num] at hpower
    exact hpower
  exact hp.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hinner))

end LeanProofs.GowersSzemeredi
