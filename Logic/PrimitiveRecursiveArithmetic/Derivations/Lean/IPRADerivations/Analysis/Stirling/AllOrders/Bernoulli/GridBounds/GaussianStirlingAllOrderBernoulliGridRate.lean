import IPRADerivations.Analysis.Polynomials.GridSums.RationalPolynomialGridMean
import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GridBounds.GaussianStirlingAllOrderBernoulliGridMean

/-!
# The original centered Bernoulli mean and its grid error

The exact moment sum of the normalized Bernoulli polynomial vanishes
in positive degree. The centered sampler therefore has the negative
of the signed constant term as its mean, with an explicit mesh error.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliGridRate

open_ipra
open BernoulliBounds (bden bden_pos bint bint_eq toZ_zint)
open BernoulliCoefficients (bc bc_mean)
open GaussianStirlingAllOrderBernoulliGridMean (coefficients)
open GaussianStirlingAllOrderCenteredBernoulli (factor)
open GaussianStirlingAllOrderPanelDerivative (signedMean mean_value mean_den_positive)
open RationalPolynomialGridMeanError (meanNumerator radius weight weight_mul)
open RationalIntegerNormalization (normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalValueBounds (upper upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem coeff_mean (m : ℕ) (hm : 0 < m) :
    meanNumerator (coefficients m) = (-factor m * bint (2*m) 0) * ((2*m+1).factorial : ℤ) := by
  let d := 2*m
  suffices ((meanNumerator (coefficients m) : ℤ) : ℚ) =
      (-(factor m : ℚ) * (bint d 0 : ℚ)) * ((d+1).factorial : ℚ) by
    exact_mod_cast this
  have hbc : ∑ i : Fin (d+1), bc d i / (((i : ℕ) : ℚ) + 1) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => bc d i / ((i : ℚ) + 1))]
    have he : d = d-1+1 := by dsimp [d]; omega
    conv_lhs => rw [he]
    exact bc_mean (d-1)
  have hc (i : Fin (d+1)) : (weight i : ℚ)*(((i : ℕ) : ℚ)+1) = ((d+1).factorial : ℚ) := by
    have q := congrArg (fun a : ℕ => (a : ℚ)) (weight_mul i)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using q
  have integral : ∑ i : Fin (d+1), (bint d i : ℚ)*(weight i : ℚ) = 0 := by
    calc
      _ = ((bden d : ℚ)*((d+1).factorial : ℚ)) *
        ∑ i : Fin (d+1), bc d i / (((i : ℕ) : ℚ)+1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [bint_eq,← hc i]
          have hd : (((i : ℕ) : ℚ)+1) ≠ 0 := by positivity
          field_simp
      _ = 0 := by simp [hbc]
  rw [Fin.sum_univ_succ] at integral
  have h0 : (weight (0 : Fin (d+1)) : ℚ) = ((d+1).factorial : ℚ) := by simp [weight]
  rw [h0] at integral
  simp only [meanNumerator,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
  rw [Fin.sum_univ_succ]
  simp only [coefficients,if_true,Fin.succ_ne_zero,if_false,Int.cast_zero,
    Int.cast_mul,_root_.mul_assoc,← Finset.mul_sum]
  linear_combination (factor m : ℚ) * integral

theorem exact_mean (m : ℕ) (hm : 0 < m) :
    Γ ⊢[PRAAx] RationalPolynomialGridMean.mean (coefficients m) (bden (2*m)) ≐ signedMean m := by
  have hD := mean_den_positive (Γ := Γ) m
  have hF : Γ ⊢[PRAAx] le one (num ((2*m+1).factorial)) :=
    Foundations.NumeralPrimes.num_le (Nat.factorial_pos _)
  have h := GaussianRationalHorner.positive_product _ _ hD hF
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (normalize_well_formed _ _ h) (normalize_well_formed _ _ hD)
    (normalize_preserves_value _ _ h) (mean_value m) h hD
  apply ZT.derive
  simp [coeff_mean m hm,GaussianStirlingAllOrderPanelDerivative.meanNumerator,
    ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint,Q.mk_mul,Q.mk_num,map_mul]
  ring

def average (m : ℕ) (M : PTm n) : PTm n :=
  RationalPolynomialGridMean.average (coefficients m) (bden (2*m)) M

theorem mean_error (m : ℕ) (M : PTm n) (hm : 0 < m) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] upper (average m M) (signedMean m) (num (radius (coefficients m))) (num (bden (2*m))*M) ⋏
      upper (signedMean m) (average m M) (num (radius (coefficients m))) (num (bden (2*m))*M) := by
  have h := RationalPolynomialGridMean.average_error (coefficients m) (bden (2*m)) (bden_pos (2*m)) M hM
  have e := exact_mean (Γ := Γ) m hm
  exact .andI (upper_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _) h.andE₁)
    (upper_congr e (.eqRefl _) (.eqRefl _) (.eqRefl _) h.andE₂)

theorem actual_original_centered_Bernoulli_mean_error_closed (m : ℕ) (hm : 0 < m) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le one (var 0) ⟶
        upper (average m (var 0)) (signedMean m) (num (radius (coefficients m))) (num (bden (2*m))*var 0) ⋏
        upper (signedMean m) (average m (var 0)) (num (radius (coefficients m))) (num (bden (2*m))*var 0)) :=
  closeUniv 1 (.impI (mean_error m _ hm Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliGridRate
