import IntegerPoints.GKBProcessAmplitude
import IntegerPoints.GKBProcessArithmetic
import IntegerPoints.GKBProcessParameters

/-!
# Graham--Kolesnik B-process: one dyadic dual block

This module combines the class, phase, and Abel-summation layers on one
dyadic frequency block.  The sum here is deliberately written with the dual
weight `sqrt (-phi'')`.  Replacing the literal stationary weight by this one,
and removing the possible endpoint frequencies, are handled outside this
module.

For every prefix, the raw dual class is restricted to the prefix interval,
lowered to the order required by the input exponent pair, and enlarged to its
accepted error.  The fixed phase `-1/8` and phase reversal do not change the
prefix norm.  Abel summation then costs only the first dual weight, which the
order-one class inequality bounds by the explicit square-root model at `J`.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

namespace GKB

/-! ## Comparing the dual weight with its model at the left dyadic scale -/

/-- Every dual weight in a class based at `J` is bounded by the model weight
at `J`.  This is the order-one class inequality plus the fact that
`nu >= c >= J` and the model power has negative exponent. -/
theorem dualWeight_le_dualModelWeight
    {J sigma eta delta c d : ℝ} {P : ℕ} {phi : ℝ → ℝ}
    (hJ : 0 < J) (hsigma : 0 < sigma) (heta : 0 < eta)
    (hP : 3 ≤ P) (hdelta : delta ≤ 1 / 4)
    (hphi : InGKClass J P sigma eta delta c d phi)
    {nu : ℝ} (hnu : nu ∈ Icc c d) :
    dualWeight phi nu ≤ dualModelWeight sigma eta J := by
  have hnu0 : 0 < nu := GK39.point_pos hJ hphi hnu
  have hmodel : 0 < sigma * eta * nu ^ (-sigma - 1) := by positivity
  have hpoint := neg_bounds_of_abs_add_model_lt hmodel.le hdelta
    (abs_iteratedDeriv_two_add_model_lt (by omega) hphi hnu)
  have hJnu : J ≤ nu := hphi.1.trans hnu.1
  have hpow : nu ^ (-sigma - 1) ≤ J ^ (-sigma - 1) :=
    Real.rpow_le_rpow_of_nonpos hJ hJnu (by linarith)
  have hmodel_le :
      5 / 4 * (sigma * eta * nu ^ (-sigma - 1)) ≤
        5 / 4 * sigma * eta * J ^ (-sigma - 1) := by
    calc
      5 / 4 * (sigma * eta * nu ^ (-sigma - 1)) ≤
          5 / 4 * (sigma * eta * J ^ (-sigma - 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg hsigma.le heta.le))
          (by norm_num)
      _ = 5 / 4 * sigma * eta * J ^ (-sigma - 1) := by ring
  unfold dualWeight dualModelWeight
  exact Real.sqrt_le_sqrt (hpoint.2.trans hmodel_le)

/-! ## Natural indices inside the real dual interval -/

private theorem natCast_mem_classInterval
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) {n : ℕ}
    (hn : n ∈ Set.Icc (⌊c⌋₊ + 1) ⌊d⌋₊) :
    (n : ℝ) ∈ Set.Icc c d := by
  constructor
  · have hfloor : ⌊c⌋₊ < n := Nat.lt_of_succ_le hn.1
    exact (Nat.floor_lt hc).mp hfloor |>.le
  · exact (Nat.le_floor_iff hd).mp hn.2

/-! ## The single-block Abel estimate -/

/-- A weighted dual exponential sum on one dyadic block is bounded by the
input exponent-pair model times the first-weight model.

The callback `hpair` is the exact fixed-parameter form of the input
exponent-pair estimate.  It is applied to every prefix after the raw class is
restricted, lowered from `P` to `P0`, and enlarged from `delta` to `eps0`.
-/
theorem norm_weighted_dual_block_le
    {J sigma eta delta eps0 c d k l Cpair : ℝ} {P P0 : ℕ}
    {phi : ℝ → ℝ}
    (hJ : 0 < J) (hsigma : 0 < sigma) (heta : 0 < eta)
    (hP : 3 ≤ P) (hdelta_quarter : delta ≤ 1 / 4)
    (hphi : InGKClass J P sigma eta delta c d phi)
    (hP0 : P0 ≤ P) (hdelta_pair : delta ≤ eps0)
    (hCpair : 0 ≤ Cpair)
    (hpair : ∀ u v : ℝ,
      InGKClass J P0 sigma eta eps0 u v phi →
      ‖∑ n ∈ intRange u v, e (phi n)‖ ≤
        Cpair *
          ((eta * J ^ (-sigma)) ^ k * J ^ l + eta⁻¹ * J ^ sigma)) :
    ‖∑ n ∈ intRange c d,
        ((dualWeight phi n : ℝ) : ℂ) * e (-phi n - 1 / 8)‖ ≤
      Cpair * ((eta * J ^ (-sigma)) ^ k * J ^ l + eta⁻¹ * J ^ sigma) *
        dualModelWeight sigma eta J := by
  let model : ℝ :=
    (eta * J ^ (-sigma)) ^ k * J ^ l + eta⁻¹ * J ^ sigma
  let M : ℝ := Cpair * model
  have hmodel : 0 ≤ model := by
    dsimp [model]
    positivity
  have hM : 0 ≤ M := mul_nonneg hCpair hmodel
  have hc0 : 0 < c := hJ.trans_le hphi.1
  have hd0 : 0 < d := hc0.trans_le hphi.2.1
  have hweight := dualWeight_pos_antitone
    hJ hsigma heta hP hdelta_quarter hphi
  by_cases hcdNat : ⌊c⌋₊ < ⌊d⌋₊
  · have hw_nonneg : ∀ n ∈ Finset.Ioc ⌊c⌋₊ ⌊d⌋₊,
        0 ≤ dualWeight phi n := by
      intro n hn
      have hnIcc : n ∈ Set.Icc (⌊c⌋₊ + 1) ⌊d⌋₊ := by
        rw [Set.mem_Icc]
        rw [Finset.mem_Ioc] at hn
        omega
      exact (hweight.1 n (natCast_mem_classInterval hc0.le hd0.le hnIcc)).le
    have hw_antitone :
        AntitoneOn (fun n : ℕ => dualWeight phi n)
          (Set.Icc (⌊c⌋₊ + 1) ⌊d⌋₊) := by
      intro m hm n hn hmn
      exact hweight.2
        (natCast_mem_classInterval hc0.le hd0.le hm)
        (natCast_mem_classInterval hc0.le hd0.le hn)
        (by exact_mod_cast hmn)
    have hprefix : ∀ T ∈ Finset.Ioc ⌊c⌋₊ ⌊d⌋₊,
        ‖∑ n ∈ Finset.Ioc ⌊c⌋₊ T, e (-phi n - 1 / 8)‖ ≤ M := by
      intro T hT
      have hT' := Finset.mem_Ioc.mp hT
      have hcT : c < (T : ℝ) := (Nat.floor_lt hc0.le).mp hT'.1
      have hTd : (T : ℝ) ≤ d := (Nat.le_floor_iff hd0.le).mp hT'.2
      have hrestricted : InGKClass J P sigma eta delta c (T : ℝ) phi :=
        InGKClass.restrictInterval hphi le_rfl hcT.le hTd
      have hweakened : InGKClass J P0 sigma eta eps0 c (T : ℝ) phi :=
        InGKClass.weaken_of_pos hJ hsigma heta hP0 hdelta_pair hrestricted
      calc
        ‖∑ n ∈ Finset.Ioc ⌊c⌋₊ T, e (-phi n - 1 / 8)‖ =
            ‖∑ n ∈ intRange c (T : ℝ), e (-phi n - 1 / 8)‖ := by
          simp only [intRange, Nat.floor_natCast]
        _ = ‖∑ n ∈ intRange c (T : ℝ), e (phi n)‖ :=
          norm_sum_intRange_e_neg_phi_sub_eighth c T phi
        _ ≤ M := by
          simpa only [M, model] using hpair c T hweakened
    have hfirst_mem : (⌊c⌋₊ + 1 : ℕ) ∈
        Set.Icc (⌊c⌋₊ + 1) ⌊d⌋₊ := by
      constructor
      · exact le_rfl
      · omega
    have hfirst :
        dualWeight phi (⌊c⌋₊ + 1 : ℕ) ≤ dualModelWeight sigma eta J :=
      dualWeight_le_dualModelWeight hJ hsigma heta hP hdelta_quarter hphi
        (natCast_mem_classInterval hc0.le hd0.le hfirst_mem)
    rw [intRange]
    calc
      ‖∑ n ∈ Finset.Ioc ⌊c⌋₊ ⌊d⌋₊,
          ((dualWeight phi n : ℝ) : ℂ) * e (-phi n - 1 / 8)‖ ≤
          M * dualWeight phi (⌊c⌋₊ + 1 : ℕ) :=
        norm_sum_Ioc_weight_mul_le hcdNat
          (fun n : ℕ => e (-phi n - 1 / 8))
          (fun n : ℕ => dualWeight phi n) M
          hw_nonneg hw_antitone hprefix
      _ ≤ M * dualModelWeight sigma eta J :=
        mul_le_mul_of_nonneg_left hfirst hM
      _ = Cpair *
          ((eta * J ^ (-sigma)) ^ k * J ^ l + eta⁻¹ * J ^ sigma) *
            dualModelWeight sigma eta J := by rfl
  · rw [intRange, Finset.Ioc_eq_empty hcdNat, Finset.sum_empty, norm_zero]
    exact mul_nonneg hM (Real.sqrt_nonneg _)

end GKB

end LeanProofs.IntegerPoints
