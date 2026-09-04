import FabiusFunction.FourierLaplaceRotation
import FabiusFunction.IntegerZeroAnalyticOrder
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Leading Laurent coefficients at the Rvachev poles

The integer-zero cofactor of `IntegerZeroAnalyticOrder` makes reciprocal
pole limits almost formal.  This file first records that reusable
product-coordinate limit, then transports it through the exact
Fourier--Laplace rotation to the centered Rvachev moment generating
function.

The pole limit is deliberately taken through a punctured neighborhood.
Lean's inverse is totalized by `0⁻¹ = 0`, so the pole-cancelled expression
does not have its limiting value at the pole itself.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Fabius

noncomputable section

/-- The moment generating function of the centered Rvachev law.  The
repository's `centeredComplexGeneratingFunction F z` uses the half-scale
coordinate, so the centered law itself is obtained at `2 * t`. -/
noncomputable def rvachevCenteredMGF (F : BoundedFabius) (t : ℂ) : ℂ :=
  centeredComplexGeneratingFunction F (2 * t)

/-- Exact Fourier--Laplace rotation for the centered Rvachev moment
generating function: `M(t) = Φ(i t / (2π))`. -/
theorem rvachevCenteredMGF_eq_rvachevFourierProduct
    (F : BoundedFabius) (hF : IsFabius F) (t : ℂ) :
    rvachevCenteredMGF F t =
      rvachevFourierProduct
        (Complex.I * t / (2 * (Real.pi : ℂ))) := by
  rw [rvachevCenteredMGF,
    centeredComplexGeneratingFunction_eq_centeredSincProduct F hF,
    centeredSincProduct_eq_rvachevFourierProduct]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]

/-- At an imaginary odd-core argument, the centered MGF is the positive-core
half-integer sinc product.  This packages the evenness needed to compare the
signed odd core in the manuscript with `Nat.divMaxPow`. -/
theorem rvachevCenteredMGF_pi_mul_I_int
    (F : BoundedFabius) (hF : IsFabius F) (u : ℤ) :
    rvachevCenteredMGF F
        ((Real.pi : ℂ) * Complex.I * (u : ℂ)) =
      rvachevFourierProduct (((u.natAbs : ℕ) : ℂ) / 2) := by
  rw [rvachevCenteredMGF_eq_rvachevFourierProduct F hF]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rcases Int.natAbs_eq u with hu | hu
  · have huC : (u : ℂ) = ((u.natAbs : ℕ) : ℂ) := by
      conv_lhs => rw [hu]
      exact Int.cast_natCast _
    rw [huC]
    have harg :
        Complex.I *
              ((Real.pi : ℂ) * Complex.I * ((u.natAbs : ℕ) : ℂ)) /
            (2 * (Real.pi : ℂ)) =
          -(((u.natAbs : ℕ) : ℂ) / 2) := by
      field_simp [hpi]
      rw [Complex.I_sq]
      ring
    rw [harg, rvachevFourierProduct_neg]
  · have huC : (u : ℂ) = -((u.natAbs : ℕ) : ℂ) := by
      conv_lhs => rw [hu]
      rw [Int.cast_neg, Int.cast_natCast]
    rw [huC]
    congr 1
    field_simp [hpi]
    rw [Complex.I_sq]
    ring

/-- The manuscript's odd-core constant is nonzero. -/
theorem rvachevCenteredMGF_pi_mul_I_int_ne_zero_of_odd
    (F : BoundedFabius) (hF : IsFabius F) {u : ℤ} (hu : Odd u) :
    rvachevCenteredMGF F
        ((Real.pi : ℂ) * Complex.I * (u : ℂ)) ≠ 0 := by
  rw [rvachevCenteredMGF_pi_mul_I_int F hF]
  exact rvachevFourierProduct_nat_div_two_ne_zero_of_odd
    (Int.natAbs_odd.mpr hu)

/-- Reciprocal-pole limit at every nonzero integer zero of the standalone
Rvachev sinc product.  If `d = v₂(|m|) + 1`, then
`(z-m)^d / Φ(z)` tends to the reciprocal of the exact analytic cofactor.
This is the reusable coordinate-free kernel of the Laurent calculation. -/
theorem tendsto_sub_pow_mul_inv_rvachevFourierProduct_int
    (m : ℤ) (hm : m ≠ 0) :
    Tendsto
      (fun z : ℂ =>
        (z - (m : ℂ)) ^ (padicValNat 2 m.natAbs + 1) *
          (rvachevFourierProduct z)⁻¹)
      (𝓝[≠] (m : ℂ))
      (𝓝 (integerZeroLocalCofactor m 0)⁻¹) := by
  have hcoord :
      Tendsto (fun z : ℂ => z - (m : ℂ))
        (𝓝[≠] (m : ℂ)) (𝓝 0) := by
    have hcontinuous :
        ContinuousAt (fun z : ℂ => z - (m : ℂ)) (m : ℂ) :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using
      (hcontinuous.tendsto.mono_left nhdsWithin_le_nhds)
  have hU :
      Tendsto
        (fun z : ℂ =>
          integerZeroLocalCofactor m (z - (m : ℂ)))
        (𝓝[≠] (m : ℂ))
        (𝓝 (integerZeroLocalCofactor m 0)) :=
    (integerZeroLocalCofactor_analyticAt m hm).continuousAt.tendsto.comp hcoord
  have hUinv := hU.inv₀ (integerZeroLocalCofactor_zero_ne m hm)
  refine hUinv.congr' ?_
  filter_upwards [
    (rvachevFourierProduct_int_eventuallyEq_sub_pow_mul_cofactor m hm).filter_mono
      nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hzne
  have hsub : z - (m : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hzne)
  symm
  rw [hz, mul_inv_rev]
  calc
    (z - (m : ℂ)) ^ (padicValNat 2 m.natAbs + 1) *
          ((integerZeroLocalCofactor m (z - (m : ℂ)))⁻¹ *
            ((z - (m : ℂ)) ^ (padicValNat 2 m.natAbs + 1))⁻¹) =
        (((z - (m : ℂ)) ^ (padicValNat 2 m.natAbs + 1)) *
            ((z - (m : ℂ)) ^ (padicValNat 2 m.natAbs + 1))⁻¹) *
          (integerZeroLocalCofactor m (z - (m : ℂ)))⁻¹ := by ring
    _ = (integerZeroLocalCofactor m (z - (m : ℂ)))⁻¹ := by
      rw [mul_inv_cancel₀ (pow_ne_zero _ hsub), one_mul]

/-- Exact leading Laurent coefficient of the reciprocal centered MGF at the
pole `Tₙ = 2π i n`.  The positive `Nat.divMaxPow` odd core is harmless:
`rvachevCenteredMGF_pi_mul_I_int` identifies it with the signed manuscript
constant by evenness. -/
theorem tendsto_rvachevCenteredMGF_laurent_int
    (F : BoundedFabius) (hF : IsFabius F) (n : ℤ) (hn : n ≠ 0) :
    Tendsto
      (fun t : ℂ =>
        (t - 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^
            (padicValNat 2 n.natAbs + 1) *
          (rvachevCenteredMGF F t)⁻¹)
      (𝓝[≠] (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))
      (𝓝
        (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^
              (padicValNat 2 n.natAbs + 1) /
          rvachevCenteredMGF F
            ((Real.pi : ℂ) * Complex.I *
              ((Nat.divMaxPow n.natAbs 2 : ℕ) : ℂ)))) := by
  let d : ℕ := padicValNat 2 n.natAbs + 1
  let q : ℕ := Nat.divMaxPow n.natAbs 2
  let T : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
  let c : ℂ := Complex.I / (2 * (Real.pi : ℂ))
  change Tendsto
    (fun t : ℂ => (t - T) ^ d * (rvachevCenteredMGF F t)⁻¹)
    (𝓝[≠] T)
    (𝓝 (-T ^ d /
      rvachevCenteredMGF F ((Real.pi : ℂ) * Complex.I * (q : ℂ))))
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hc : c ≠ 0 := by
    exact div_ne_zero Complex.I_ne_zero (mul_ne_zero (by norm_num) hpi)
  have hTc : T * c = -(n : ℂ) := by
    dsimp only [T, c]
    field_simp [hpi]
    rw [Complex.I_sq]
  have hmap :
      Tendsto (fun t : ℂ => t * c) (𝓝[≠] T) (𝓝[≠] (-(n : ℂ))) := by
    have h : Tendsto (fun t : ℂ => t * c)
        (𝓝[≠] T) (𝓝[≠] (T * c)) :=
      le_of_eq ((Homeomorph.mulRight₀ c hc).map_punctured_nhds_eq T)
    simpa only [hTc] using h
  have hbase :=
    tendsto_sub_pow_mul_inv_rvachevFourierProduct_int (-n)
      (neg_ne_zero.mpr hn)
  have hbase' :
      Tendsto
        (fun z : ℂ =>
          (z - (-(n : ℂ))) ^ d * (rvachevFourierProduct z)⁻¹)
        (𝓝[≠] (-(n : ℂ)))
        (𝓝 (integerZeroLocalCofactor (-n) 0)⁻¹) := by
    simpa only [d, Int.natAbs_neg, Int.cast_neg] using hbase
  have hscaled := (hbase'.comp hmap).const_mul ((c⁻¹) ^ d)
  have hraw :
      Tendsto
        (fun t : ℂ => (t - T) ^ d * (rvachevCenteredMGF F t)⁻¹)
        (𝓝[≠] T)
        (𝓝 ((c⁻¹) ^ d * (integerZeroLocalCofactor (-n) 0)⁻¹)) := by
    refine hscaled.congr' ?_
    filter_upwards with t
    change
      (c⁻¹) ^ d *
          ((t * c - (-(n : ℂ))) ^ d *
            (rvachevFourierProduct (t * c))⁻¹) =
        (t - T) ^ d * (rvachevCenteredMGF F t)⁻¹
    have hcoord : t * c =
        Complex.I * t / (2 * (Real.pi : ℂ)) := by
      dsimp only [c]
      ring
    have hdelta : t * c - (-(n : ℂ)) = c * (t - T) := by
      rw [← hTc]
      ring
    rw [rvachevCenteredMGF_eq_rvachevFourierProduct F hF, ← hcoord,
      hdelta, mul_pow]
    calc
      (c⁻¹) ^ d *
            (c ^ d * (t - T) ^ d * (rvachevFourierProduct (t * c))⁻¹) =
          (((c⁻¹) ^ d * c ^ d) *
            ((t - T) ^ d * (rvachevFourierProduct (t * c))⁻¹)) := by ring
      _ = (t - T) ^ d * (rvachevFourierProduct (t * c))⁻¹ := by
        rw [← mul_pow, inv_mul_cancel₀ hc, one_pow, one_mul]
  have hcinv_mul : c⁻¹ * (-(n : ℂ)) = T := by
    dsimp only [c, T]
    field_simp [hpi]
    rw [Complex.I_sq]
  have hmgf_q :
      rvachevCenteredMGF F
          ((Real.pi : ℂ) * Complex.I * (q : ℂ)) =
        rvachevFourierProduct ((q : ℂ) / 2) := by
    simpa only [Int.natAbs_natCast, Int.cast_natCast] using
      (rvachevCenteredMGF_pi_mul_I_int F hF (q : ℤ))
  have htarget :
      (c⁻¹) ^ d * (integerZeroLocalCofactor (-n) 0)⁻¹ =
        -T ^ d /
          rvachevCenteredMGF F
            ((Real.pi : ℂ) * Complex.I * (q : ℂ)) := by
    rw [integerZeroLocalCofactor_zero]
    simp only [q, d, Int.natAbs_neg, Int.cast_neg]
    change
      (c⁻¹) ^ d *
          (-rvachevFourierProduct ((q : ℂ) / 2) /
            (-(n : ℂ)) ^ d)⁻¹ =
        -T ^ d /
          rvachevCenteredMGF F
            ((Real.pi : ℂ) * Complex.I * (q : ℂ))
    rw [hmgf_q]
    simp only [inv_div, div_neg]
    calc
      (c⁻¹) ^ d *
            -(((-(n : ℂ)) ^ d) /
              rvachevFourierProduct (((q : ℕ) : ℂ) / 2)) =
          -(c⁻¹ * (-(n : ℂ))) ^ d /
            rvachevFourierProduct (((q : ℕ) : ℂ) / 2) := by
        rw [mul_pow]
        ring
      _ = -T ^ d /
            rvachevFourierProduct (((q : ℕ) : ℂ) / 2) := by
        rw [hcinv_mul]
  rw [htarget] at hraw
  exact hraw

/-- Manuscript-normalized Laurent limit.  If `n = 2^v u` with `u` odd,
the pole has order `v + 1` and leading coefficient `-Tₙ^(v+1) / C_u`,
where `C_u = M(π i u) ≠ 0`. -/
theorem tendsto_rvachevCenteredMGF_laurent_two_pow_mul_odd
    (F : BoundedFabius) (hF : IsFabius F) (v : ℕ) (u : ℤ) (hu : Odd u) :
    Tendsto
      (fun t : ℂ =>
        (t - 2 * (Real.pi : ℂ) * Complex.I *
              ((((2 : ℤ) ^ v) * u : ℤ) : ℂ)) ^ (v + 1) *
          (rvachevCenteredMGF F t)⁻¹)
      (𝓝[≠]
        (2 * (Real.pi : ℂ) * Complex.I *
          ((((2 : ℤ) ^ v) * u : ℤ) : ℂ)))
      (𝓝
        (-(2 * (Real.pi : ℂ) * Complex.I *
              ((((2 : ℤ) ^ v) * u : ℤ) : ℂ)) ^ (v + 1) /
          rvachevCenteredMGF F
            ((Real.pi : ℂ) * Complex.I * (u : ℂ)))) := by
  let n : ℤ := (2 : ℤ) ^ v * u
  change Tendsto
    (fun t : ℂ =>
      (t - 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ (v + 1) *
        (rvachevCenteredMGF F t)⁻¹)
    (𝓝[≠] (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))
    (𝓝
      (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ (v + 1) /
        rvachevCenteredMGF F
          ((Real.pi : ℂ) * Complex.I * (u : ℂ))))
  have hu0 : u ≠ 0 := by
    intro hzero
    subst u
    obtain ⟨k, hk⟩ := hu
    omega
  have hn : n ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero v (by norm_num)) hu0
  have habs : n.natAbs = 2 ^ v * u.natAbs := by
    dsimp only [n]
    rw [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  have huabs0 : u.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hu0
  have hvalU : padicValNat 2 u.natAbs = 0 := by
    refine padicValNat.eq_zero_of_not_dvd ?_
    have hmod : u.natAbs % 2 = 1 :=
      Nat.odd_iff.mp (Int.natAbs_odd.mpr hu)
    omega
  have hval : padicValNat 2 n.natAbs = v := by
    rw [habs, padicValNat_base_pow_mul (by norm_num) huabs0 v, hvalU]
    exact zero_add v
  have hqU : Nat.divMaxPow u.natAbs 2 = u.natAbs := by
    have h := Nat.pow_padicValNat_mul_divMaxPow 2 u.natAbs
    simpa only [hvalU, pow_zero, one_mul] using h
  have hq : Nat.divMaxPow n.natAbs 2 = u.natAbs := by
    rw [habs, Nat.divMaxPow_base_pow_mul (by norm_num) u.natAbs v, hqU]
  have hcore :
      rvachevCenteredMGF F
          ((Real.pi : ℂ) * Complex.I *
            ((Nat.divMaxPow n.natAbs 2 : ℕ) : ℂ)) =
        rvachevCenteredMGF F
          ((Real.pi : ℂ) * Complex.I * (u : ℂ)) := by
    calc
      rvachevCenteredMGF F
            ((Real.pi : ℂ) * Complex.I *
              ((Nat.divMaxPow n.natAbs 2 : ℕ) : ℂ)) =
          rvachevFourierProduct
            (((Nat.divMaxPow n.natAbs 2 : ℕ) : ℂ) / 2) := by
        simpa only [Int.natAbs_natCast, Int.cast_natCast] using
          (rvachevCenteredMGF_pi_mul_I_int F hF
            (Nat.divMaxPow n.natAbs 2 : ℤ))
      _ = rvachevFourierProduct (((u.natAbs : ℕ) : ℂ) / 2) := by
        rw [hq]
      _ = rvachevCenteredMGF F
            ((Real.pi : ℂ) * Complex.I * (u : ℂ)) :=
        (rvachevCenteredMGF_pi_mul_I_int F hF u).symm
  have h := tendsto_rvachevCenteredMGF_laurent_int F hF n hn
  simpa only [hval, hcore] using h

end

end Fabius
