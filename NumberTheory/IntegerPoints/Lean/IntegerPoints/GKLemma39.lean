import IntegerPoints.GKLemma39Jets

/-!
# Graham--Kolesnik, Lemma 3.9

This module completes the quantitative inverse-function argument begun in
`GKLemma39Local` and `GKLemma39Jets`.  The finite inverse-jet estimate is first
unnormalized on the open derivative interval.  The Legendre identity identifies
`phi'` with the inverse point there.  Finally, continuity extends the resulting
nonstrict estimate to the two endpoint frequencies; increasing the uniform
constant by one recovers the strict inequality in the published statement.
-/

open Real Finset Set Filter
open scoped BigOperators Topology

namespace LeanProofs.IntegerPoints

namespace GK39

/-! ### Uniformly unnormalizing the inverse jets -/

/-- A finite envelope for the reciprocals of the positive model coefficients.
It is the only place where the final constant depends on the derivative order
`P`. -/
private noncomputable def reciprocalEnvelope (s : ℝ) (P : ℕ) : ℝ :=
  ∑ p ∈ range P, (InverseJet.risingCoeff (1 / s) p)⁻¹

private theorem reciprocal_le_envelope {s : ℝ} {P p : ℕ} (hs : 0 < s)
    (hp : p < P) :
    (InverseJet.risingCoeff (1 / s) p)⁻¹ ≤ reciprocalEnvelope s P := by
  rw [reciprocalEnvelope]
  exact Finset.single_le_sum
    (s := range P) (f := fun q => (InverseJet.risingCoeff (1 / s) q)⁻¹)
    (fun q _ => inv_nonneg.mpr
      (InverseJet.risingCoeff_pos (one_div_pos.mpr hs) q).le)
    (mem_range.mpr hp)

private theorem reciprocalEnvelope_nonneg {s : ℝ} {P : ℕ} (hs : 0 < s) :
    0 ≤ reciprocalEnvelope s P := by
  apply Finset.sum_nonneg
  intro p hp
  exact inv_nonneg.mpr (InverseJet.risingCoeff_pos (one_div_pos.mpr hs) p).le

/-- The power model in the statement is the unnormalized inverse-jet model. -/
private theorem model_eq_inverseCoeff_mul_div {s y nu : ℝ} (hnu : 0 < nu)
    (p : ℕ) :
    (-1 : ℝ) ^ p * InverseJet.risingCoeff (1 / s) p * y ^ (1 / s) *
        nu ^ (-(1 / s) - p) =
      InverseJet.inverseCoeff s p *
        (y ^ (1 / s) * nu ^ (-(1 / s))) / nu ^ p := by
  unfold InverseJet.inverseCoeff
  rw [show -(1 / s) - (p : ℝ) = -(1 / s) + -(p : ℝ) by ring,
    Real.rpow_add hnu, Real.rpow_neg hnu.le (1 / s),
    Real.rpow_neg hnu.le (p : ℝ), Real.rpow_natCast]
  simp only [div_eq_mul_inv]
  ring

private theorem abs_inverseCoeff_eq_risingCoeff {s : ℝ} (hs : 0 < s)
    (p : ℕ) :
    |InverseJet.inverseCoeff s p| = InverseJet.risingCoeff (1 / s) p := by
  rw [InverseJet.inverseCoeff, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_pos (InverseJet.risingCoeff_pos (one_div_pos.mpr hs) p)]

/-- An elementary unnormalization estimate.  The factor `T` bounds `r⁻¹`;
this allows one constant to work for all positive jet orders below `P`. -/
private theorem unnormalize_inverse_jet {D X Y nu c r K L T eps : ℝ}
    (p : ℕ) (hX : 0 < X) (hY : 0 < Y) (hnu : 0 < nu)
    (hr : 0 < r) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (heps : 0 ≤ eps) (heps_one : eps ≤ 1)
    (hc : |c| = r) (hrecip : r⁻¹ ≤ T)
    (hnormalized : |D * nu ^ p / X - c| ≤ K * eps)
    (hscale : |X - Y| ≤ L * eps * Y) :
    |D - c * Y / nu ^ p| ≤
      (K * (1 + L) * T + L) * eps * r * Y / nu ^ p := by
  have hnu_pow : 0 < nu ^ p := pow_pos hnu p
  let z : ℝ := D * nu ^ p / X
  have hD : D = z * X / nu ^ p := by
    dsimp [z]
    field_simp [hX.ne', hnu_pow.ne']
  have hscale' : |X - Y| ≤ L * Y := by
    calc
      |X - Y| ≤ L * eps * Y := hscale
      _ ≤ L * 1 * Y := by gcongr
      _ = L * Y := by ring
  have hX_le : X ≤ (1 + L) * Y := by
    have hdiff : X - Y ≤ |X - Y| := le_abs_self (X - Y)
    calc
      X ≤ Y + |X - Y| := by linarith
      _ ≤ Y + L * Y := add_le_add_right hscale' Y
      _ = (1 + L) * Y := by ring
  have hsum :
      |(z - c) * X + c * (X - Y)| ≤
        K * eps * ((1 + L) * Y) + r * (L * eps * Y) := by
    calc
      |(z - c) * X + c * (X - Y)| ≤
          |(z - c) * X| + |c * (X - Y)| := abs_add_le _ _
      _ = |z - c| * X + r * |X - Y| := by
        rw [abs_mul, abs_mul, abs_of_pos hX, hc]
      _ ≤ K * eps * ((1 + L) * Y) + r * (L * eps * Y) := by
        apply add_le_add
        · exact mul_le_mul hnormalized hX_le hX.le (mul_nonneg hK heps)
        · exact mul_le_mul_of_nonneg_left hscale hr.le
  have hTr : 1 ≤ T * r := by
    have h := mul_le_mul_of_nonneg_right hrecip hr.le
    simpa [inv_mul_cancel₀ hr.ne'] using h
  have hfirst :
      K * eps * ((1 + L) * Y) ≤ K * (1 + L) * T * eps * r * Y := by
    calc
      K * eps * ((1 + L) * Y) = (K * (1 + L) * eps * Y) * 1 := by ring
      _ ≤ (K * (1 + L) * eps * Y) * (T * r) :=
        mul_le_mul_of_nonneg_left hTr (by positivity)
      _ = K * (1 + L) * T * eps * r * Y := by ring
  have hnumerator :
      K * eps * ((1 + L) * Y) + r * (L * eps * Y) ≤
        (K * (1 + L) * T + L) * eps * r * Y := by
    calc
      K * eps * ((1 + L) * Y) + r * (L * eps * Y) ≤
          K * (1 + L) * T * eps * r * Y + r * (L * eps * Y) :=
        add_le_add hfirst le_rfl
      _ = (K * (1 + L) * T + L) * eps * r * Y := by ring
  calc
    |D - c * Y / nu ^ p| =
        |(z - c) * X + c * (X - Y)| / nu ^ p := by
      rw [hD]
      have halgebra :
          z * X / nu ^ p - c * Y / nu ^ p =
            ((z - c) * X + c * (X - Y)) / nu ^ p := by ring
      rw [halgebra, abs_div, abs_of_pos hnu_pow]
    _ ≤ (K * eps * ((1 + L) * Y) + r * (L * eps * Y)) / nu ^ p :=
      div_le_div_of_nonneg_right hsum hnu_pow.le
    _ ≤ ((K * (1 + L) * T + L) * eps * r * Y) / nu ^ p :=
      div_le_div_of_nonneg_right hnumerator hnu_pow.le
    _ = (K * (1 + L) * T + L) * eps * r * Y / nu ^ p := rfl

end GK39

open GK39

/-! ### Interior estimate and endpoint closure -/

/-- **Graham--Kolesnik, Lemma 3.9** holds. -/
theorem gk_lemma39_holds : gk_lemma39 := by
  intro s P hs hP
  obtain ⟨K, hK, hjet⟩ := GK39Jets.exists_normalizedInverseJet_bound s P hs
  obtain ⟨L, hL, hscale⟩ := GK39Jets.exists_inverseScale_comparison_constant s hs
  let T : ℝ := reciprocalEnvelope s P
  have hT : 0 ≤ T := by
    simpa only [T] using reciprocalEnvelope_nonneg (s := s) (P := P) hs
  let C0 : ℝ := K * (1 + L) * T + L
  refine ⟨C0 + 1, ?_⟩
  intro N y eps a b f x phi hN hy heps heps_half hf hab hphi hx hphi_value
    p hp nu hnu
  change
    |iteratedDeriv (p + 1) phi nu -
        (-1 : ℝ) ^ p * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * nu ^ (-(1 / s) - p)| <
      (C0 + 1) * eps * InverseJet.risingCoeff (1 / s) p *
        y ^ (1 / s) * nu ^ (-(1 / s) - p)
  have hinterval :=
    deriv_interval_pos hN hs hy hP heps heps_half hf hab
  have hinterior : ∀ v ∈ Ioo (deriv f b) (deriv f a),
      |iteratedDeriv (p + 1) phi v -
          (-1 : ℝ) ^ p * InverseJet.risingCoeff (1 / s) p *
            y ^ (1 / s) * v ^ (-(1 / s) - p)| ≤
        C0 * eps * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * v ^ (-(1 / s) - p) := by
    intro v hv
    have hv0 : 0 < v := hinterval.1.trans hv.1
    by_cases hp0 : p = 0
    · subst p
      have hphi_deriv : deriv phi v = x v :=
        deriv_phi_eq_inverse hN hs hy hP heps heps_half hf hab hx hphi_value hv
      have hscale0 := hscale N y eps a b P f x hN hy heps heps_half hP hf hx v hv
      have hL_le : L ≤ C0 := by
        dsimp [C0]
        have : 0 ≤ K * (1 + L) * T := by positivity
        linarith
      have hbound :
          |x v - y ^ (1 / s) * v ^ (-(1 / s))| ≤
            C0 * eps * (y ^ (1 / s) * v ^ (-(1 / s))) := by
        exact hscale0.trans (by gcongr)
      simpa [iteratedDeriv_one, hphi_deriv, InverseJet.risingCoeff, mul_assoc] using hbound
    · have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp0
      have hpP : p ≤ P - 1 := Nat.le_sub_one_of_lt hp
      have hv_closed : v ∈ Icc (deriv f b) (deriv f a) := ⟨hv.1.le, hv.2.le⟩
      have hxv := hx v hv_closed
      have hX0 : 0 < x v := point_pos hN hf hxv.1
      let Y : ℝ := y ^ (1 / s) * v ^ (-(1 / s))
      have hY0 : 0 < Y := by dsimp [Y]; positivity
      let r : ℝ := InverseJet.risingCoeff (1 / s) p
      have hr : 0 < r := by
        dsimp [r]
        exact InverseJet.risingCoeff_pos (one_div_pos.mpr hs) p
      let c : ℝ := InverseJet.inverseCoeff s p
      have hc : |c| = r := by
        simpa only [c, r] using abs_inverseCoeff_eq_risingCoeff hs p
      have hnormalized :
          |iteratedDeriv p x v * v ^ p / x v - c| ≤ K * eps := by
        simpa only [GK39Jets.normalizedInverseJet, c] using
          hjet N y eps a b f x hN hy heps heps_half hP hf hab hx v hv p hp1 hpP
      have hscale0 : |x v - Y| ≤ L * eps * Y := by
        simpa only [Y] using
          hscale N y eps a b P f x hN hy heps heps_half hP hf hx v hv
      have hrecip : r⁻¹ ≤ T := by
        simpa only [r, T] using reciprocal_le_envelope hs hp
      have hunnormalized :
          |iteratedDeriv p x v - c * Y / v ^ p| ≤
            C0 * eps * r * Y / v ^ p := by
        simpa only [C0] using
          unnormalize_inverse_jet p hX0 hY0 hv0 hr hK hL heps.le
            (heps_half.trans (by norm_num)).le hc hrecip
            hnormalized hscale0
      have hphi_eventually : deriv phi =ᶠ[nhds v] x := by
        filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
        exact deriv_phi_eq_inverse hN hs hy hP heps heps_half hf hab hx hphi_value hw
      have hphi_x : iteratedDeriv (p + 1) phi v = iteratedDeriv p x v := by
        rw [iteratedDeriv_succ']
        exact Filter.EventuallyEq.iteratedDeriv_eq p hphi_eventually
      have hmodel := model_eq_inverseCoeff_mul_div (s := s) (y := y) hv0 p
      rw [hphi_x, hmodel]
      calc
        |iteratedDeriv p x v - InverseJet.inverseCoeff s p *
            (y ^ (1 / s) * v ^ (-(1 / s))) / v ^ p| ≤
            C0 * eps * InverseJet.risingCoeff (1 / s) p *
              (y ^ (1 / s) * v ^ (-(1 / s))) / v ^ p := by
          simpa only [c, r, Y] using hunnormalized
        _ = C0 * eps * InverseJet.risingCoeff (1 / s) p *
            y ^ (1 / s) * v ^ (-(1 / s) - p) := by
          rw [show -(1 / s) - (p : ℝ) = -(1 / s) + -(p : ℝ) by ring,
            Real.rpow_add hv0, Real.rpow_neg hv0.le (p : ℝ),
            Real.rpow_natCast]
          field_simp [pow_ne_zero p hv0.ne']
  have hp_succ : p + 1 ≤ P := Nat.succ_le_iff.mpr hp
  have hderiv_cont : Continuous (iteratedDeriv (p + 1) phi) :=
    hphi.continuous_iteratedDeriv (p + 1) (by exact_mod_cast hp_succ)
  have hpow_cont :
      ContinuousOn (fun v : ℝ => v ^ (-(1 / s) - p))
        (Icc (deriv f b) (deriv f a)) :=
    continuousOn_id.rpow_const fun v hv =>
      Or.inl (show v ≠ 0 by linarith [hinterval.1, hv.1])
  have hmodel_cont :
      ContinuousOn
        (fun v : ℝ => (-1 : ℝ) ^ p * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * v ^ (-(1 / s) - p))
        (Icc (deriv f b) (deriv f a)) :=
    continuousOn_const.mul hpow_cont
  have hleft_cont :
      ContinuousOn
        (fun v : ℝ =>
          |iteratedDeriv (p + 1) phi v -
            (-1 : ℝ) ^ p * InverseJet.risingCoeff (1 / s) p *
              y ^ (1 / s) * v ^ (-(1 / s) - p)|)
        (closure (Ioo (deriv f b) (deriv f a))) := by
    rw [closure_Ioo hinterval.2.ne]
    exact (hderiv_cont.continuousOn.sub hmodel_cont).abs
  have hright_cont :
      ContinuousOn
        (fun v : ℝ => C0 * eps * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * v ^ (-(1 / s) - p))
        (closure (Ioo (deriv f b) (deriv f a))) := by
    rw [closure_Ioo hinterval.2.ne]
    exact continuousOn_const.mul hpow_cont
  have hnu_closure : nu ∈ closure (Ioo (deriv f b) (deriv f a)) := by
    rw [closure_Ioo hinterval.2.ne]
    exact hnu
  have hclosed := le_on_closure hinterior hleft_cont hright_cont hnu_closure
  have hnu0 : 0 < nu := hinterval.1.trans_le hnu.1
  have hr0 : 0 < InverseJet.risingCoeff (1 / s) p :=
    InverseJet.risingCoeff_pos (one_div_pos.mpr hs) p
  have hbase :
      0 < eps * InverseJet.risingCoeff (1 / s) p *
        y ^ (1 / s) * nu ^ (-(1 / s) - p) := by positivity
  calc
    |iteratedDeriv (p + 1) phi nu -
        (-1 : ℝ) ^ p * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * nu ^ (-(1 / s) - p)| ≤
        C0 * eps * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * nu ^ (-(1 / s) - p) := hclosed
    _ = C0 * (eps * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * nu ^ (-(1 / s) - p)) := by ring
    _ < (C0 + 1) * (eps * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * nu ^ (-(1 / s) - p)) :=
      mul_lt_mul_of_pos_right (lt_add_one C0) hbase
    _ = (C0 + 1) * eps * InverseJet.risingCoeff (1 / s) p *
          y ^ (1 / s) * nu ^ (-(1 / s) - p) := by ring

end LeanProofs.IntegerPoints
