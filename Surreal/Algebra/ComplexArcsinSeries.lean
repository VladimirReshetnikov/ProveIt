import Surreal.Algebra.ArcsinTaylor
import Surreal.Algebra.AnalyticComposition
import Surreal.Algebra.ComplexTrigSeries

/-!
# The complex formal inverse-sine germ

The real analytic inverse identities give both formal compositional
inverse identities, which remain true after scalar extension to the
complex numbers. This supplies the inverse germ in
`trigonometry:thm:fold` and `trigonometry:eq:foldroots`, without choosing
a global complex inverse-sine branch. Its odd coefficients are the
explicit real central-binomial coefficients.
-/

namespace Surreal.Analytic

open Filter Topology

noncomputable section

private theorem analyticAt_real_arcsin_zero : AnalyticAt ℝ Real.arcsin 0 :=
  (Real.contDiffAt_arcsin (by norm_num) (by norm_num)).analyticAt

/-- The real sine Taylor series has the inverse-sine Taylor series as a right inverse. -/
theorem taylorSeries_sin_subst_arcsin :
    (taylorSeries Real.sin 0).subst (taylorSeries Real.arcsin 0) = PowerSeries.X := by
  have hg : Real.sin ∘ Real.arcsin =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact Real.sin_arcsin hx.1.le hx.2.le
  have hc := taylorSeries_comp (f := Real.sin) (g := Real.arcsin) (c := 0)
    Real.analyticAt_sin analyticAt_real_arcsin_zero
  simpa only [centeredTaylorSeries, Real.arcsin_zero, map_zero, sub_zero,
    taylorSeries_congr hg, taylorSeries_id, zero_add] using hc.symm

/-- The reverse inverse identity holds at the zero-centered sine germ as well. -/
theorem taylorSeries_arcsin_subst_sin :
    (taylorSeries Real.arcsin 0).subst (taylorSeries Real.sin 0) = PowerSeries.X := by
  have hp : (0 : ℝ) < Real.pi / 2 := half_pos Real.pi_pos
  have hg : Real.arcsin ∘ Real.sin =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hp) hp] with x hx
    exact Real.arcsin_sin hx.1.le hx.2.le
  have hc := taylorSeries_comp (f := Real.arcsin) (g := Real.sin) (c := 0)
    (by simpa only [Real.sin_zero] using analyticAt_real_arcsin_zero) Real.analyticAt_sin
  simpa only [centeredTaylorSeries, Real.sin_zero, map_zero, sub_zero,
    taylorSeries_congr hg, taylorSeries_id, zero_add] using hc.symm

/-- Scalar extension identifies the real sine Taylor series with the complex sine germ. -/
theorem map_taylorSeries_real_sin :
    (taylorSeries Real.sin 0).map Complex.ofRealHom = complexSinSeries := by
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [complexSinSeries, PowerSeries.coeff_map, coeff_taylorSeries,
      Real.iteratedDeriv_even_sin, Complex.iteratedDeriv_even_sin]
  · simp [complexSinSeries, PowerSeries.coeff_map, coeff_taylorSeries]

/-- Scalar extension also identifies the real and complex cosine Taylor germs. -/
theorem map_taylorSeries_real_cos :
    (taylorSeries Real.cos 0).map Complex.ofRealHom = complexCosSeries := by
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [complexCosSeries, PowerSeries.coeff_map, coeff_taylorSeries,
      Real.iteratedDeriv_even_cos, Complex.iteratedDeriv_even_cos]
  · simp [complexCosSeries, PowerSeries.coeff_map, coeff_taylorSeries]

/-- The zero-centered complex formal inverse sine, defined by its real Taylor coefficients. -/
def complexArcsinSeries : PowerSeries ℂ :=
  (taylorSeries Real.arcsin 0).map Complex.ofRealHom

@[simp] theorem constantCoeff_complexArcsinSeries : complexArcsinSeries.constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [complexArcsinSeries, PowerSeries.coeff_map,
    coeff_taylorSeries_arcsin_even 0, map_zero]

@[simp] theorem coeff_complexArcsinSeries_one : complexArcsinSeries.coeff 1 = 1 := by
  simp only [complexArcsinSeries, PowerSeries.coeff_map, coeff_taylorSeries_arcsin_one, map_one]

/-- The even coefficients vanish, including the constant coefficient. -/
@[simp] theorem coeff_complexArcsinSeries_even (n : ℕ) :
    complexArcsinSeries.coeff (2 * n) = 0 := by
  simp only [complexArcsinSeries, PowerSeries.coeff_map, coeff_taylorSeries_arcsin_even, map_zero]

/-- The full odd coefficient formula, with no truncation or analytic convergence premise. -/
theorem coeff_complexArcsinSeries_odd (n : ℕ) :
    complexArcsinSeries.coeff (2 * n + 1) =
      (Nat.centralBinom n : ℂ) / (4 ^ n * (2 * n + 1)) := by
  simp only [complexArcsinSeries, PowerSeries.coeff_map, coeff_taylorSeries_arcsin_odd,
    map_div₀, map_natCast, map_mul, map_pow, map_ofNat, map_add, map_one]

theorem complexArcsinSeries_ne_zero : complexArcsinSeries ≠ 0 := by
  intro he
  have hc := coeff_complexArcsinSeries_one
  rw [he, map_zero] at hc
  exact zero_ne_one hc

/-- The inverse germ has a nonzero linear coefficient and formal order one. -/
theorem order_complexArcsinSeries : complexArcsinSeries.order = 1 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · rw [coeff_complexArcsinSeries_one]
    exact one_ne_zero
  · intro n hn
    have hn0 : n = 0 := Nat.lt_one_iff.mp hn
    subst n
    simpa only [zero_mul] using coeff_complexArcsinSeries_even 0

/-- Complex formal sine after the inverse germ is exactly the identity. -/
theorem complexSinSeries_subst_arcsin :
    complexSinSeries.subst complexArcsinSeries = PowerSeries.X := by
  have ha : PowerSeries.HasSubst (taylorSeries Real.arcsin 0) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have he := congrArg (PowerSeries.map Complex.ofRealHom) taylorSeries_sin_subst_arcsin
  change MvPowerSeries.map Complex.ofRealHom _ = MvPowerSeries.map Complex.ofRealHom _ at he
  rw [PowerSeries.map_subst ha] at he
  change ((taylorSeries Real.sin 0).map Complex.ofRealHom).subst complexArcsinSeries =
    (PowerSeries.map Complex.ofRealHom) PowerSeries.X at he
  simpa only [PowerSeries.map_X, map_taylorSeries_real_sin] using he

/-- The inverse germ after complex formal sine is exactly the identity. -/
theorem complexArcsinSeries_subst_sin :
    complexArcsinSeries.subst complexSinSeries = PowerSeries.X := by
  have hs : PowerSeries.HasSubst (taylorSeries Real.sin 0) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have he := congrArg (PowerSeries.map Complex.ofRealHom) taylorSeries_arcsin_subst_sin
  change MvPowerSeries.map Complex.ofRealHom _ = MvPowerSeries.map Complex.ofRealHom _ at he
  rw [PowerSeries.map_subst hs] at he
  change complexArcsinSeries.subst ((taylorSeries Real.sin 0).map Complex.ofRealHom) =
    (PowerSeries.map Complex.ofRealHom) PowerSeries.X at he
  simpa only [PowerSeries.map_X, map_taylorSeries_real_sin] using he

/-- Negating the formal argument negates the inverse germ. -/
theorem complexArcsinSeries_rescale_neg_one :
    PowerSeries.rescale (-1) complexArcsinSeries = -complexArcsinSeries := by
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp only [PowerSeries.coeff_rescale, map_neg, coeff_complexArcsinSeries_even,
      mul_zero, neg_zero]
  · simp only [PowerSeries.coeff_rescale, map_neg, pow_add, pow_mul, neg_one_sq,
      one_pow, pow_one, one_mul, neg_one_mul]

/-- Oddness in the same native substitution language as the inverse identities. -/
theorem complexArcsinSeries_subst_neg_X :
    complexArcsinSeries.subst (-PowerSeries.X) = -complexArcsinSeries := by
  have he := complexArcsinSeries_rescale_neg_one
  rw [PowerSeries.rescale_eq_subst, neg_one_smul] at he
  exact he

/-- Complex conjugation fixes every coefficient of the inverse-sine germ. -/
theorem map_conj_complexArcsinSeries :
    complexArcsinSeries.map (starRingEnd ℂ) = complexArcsinSeries := by
  ext n
  simp [complexArcsinSeries]

end
end Surreal.Analytic
