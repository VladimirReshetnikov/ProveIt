import FabiusFunction.FabiusInverse
import FabiusFunction.SubgraphFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weighted inverse layer-cake identities

This module turns `SubgraphFubini` into an interval identity for mutually
inverse increasing clocks on arbitrary compact intervals.  Its Fabius
specialization exchanges a
primitive evaluated at `fabiusInv` with the complementary primitive above
`fabiusReal`:

`∫₀¹ φ(u) • ∫₀ᴳ⁽ᵘ⁾ ψ(x) dx du
  = ∫₀¹ (∫_F(x)¹ φ(u) du) • ψ(x) dx`.

The theorem is weighted, complex-scalar compatible, and Banach-valued.  It
uses only measurability, interval integrability, range preservation, and the
strict order equivalence between the two clocks; differentiability and a
change-of-variables Jacobian are unnecessary.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Fabius

/-- **Weighted inverse layer cake on a rectangle.**  Suppose `C` maps
`[a,b]` to `[c,d]`, `Q` maps `[c,d]` back to `[a,b]`, and

`C x < u ↔ x < Q u`.

Then a scalar-weighted primitive stopped at `Q u` may be integrated in the
opposite order as the complementary scalar primitive starting at `C x`.
The scalar field may be real or complex, and the second integrand may take
values in any complete compatible normed space. -/
theorem intervalIntegral_smul_intervalIntegral_of_lt_iff_lt
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [CompleteSpace E]
    (C Q : ℝ → ℝ) (hQm : Measurable Q)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hC : MapsTo C (Icc a b) (Icc c d))
    (hQ : MapsTo Q (Icc c d) (Icc a b))
    (hinv : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Q u))
    (φ : ℝ → 𝕜) (hφ : IntervalIntegrable φ volume c d)
    (ψ : ℝ → E) (hψ : IntervalIntegrable ψ volume a b) :
    (∫ u in c..d, φ u • (∫ x in a..Q u, ψ x)) =
      ∫ x in a..b, (∫ u in C x..d, φ u) • ψ x := by
  let domain : Set ℝ := Icc a b
  let levels : Set ℝ := Icc c d
  have hφOn : IntegrableOn φ levels volume := by
    simpa only [levels] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mp hφ
  have hψOn : IntegrableOn ψ domain volume := by
    simpa only [domain] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hψ
  have hlower (u : ℝ) (hu : u ∈ levels) :
      (∫ x in Iio (Q u) ∩ domain, ψ x) =
        ∫ x in a..Q u, ψ x := by
    have hset : Iio (Q u) ∩ domain = Ico a (Q u) := by
      ext x
      simp only [domain, mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨hxQ, hxa, _hxb⟩
        exact ⟨hxa, hxQ⟩
      · rintro ⟨hxa, hxQ⟩
        exact ⟨hxQ, hxa, hxQ.le.trans (hQ hu).2⟩
    rw [hset, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (hQ hu).1]
  have hupper (x : ℝ) (hx : x ∈ domain) :
      (∫ u in Q ⁻¹' Ioi x, φ u ∂volume.restrict levels) =
        ∫ u in C x..d, φ u := by
    have hset : (Q ⁻¹' Ioi x) ∩ levels = Ioc (C x) d := by
      ext u
      simp only [levels, mem_inter_iff, mem_preimage, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨hxu, huc, hud⟩
        exact ⟨(hinv hx ⟨huc, hud⟩).mpr hxu, hud⟩
      · rintro ⟨hCu, hud⟩
        have huc : c ≤ u := (hC hx).1.trans hCu.le
        have hu : u ∈ Icc c d := ⟨huc, hud⟩
        exact ⟨(hinv hx hu).mp hCu, huc, hud⟩
    change (∫ u, φ u ∂((volume.restrict levels).restrict (Q ⁻¹' Ioi x))) = _
    rw [Measure.restrict_restrict (hQm measurableSet_Ioi), hset,
      ← intervalIntegral.integral_of_le (hC hx).2]
  have hcore := integral_smul_setIntegral_subgraph
    (μ := volume.restrict levels) (ν := volume)
    (Q := Q) hQm (w := φ) hφOn (k := ψ) (s := domain) hψOn
  change
    (∫ u in levels, φ u • (∫ x in Iio (Q u) ∩ domain, ψ x)) =
      ∫ x in domain,
        (∫ u in Q ⁻¹' Ioi x, φ u ∂volume.restrict levels) • ψ x at hcore
  have hlevels (f : ℝ → E) :
      (∫ u in c..d, f u) = ∫ u in levels, f u := by
    rw [intervalIntegral.integral_of_le hcd,
      ← integral_Icc_eq_integral_Ioc]
  have hdomain (f : ℝ → E) :
      (∫ x in a..b, f x) = ∫ x in domain, f x := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ u in c..d, φ u • (∫ x in a..Q u, ψ x)) =
        ∫ u in levels, φ u • (∫ x in a..Q u, ψ x) :=
      hlevels _
    _ = ∫ u in levels, φ u • (∫ x in Iio (Q u) ∩ domain, ψ x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      rw [hlower u hu]
    _ = ∫ x in domain,
        (∫ u in Q ⁻¹' Ioi x, φ u ∂volume.restrict levels) • ψ x := hcore
    _ = ∫ x in domain, (∫ u in C x..d, φ u) • ψ x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [hupper x hx]
    _ = ∫ x in a..b, (∫ u in C x..d, φ u) • ψ x :=
      (hdomain _).symm

/-- **Differentiable weighted inverse layer cake.**  Under the same order
equivalence as `intervalIntegral_smul_intervalIntegral_of_lt_iff_lt`, a
primitive `Ψ` with continuous derivative `ψ` may replace the explicit inner
integral.  This is a pointwise-`C¹` theorem; no derivative of either clock is
used. -/
theorem intervalIntegral_smul_comp_of_lt_iff_lt
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [CompleteSpace E]
    (C Q : ℝ → ℝ) (hQm : Measurable Q)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hC : MapsTo C (Icc a b) (Icc c d))
    (hQ : MapsTo Q (Icc c d) (Icc a b))
    (hinv : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Q u))
    (φ : ℝ → 𝕜) (hφ : IntervalIntegrable φ volume c d)
    (Ψ ψ : ℝ → E) (hψ : ContinuousOn ψ (Icc a b))
    (hΨa : Ψ a = 0)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt Ψ (ψ x) x) :
    (∫ u in c..d, φ u • Ψ (Q u)) =
      ∫ x in a..b, (∫ u in C x..d, φ u) • ψ x := by
  have hprimitive (y : ℝ) (hy : y ∈ Icc a b) :
      Ψ y = ∫ x in a..y, ψ x := by
    have hψy : IntervalIntegrable ψ volume a y :=
      (hψ.mono (Icc_subset_Icc_right hy.2)).intervalIntegrable_of_Icc hy.1
    have hftc : (∫ x in a..y, ψ x) = Ψ y - Ψ a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        rw [uIcc_of_le hy.1] at hx
        exact hderiv x ⟨hx.1, hx.2.trans hy.2⟩
      · exact hψy
    rw [hΨa, sub_zero] at hftc
    exact hftc.symm
  calc
    (∫ u in c..d, φ u • Ψ (Q u)) =
        ∫ u in c..d, φ u • (∫ x in a..Q u, ψ x) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hcd] at hu
      change φ u • Ψ (Q u) = φ u • ∫ x in a..Q u, ψ x
      rw [hprimitive (Q u) (hQ hu)]
    _ = ∫ x in a..b, (∫ u in C x..d, φ u) • ψ x :=
      intervalIntegral_smul_intervalIntegral_of_lt_iff_lt
        C Q hQm hab hcd hC hQ hinv φ hφ ψ
          (hψ.intervalIntegrable_of_Icc hab)

/-- **Weighted inverse layer cake for the Fabius clocks.**  Integrating a
primitive at `fabiusInv F hF u` is equivalent to integrating the complementary
weight above `fabiusReal F x`.  This is the Banach-valued and complex-weighted
form of the inverse-area identity from the fractional-transform frontier. -/
theorem intervalIntegral_smul_intervalIntegral_fabiusInv
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F)
    (φ : ℝ → 𝕜) (hφ : IntervalIntegrable φ volume 0 1)
    (ψ : ℝ → E) (hψ : IntervalIntegrable ψ volume 0 1) :
    (∫ u in (0 : ℝ)..1,
        φ u • (∫ x in (0 : ℝ)..fabiusInv F hF u, ψ x)) =
      ∫ x in (0 : ℝ)..1,
        (∫ u in fabiusReal F x..1, φ u) • ψ x := by
  apply intervalIntegral_smul_intervalIntegral_of_lt_iff_lt
    (C := fabiusReal F) (Q := fabiusInv F hF)
  · exact (continuous_fabiusInv F hF).measurable
  · norm_num
  · norm_num
  · intro x _hx
    exact ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩
  · intro u _hu
    exact fabiusInv_mem_Icc F hF u
  · intro x u hx hu
    exact fabiusReal_lt_iff_lt_fabiusInv F hF hx hu
  · exact hφ
  · exact hψ

/-- Pointwise-`C¹` form of the weighted Fabius inverse layer cake.  If
`Ψ(0) = 0` and `Ψ' = ψ` on `[0,1]`, then

`∫₀¹ φ(u) • Ψ(fabiusInv u)
  = ∫₀¹ (∫_{fabiusReal x}¹ φ(u) du) • ψ(x) dx`. -/
theorem intervalIntegral_smul_comp_fabiusInv
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F)
    (φ : ℝ → 𝕜) (hφ : IntervalIntegrable φ volume 0 1)
    (Ψ ψ : ℝ → E) (hψ : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hΨ0 : Ψ 0 = 0)
    (hderiv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt Ψ (ψ x) x) :
    (∫ u in (0 : ℝ)..1, φ u • Ψ (fabiusInv F hF u)) =
      ∫ x in (0 : ℝ)..1,
        (∫ u in fabiusReal F x..1, φ u) • ψ x := by
  apply intervalIntegral_smul_comp_of_lt_iff_lt
    (C := fabiusReal F) (Q := fabiusInv F hF)
  · exact (continuous_fabiusInv F hF).measurable
  · norm_num
  · norm_num
  · intro x _hx
    exact ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩
  · intro u _hu
    exact fabiusInv_mem_Icc F hF u
  · intro x u hx hu
    exact fabiusReal_lt_iff_lt_fabiusInv F hF hx hu
  · exact hφ
  · exact hψ
  · exact hΨ0
  · exact hderiv

/-- **Weighted area identity for the inverse Fabius function.**  Every
integrable real weight satisfies

`∫₀¹ w(u) fabiusInv(u) du
  = ∫₀¹ ∫_{fabiusReal(x)}¹ w(u) du dx`. -/
theorem intervalIntegral_mul_fabiusInv_eq
    (F : BoundedFabius) (hF : IsFabius F)
    (w : ℝ → ℝ) (hw : IntervalIntegrable w volume 0 1) :
    (∫ u in (0 : ℝ)..1, w u * fabiusInv F hF u) =
      ∫ x in (0 : ℝ)..1, ∫ u in fabiusReal F x..1, w u := by
  simpa only [smul_eq_mul, mul_one, id_eq] using
    (intervalIntegral_smul_comp_fabiusInv
      (𝕜 := ℝ) (E := ℝ) F hF w hw id (fun _ => 1)
      continuousOn_const (by rfl) (fun x _ => hasDerivAt_id x))

/-- The area under the inverse Fabius function on the unit interval equals
the area under Rvachev's `up` function on the same interval.  Equivalently,
this is the inverse-area identity against the survival profile
`x ↦ 1 - fabiusReal F x`. -/
theorem intervalIntegral_fabiusInv_eq_intervalIntegral_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ u in (0 : ℝ)..1, fabiusInv F hF u) =
      ∫ x in (0 : ℝ)..1, rvachevUp F x := by
  have harea := intervalIntegral_mul_fabiusInv_eq F hF
    (fun _ : ℝ => (1 : ℝ))
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1)
  calc
    (∫ u in (0 : ℝ)..1, fabiusInv F hF u) =
        ∫ u in (0 : ℝ)..1, (1 : ℝ) * fabiusInv F hF u := by
      simp only [one_mul]
    _ = ∫ x in (0 : ℝ)..1,
          ∫ u in fabiusReal F x..1, (1 : ℝ) := harea
    _ = ∫ x in (0 : ℝ)..1, rvachevUp F x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      change (∫ u in fabiusReal F x..1, (1 : ℝ)) = rvachevUp F x
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one,
        rvachevUp_eq_fabiusReal_one_sub F hx.1, hF.symmetry x hx]

/-- The mean of the inverse Fabius function under the uniform law on the
unit interval is `1 / 2`.  This follows directly from the global reflection
identity `fabiusInv F hF (1 - u) = 1 - fabiusInv F hF u`. -/
theorem intervalIntegral_fabiusInv_eq_one_half
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ u in (0 : ℝ)..1, fabiusInv F hF u) = 1 / 2 := by
  have hintegrable :
      IntervalIntegrable (fabiusInv F hF) volume 0 1 :=
    (continuous_fabiusInv F hF).intervalIntegrable 0 1
  have hreflect :
      (∫ u in (0 : ℝ)..1, fabiusInv F hF u) =
        ∫ u in (0 : ℝ)..1, fabiusInv F hF (1 - u) := by
    symm
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (f := fabiusInv F hF) (a := (0 : ℝ)) (b := 1) 1
  have hbalance :
      (∫ u in (0 : ℝ)..1, fabiusInv F hF u) =
        1 - ∫ u in (0 : ℝ)..1, fabiusInv F hF u := by
    calc
      (∫ u in (0 : ℝ)..1, fabiusInv F hF u) =
          ∫ u in (0 : ℝ)..1, fabiusInv F hF (1 - u) := hreflect
      _ = ∫ u in (0 : ℝ)..1, (1 - fabiusInv F hF u) := by
        apply intervalIntegral.integral_congr
        intro u _hu
        change fabiusInv F hF (1 - u) = 1 - fabiusInv F hF u
        rw [fabiusInv_one_sub F hF u]
      _ = 1 - ∫ u in (0 : ℝ)..1, fabiusInv F hF u := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const hintegrable,
          intervalIntegral.integral_const]
        norm_num
  linarith

end Fabius
