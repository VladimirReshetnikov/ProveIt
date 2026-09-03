import FabiusFunction.DyadicCombTrapezoid
import FabiusFunction.FabiusInverse
import FabiusFunction.SubgraphFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# Weighted inverse layer-cake identities

This module turns `SubgraphFubini` into an interval identity for mutually
inverse increasing clocks on arbitrary compact intervals.  Its Fabius
specialization exchanges a
primitive evaluated at `fabiusInv` with the complementary primitive above
`fabiusReal`:

`∫₀¹ φ(u) • ∫₀ᴳ⁽ᵘ⁾ ψ(x) dx du
  = ∫₀¹ (∫_F(x)¹ φ(u) du) • ψ(x) dx`.

The foundational Fubini argument is weighted, complex-scalar compatible, and
Banach-valued.  On an ordered compact rectangle, the strict order equivalence
makes the restricted clocks a Galois connection.  Their monotonicity supplies
a canonical measurable clamped extension, so the public interval identities
need no global measurability assumption on either clock.  Differentiability
and a change-of-variables Jacobian are also unnecessary.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Fabius

/-- **The interval restrictions of inverse clocks form a Galois connection.**
Suppose `C` maps `[a,b]` into `[c,d]`, `Q` maps `[c,d]` into `[a,b]`, and

`C x < u ↔ x < Q u`.

Then the interval restriction of `Q` is lower adjoint to the interval
restriction of `C`.  In particular, both restricted clocks are monotone. -/
theorem galoisConnection_Icc_restrict_of_lt_iff_lt
    (C Q : ℝ → ℝ) {a b c d : ℝ}
    (hC : MapsTo C (Icc a b) (Icc c d))
    (hQ : MapsTo Q (Icc c d) (Icc a b))
    (hinv : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Q u)) :
    GaloisConnection
      (fun u : Icc c d ↦ ⟨Q u, hQ u.2⟩)
      (fun x : Icc a b ↦ ⟨C x, hC x.2⟩) := by
  intro u x
  change Q u ≤ x ↔ u ≤ C x
  simpa only [not_lt] using (not_congr (hinv x.2 u.2)).symm

private theorem intervalIntegral_smul_intervalIntegral_of_lt_iff_lt_of_measurable
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

/-- **Weighted inverse layer cake on a compact rectangle.**  Suppose `C`
maps `[a,b]` into `[c,d]`, `Q` maps `[c,d]` into `[a,b]`, and

`C x < u ↔ x < Q u`.

Then a scalar-weighted primitive stopped at `Q u` may be integrated in the
opposite order as the complementary scalar primitive starting at `C x`.
The scalar field may be real or complex, and the second integrand may take
values in any complete compatible normed space.

No global measurability assumption on either clock is needed.  The restricted
clocks form a Galois connection, so `Q` is monotone on `[c,d]`; the proof
applies the measurable subgraph theorem to its canonical clamped extension.
Consequently, values of both clocks outside their stated intervals play no
role. -/
theorem intervalIntegral_smul_intervalIntegral_of_lt_iff_lt
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [CompleteSpace E]
    (C Q : ℝ → ℝ)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hC : MapsTo C (Icc a b) (Icc c d))
    (hQ : MapsTo Q (Icc c d) (Icc a b))
    (hinv : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Q u))
    (φ : ℝ → 𝕜) (hφ : IntervalIntegrable φ volume c d)
    (ψ : ℝ → E) (hψ : IntervalIntegrable ψ volume a b) :
    (∫ u in c..d, φ u • (∫ x in a..Q u, ψ x)) =
      ∫ x in a..b, (∫ u in C x..d, φ u) • ψ x := by
  classical
  have hgc := galoisConnection_Icc_restrict_of_lt_iff_lt C Q hC hQ hinv
  have hQsubmono : Monotone (fun u : Icc c d ↦ Q u) := by
    intro u v huv
    exact hgc.monotone_l huv
  let Qext : ℝ → ℝ := IccExtend hcd (fun u : Icc c d ↦ Q u)
  have hQextm : Measurable Qext := by
    change Measurable (IccExtend hcd (fun u : Icc c d ↦ Q u))
    exact (hQsubmono.IccExtend hcd).measurable
  have hQext_eq (u : ℝ) (hu : u ∈ Icc c d) : Qext u = Q u := by
    change IccExtend hcd (fun z : Icc c d ↦ Q z) u = Q u
    simpa using IccExtend_of_mem hcd (fun z : Icc c d ↦ Q z) hu
  have hQext : MapsTo Qext (Icc c d) (Icc a b) := by
    intro u hu
    rw [hQext_eq u hu]
    exact hQ hu
  have hinvExt : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Qext u) := by
    intro x u hx hu
    rw [hQext_eq u hu]
    exact hinv hx hu
  have hlayer :=
    intervalIntegral_smul_intervalIntegral_of_lt_iff_lt_of_measurable
      C Qext hQextm hab hcd hC hQext hinvExt φ hφ ψ hψ
  calc
    (∫ u in c..d, φ u • (∫ x in a..Q u, ψ x)) =
        ∫ u in c..d, φ u • (∫ x in a..Qext u, ψ x) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hcd] at hu
      change φ u • (∫ x in a..Q u, ψ x) =
        φ u • (∫ x in a..Qext u, ψ x)
      rw [hQext_eq u hu]
    _ = ∫ x in a..b, (∫ u in C x..d, φ u) • ψ x := hlayer

/-- **Differentiable weighted inverse layer cake.**  Under the same order
equivalence as `intervalIntegral_smul_intervalIntegral_of_lt_iff_lt`, a
primitive `Ψ` with continuous derivative `ψ` may replace the explicit inner
integral.  This is a pointwise-`C¹` theorem; no derivative, Jacobian, or
measurability hypothesis on either clock is used. -/
theorem intervalIntegral_smul_comp_of_lt_iff_lt
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [CompleteSpace E]
    (C Q : ℝ → ℝ)
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
        C Q hab hcd hC hQ hinv φ hφ ψ
          (hψ.intervalIntegrable_of_Icc hab)

/-- **Absolutely-continuous weighted inverse layer cake on a rectangle.**
Suppose `C` maps `[a,b]` into `[c,d]`, `Q` maps `[c,d]` into `[a,b]`, and

`C x < u ↔ x < Q u`

throughout the rectangle.  If `φ` is interval integrable and `Ψ` is
absolutely continuous on `[a,b]`, then

`∫_c^d φ(u) (Ψ(Q(u)) - Ψ(a)) du
  = ∫_a^b Ψ'(x) (∫_{C(x)}^d φ(u) du) dx`.

The weight may be real or complex.  No measurability assumption on either
clock is needed; this follows from the measurable-free weighted layer-cake
theorem above.  Absolute continuity supplies an integrable derivative, so no
separate integrability hypothesis on the right-hand side is needed. -/
theorem intervalIntegral_mul_comp_sub_of_lt_iff_lt_of_absolutelyContinuousOnInterval
    {𝕜 : Type*} [RCLike 𝕜]
    (C Q : ℝ → ℝ)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hC : MapsTo C (Icc a b) (Icc c d))
    (hQ : MapsTo Q (Icc c d) (Icc a b))
    (hinv : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Q u))
    (φ : ℝ → 𝕜) (hφ : IntervalIntegrable φ volume c d)
    (Ψ : ℝ → ℝ) (hΨ : AbsolutelyContinuousOnInterval Ψ a b) :
    (∫ u in c..d, φ u * ((Ψ (Q u) - Ψ a : ℝ) : 𝕜)) =
      ∫ x in a..b,
        ((deriv Ψ x : ℝ) : 𝕜) * (∫ u in C x..d, φ u) := by
  have hderivReal : IntervalIntegrable (deriv Ψ) volume a b :=
    hΨ.intervalIntegrable_deriv
  have hderiv :
      IntervalIntegrable (fun x ↦ ((deriv Ψ x : ℝ) : 𝕜)) volume a b :=
    ⟨hderivReal.1.ofReal, hderivReal.2.ofReal⟩
  have hprimitive (y : ℝ) (hy : y ∈ Icc a b) :
      (∫ x in a..y, ((deriv Ψ x : ℝ) : 𝕜)) =
        ((Ψ y - Ψ a : ℝ) : 𝕜) := by
    have hΨy : AbsolutelyContinuousOnInterval Ψ a y :=
      hΨ.mono (by
        rw [uIcc_of_le hy.1, uIcc_of_le hab]
        exact Icc_subset_Icc_right hy.2)
    rw [RCLike.intervalIntegral_ofReal, hΨy.integral_deriv_eq_sub]
  have hlayer := intervalIntegral_smul_intervalIntegral_of_lt_iff_lt
    (𝕜 := 𝕜) (E := 𝕜) C Q hab hcd hC hQ hinv
      φ hφ (fun x ↦ ((deriv Ψ x : ℝ) : 𝕜)) hderiv
  calc
    (∫ u in c..d, φ u * ((Ψ (Q u) - Ψ a : ℝ) : 𝕜)) =
        ∫ u in c..d, φ u *
          (∫ x in a..Q u, ((deriv Ψ x : ℝ) : 𝕜)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hcd] at hu
      change φ u * ((Ψ (Q u) - Ψ a : ℝ) : 𝕜) =
        φ u * (∫ x in a..Q u, ((deriv Ψ x : ℝ) : 𝕜))
      rw [hprimitive (Q u) (hQ hu)]
    _ = ∫ x in a..b,
        (∫ u in C x..d, φ u) * ((deriv Ψ x : ℝ) : 𝕜) := by
      simpa only [smul_eq_mul] using hlayer
    _ = ∫ x in a..b,
        ((deriv Ψ x : ℝ) : 𝕜) * (∫ u in C x..d, φ u) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change (∫ u in C x..d, φ u) * ((deriv Ψ x : ℝ) : 𝕜) =
        ((deriv Ψ x : ℝ) : 𝕜) * (∫ u in C x..d, φ u)
      rw [mul_comm]

/-- Normalized absolutely-continuous inverse layer cake.  This is the
preceding theorem when the primitive vanishes at the left endpoint. -/
theorem intervalIntegral_mul_comp_of_lt_iff_lt_of_absolutelyContinuousOnInterval
    {𝕜 : Type*} [RCLike 𝕜]
    (C Q : ℝ → ℝ)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hC : MapsTo C (Icc a b) (Icc c d))
    (hQ : MapsTo Q (Icc c d) (Icc a b))
    (hinv : ∀ ⦃x u : ℝ⦄, x ∈ Icc a b → u ∈ Icc c d →
      (C x < u ↔ x < Q u))
    (φ : ℝ → 𝕜) (hφ : IntervalIntegrable φ volume c d)
    (Ψ : ℝ → ℝ) (hΨ : AbsolutelyContinuousOnInterval Ψ a b)
    (hΨa : Ψ a = 0) :
    (∫ u in c..d, φ u * (Ψ (Q u) : 𝕜)) =
      ∫ x in a..b,
        ((deriv Ψ x : ℝ) : 𝕜) * (∫ u in C x..d, φ u) := by
  simpa only [hΨa, sub_zero] using
    (intervalIntegral_mul_comp_sub_of_lt_iff_lt_of_absolutelyContinuousOnInterval
      C Q hab hcd hC hQ hinv φ hφ Ψ hΨ)

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

/-- **Absolutely-continuous weighted inverse layer cake for the Fabius
clocks.**  For every real or complex interval-integrable weight `φ` and every
real absolutely continuous primitive `Ψ` with `Ψ 0 = 0`,

`∫₀¹ φ(u) Ψ(fabiusInv(u)) du
  = ∫₀¹ Ψ'(x) (∫_{fabiusReal(x)}¹ φ(u) du) dx`.

This is the exact proper-compact `L¹`/absolutely-continuous form of the
forward--inverse layer-cake theorem.  No derivative or measurability
hypothesis on either Fabius clock is required. -/
theorem intervalIntegral_mul_comp_fabiusInv_of_absolutelyContinuousOnInterval
    {𝕜 : Type*} [RCLike 𝕜]
    (F : BoundedFabius) (hF : IsFabius F)
    (φ : ℝ → 𝕜) (hφ : IntervalIntegrable φ volume 0 1)
    (Ψ : ℝ → ℝ) (hΨ : AbsolutelyContinuousOnInterval Ψ 0 1)
    (hΨ0 : Ψ 0 = 0) :
    (∫ u in (0 : ℝ)..1, φ u * (Ψ (fabiusInv F hF u) : 𝕜)) =
      ∫ x in (0 : ℝ)..1,
        ((deriv Ψ x : ℝ) : 𝕜) * (∫ u in fabiusReal F x..1, φ u) := by
  apply intervalIntegral_mul_comp_of_lt_iff_lt_of_absolutelyContinuousOnInterval
    (C := fabiusReal F) (Q := fabiusInv F hF)
  · norm_num
  · norm_num
  · intro x _hx
    exact ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩
  · intro u _hu
    exact fabiusInv_mem_Icc F hF u
  · intro x u hx hu
    exact fabiusReal_lt_iff_lt_fabiusInv F hF hx hu
  · exact hφ
  · exact hΨ
  · exact hΨ0

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
    (∫ u in (0 : ℝ)..1, fabiusInv F hF u) = 1 / 2 :=
  integral_unit_of_reflect (fabiusInv_one_sub F hF)
    ((continuous_fabiusInv F hF).intervalIntegrable 0 1)

end Fabius
