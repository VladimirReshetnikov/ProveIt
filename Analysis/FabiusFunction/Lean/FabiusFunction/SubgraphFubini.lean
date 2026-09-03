import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weighted Fubini transport across measurable subgraphs and supergraphs

This module isolates reusable Bochner-valued forms of the elementary
subgraph and supergraph arguments behind survival, cumulative-distribution,
and quantile layer-cake formulas.  For a measurable height `Q`, an integrable
scalar weight `w`, and an integrable vector-valued kernel `k`, the strict
subgraph exchanges `{t | t < Q ω}` with `{ω | t < Q ω}`.  Its closed
supergraph dual exchanges `{t | Q ω ≤ t}` with `{ω | Q ω ≤ t}`, preserving
atoms on the graph.

The result works for arbitrary s-finite measures.  Probability, compact
support, positivity, differentiability, and a density are not required.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Fabius

/-- **Weighted subgraph Fubini theorem.**  Integrating a scalar-weighted
lower section of a measurable subgraph is the same as integrating the scalar
mass of each upper section against the vector-valued kernel:

`∫ ω, w ω • ∫_{t ∈ s, t < Q ω} k t
  = ∫_{t ∈ s} (∫_{ω, t < Q ω} w ω) • k t`.

Both measures may be arbitrary s-finite measures.  The scalar field may be
real or complex, and the target may be any complete normed space over it. -/
theorem integral_smul_setIntegral_subgraph
    {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [CompleteSpace E]
    (μ : Measure Ω) [SFinite μ] (ν : Measure ℝ) [SFinite ν]
    (Q : Ω → ℝ) (hQ : Measurable Q)
    (w : Ω → 𝕜) (hw : Integrable w μ)
    (k : ℝ → E) {s : Set ℝ} (hk : IntegrableOn k s ν) :
    (∫ ω, w ω • (∫ t in Iio (Q ω) ∩ s, k t ∂ν) ∂μ) =
      ∫ t in s, (∫ ω in Q ⁻¹' Ioi t, w ω ∂μ) • k t ∂ν := by
  let νs : Measure ℝ := ν.restrict s
  let A : Set (Ω × ℝ) := {z | z.2 < Q z.1}
  let H : Ω × ℝ → E :=
    fun z => A.indicator (fun z => w z.1 • k z.2) z
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_snd (hQ.comp measurable_fst)
  have hbase : Integrable (fun z : Ω × ℝ => w z.1 • k z.2) (μ.prod νs) := by
    exact hw.smul_prod hk
  have hH : Integrable H (μ.prod νs) := hbase.indicator hA
  have hleft (ω : Ω) :
      (∫ t, H (ω, t) ∂νs) =
        w ω • ∫ t in Iio (Q ω) ∩ s, k t ∂ν := by
    have hind : (fun t : ℝ => H (ω, t)) =
        (Iio (Q ω)).indicator (fun t => w ω • k t) := by
      funext t
      simp only [H, A, indicator, mem_setOf_eq, mem_Iio]
    rw [hind, integral_indicator measurableSet_Iio]
    change (∫ t, w ω • k t ∂(νs.restrict (Iio (Q ω)))) = _
    rw [show νs.restrict (Iio (Q ω)) =
        ν.restrict (Iio (Q ω) ∩ s) by
      dsimp [νs]
      exact Measure.restrict_restrict measurableSet_Iio]
    exact integral_smul (w ω) k
  have hright (t : ℝ) :
      (∫ ω, H (ω, t) ∂μ) =
        (∫ ω in Q ⁻¹' Ioi t, w ω ∂μ) • k t := by
    have hind : (fun ω : Ω => H (ω, t)) =
        (Q ⁻¹' Ioi t).indicator (fun ω => w ω • k t) := by
      funext ω
      simp only [H, A, indicator, mem_setOf_eq, mem_preimage, mem_Ioi]
    rw [hind, integral_indicator (hQ measurableSet_Ioi), integral_smul_const]
  have hswap :
      (∫ ω, ∫ t, H (ω, t) ∂νs ∂μ) =
        ∫ t, ∫ ω, H (ω, t) ∂μ ∂νs := by
    exact integral_integral_swap hH
  calc
    (∫ ω, w ω • (∫ t in Iio (Q ω) ∩ s, k t ∂ν) ∂μ) =
        ∫ ω, ∫ t, H (ω, t) ∂νs ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hleft ω).symm
    _ = ∫ t, ∫ ω, H (ω, t) ∂μ ∂νs := hswap
    _ = ∫ t in s, (∫ ω in Q ⁻¹' Ioi t, w ω ∂μ) • k t ∂ν := by
      apply integral_congr_ae
      filter_upwards with t
      exact hright t

/-- **Weighted closed-supergraph Fubini theorem.**  Integrating a
scalar-weighted upper section of a measurable closed supergraph is the same
as integrating the scalar mass of each lower section against the
vector-valued kernel:

`∫ ω, w ω • ∫_{t ∈ s, Q ω ≤ t} k t
  = ∫_{t ∈ s} (∫_{ω, Q ω ≤ t} w ω) • k t`.

The non-strict inequalities on both fibers preserve mass carried by the
graph.  Both measures may be arbitrary s-finite measures; no measurability
hypothesis on `s` is needed.  The scalar field may be real or complex, and
the target may be any complete compatible normed space. -/
theorem integral_smul_setIntegral_supergraph
    {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [CompleteSpace E]
    (μ : Measure Ω) [SFinite μ] (ν : Measure ℝ) [SFinite ν]
    (Q : Ω → ℝ) (hQ : Measurable Q)
    (w : Ω → 𝕜) (hw : Integrable w μ)
    (k : ℝ → E) {s : Set ℝ} (hk : IntegrableOn k s ν) :
    (∫ ω, w ω • (∫ t in Ici (Q ω) ∩ s, k t ∂ν) ∂μ) =
      ∫ t in s, (∫ ω in Q ⁻¹' Iic t, w ω ∂μ) • k t ∂ν := by
  let νs : Measure ℝ := ν.restrict s
  let A : Set (Ω × ℝ) := {z | Q z.1 ≤ z.2}
  let H : Ω × ℝ → E :=
    fun z => A.indicator (fun z => w z.1 • k z.2) z
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le (hQ.comp measurable_fst) measurable_snd
  have hbase : Integrable (fun z : Ω × ℝ => w z.1 • k z.2) (μ.prod νs) := by
    exact hw.smul_prod hk
  have hH : Integrable H (μ.prod νs) := hbase.indicator hA
  have hleft (ω : Ω) :
      (∫ t, H (ω, t) ∂νs) =
        w ω • ∫ t in Ici (Q ω) ∩ s, k t ∂ν := by
    have hind : (fun t : ℝ => H (ω, t)) =
        (Ici (Q ω)).indicator (fun t => w ω • k t) := by
      funext t
      simp only [H, A, indicator, mem_setOf_eq, mem_Ici]
    rw [hind, integral_indicator measurableSet_Ici]
    change (∫ t, w ω • k t ∂(νs.restrict (Ici (Q ω)))) = _
    rw [show νs.restrict (Ici (Q ω)) =
        ν.restrict (Ici (Q ω) ∩ s) by
      dsimp [νs]
      exact Measure.restrict_restrict measurableSet_Ici]
    exact integral_smul (w ω) k
  have hright (t : ℝ) :
      (∫ ω, H (ω, t) ∂μ) =
        (∫ ω in Q ⁻¹' Iic t, w ω ∂μ) • k t := by
    have hind : (fun ω : Ω => H (ω, t)) =
        (Q ⁻¹' Iic t).indicator (fun ω => w ω • k t) := by
      funext ω
      simp only [H, A, indicator, mem_setOf_eq, mem_preimage, mem_Iic]
    rw [hind, integral_indicator (hQ measurableSet_Iic), integral_smul_const]
  have hswap :
      (∫ ω, ∫ t, H (ω, t) ∂νs ∂μ) =
        ∫ t, ∫ ω, H (ω, t) ∂μ ∂νs := by
    exact integral_integral_swap hH
  calc
    (∫ ω, w ω • (∫ t in Ici (Q ω) ∩ s, k t ∂ν) ∂μ) =
        ∫ ω, ∫ t, H (ω, t) ∂νs ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hleft ω).symm
    _ = ∫ t, ∫ ω, H (ω, t) ∂μ ∂νs := hswap
    _ = ∫ t in s, (∫ ω in Q ⁻¹' Iic t, w ω ∂μ) • k t ∂ν := by
      apply integral_congr_ae
      filter_upwards with t
      exact hright t

end Fabius
