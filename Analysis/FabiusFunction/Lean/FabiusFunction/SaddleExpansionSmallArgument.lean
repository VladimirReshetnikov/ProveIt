import FabiusFunction.FabiusSmallArgumentScale
import FabiusFunction.SaddleExpansionFlat

/-!
# Transporting full saddle expansions to small arguments

The exact inverse coordinate maps `t ↦ 2⁻ᵗ` and `x ↦ -log₂ x` identify
`t → ∞` with `x → 0⁺`.  This module upgrades the existing single-estimate
transfer to the full parameter-dependent Poincaré-expansion API, for scales
in arbitrary normed fields and functions valued in arbitrary normed vector
spaces. The same equivalence is exposed directly for remainders negligible at
every algebraic order.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius.SaddleExpansion

variable {𝕜 ℰ : Type*} [NormedField 𝕜]
  [NormedAddCommGroup ℰ] [NormedSpace 𝕜 ℰ]

/-- Transfer a full expansion in the exact logarithmic coordinate
`t ↦ 2⁻ᵗ` back to the small-positive-argument filter.  The scale may
take values in any normed field and the expanded function in any normed
vector space over that field. -/
theorem HasAsymptoticExpansion.smallArgument_of_logScale
    {scale : ℝ → 𝕜} {f : ℝ → ℰ} {coeff : ℕ → ℝ → ℰ}
    (h : HasAsymptoticExpansion atTop
      (scale ∘ fabiusLogArgument) (f ∘ fabiusLogArgument)
      (fun k => coeff k ∘ fabiusLogArgument)) :
    HasAsymptoticExpansion (nhdsWithin 0 (Ioi 0)) scale f coeff := by
  have hcomp := h.comp_tendsto fabiusSmallArgumentLog
    fabiusSmallArgumentLog_tendsto_atTop
  have hscale : ((scale ∘ fabiusLogArgument) ∘ fabiusSmallArgumentLog) =ᶠ[
      nhdsWithin 0 (Ioi 0)] scale := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Function.comp_apply, fabiusLogArgument_smallArgumentLog hx]
  have hf : ((f ∘ fabiusLogArgument) ∘ fabiusSmallArgumentLog) =ᶠ[
      nhdsWithin 0 (Ioi 0)] f := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Function.comp_apply, fabiusLogArgument_smallArgumentLog hx]
  have hcoeff : ∀ k, ((coeff k ∘ fabiusLogArgument) ∘
      fabiusSmallArgumentLog) =ᶠ[nhdsWithin 0 (Ioi 0)] coeff k := by
    intro k
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Function.comp_apply, fabiusLogArgument_smallArgumentLog hx]
  exact (hcomp.congr hscale hf).congr_coeff hcoeff

/-- Pull a full small-positive-argument expansion back to the exact
logarithmic coordinate `t ↦ 2⁻ᵗ`, with arbitrary normed scalar and
vector codomains. -/
theorem HasAsymptoticExpansion.logScale_of_smallArgument
    {scale : ℝ → 𝕜} {f : ℝ → ℰ} {coeff : ℕ → ℝ → ℰ}
    (h : HasAsymptoticExpansion (nhdsWithin 0 (Ioi 0)) scale f coeff) :
    HasAsymptoticExpansion atTop
      (scale ∘ fabiusLogArgument) (f ∘ fabiusLogArgument)
      (fun k => coeff k ∘ fabiusLogArgument) :=
  h.comp_tendsto fabiusLogArgument fabiusLogArgument_tendsto_smallArgument

/-- Full expansions in the exact logarithmic coordinate are equivalent to
full expansions at zero from the right, for arbitrary normed scalar and
vector codomains. -/
theorem hasAsymptoticExpansion_logScale_iff_smallArgument
    {scale : ℝ → 𝕜} {f : ℝ → ℰ} {coeff : ℕ → ℝ → ℰ} :
    HasAsymptoticExpansion atTop
        (scale ∘ fabiusLogArgument) (f ∘ fabiusLogArgument)
        (fun k => coeff k ∘ fabiusLogArgument) ↔
      HasAsymptoticExpansion (nhdsWithin 0 (Ioi 0)) scale f coeff :=
  ⟨HasAsymptoticExpansion.smallArgument_of_logScale,
    HasAsymptoticExpansion.logScale_of_smallArgument⟩

/-- Negligibility at every algebraic order is invariant under the exact
coordinate change `x = 2⁻ᵗ`. Unlike a one-way `IsBigO.comp_tendsto`
statement, this is an equivalence because `fabiusLogArgument` and
`fabiusSmallArgumentLog` are inverse on the relevant filters. -/
theorem isBigO_all_logScale_iff_smallArgument
    {scale : ℝ → 𝕜} {f : ℝ → ℰ} :
    (∀ N, (f ∘ fabiusLogArgument) =O[atTop]
        (fun t => (scale ∘ fabiusLogArgument) t ^ N)) ↔
      ∀ N, f =O[nhdsWithin 0 (Ioi 0)] (fun x => scale x ^ N) := by
  constructor
  · intro hflat
    have htop : HasAsymptoticExpansion atTop
        (scale ∘ fabiusLogArgument) (f ∘ fabiusLogArgument)
        (fun _k _t => (0 : ℰ)) :=
      hasAsymptoticExpansion_zero_coeff_iff_isBigO_all.mpr hflat
    have htop' : HasAsymptoticExpansion atTop
        (scale ∘ fabiusLogArgument) (f ∘ fabiusLogArgument)
        (fun k => (fun _x : ℝ => (0 : ℰ)) ∘ fabiusLogArgument) := by
      simpa [Function.comp_def] using htop
    have hsmall := htop'.smallArgument_of_logScale
    apply hasAsymptoticExpansion_zero_coeff_iff_isBigO_all.mp
    simpa [Function.comp_def] using hsmall
  · intro hflat
    have hsmall : HasAsymptoticExpansion (nhdsWithin 0 (Ioi 0)) scale f
        (fun _k _x => (0 : ℰ)) :=
      hasAsymptoticExpansion_zero_coeff_iff_isBigO_all.mpr hflat
    have htop := hsmall.logScale_of_smallArgument
    apply hasAsymptoticExpansion_zero_coeff_iff_isBigO_all.mp
    simpa [Function.comp_def] using htop

end Fabius.SaddleExpansion
