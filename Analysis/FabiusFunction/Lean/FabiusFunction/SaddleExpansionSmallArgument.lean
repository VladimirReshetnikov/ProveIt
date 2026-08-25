import FabiusFunction.FabiusSmallArgumentScale
import FabiusFunction.SaddleExpansionAlgebra

/-!
# Transporting full saddle expansions to small arguments

The exact inverse coordinate maps `t ↦ 2⁻ᵗ` and `x ↦ -log₂ x` identify
`t → ∞` with `x → 0⁺`.  This module upgrades the existing single-estimate
transfer to the full parameter-dependent Poincaré-expansion API, for scales
in arbitrary normed fields and functions valued in arbitrary normed vector
spaces.
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
  constructor
  · intro k
    have hc := (h.coeff_isBigO k).comp_tendsto
      fabiusSmallArgumentLog_tendsto_atTop
    apply hc.congr'
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact congrArg (coeff k) (fabiusLogArgument_smallArgumentLog hx)
    · filter_upwards with x
      rfl
  · intro N
    have hc := (h.remainder_isBigO N).comp_tendsto
      fabiusSmallArgumentLog_tendsto_atTop
    apply hc.congr'
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Function.comp_apply]
      rw [show fabiusLogArgument (fabiusSmallArgumentLog x) = x from
        fabiusLogArgument_smallArgumentLog hx]
      simp [partialSum, Function.comp_apply,
        fabiusLogArgument_smallArgumentLog hx]
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Function.comp_apply]
      rw [show fabiusLogArgument (fabiusSmallArgumentLog x) = x from
        fabiusLogArgument_smallArgumentLog hx]

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

end Fabius.SaddleExpansion
