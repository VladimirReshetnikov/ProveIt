import FabiusFunction.FabiusSmallArgumentScale
import FabiusFunction.SaddleExpansionAlgebra

/-!
# Transporting full saddle expansions to small arguments

The exact inverse coordinate maps `t ↦ 2⁻ᵗ` and `x ↦ -log₂ x` identify
`t → ∞` with `x → 0⁺`.  This module upgrades the existing single-estimate
transfer to the full parameter-dependent Poincaré-expansion API.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius.SaddleExpansion

/-- Transfer a full expansion in the exact logarithmic coordinate
`t ↦ 2⁻ᵗ` back to the small-positive-argument filter. -/
theorem HasAsymptoticExpansion.smallArgument_of_logScale
    {scale f : ℝ → ℝ} {coeff : ℕ → ℝ → ℝ}
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

end Fabius.SaddleExpansion
