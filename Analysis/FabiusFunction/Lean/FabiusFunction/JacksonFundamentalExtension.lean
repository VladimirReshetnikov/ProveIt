import FabiusFunction.JacksonIntegral

/-!
# The fundamental theorem of `q`-calculus: the continuous extension at `0`

`qDeriv_jacksonIntegral` gives `D_q (∫₀ᵗ f) (x) = f(x)` for `x ≠ 0`.  If moreover `f` is
continuous at `0`, then `D_q (∫₀ᵗ f)` tends to `f(0)` as `x → 0`, `x ≠ 0`
(`tendsto_qDeriv_jacksonIntegral_nhdsWithin`): the `q`-derivative of the Jackson integral has
the continuous extension `f(0)` at the origin, the last clause of thm:q-fundamental.
-/

set_option autoImplicit false

open Filter Topology

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
/-- The continuous extension of `D_q (∫₀ᵗ f)` at `0` is `f(0)`. -/
theorem tendsto_qDeriv_jacksonIntegral_nhdsWithin {q : 𝕜} (hq1 : q ≠ 1) (f : 𝕜 → 𝕜)
    (hs : ∀ x, Summable fun n : ℕ => q ^ n * f (x * q ^ n)) (hf : ContinuousAt f 0) :
    Tendsto (fun x => qDeriv q (fun y => jacksonIntegral q f y) x) (𝓝[≠] 0) (𝓝 (f 0)) := by
  refine (hf.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (qDeriv_jacksonIntegral hq1 f hx (hs x)).symm

end Fabius
