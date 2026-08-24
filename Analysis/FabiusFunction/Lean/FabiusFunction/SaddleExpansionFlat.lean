import FabiusFunction.SaddleExpansionAlgebra

/-!
# Flat remainders in full asymptotic expansions

This module records the generic bridge from estimates at every algebraic
order to the parameter-dependent Poincare-expansion API.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius.SaddleExpansion

variable {α 𝕜 ℰ : Type*} [NormedField 𝕜]
  [NormedAddCommGroup ℰ] [NormedSpace 𝕜 ℰ]

/-- A function which is `O(scale^N)` for every `N` has the full asymptotic
expansion whose coefficient families all vanish. -/
theorem hasAsymptoticExpansion_zero_coeff_of_isBigO_all
    {l : Filter α} {scale : α → 𝕜} {f : α → ℰ}
    (hflat : ∀ N, f =O[l] (fun x => scale x ^ N)) :
    HasAsymptoticExpansion l scale f (fun _k _x => (0 : ℰ)) := by
  constructor
  · intro k
    exact isBigO_zero (fun _x : α => (1 : 𝕜)) l
  · intro N
    simpa [partialSum] using hflat N

/-- Adding a remainder which is negligible to every order leaves every
coefficient of a full asymptotic expansion unchanged. -/
theorem HasAsymptoticExpansion.add_flat
    {l : Filter α} {scale : α → 𝕜} {f r : α → ℰ}
    {coeff : ℕ → α → ℰ}
    (hf : HasAsymptoticExpansion l scale f coeff)
    (hr : ∀ N, r =O[l] (fun x => scale x ^ N)) :
    HasAsymptoticExpansion l scale (fun x => f x + r x) coeff := by
  have hz := hasAsymptoticExpansion_zero_coeff_of_isBigO_all hr
  simpa using hf.add hz

/-- Subtracting a remainder which is negligible to every order leaves every
coefficient of a full asymptotic expansion unchanged. -/
theorem HasAsymptoticExpansion.sub_flat
    {l : Filter α} {scale : α → 𝕜} {f r : α → ℰ}
    {coeff : ℕ → α → ℰ}
    (hf : HasAsymptoticExpansion l scale f coeff)
    (hr : ∀ N, r =O[l] (fun x => scale x ^ N)) :
    HasAsymptoticExpansion l scale (fun x => f x - r x) coeff := by
  have hz := hasAsymptoticExpansion_zero_coeff_of_isBigO_all hr
  simpa using hf.sub hz

end Fabius.SaddleExpansion
