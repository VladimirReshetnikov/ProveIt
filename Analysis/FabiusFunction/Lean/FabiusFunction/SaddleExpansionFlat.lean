import FabiusFunction.SaddleExpansionAlgebra

/-!
# Flat remainders in full asymptotic expansions

This module records the generic bridge from estimates at every algebraic
order to the parameter-dependent Poincare-expansion API.  It also
characterizes when two functions have the same full expansion: precisely
when their difference is negligible at every algebraic order.
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

/-- A full expansion with identically zero coefficients is exactly a
remainder negligible at every algebraic order. This includes order zero,
where the assertion is boundedness relative to the constant scale `1`. -/
theorem hasAsymptoticExpansion_zero_coeff_iff_isBigO_all
    {l : Filter α} {scale : α → 𝕜} {f : α → ℰ} :
    HasAsymptoticExpansion l scale f (fun _k _x => (0 : ℰ)) ↔
      ∀ N, f =O[l] (fun x => scale x ^ N) := by
  constructor
  · intro h N
    simpa [partialSum] using h.remainder_isBigO N
  · exact hasAsymptoticExpansion_zero_coeff_of_isBigO_all

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

/-- A flat remainder may equally be added on the left. -/
theorem HasAsymptoticExpansion.flat_add
    {l : Filter α} {scale : α → 𝕜} {f r : α → ℰ}
    {coeff : ℕ → α → ℰ}
    (hf : HasAsymptoticExpansion l scale f coeff)
    (hr : ∀ N, r =O[l] (fun x => scale x ^ N)) :
    HasAsymptoticExpansion l scale (fun x => r x + f x) coeff := by
  have hz := hasAsymptoticExpansion_zero_coeff_of_isBigO_all hr
  simpa using hz.add hf

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

/-- Two full expansions with the same coefficients differ by a remainder
which is negligible at every algebraic order.  This is the uniqueness
statement naturally available without any nondegeneracy assumption on the
asymptotic scale. -/
theorem HasAsymptoticExpansion.sub_same_coeff_isBigO_all
    {l : Filter α} {scale : α → 𝕜} {f g : α → ℰ}
    {coeff : ℕ → α → ℰ}
    (hf : HasAsymptoticExpansion l scale f coeff)
    (hg : HasAsymptoticExpansion l scale g coeff) :
    ∀ N, (fun x ↦ f x - g x) =O[l] (fun x ↦ scale x ^ N) := by
  intro N
  have h := (hf.remainder_isBigO N).sub (hg.remainder_isBigO N)
  apply h.congr'
  · filter_upwards with x
    change (f x - partialSum scale coeff N x) -
        (g x - partialSum scale coeff N x) = f x - g x
    abel
  · exact Filter.EventuallyEq.rfl

/-- Once one full expansion is known, another function has exactly the same
coefficients if and only if their difference is negligible at every
algebraic order. -/
theorem hasAsymptoticExpansion_iff_sub_isBigO_all
    {l : Filter α} {scale : α → 𝕜} {f g : α → ℰ}
    {coeff : ℕ → α → ℰ}
    (hf : HasAsymptoticExpansion l scale f coeff) :
    HasAsymptoticExpansion l scale g coeff ↔
      ∀ N, (fun x ↦ g x - f x) =O[l] (fun x ↦ scale x ^ N) := by
  constructor
  · intro hg
    exact hg.sub_same_coeff_isBigO_all hf
  · intro hflat
    apply (hf.add_flat hflat).congr Filter.EventuallyEq.rfl
    filter_upwards with x
    abel

/-- Adding a flat remainder preserves a full expansion in both directions. -/
theorem hasAsymptoticExpansion_add_flat_iff
    {l : Filter α} {scale : α → 𝕜} {f r : α → ℰ}
    {coeff : ℕ → α → ℰ}
    (hr : ∀ N, r =O[l] (fun x => scale x ^ N)) :
    HasAsymptoticExpansion l scale (fun x => f x + r x) coeff ↔
      HasAsymptoticExpansion l scale f coeff := by
  constructor
  · intro h
    simpa using h.sub_flat hr
  · intro h
    exact h.add_flat hr

/-- Subtracting a flat remainder preserves a full expansion in both directions. -/
theorem hasAsymptoticExpansion_sub_flat_iff
    {l : Filter α} {scale : α → 𝕜} {f r : α → ℰ}
    {coeff : ℕ → α → ℰ}
    (hr : ∀ N, r =O[l] (fun x => scale x ^ N)) :
    HasAsymptoticExpansion l scale (fun x => f x - r x) coeff ↔
      HasAsymptoticExpansion l scale f coeff := by
  constructor
  · intro h
    simpa using h.add_flat hr
  · intro h
    exact h.sub_flat hr

end Fabius.SaddleExpansion
