import FabiusFunction.ElementaryFunction
import FabiusFunction.NowhereAnalytic

/-!
# The Fabius function is not an elementary function

The Fabius function is real analytic at no point of `[0,1]`
(`Fabius.canonical_fabius_not_analyticAt`), whereas the analytic locus of an
elementary function is dense (`Fabius.IsElementary.dense_analyticLocus`) and
open (`Fabius.isOpen_analyticLocus`).  A dense set meets the interior of every
set whose interior is nonempty, so no elementary function can agree with the
Fabius function on any such subset of `[0,1]` — in particular not on `(0,1)`.
Restricting to `(0,1)` first, the Fabius function is therefore not elementary
as a function on `ℝ` either.

This is the sharpest form the argument supports, and it is the form one wants:
"the Fabius function is not elementary" would be a weaker statement, since it
would leave open the possibility that some elementary function agrees with it
on a substantial subset of the unit interval and differs elsewhere.

The corresponding statements for Rvachev's `up` function and for the signed
global extension are recorded as well.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-! ## Non-elementarity on any subset with nonempty interior -/

/-- No elementary function agrees with a bounded Fabius function on a subset
of `[0,1]` with nonempty interior. -/
theorem not_isElementary_eqOn_of_interior_nonempty
    (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementary g) {U : Set ℝ}
    (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1)
    (heq : EqOn g (fabiusReal F) U) : False :=
  (hg.not_eqOn_of_interior_nonempty hUne fun _x hx =>
    fabius_not_analyticAt F hF (hsub (interior_subset hx))) heq

/-- No elementary function agrees with a bounded Fabius function on a nonempty
open subset of `[0,1]`. -/
theorem not_isElementary_eqOn (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementary g) {U : Set ℝ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hsub : U ⊆ Icc (0 : ℝ) 1) (heq : EqOn g (fabiusReal F) U) : False := by
  apply not_isElementary_eqOn_of_interior_nonempty F hF hg ?_ hsub heq
  simpa only [hU.interior_eq] using hUne

/-- The bounded Fabius function is not elementary on `(0,1)`: no elementary
function agrees with it there. -/
theorem not_isElementary_eqOn_Ioo (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementary g) (heq : EqOn g (fabiusReal F) (Ioo (0 : ℝ) 1)) :
    False :=
  not_isElementary_eqOn F hF hg isOpen_Ioo ⟨1 / 2, by norm_num⟩ Ioo_subset_Icc_self heq

/-- A bounded Fabius function is not itself an elementary function. -/
theorem fabius_not_isElementary (F : BoundedFabius) (hF : IsFabius F) :
    ¬ IsElementary (fabiusReal F) := fun hg =>
  not_isElementary_eqOn_Ioo F hF hg fun _ _ => rfl

/-! ## The canonical Fabius function -/

/-- **The Fabius function is not elementary on `(0,1)`.**

There is no elementary function `g : ℝ → ℝ` with `g x = F x` for every
`x ∈ (0,1)`, where `F` is the Fabius function. -/
theorem canonical_fabius_not_isElementary_on_Ioo :
    ¬ ∃ g : ℝ → ℝ, IsElementary g ∧ EqOn g (fabiusReal fabius) (Ioo (0 : ℝ) 1) := by
  rintro ⟨g, hg, heq⟩
  exact not_isElementary_eqOn_Ioo fabius fabius_spec hg heq

/-- **The Fabius function is not an elementary function.** -/
theorem canonical_fabius_not_isElementary : ¬ IsElementary (fabiusReal fabius) :=
  fabius_not_isElementary fabius fabius_spec

/-- No elementary function agrees with the Fabius function on a subset of the
unit interval with nonempty interior. -/
theorem canonical_fabius_not_isElementary_eqOn_of_interior_nonempty
    {g : ℝ → ℝ} (hg : IsElementary g) {U : Set ℝ}
    (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1)
    (heq : EqOn g (fabiusReal fabius) U) : False :=
  not_isElementary_eqOn_of_interior_nonempty fabius fabius_spec hg hUne hsub heq

/-- No elementary function agrees with the Fabius function on any nonempty open
subset of the unit interval. -/
theorem canonical_fabius_not_isElementary_eqOn {g : ℝ → ℝ} (hg : IsElementary g)
    {U : Set ℝ} (hU : IsOpen U) (hUne : U.Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1)
    (heq : EqOn g (fabiusReal fabius) U) : False :=
  not_isElementary_eqOn fabius fabius_spec hg hU hUne hsub heq

/-! ## Rvachev's `up` function and the signed global extension -/

/-- No elementary function agrees with Rvachev's `up` function on a subset
of `[-1,1]` with nonempty interior. -/
theorem rvachev_not_isElementary_eqOn_of_interior_nonempty
    (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementary g) {U : Set ℝ}
    (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (-1 : ℝ) 1)
    (heq : EqOn g (rvachevUp F) U) : False :=
  (hg.not_eqOn_of_interior_nonempty hUne fun x hx =>
    rvachev_not_analyticAt F hF x (hsub (interior_subset hx))) heq

/-- No elementary function agrees with Rvachev's `up` function on a nonempty
open subset of `[-1,1]`. -/
theorem rvachev_not_isElementary_eqOn (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementary g) {U : Set ℝ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hsub : U ⊆ Icc (-1 : ℝ) 1) (heq : EqOn g (rvachevUp F) U) : False := by
  apply rvachev_not_isElementary_eqOn_of_interior_nonempty F hF hg ?_ hsub heq
  simpa only [hU.interior_eq] using hUne

/-- Rvachev's `up` function is not an elementary function. -/
theorem rvachev_not_isElementary (F : BoundedFabius) (hF : IsFabius F) :
    ¬ IsElementary (rvachevUp F) := fun hg =>
  rvachev_not_isElementary_eqOn F hF hg isOpen_Ioo ⟨0, by norm_num⟩
    (Ioo_subset_Icc_self (a := (-1 : ℝ)) (b := 1)) fun _ _ => rfl

/-- The signed global extension cannot agree with an elementary function on
any subset of `[0,2)` with nonempty interior. -/
theorem extendedFabius_not_isElementary_eqOn_of_interior_nonempty
    (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementary g) {U : Set ℝ}
    (hUne : (interior U).Nonempty) (hsub : U ⊆ Ico (0 : ℝ) 2)
    (heq : EqOn g (extendedFabius F) U) : False :=
  (hg.not_eqOn_of_interior_nonempty hUne fun _x hx =>
    extendedFabius_not_analyticAt F hF
      (hsub (interior_subset hx))) heq

/-- The signed global extension of the Fabius function is not elementary on any
nonempty open subset of `[0,2)`. -/
theorem extendedFabius_not_isElementary_eqOn (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementary g) {U : Set ℝ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hsub : U ⊆ Ico (0 : ℝ) 2) (heq : EqOn g (extendedFabius F) U) : False := by
  apply extendedFabius_not_isElementary_eqOn_of_interior_nonempty F hF hg
    ?_ hsub heq
  simpa only [hU.interior_eq] using hUne

/-- The signed global extension of the Fabius function is not elementary. -/
theorem extendedFabius_not_isElementary (F : BoundedFabius) (hF : IsFabius F) :
    ¬ IsElementary (extendedFabius F) := fun hg =>
  extendedFabius_not_isElementary_eqOn F hF hg isOpen_Ioo ⟨1, by norm_num⟩
    (Ioo_subset_Ico_self (a := (0 : ℝ)) (b := 2)) fun _ _ => rfl

end Fabius
