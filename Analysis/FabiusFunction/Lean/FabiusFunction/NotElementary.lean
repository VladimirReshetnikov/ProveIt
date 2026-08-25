import FabiusFunction.AlgebraicBranch
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

/-! ## Algebraic functions over the elementary functions

The class `Fabius.IsElementary` is closed under `n`-th roots but has no
constructor for a general algebraic function.  That gap is closed here, not by
enlarging the class — which would cost `Fabius.IsElementary.comp`, since
composing an algebraic branch with an elementary function needs the *inner*
function to be continuous, and elementary functions need not be — but by
proving the non-elementarity statement directly for continuous branches. -/

/-- A continuous branch of a polynomial equation with elementary coefficients
is analytic on a dense subset of every open region on which its leading
coefficient does not vanish.

More precisely, every nonempty open subset of `U` contains a point where the
branch is analytic.  The proof restricts to the common analytic locus of the
finitely many coefficients, applies `Fabius.analyticDenseOn_of_algebraic`
there, and then removes that dense-open restriction with
`Fabius.analyticDenseOn_of_inter_open_dense`. -/
theorem analyticDenseOn_of_isElementary_coeffs
    {n : ℕ} {a : ℕ → ℝ → ℝ} {y : ℝ → ℝ} {U : Set ℝ}
    (ha : ∀ i ≤ n, IsElementary (a i)) (hU : IsOpen U)
    (hlead : ∀ x ∈ U, a n x ≠ 0) (hy : ContinuousOn y U)
    (hpoly : ∀ x ∈ U, branchPoly a n (x, y x) = 0) :
    AnalyticDenseOn y U := by
  have hWopen : IsOpen (⋂ i ∈ (Set.Iic n : Set ℕ), analyticLocus (a i)) :=
    (Set.finite_Iic n).isOpen_biInter fun i _ => isOpen_analyticLocus (a i)
  have hWdense : Dense (⋂ i ∈ (Set.Iic n : Set ℕ), analyticLocus (a i)) :=
    dense_biInter_of_isOpen (fun i _ => isOpen_analyticLocus (a i))
      (Set.finite_Iic n).countable fun i hi => (ha i hi).dense_analyticLocus
  refine analyticDenseOn_of_inter_open_dense hWopen hWdense ?_
  exact analyticDenseOn_of_algebraic n a y _ (hU.inter hWopen)
    (fun i hi x hx =>
      Set.mem_iInter₂.1 hx.2 i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
    (fun x hx => hlead x hx.1) (hy.mono Set.inter_subset_left)
    (fun x hx => hpoly x hx.1)

/-- A continuous branch of a polynomial equation whose coefficients are
elementary and whose leading coefficient vanishes nowhere has dense analytic
locus.

This is the global specialization of
`Fabius.analyticDenseOn_of_isElementary_coeffs`. -/
theorem dense_analyticLocus_of_isElementary_coeffs
    {n : ℕ} {a : ℕ → ℝ → ℝ} {y : ℝ → ℝ}
    (ha : ∀ i ≤ n, IsElementary (a i)) (hlead : ∀ x, a n x ≠ 0)
    (hy : Continuous y) (hpoly : ∀ x, branchPoly a n (x, y x) = 0) :
    Dense (analyticLocus y) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x, hxU, hxy⟩ :=
    analyticDenseOn_of_isElementary_coeffs (U := Set.univ) ha isOpen_univ
      (fun x _ => hlead x) hy.continuousOn (fun x _ => hpoly x)
      U hU hUne (fun _ _ => Set.mem_univ _)
  exact ⟨x, hxU, hxy⟩

/-- The localized form, and the one the applications use: a branch need only
be continuous **on the open set `U`**, solve the equation **on `U`**, and have
nonvanishing leading coefficient **on `U`**.  Then it is analytic at some
point of `U`.

Localizing matters, and is not a cosmetic generalization.  For example, a
global solution of `y x ^ 5 - y x = x` would be a continuous right inverse of
`w ↦ w ^ 5 - w`, but that polynomial has no global continuous right inverse.
Its positive real branch is nevertheless a perfectly good algebraic function
on `(0,1)` (with non-solvable generic Galois group), and only the localized
statement reaches it. -/
theorem exists_analyticAt_of_isElementary_coeffs
    {n : ℕ} {a : ℕ → ℝ → ℝ} {y : ℝ → ℝ} {U : Set ℝ}
    (ha : ∀ i ≤ n, IsElementary (a i)) (hU : IsOpen U) (hUne : U.Nonempty)
    (hlead : ∀ x ∈ U, a n x ≠ 0) (hy : ContinuousOn y U)
    (hpoly : ∀ x ∈ U, branchPoly a n (x, y x) = 0) :
    ∃ x ∈ U, AnalyticAt ℝ y x := by
  exact analyticDenseOn_of_isElementary_coeffs ha hU hlead hy hpoly
    U hU hUne subset_rfl

/-- **The Fabius function is not an algebraic function over the elementary
functions.**

Let `U` be a nonempty open subset of `[0,1]`.  If `a 0, …, a n` are
elementary, the leading coefficient `a n` vanishes nowhere on `U`, and `y` is
continuous on `U` with `∑ i ≤ n, a i x * y x ^ i = 0` for every `x ∈ U`, then
`y` does not agree with a bounded Fabius function on `U`.

Every hypothesis on the branch is confined to `U`, so this reaches the
algebraic functions that exist only locally — including branches whose Galois
group is not solvable, which are therefore not expressible by radicals at all.
It thus goes past the description of the elementary functions in terms of
roots, towards Liouville's differential-field notion. -/
theorem not_algebraicBranch_eqOn (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} {a : ℕ → ℝ → ℝ} {y : ℝ → ℝ}
    (ha : ∀ i ≤ n, IsElementary (a i))
    {U : Set ℝ} (hU : IsOpen U) (hUne : U.Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1)
    (hlead : ∀ x ∈ U, a n x ≠ 0) (hy : ContinuousOn y U)
    (hpoly : ∀ x ∈ U, branchPoly a n (x, y x) = 0)
    (heq : EqOn y (fabiusReal F) U) : False := by
  exact
    (analyticDenseOn_of_isElementary_coeffs ha hU hlead hy hpoly).not_eqOn_of_forall_not_analyticAt
      hU hUne (fun x hx => fabius_not_analyticAt F hF (hsub hx)) heq

/-- The interior form: such a branch cannot agree with a bounded Fabius
function on any subset of `[0,1]` with nonempty interior. -/
theorem not_algebraicBranch_eqOn_of_interior_nonempty (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} {a : ℕ → ℝ → ℝ} {y : ℝ → ℝ}
    (ha : ∀ i ≤ n, IsElementary (a i))
    {U : Set ℝ} (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1)
    (hlead : ∀ x ∈ interior U, a n x ≠ 0) (hy : ContinuousOn y (interior U))
    (hpoly : ∀ x ∈ interior U, branchPoly a n (x, y x) = 0)
    (heq : EqOn y (fabiusReal F) U) : False :=
  not_algebraicBranch_eqOn F hF ha isOpen_interior hUne
    (interior_subset.trans hsub) hlead hy hpoly (heq.mono interior_subset)

/-- **The Fabius function on `(0,1)` is not an algebraic function over the
elementary functions.**

Every hypothesis is confined to `(0,1)`, so this applies to branches that are
defined and continuous only there. -/
theorem canonical_fabius_not_algebraicBranch_on_Ioo
    {n : ℕ} {a : ℕ → ℝ → ℝ} {y : ℝ → ℝ}
    (ha : ∀ i ≤ n, IsElementary (a i))
    (hlead : ∀ x ∈ Ioo (0 : ℝ) 1, a n x ≠ 0)
    (hy : ContinuousOn y (Ioo (0 : ℝ) 1))
    (hpoly : ∀ x ∈ Ioo (0 : ℝ) 1, branchPoly a n (x, y x) = 0) :
    ¬ EqOn y (fabiusReal fabius) (Ioo (0 : ℝ) 1) := fun heq =>
  not_algebraicBranch_eqOn fabius fabius_spec ha isOpen_Ioo
    ⟨1 / 2, by norm_num⟩ Ioo_subset_Icc_self hlead hy hpoly heq

/-- The interior form for the canonical Fabius function. -/
theorem canonical_fabius_not_algebraicBranch_of_interior_nonempty
    {n : ℕ} {a : ℕ → ℝ → ℝ} {y : ℝ → ℝ}
    (ha : ∀ i ≤ n, IsElementary (a i))
    {U : Set ℝ} (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1)
    (hlead : ∀ x ∈ interior U, a n x ≠ 0) (hy : ContinuousOn y (interior U))
    (hpoly : ∀ x ∈ interior U, branchPoly a n (x, y x) = 0) :
    ¬ EqOn y (fabiusReal fabius) U := fun heq =>
  not_algebraicBranch_eqOn_of_interior_nonempty fabius fabius_spec ha hUne hsub
    hlead hy hpoly heq

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
