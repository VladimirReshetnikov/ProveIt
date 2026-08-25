import FabiusFunction.FabiusInverse
import FabiusFunction.InverseBranch
import FabiusFunction.NotElementary

/-!
# The inverse Fabius function is not elementary either, and neither is reachable by inverting

The Fabius function `F` is a homeomorphism of `[0,1]` onto itself, so it has a
continuous inverse `Fabius.fabiusInv`.  This file proves that the inverse is
real analytic at no point of `[0,1]` — hence not elementary on `(0,1)` — and
then strengthens both non-elementarity theorems to the class
`Fabius.IsElementaryOrInverse`, which is closed under continuous inverse
branches satisfying an analytic completion hypothesis on the interior of the
complementary region, at any depth.  Branch-domain boundaries are deliberately
excluded from that side condition, so standard boundary singularities such as
that of principal real Lambert `W` are compatible with the constructor.

## Why the inverse is no better behaved

One might hope that inverting improves matters: `F` is flat to infinite order
at the endpoints, so `F⁻¹` is steep there, and steepness is not obviously an
obstruction.  It is not an improvement, and the reason is the inverse function
theorem run backwards.

If `F⁻¹` were analytic at some `y₀` in the interior, then `F` — being its
inverse near that point — would be analytic at `F⁻¹ y₀`, *provided* `F⁻¹` has
no critical point there.  The stronger interior calculus in
`FabiusFunction.FabiusInverse` gives the exact formula
`(F⁻¹)'(y) = 1 / F'(F⁻¹ y) > 0` without any analyticity assumption.  So
analyticity of `F⁻¹` anywhere in `(0,1)` would hand back
analyticity of `F` somewhere in `(0,1)`, which
`Fabius.fabius_not_analyticAt` forbids.

`F'` enters this file only there, through the imported
`Fabius.deriv_fabiusInv_pos` and its corollary
`Fabius.deriv_fabiusInv_ne_zero`.  Everywhere else `F` is used through its
continuity — `Fabius.fabius_differentiable` appears once more below, but only
to produce a `ContinuousAt` — and through its failure to be analytic.

The direction matters.  Differentiating `F⁻¹ ∘ F = id` to get
`(F⁻¹)' · F' = 1` would be circular, since it presupposes that `F⁻¹` is
differentiable; positivity of `F'` is what supplies that.

At the endpoints the argument is different and simpler.  `F⁻¹` is identically
`0` to the left of `0`; an analytic germ agreeing with `0` on a set with an
accumulation point vanishes identically, so `F⁻¹` would vanish just to the
right of `0` as well — contradicting strict monotonicity.  Symmetrically
at `1`.

## Why inverting cannot help at all

`Fabius.IsElementaryOrInverse` adds to the elementary functions the continuous
inverse branches — of members, of branches of members, and so on without
limit.  "Continuous" is not the only condition: a branch is admitted with an
open set `U` carrying the identity, and must be analytic on `interior Uᶜ`,
which is a constraint on how it is continued past `U`.  Without that clause
the density theorem would be false, since a branch is otherwise unconstrained
off `U`.  By `Fabius.IsElementaryOrInverse.dense_analyticLocus` every
member is still analytic on a dense set, so
`Fabius.not_eqOn_of_dense_analyticLocus` applies unchanged.  Neither `F` nor
`F⁻¹` is reachable.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Fabius

/-! ## The inverse is differentiable, with no critical point, in the interior -/

/-- **The inverse Fabius function has no critical point in `(0,1)`.**

Its derivative there is the positive reciprocal of `F'`, so the result is
unconditional and does not assume analyticity anywhere. -/
theorem deriv_fabiusInv_ne_zero (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : deriv (fabiusInv F hF) y ≠ 0 :=
  (deriv_fabiusInv_pos F hF hy).ne'

/-! ## The inverse is analytic at no point of the unit interval -/

/-- **The inverse Fabius function is real analytic at no point of `[0,1]`.**

In the interior this is the inverse function theorem run backwards: an
analytic germ of `F⁻¹` with nonvanishing derivative — and by
`Fabius.deriv_fabiusInv_ne_zero` there is no other kind — makes `F` analytic
at the corresponding point.  At the endpoints it is the identity theorem: the
inverse is constant on one side, so an analytic germ would make it constant on
both, contradicting strict monotonicity. -/
theorem fabiusInv_not_analyticAt (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : ¬ AnalyticAt ℝ (fabiusInv F hF) y := by
  intro hana
  rcases eq_or_lt_of_le hy.1 with h0 | h0
  · -- `y = 0`: the inverse vanishes to the left, hence — being analytic — on both sides.
    subst h0
    have hzero : ∀ᶠ t in 𝓝 (0 : ℝ), fabiusInv F hF t = 0 := by
      rcases hana.eventually_eq_zero_or_eventually_ne_zero with h | h
      · exact h
      · exfalso
        have hleft : ∀ᶠ t in 𝓝[<] (0 : ℝ), fabiusInv F hF t = 0 := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact fabiusInv_eq_zero_of_nonpos F hF (le_of_lt ht)
        have hle : 𝓝[<] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
          nhdsWithin_mono _ fun t ht => ne_of_lt ht
        obtain ⟨t, ht₁, ht₂⟩ := ((h.filter_mono hle).and hleft).exists
        exact ht₁ ht₂
    obtain ⟨t, ht0, htpos, htlt⟩ : ∃ t : ℝ, fabiusInv F hF t = 0 ∧ 0 < t ∧ t < 1 := by
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), fabiusInv F hF t = 0 ∧ 0 < t ∧ t < 1 := by
        filter_upwards [nhdsWithin_le_nhds hzero, self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with t h1 h2 h3
        exact ⟨h1, h2, h3⟩
      exact hev.exists
    have h0' : fabiusInv F hF 0 = 0 := fabiusInv_eq_zero_of_nonpos F hF le_rfl
    have hlt := strictMonoOn_fabiusInv F hF (left_mem_Icc.2 zero_le_one)
      ⟨le_of_lt htpos, le_of_lt htlt⟩ htpos
    rw [h0', ht0] at hlt
    exact lt_irrefl _ hlt
  · rcases eq_or_lt_of_le hy.2 with h1 | h1
    · -- `y = 1`: the same argument, reflected.
      subst h1
      have hsub : AnalyticAt ℝ (fun t : ℝ => fabiusInv F hF t - 1) 1 :=
        hana.fun_sub (analyticAt_const (v := (1 : ℝ)))
      have hzero : ∀ᶠ t in 𝓝 (1 : ℝ), fabiusInv F hF t - 1 = 0 := by
        rcases hsub.eventually_eq_zero_or_eventually_ne_zero with h | h
        · exact h
        · exfalso
          have hright : ∀ᶠ t in 𝓝[>] (1 : ℝ), fabiusInv F hF t - 1 = 0 := by
            filter_upwards [self_mem_nhdsWithin] with t ht
            rw [fabiusInv_eq_one_of_one_le F hF (le_of_lt ht), sub_self]
          have hle : 𝓝[>] (1 : ℝ) ≤ 𝓝[≠] (1 : ℝ) :=
            nhdsWithin_mono _ fun t ht => ne_of_gt ht
          obtain ⟨t, ht₁, ht₂⟩ := ((h.filter_mono hle).and hright).exists
          exact ht₁ ht₂
      obtain ⟨t, ht0, htpos, htlt⟩ :
          ∃ t : ℝ, fabiusInv F hF t - 1 = 0 ∧ 0 < t ∧ t < 1 := by
        have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), fabiusInv F hF t - 1 = 0 ∧ 0 < t ∧ t < 1 := by
          filter_upwards [nhdsWithin_le_nhds hzero,
            nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
            self_mem_nhdsWithin] with t h1 h2 h3
          exact ⟨h1, h2, h3⟩
        exact hev.exists
      have h1' : fabiusInv F hF 1 = 1 := fabiusInv_eq_one_of_one_le F hF le_rfl
      have hlt := strictMonoOn_fabiusInv F hF ⟨le_of_lt htpos, le_of_lt htlt⟩
        (right_mem_Icc.2 zero_le_one) htlt
      rw [h1', sub_eq_zero.1 ht0] at hlt
      exact lt_irrefl _ hlt
    · -- the interior: the inverse function theorem, run backwards
      have hyIoo : y ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
      have hx₀ : fabiusInv F hF y ∈ Ioo (0 : ℝ) 1 := fabiusInv_mem_Ioo F hF hyIoo
      have hFx₀ : fabiusReal F (fabiusInv F hF y) = y :=
        fabiusReal_fabiusInv F hF ⟨hy.1, hy.2⟩
      refine fabius_not_analyticAt F hF (Ioo_subset_Icc_self hx₀) ?_
      refine analyticAt_of_rightInverse (h := fabiusInv F hF) ?_ ?_ ?_ ?_
      · rw [hFx₀]; exact hana
      · rw [hFx₀]; exact deriv_fabiusInv_ne_zero F hF hyIoo
      · exact (fabius_differentiable F hF _).continuousAt
      · filter_upwards [isOpen_Ioo.mem_nhds hx₀] with x hx
        exact fabiusInv_fabiusReal F hF ⟨le_of_lt hx.1, le_of_lt hx.2⟩

/-- The analytic locus of the inverse is exactly the complement of `[0,1]`,
just as for the Fabius function itself: outside the unit interval the inverse
is locally constant. -/
theorem fabiusInv_analyticAt_iff (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) :
    AnalyticAt ℝ (fabiusInv F hF) y ↔ y ∉ Icc (0 : ℝ) 1 := by
  constructor
  · intro h hmem
    exact fabiusInv_not_analyticAt F hF hmem h
  · intro hmem
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    rcases hmem with h | h
    · refine (analyticAt_const (v := (0 : ℝ))).congr ?_
      filter_upwards [Iio_mem_nhds h] with t ht
      exact (fabiusInv_eq_zero_of_nonpos F hF ht.le).symm
    · refine (analyticAt_const (v := (1 : ℝ))).congr ?_
      filter_upwards [Ioi_mem_nhds h] with t ht
      exact (fabiusInv_eq_one_of_one_le F hF ht.le).symm

/-- Exact set-valued form of `fabiusInv_analyticAt_iff`: the analytic locus
of the totalized inverse consists precisely of its two open constant tails. -/
theorem analyticLocus_fabiusInv (F : BoundedFabius) (hF : IsFabius F) :
    analyticLocus (fabiusInv F hF) = (Icc (0 : ℝ) 1)ᶜ := by
  ext y
  simpa only [mem_analyticLocus, mem_compl_iff] using
    fabiusInv_analyticAt_iff F hF y

/-! ## Non-representability of the inverse -/

/-- No function whose analytic locus is dense relative to `interior U` agrees
with the inverse Fabius function on `U ⊆ [0,1]` when that interior is
nonempty.

This local hypothesis is strictly weaker than asking for a globally dense
analytic locus.  In particular it can be supplied directly by
`Fabius.analyticDenseOn_of_rightInverse` for a continuous inverse branch that
is only defined on the region under consideration. -/
theorem not_eqOn_fabiusInv_of_analyticDenseOn (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} {U : Set ℝ} (hg : AnalyticDenseOn g (interior U))
    (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1) :
    ¬ EqOn g (fabiusInv F hF) U := by
  intro heq
  exact hg.not_eqOn_of_forall_not_analyticAt isOpen_interior hUne
    (fun x hx => fabiusInv_not_analyticAt F hF (hsub (interior_subset hx)))
    (heq.mono interior_subset)

/-- No function analytic on a dense set — in particular no elementary
function, and no member of `Fabius.IsElementaryOrInverse` — agrees with the
inverse Fabius function on a subset of `[0,1]` with nonempty interior. -/
theorem not_eqOn_fabiusInv_of_dense_analyticLocus (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : Dense (analyticLocus g)) {U : Set ℝ}
    (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1) :
    ¬ EqOn g (fabiusInv F hF) U := by
  apply not_eqOn_fabiusInv_of_analyticDenseOn F hF ?_ hUne hsub
  intro V hV hVne _
  obtain ⟨x, hxV, hxg⟩ := (dense_iff_inter_open.mp hg) V hV hVne
  exact ⟨x, hxV, hxg⟩

/-- **The inverse Fabius function on `(0,1)` is not an elementary function.** -/
theorem canonical_fabiusInv_not_isElementary_on_Ioo :
    ¬ ∃ g : ℝ → ℝ, IsElementary g ∧
      EqOn g (fabiusInv fabius fabius_spec) (Ioo (0 : ℝ) 1) := by
  rintro ⟨g, hg, heq⟩
  refine not_eqOn_fabiusInv_of_dense_analyticLocus fabius fabius_spec
    hg.dense_analyticLocus ?_ Ioo_subset_Icc_self heq
  rw [isOpen_Ioo.interior_eq]
  exact ⟨1 / 2, by norm_num⟩

/-- The inverse Fabius function is not itself an elementary function. -/
theorem fabiusInv_not_isElementary (F : BoundedFabius) (hF : IsFabius F) :
    ¬ IsElementary (fabiusInv F hF) := fun hg =>
  not_eqOn_fabiusInv_of_dense_analyticLocus F hF hg.dense_analyticLocus
    (by rw [isOpen_Ioo.interior_eq]; exact ⟨1 / 2, by norm_num⟩)
    (Ioo_subset_Icc_self (a := (0 : ℝ)) (b := 1)) fun _ _ => rfl

/-! ## Neither function is reachable by inverting -/

/-- **Adjoining inverses does not reach the Fabius function.**

No member of `Fabius.IsElementaryOrInverse` — the elementary functions closed
under the inverse-branch constructor of `FabiusFunction.InverseBranch` at any
depth — agrees with the Fabius function on a subset of `[0,1]` with nonempty
interior. -/
theorem not_isElementaryOrInverse_eqOn_fabius (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementaryOrInverse g) {U : Set ℝ}
    (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1) :
    ¬ EqOn g (fabiusReal F) U :=
  not_eqOn_of_dense_analyticLocus hg.dense_analyticLocus hUne fun _ hx =>
    fabius_not_analyticAt F hF (hsub (interior_subset hx))

/-- **Adjoining inverses does not reach the inverse Fabius function either.** -/
theorem not_isElementaryOrInverse_eqOn_fabiusInv (F : BoundedFabius) (hF : IsFabius F)
    {g : ℝ → ℝ} (hg : IsElementaryOrInverse g) {U : Set ℝ}
    (hUne : (interior U).Nonempty) (hsub : U ⊆ Icc (0 : ℝ) 1) :
    ¬ EqOn g (fabiusInv F hF) U :=
  not_eqOn_fabiusInv_of_dense_analyticLocus F hF hg.dense_analyticLocus hUne hsub

/-- The Fabius function itself does not belong to the class generated by
elementary functions and continuous inverse branches. -/
theorem fabius_not_isElementaryOrInverse
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ IsElementaryOrInverse (fabiusReal F) := fun hg =>
  not_isElementaryOrInverse_eqOn_fabius F hF hg
    (U := Ioo (0 : ℝ) 1)
    (by rw [isOpen_Ioo.interior_eq]; exact ⟨1 / 2, by norm_num⟩)
    Ioo_subset_Icc_self (fun _ _ => rfl)

/-- The totalized inverse Fabius function itself does not belong to the class
generated by elementary functions and continuous inverse branches. -/
theorem fabiusInv_not_isElementaryOrInverse
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ IsElementaryOrInverse (fabiusInv F hF) := fun hg =>
  not_isElementaryOrInverse_eqOn_fabiusInv F hF hg
    (U := Ioo (0 : ℝ) 1)
    (by rw [isOpen_Ioo.interior_eq]; exact ⟨1 / 2, by norm_num⟩)
    Ioo_subset_Icc_self (fun _ _ => rfl)

/-- **The Fabius function on `(0,1)` is not representable by elementary
functions and their inverses.** -/
theorem canonical_fabius_not_isElementaryOrInverse_on_Ioo :
    ¬ ∃ g : ℝ → ℝ, IsElementaryOrInverse g ∧
      EqOn g (fabiusReal fabius) (Ioo (0 : ℝ) 1) := by
  rintro ⟨g, hg, heq⟩
  refine not_isElementaryOrInverse_eqOn_fabius fabius fabius_spec hg ?_
    Ioo_subset_Icc_self heq
  rw [isOpen_Ioo.interior_eq]
  exact ⟨1 / 2, by norm_num⟩

/-- **The inverse Fabius function on `(0,1)` is not representable by
elementary functions and their inverses.** -/
theorem canonical_fabiusInv_not_isElementaryOrInverse_on_Ioo :
    ¬ ∃ g : ℝ → ℝ, IsElementaryOrInverse g ∧
      EqOn g (fabiusInv fabius fabius_spec) (Ioo (0 : ℝ) 1) := by
  rintro ⟨g, hg, heq⟩
  refine not_isElementaryOrInverse_eqOn_fabiusInv fabius fabius_spec hg ?_
    Ioo_subset_Icc_self heq
  rw [isOpen_Ioo.interior_eq]
  exact ⟨1 / 2, by norm_num⟩

end Fabius
