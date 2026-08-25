import FabiusFunction.AlgebraicBranch
import FabiusFunction.ElementaryFunction

/-!
# Inverse branches, and why inverting cannot escape analyticity

This file is independent of the Fabius function.  It shows that the class of
functions that are real analytic on a dense set — the invariant that
`FabiusFunction.ElementaryFunction` establishes for the elementary functions —
is also closed under passage to a **continuous inverse branch**.

That closure is what makes the non-elementarity results robust.  Adjoining
`Real.log` to a class already containing `Real.exp` adds nothing that was not
already tame, and the same is true of the Lambert `W` function, of the
inverses of those, and of anything assembled from them by the elementary
operations.  A function that is analytic at *no* point of an interval is
therefore outside the entire tower, not merely outside its ground floor.

## The two theorems

`Fabius.analyticAt_of_rightInverse` is the analytic inverse function theorem,
and it is obtained here for free.  The observation is that a left inverse is
an implicit branch of the simplest possible equation: `h (g x) = x` says
exactly that `g` is a continuous branch of

`P (x, z) = h z - x = 0`,

whose partial derivative in `z` is `h'`.  So the analytic implicit function
theorem `Fabius.analyticAt_of_continuous_branch`, proved in
`FabiusFunction.AlgebraicBranch` for the algebraic application, delivers the
inverse function theorem with no further analysis.

`Fabius.exists_analyticAt_of_rightInverse` is the global statement: if `f` is
analytic on a dense set and `g` is a continuous right inverse of `f` on a
nonempty open `U`, then `g` is analytic somewhere in `U`.  Two facts drive it.
A continuous right inverse is injective, and a continuous injection carries a
closed interval to a set containing an interval — this is the intermediate
value theorem — so the image `g '' U` is *fat*, and a dense set must meet it.
And on that image `f` is injective, so `f` cannot be locally constant there;
its derivative therefore fails to vanish somewhere, which is what the inverse
function theorem needs.

The critical points are exactly where the argument must be allowed to move:
`x ↦ x ^ 3` is analytic and invertible, but its inverse is not analytic at
`0`.  That inverse is the classical cube root `t ↦ t / |t| * |t| ^ (3 : ℝ)⁻¹`,
not `t ↦ t ^ (1/3 : ℝ)`: `Mathlib`'s `Real.rpow` gives `(-8 : ℝ) ^ (1/3 : ℝ) = 1`,
so the `rpow` version is a right inverse of the cube only on `[0, ∞)`.  The
signed form is a right inverse on all of `ℝ`, by `Fabius.signedRoot_pow`.  This
is why the conclusion is "analytic somewhere in `U`" rather than "analytic on
`U`", and it is the same phenomenon that makes density, not analyticity
everywhere, the right invariant throughout.

## The extended class

`Fabius.IsElementaryOrInverse` is the elementary functions closed under
inverse branches at any depth.  Its inverse constructor carries the open set
`U` on which the branch identity holds, and asks that the function be analytic
on the interior of the complement of `U`.

Two things are deliberate there, and the Lambert `W` function shows why both
are needed.  `W` satisfies `W y * exp (W y) = y` only on `[-1/e, ∞)`, so a
constructor demanding a *global* identity would not reach it.  And the branch
point `-1/e` sits on the boundary of the natural `U = Ioi (-1/e)`, where `W`
is emphatically not analytic, so a constructor demanding analyticity at every
point *outside* `U` would not reach it either.  Taking the interior of the
complement drops exactly that boundary, which is nowhere dense and therefore
irrelevant to density of the analytic locus.

The analyticity clause is a constraint on how the branch is continued past
`U`, not a consequence of `Mathlib`'s junk-value conventions; extension by a
constant always satisfies it.  At `U = ∅` it degenerates into "the function is
entire", so the constructor also adjoins every everywhere-analytic function —
which changes nothing, those being densely analytic already.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Fabius

/-! ## The analytic inverse function theorem -/

/-- **Analytic inverse function theorem.**  If `h` is analytic at `g x₀` with
nonzero derivative there, `g` is continuous at `x₀`, and `h ∘ g` is the
identity near `x₀`, then `g` is analytic at `x₀`.

Both this and `Fabius.exists_analyticAt_of_rightInverse` are named for the
same relation, read from the same side: the conclusion is about `g`, and the
hypothesis makes `g` a *right* inverse of the other function, `h ∘ g = id`.
Equivalently, `h` is a left inverse of `g`; that is the reading under which
the proof is a single application of the implicit function theorem, since
`h ∘ g = id` says that `g` is a continuous branch of `h z - x = 0`, an
equation whose partial derivative in `z` is `h'`. -/
theorem analyticAt_of_rightInverse {h g : ℝ → ℝ} {x₀ : ℝ}
    (hh : AnalyticAt ℝ h (g x₀)) (hderiv : deriv h (g x₀) ≠ 0)
    (hg : ContinuousAt g x₀) (hinv : ∀ᶠ x in 𝓝 x₀, h (g x) = x) :
    AnalyticAt ℝ g x₀ := by
  have hd : HasDerivAt h (deriv h (g x₀)) (g x₀) := hh.differentiableAt.hasDerivAt
  have hsnd : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2) (x₀, g x₀) := analyticAt_snd
  have hfst : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) (x₀, g x₀) := analyticAt_fst
  have hcomp : AnalyticAt ℝ (fun p : ℝ × ℝ => h p.2) (x₀, g x₀) := by
    simpa [Function.comp_def] using
      AnalyticAt.comp (f := fun p : ℝ × ℝ => p.2) (x := (x₀, g x₀)) hh hsnd
  refine analyticAt_of_continuous_branch (f := fun p : ℝ × ℝ => h p.2 - p.1)
    (hcomp.fun_sub hfst) (hd.sub_const x₀) hderiv hg ?_
  have hx₀ : h (g x₀) = x₀ := hinv.self_of_nhds
  filter_upwards [hinv] with x hx
  simp [hx, hx₀]

/-! ## Inverting cannot escape analyticity -/

/-- **A continuous inverse branch of a densely analytic function is analytic
somewhere.**

If `f` is analytic at the points of a dense set and `g` is continuous on a
nonempty open `U` with `f (g y) = y` there, then `g` is analytic at some point
of `U`.

"Somewhere" cannot be improved to "everywhere": the classical cube root
`t ↦ t / |t| * |t| ^ (3 : ℝ)⁻¹` is a continuous right inverse of the entire
function `x ↦ x ^ 3` on all of `ℝ` — that is `Fabius.signedRoot_pow` — and it
is not analytic at the origin. -/
theorem exists_analyticAt_of_rightInverse {f g : ℝ → ℝ} {U : Set ℝ}
    (hf : Dense (analyticLocus f)) (hU : IsOpen U) (hUne : U.Nonempty)
    (hg : ContinuousOn g U) (hinv : ∀ y ∈ U, f (g y) = y) :
    ∃ y ∈ U, AnalyticAt ℝ g y := by
  -- A closed interval inside `U`.
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨a, b, hy₀ab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hU.mem_nhds hy₀)
  obtain ⟨c, d, hcd, hcdsub⟩ : ∃ c d : ℝ, c < d ∧ Icc c d ⊆ U := by
    refine ⟨(a + y₀) / 2, (y₀ + b) / 2, by have := hy₀ab.1; have := hy₀ab.2; linarith, ?_⟩
    intro x hx
    exact hab ⟨by have := hy₀ab.1; have := hx.1; linarith,
      by have := hy₀ab.2; have := hx.2; linarith⟩
  have hgc : ContinuousOn g (Icc c d) := hg.mono hcdsub
  -- `g` is injective, because `f` is a left inverse of it.
  have hgne : g c ≠ g d := by
    intro hgcd
    refine absurd ?_ hcd.ne
    rw [← hinv c (hcdsub (left_mem_Icc.2 hcd.le)), ← hinv d (hcdsub (right_mem_Icc.2 hcd.le)),
      hgcd]
  -- Hence the image of `[c,d]` contains an interval: the intermediate value theorem.
  obtain ⟨p, q, hpq, himg⟩ : ∃ p q : ℝ, p < q ∧ Ioo p q ⊆ g '' Ioo c d := by
    rcases hgne.lt_or_gt with hlt | hlt
    · exact ⟨g c, g d, hlt, intermediate_value_Ioo hcd.le hgc⟩
    · exact ⟨g d, g c, hlt, intermediate_value_Ioo' hcd.le hgc⟩
  -- On that image `f` is injective, being inverse to `g`.
  have hfinj : ∀ x₁ ∈ g '' Ioo c d, ∀ x₂ ∈ g '' Ioo c d, f x₁ = f x₂ → x₁ = x₂ := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ heq
    rw [hinv u (hcdsub (Ioo_subset_Icc_self hu)),
      hinv v (hcdsub (Ioo_subset_Icc_self hv))] at heq
    rw [heq]
  -- A subinterval on which `f` is analytic.
  obtain ⟨x₀, hx₀J, hx₀a⟩ := (dense_iff_inter_open.mp hf) (Ioo p q) isOpen_Ioo
    ⟨(p + q) / 2, by constructor <;> linarith⟩
  obtain ⟨r, s, hx₀rs, hrs⟩ := mem_nhds_iff_exists_Ioo_subset.1
    ((isOpen_Ioo.inter (isOpen_analyticLocus f)).mem_nhds ⟨hx₀J, hx₀a⟩)
  have hrs' : r < s := lt_trans hx₀rs.1 hx₀rs.2
  -- `f` is not locally constant there, so its derivative vanishes somewhere it does not.
  obtain ⟨x₁, hx₁mem, hx₁deriv⟩ : ∃ x₁ ∈ Ioo r s, deriv f x₁ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hdiff : DifferentiableOn ℝ f (Ioo r s) := fun x hx =>
      (hrs hx).2.differentiableAt.differentiableWithinAt
    have hu : (2 * r + s) / 3 ∈ Ioo r s := ⟨by linarith, by linarith⟩
    have hv : (r + 2 * s) / 3 ∈ Ioo r s := ⟨by linarith, by linarith⟩
    have hconst : f ((2 * r + s) / 3) = f ((r + 2 * s) / 3) :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff
        (fun x hx => hcon x hx) hu hv
    have := hfinj _ (himg (hrs hu).1) _ (himg (hrs hv).1) hconst
    have : r = s := by linarith
    exact absurd this hrs'.ne
  -- Transport back through the branch.
  obtain ⟨y₁, hy₁, hgy₁⟩ := himg (hrs hx₁mem).1
  have hy₁U : y₁ ∈ U := hcdsub (Ioo_subset_Icc_self hy₁)
  refine ⟨y₁, hy₁U, analyticAt_of_rightInverse (h := f) ?_ ?_ ?_ ?_⟩
  · rw [hgy₁]; exact (hrs hx₁mem).2
  · rw [hgy₁]; exact hx₁deriv
  · exact hg.continuousAt (hU.mem_nhds hy₁U)
  · filter_upwards [hU.mem_nhds hy₁U] with y hy using hinv y hy

/-! ## Elementary functions extended by inverse branches -/

/-- Elementary functions of one real variable, closed under continuous inverse
branches at any depth.

The `invBranch` constructor carries the open set `U` on which the branch
identity `f (g y) = y` holds, and asks that `g` be analytic at every point of
the *interior of the complement* of `U`.  Localizing the identity is
essential: the Lambert `W` function satisfies `W y * Real.exp (W y) = y` only
on `[-1/e, ∞)`, so a constructor demanding a global identity would not reach
it.  See `Fabius.isElementaryOrInverse_of_lambertW`.

The analyticity side condition constrains the *chosen extension* of the branch
beyond `U`; it is not something `Mathlib`'s junk-value conventions supply for
free.  For `W` the constant extension satisfies it, since
`interior (Ioi (-Real.exp (-1)))ᶜ = Iio (-Real.exp (-1))`.  Other junk values
are analytic without being constant — `Real.log y = Real.log |y|` is the
standard example.  And taking `U = ∅` reduces the condition to "`g` is
entire", so the constructor also adjoins every everywhere-analytic function;
harmlessly, since those already have dense analytic locus.

Because inversion is available, the class contains `Real.log` twice over: once
by its own constructor, once as a branch inverting `Real.exp`.  What it does
*not* contain is every set-theoretic inverse of every member — a branch must
be continuous on `U` and analytic on `interior Uᶜ`.  Everything it does
contain is analytic on a dense set, by
`Fabius.IsElementaryOrInverse.dense_analyticLocus`, so the enlarged class
still cannot reach the Fabius function or its inverse. -/
inductive IsElementaryOrInverse : (ℝ → ℝ) → Prop
  /-- Every elementary function belongs to the class. -/
  | ofElementary {f : ℝ → ℝ} : IsElementary f → IsElementaryOrInverse f
  /-- A continuous inverse branch of a member, on an open set `U`, belongs to
  the class, provided it is analytic on the *interior of the complement* of
  `U` — where the junk values live.

  Asking for analyticity at every point outside `U` would be too much, and
  would make the Lambert `W` instance vacuous: the natural `U` for `W` is
  `Ioi (-exp (-1))`, whose complement has the branch point `-1/e` on its
  boundary, and `W` is certainly not analytic there.  Taking the interior
  drops exactly that boundary, which is nowhere dense and so cannot affect
  density of the analytic locus. -/
  | invBranch {f g : ℝ → ℝ} (U : Set ℝ) : IsElementaryOrInverse f → IsOpen U →
      ContinuousOn g U → (∀ y ∈ U, f (g y) = y) →
      (∀ y ∈ interior Uᶜ, AnalyticAt ℝ g y) →
      IsElementaryOrInverse g
  /-- Closed under addition. -/
  | add {f g : ℝ → ℝ} : IsElementaryOrInverse f → IsElementaryOrInverse g →
      IsElementaryOrInverse fun x => f x + g x
  /-- Closed under multiplication. -/
  | mul {f g : ℝ → ℝ} : IsElementaryOrInverse f → IsElementaryOrInverse g →
      IsElementaryOrInverse fun x => f x * g x
  /-- Closed under negation. -/
  | neg {f : ℝ → ℝ} : IsElementaryOrInverse f → IsElementaryOrInverse fun x => -f x
  /-- Closed under reciprocals. -/
  | inv {f : ℝ → ℝ} : IsElementaryOrInverse f → IsElementaryOrInverse fun x => (f x)⁻¹
  /-- Closed under fixed real powers. -/
  | rpow {f : ℝ → ℝ} (r : ℝ) : IsElementaryOrInverse f →
      IsElementaryOrInverse fun x => f x ^ r
  /-- Closed under the exponential. -/
  | exp {f : ℝ → ℝ} : IsElementaryOrInverse f → IsElementaryOrInverse fun x => Real.exp (f x)
  /-- Closed under the logarithm. -/
  | log {f : ℝ → ℝ} : IsElementaryOrInverse f → IsElementaryOrInverse fun x => Real.log (f x)
  /-- Closed under the sine. -/
  | sin {f : ℝ → ℝ} : IsElementaryOrInverse f → IsElementaryOrInverse fun x => Real.sin (f x)
  /-- Closed under the cosine. -/
  | cos {f : ℝ → ℝ} : IsElementaryOrInverse f → IsElementaryOrInverse fun x => Real.cos (f x)
  /-- Closed under the arcsine. -/
  | arcsin {f : ℝ → ℝ} : IsElementaryOrInverse f →
      IsElementaryOrInverse fun x => Real.arcsin (f x)
  /-- Closed under the arctangent. -/
  | arctan {f : ℝ → ℝ} : IsElementaryOrInverse f →
      IsElementaryOrInverse fun x => Real.arctan (f x)

/-- **Adjoining inverses changes nothing: the extended class is still analytic
on a dense set.**

The elementary cases are `Fabius.IsElementary.dense_analyticLocus` and the
closure lemmas behind it; the inverse case is
`Fabius.exists_analyticAt_of_rightInverse` inside `U`, together with the
hypothesis that the branch is analytic on `interior Uᶜ`.  The two cases are
separated by whether the open test set meets `U`; if it does not, it is
contained in `Uᶜ` and, being open, in `interior Uᶜ`. -/
theorem IsElementaryOrInverse.dense_analyticLocus {f : ℝ → ℝ}
    (hf : IsElementaryOrInverse f) : Dense (analyticLocus f) := by
  induction hf with
  | ofElementary h => exact h.dense_analyticLocus
  | invBranch U _ hU hg hinv hout ih =>
      rw [dense_iff_inter_open]
      intro B hB hBne
      rcases Set.eq_empty_or_nonempty (B ∩ U) with hBU | hBU
      · obtain ⟨y, hyB⟩ := hBne
        have hBsub : B ⊆ Uᶜ := fun z hz hzU =>
          Set.eq_empty_iff_forall_notMem.1 hBU z ⟨hz, hzU⟩
        exact ⟨y, hyB, hout y (interior_maximal hBsub hB hyB)⟩
      · obtain ⟨y, hy, hya⟩ :=
          exists_analyticAt_of_rightInverse ih (hB.inter hU) hBU
            (hg.mono Set.inter_subset_right) (fun y hy => hinv y hy.2)
        exact ⟨y, hy.1, hya⟩
  | add _ _ ih₁ ih₂ =>
      refine (ih₁.inter_of_isOpen_left ih₂ (isOpen_analyticLocus _)).mono ?_
      rintro x ⟨hx₁, hx₂⟩
      exact AnalyticAt.fun_add hx₁ hx₂
  | mul _ _ ih₁ ih₂ =>
      refine (ih₁.inter_of_isOpen_left ih₂ (isOpen_analyticLocus _)).mono ?_
      rintro x ⟨hx₁, hx₂⟩
      exact AnalyticAt.fun_mul hx₁ hx₂
  | neg _ ih =>
      refine ih.mono ?_
      intro x hx
      exact AnalyticAt.fun_neg hx
  | inv _ ih =>
      exact dense_analyticLocus_comp _ (fun t : ℝ => t⁻¹) {0} ih fun y hy =>
        analyticAt_inv (by simpa using hy)
  | rpow r _ ih =>
      exact dense_analyticLocus_comp _ (fun t : ℝ => t ^ r) {0} ih fun y hy =>
        analyticAt_rpow_const (by simpa using hy) r
  | exp _ ih =>
      exact dense_analyticLocus_comp _ Real.exp ∅ ih fun _ _ => analyticAt_rexp
  | log _ ih =>
      exact dense_analyticLocus_comp _ Real.log {0} ih fun y hy =>
        analyticAt_log_of_ne_zero (by simpa using hy)
  | sin _ ih =>
      exact dense_analyticLocus_comp _ Real.sin ∅ ih fun _ _ => Real.analyticAt_sin
  | cos _ ih =>
      exact dense_analyticLocus_comp _ Real.cos ∅ ih fun _ _ => Real.analyticAt_cos
  | arcsin _ ih =>
      refine dense_analyticLocus_comp _ Real.arcsin {-1, 1} ih fun y hy => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      exact analyticAt_arcsin hy.1 hy.2
  | arctan _ ih =>
      exact dense_analyticLocus_comp _ Real.arctan ∅ ih fun y _ => analyticAt_arctan y

/-- An elementary function is analytic at some point of every nonempty open
set; so is any function in the class extended by inverse branches. -/
theorem IsElementaryOrInverse.exists_analyticAt_of_isOpen {f : ℝ → ℝ}
    (hf : IsElementaryOrInverse f) {U : Set ℝ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ x ∈ U, AnalyticAt ℝ f x := by
  obtain ⟨x, hxU, hxf⟩ := (dense_iff_inter_open.mp hf.dense_analyticLocus) U hU hUne
  exact ⟨x, hxU, hxf⟩

/-- **The Lambert `W` function belongs to the extended class.**

Any function satisfying the defining identity `W y * exp (W y) = y` on an open
set `U`, continuous there and analytic on the interior of the complement of
`U`, is a member.  For the principal real branch take `U = Ioi (-Real.exp (-1))`:
the identity holds there, `W` is continuous there, and on
`interior (Ioi (-Real.exp (-1)))ᶜ = Iio (-Real.exp (-1))` any of the usual
junk-value conventions is constant, hence analytic.  Note that the branch
point `-1/e` itself is in neither set, which is exactly why the constructor
asks for the interior — `W` is not analytic there.

The statement is phrased for an arbitrary such branch because `Mathlib` does
not define `W`; it applies verbatim to any construction of it. -/
theorem isElementaryOrInverse_of_lambertW {W : ℝ → ℝ} (U : Set ℝ) (hU : IsOpen U)
    (hW : ContinuousOn W U) (hWinv : ∀ y ∈ U, W y * Real.exp (W y) = y)
    (hWout : ∀ y ∈ interior Uᶜ, AnalyticAt ℝ W y) : IsElementaryOrInverse W :=
  IsElementaryOrInverse.invBranch U
    (IsElementaryOrInverse.ofElementary (IsElementary.id.mul IsElementary.id.exp))
    hU hW hWinv hWout

end Fabius
