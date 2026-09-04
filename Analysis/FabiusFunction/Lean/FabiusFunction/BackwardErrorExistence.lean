import FabiusFunction.MeanValueBracket
import Mathlib.Topology.Order.IntermediateValue

/-!
# The residual is a certificate: existence, location, and uniqueness

`MeanValueBracket.lean` transfers a residual into an error bound *given* that a
root exists — the bound is stated against a right inverse `g` that is assumed
to be there.  The transseries volume's `q3:prop:transfer` observes that this is
the weaker half of what the backward-error theorem says: a slope bound below
also *produces* the root, so no separate existence argument is needed.

That is what this module supplies.  If `f` is continuous on `[a,b]` and its
increments grow at least at rate `m > 0`, then a candidate `x` whose residual
is `r = f x - y` has a genuine solution of `f z = y` within `|r|/m` of it, as
soon as that ball fits inside `[a,b]`; and with `m > 0` the solution is unique,
so "a root" is "the root".

The mechanism is the intermediate value theorem applied on one side only.  The
residual's sign says which side: if `f x` overshoots `y`, then `f` has already
come down below `y` by the time it reaches `x - |r|/m`, because the slope bound
forces a drop of at least `m · |r|/m = |r|` over that distance.  So the sign of
the residual is not merely diagnostic, as in `residual_pos_iff`; it selects the
half-interval on which the root is found.

The hypothesis is stated as a *slope* condition rather than a derivative bound,
so no differentiability is needed; `exists_eq_of_le_deriv` derives it from
`m ≤ f'` for the differentiable case.
-/

set_option autoImplicit false

open Set

namespace Fabius

variable {f : ℝ → ℝ} {a b m x y : ℝ}

/-- The slope condition: increments of `f` grow at least at rate `m`. -/
def HasSlopeLowerBound (f : ℝ → ℝ) (D : Set ℝ) (m : ℝ) : Prop :=
  ∀ u ∈ D, ∀ v ∈ D, u ≤ v → m * (v - u) ≤ f v - f u

/-- A derivative bound below gives the slope bound, by the mean value theorem. -/
theorem hasSlopeLowerBound_of_le_deriv {D : Set ℝ} (hD : Convex ℝ D)
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hm : ∀ z ∈ interior D, m ≤ deriv f z) : HasSlopeLowerBound f D m :=
  fun u hu v hv huv => Convex.mul_sub_le_image_sub_of_le_deriv hD hf hf' hm u hu v hv huv

/-- **`q3:prop:transfer`, existence clause.**  A residual of size `|r|` at `x`
guarantees a solution of `f z = y` within `|r| / m`, provided that ball lies in
the interval where the slope bound holds. -/
theorem exists_eq_of_residual (hm : 0 < m) (hcont : ContinuousOn f (Icc a b))
    (hslope : HasSlopeLowerBound f (Icc a b) m) (hx : x ∈ Icc a b)
    (hball : Icc (x - |f x - y| / m) (x + |f x - y| / m) ⊆ Icc a b) :
    ∃ z ∈ Icc (x - |f x - y| / m) (x + |f x - y| / m), f z = y := by
  set r := |f x - y| with hr
  set ρ := r / m with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (abs_nonneg _) hm.le
  have hmρ : m * ρ = r := by
    rw [hρ, mul_div_cancel₀ _ hm.ne']
  have hxmem : x ∈ Icc (x - ρ) (x + ρ) := ⟨by linarith, by linarith⟩
  rcases le_or_gt y (f x) with hle | hgt
  · -- the candidate overshoots: come down on the left
    have hpmem : x - ρ ∈ Icc (x - ρ) (x + ρ) := ⟨le_rfl, by linarith⟩
    have hp : x - ρ ∈ Icc a b := hball hpmem
    have hdrop := hslope (x - ρ) hp x hx (by linarith)
    have habs : r = f x - y := by rw [hr, abs_of_nonneg (by linarith)]
    have hfp : f (x - ρ) ≤ y := by
      have : m * (x - (x - ρ)) = r := by rw [show x - (x - ρ) = ρ by ring, hmρ]
      rw [this] at hdrop
      rw [habs] at hdrop
      linarith
    have hsub : Icc (x - ρ) x ⊆ Icc a b := fun t ht =>
      hball ⟨ht.1, by have := ht.2; linarith⟩
    have hmem : y ∈ f '' Icc (x - ρ) x :=
      intermediate_value_Icc (by linarith) (hcont.mono hsub) ⟨hfp, hle⟩
    obtain ⟨z, hz, hzy⟩ := hmem
    exact ⟨z, ⟨hz.1, by have := hz.2; linarith⟩, hzy⟩
  · -- the candidate undershoots: climb on the right
    have hqmem : x + ρ ∈ Icc (x - ρ) (x + ρ) := ⟨by linarith, le_rfl⟩
    have hq : x + ρ ∈ Icc a b := hball hqmem
    have hrise := hslope x hx (x + ρ) hq (by linarith)
    have habs : r = y - f x := by
      rw [hr, abs_of_nonpos (by linarith), neg_sub]
    have hfq : y ≤ f (x + ρ) := by
      have : m * (x + ρ - x) = r := by rw [show x + ρ - x = ρ by ring, hmρ]
      rw [this] at hrise
      rw [habs] at hrise
      linarith
    have hsub : Icc x (x + ρ) ⊆ Icc a b := fun t ht =>
      hball ⟨by have := ht.1; linarith, ht.2⟩
    have hmem : y ∈ f '' Icc x (x + ρ) :=
      intermediate_value_Icc (by linarith) (hcont.mono hsub) ⟨hgt.le, hfq⟩
    obtain ⟨z, hz, hzy⟩ := hmem
    exact ⟨z, ⟨by have := hz.1; linarith, hz.2⟩, hzy⟩

/-- A positive slope bound makes `f` injective, so the root found above is the
only one in the interval. -/
theorem injOn_of_hasSlopeLowerBound (hm : 0 < m) (hslope : HasSlopeLowerBound f (Icc a b) m) :
    Set.InjOn f (Icc a b) := by
  intro u hu v hv huv
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hslope u hu v hv h.le
    nlinarith [sub_pos.mpr h]
  · have := hslope v hv u hu h.le
    nlinarith [sub_pos.mpr h]

/-- **`q3:prop:transfer`, packaged.**  Existence, location and uniqueness at
once: the residual certifies a *unique* solution within `|r| / m`. -/
theorem existsUnique_eq_of_residual (hm : 0 < m) (hcont : ContinuousOn f (Icc a b))
    (hslope : HasSlopeLowerBound f (Icc a b) m) (hx : x ∈ Icc a b)
    (hball : Icc (x - |f x - y| / m) (x + |f x - y| / m) ⊆ Icc a b) :
    ∃! z, z ∈ Icc a b ∧ f z = y := by
  obtain ⟨z, hz, hzy⟩ := exists_eq_of_residual hm hcont hslope hx hball
  refine ⟨z, ⟨hball hz, hzy⟩, ?_⟩
  rintro w ⟨hw, hwy⟩
  exact injOn_of_hasSlopeLowerBound hm hslope hw (hball hz) (by rw [hwy, hzy])

/-- The located root is within `|r| / m` of the candidate, which is the volume's
`q3:eq:one-sided` with the existence hypothesis discharged rather than
assumed. -/
theorem exists_eq_and_abs_sub_le (hm : 0 < m) (hcont : ContinuousOn f (Icc a b))
    (hslope : HasSlopeLowerBound f (Icc a b) m) (hx : x ∈ Icc a b)
    (hball : Icc (x - |f x - y| / m) (x + |f x - y| / m) ⊆ Icc a b) :
    ∃ z ∈ Icc a b, f z = y ∧ |x - z| ≤ |f x - y| / m := by
  obtain ⟨z, hz, hzy⟩ := exists_eq_of_residual hm hcont hslope hx hball
  refine ⟨z, hball hz, hzy, ?_⟩
  rw [abs_le]
  constructor
  · have := hz.2; linarith
  · have := hz.1; linarith

/-- The differentiable form, for use where a derivative bound is what is
available. -/
theorem exists_eq_of_le_deriv (hm : 0 < m) (hcont : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (interior (Icc a b)))
    (hderiv : ∀ z ∈ interior (Icc a b), m ≤ deriv f z) (hx : x ∈ Icc a b)
    (hball : Icc (x - |f x - y| / m) (x + |f x - y| / m) ⊆ Icc a b) :
    ∃ z ∈ Icc (x - |f x - y| / m) (x + |f x - y| / m), f z = y :=
  exists_eq_of_residual hm hcont
    (hasSlopeLowerBound_of_le_deriv (convex_Icc a b) hcont hf' hderiv) hx hball

end Fabius
