import FabiusFunction.OriginalPaperSupplement
import FabiusFunction.PaperStatements

/-!
# The exact real-analytic locus of the Fabius function

The unnumbered corollary to equation (24) of Arias de Reyna,
arXiv:1702.06487v3, states that Rvachev's `up` is real analytic at no point of
`[-1,1]`; that corollary is `Fabius.rvachev_not_analyticAt`.  The
corresponding statement for the bounded Fabius function itself was missing,
even though it follows from the reflection `F(y) = up(1 - y)`, valid for every
`y ≤ 1`.

This file transfers the corollary and then determines the analytic locus
exactly.  Outside `[0,1]` the bounded function is locally constant, hence
analytic there, so

`AnalyticAt ℝ (fabiusReal F) x ↔ x ∉ [0,1]`.

The right endpoint needs a separate argument: the reflection identity is not
an identity of germs at `1`, so analyticity at `1` is instead pushed to
analyticity at `0` through `IsFabius.symmetry_all`.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- Analyticity is preserved by precomposition with the reflection `y ↦ c - y`. -/
private lemma analyticAt_comp_const_sub {f : ℝ → ℝ} {c a : ℝ}
    (h : AnalyticAt ℝ f (c - a)) :
    AnalyticAt ℝ (fun y : ℝ => f (c - y)) a := by
  have haffine : AnalyticAt ℝ (fun y : ℝ => c - y) a := by fun_prop
  refine (h.comp haffine).congr ?_
  filter_upwards with y
  rfl

/-- The bounded Fabius function is the reflection of Rvachev's function at
every argument at most one, including both endpoints. -/
theorem fabiusReal_eq_rvachevUp_one_sub (F : BoundedFabius) {y : ℝ} (hy : y ≤ 1) :
    fabiusReal F y = rvachevUp F (1 - y) := by
  rw [rvachevUp_eq_fabiusReal_one_sub F (show (0 : ℝ) ≤ 1 - y by linarith),
    show (1 : ℝ) - (1 - y) = y by ring]

/-! ## Non-analyticity on the unit interval -/

/-- The bounded Fabius function is not real analytic at any point of `[0,1)`. -/
theorem fabius_not_analyticAt_of_lt_one (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ¬ AnalyticAt ℝ (fabiusReal F) x := by
  intro h
  have hx' : AnalyticAt ℝ (fabiusReal F) (1 - (1 - x)) := by
    rw [show (1 : ℝ) - (1 - x) = x by ring]
    exact h
  have hcomp : AnalyticAt ℝ (fun y : ℝ => fabiusReal F (1 - y)) (1 - x) :=
    analyticAt_comp_const_sub hx'
  have hup : AnalyticAt ℝ (rvachevUp F) (1 - x) := by
    refine hcomp.congr ?_
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 - x by linarith)] with y hy
    exact (rvachevUp_of_pos F hy).symm
  exact rvachev_not_analyticAt F hF (1 - x) ⟨by linarith, by linarith⟩ hup

/-- The bounded Fabius function is not real analytic at the right endpoint. -/
theorem fabius_not_analyticAt_one (F : BoundedFabius) (hF : IsFabius F) :
    ¬ AnalyticAt ℝ (fabiusReal F) 1 := by
  intro h
  have h1 : AnalyticAt ℝ (fabiusReal F) (1 - (0 : ℝ)) := by
    rw [show (1 : ℝ) - (0 : ℝ) = 1 by norm_num]
    exact h
  have hrefl : AnalyticAt ℝ (fun y : ℝ => fabiusReal F (1 - y)) 0 :=
    analyticAt_comp_const_sub h1
  have hconst : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) 0 := analyticAt_const
  have hzero : AnalyticAt ℝ (fabiusReal F) 0 := by
    refine (hconst.sub hrefl).congr ?_
    filter_upwards with y
    rw [hF.symmetry_all y]
    ring
  exact fabius_not_analyticAt_of_lt_one F hF le_rfl (by norm_num) hzero

/-- The bounded Fabius function is real analytic at no point of `[0,1]`. -/
theorem fabius_not_analyticAt (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ¬ AnalyticAt ℝ (fabiusReal F) x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · subst h
    exact fabius_not_analyticAt_one F hF
  · exact fabius_not_analyticAt_of_lt_one F hF hx.1 h

/-- The signed global extension is not real analytic at any interior point of
the unit interval. -/
theorem extendedFabius_not_analyticAt (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ¬ AnalyticAt ℝ (extendedFabius F) x := by
  intro h
  refine fabius_not_analyticAt F hF (Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩) ?_
  refine h.congr ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact extendedFabius_eq_fabiusReal F hF (Set.mem_Icc.mpr ⟨hy.1.le, hy.2.le⟩)

/-! ## Analyticity off the unit interval -/

/-- To the left of the unit interval the bounded Fabius function is locally
constant, hence analytic. -/
theorem fabius_analyticAt_of_neg (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x < 0) : AnalyticAt ℝ (fabiusReal F) x := by
  have hconst : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) x := analyticAt_const
  refine hconst.congr ?_
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact (hF.zero_of_nonpos y (le_of_lt hy)).symm

/-- To the right of the unit interval the bounded Fabius function is locally
constant, hence analytic. -/
theorem fabius_analyticAt_of_one_lt (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : 1 < x) : AnalyticAt ℝ (fabiusReal F) x := by
  have hconst : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) x := analyticAt_const
  refine hconst.congr ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact (hF.one_of_one_le y (le_of_lt hy)).symm

/-- The real-analytic locus of the bounded Fabius function is exactly the
complement of the unit interval. -/
theorem fabius_analyticAt_iff (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    AnalyticAt ℝ (fabiusReal F) x ↔ x ∉ Icc (0 : ℝ) 1 := by
  constructor
  · intro h hx
    exact fabius_not_analyticAt F hF hx h
  · intro hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · exact fabius_analyticAt_of_neg F hF h
    · exact fabius_analyticAt_of_one_lt F hF h

/-! ## The canonical Fabius function -/

/-- The canonical Fabius function is real analytic at no point of `[0,1]`. -/
theorem canonical_fabius_not_analyticAt {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ¬ AnalyticAt ℝ (fabiusReal fabius) x :=
  fabius_not_analyticAt fabius fabius_spec hx

/-- The real-analytic locus of the canonical Fabius function. -/
theorem canonical_fabius_analyticAt_iff (x : ℝ) :
    AnalyticAt ℝ (fabiusReal fabius) x ↔ x ∉ Icc (0 : ℝ) 1 :=
  fabius_analyticAt_iff fabius fabius_spec x

/-- Rvachev's function attached to the canonical Fabius function is real
analytic at no point of its support. -/
theorem canonical_rvachev_not_analyticAt {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ¬ AnalyticAt ℝ (rvachevUp fabius) x :=
  rvachev_not_analyticAt fabius fabius_spec x hx

end Fabius
