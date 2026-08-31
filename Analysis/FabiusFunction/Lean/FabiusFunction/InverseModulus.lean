import FabiusFunction.FabiusInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The exact modulus of continuity of the inverse Fabius function

For an interval of geometric length `h`, write

`fabiusIntervalMass F h x = F (x + h) - F x`.

The derivative of `F` is symmetric and single-peaked about `1 / 2`.  Therefore
this interval mass increases while the interval centre approaches `1 / 2`, is
unchanged by reflection, and decreases afterwards.  In particular, among all
subintervals of `[0,1]` of length `h`, the two endpoint intervals have the
least mass:

`F (b - a) ≤ F b - F a` for `0 ≤ a ≤ b ≤ 1`.

Transporting this inequality through the order isomorphism defined in
`FabiusFunction.FabiusInverse` gives the sharp nonlinear triangle inequality

`|G u - G v| ≤ G |u - v|`,

where `G = fabiusInv F hF` is already clamped outside `[0,1]`.  The bound is
attained at `u = 0`, `v = η`; consequently the ordinary modulus of continuity
of the totalized inverse is exactly `G η` for every `η ≥ 0`.  On `[0,1]` this
is the manuscript identity `ω_G(η) = G(η)`, and beyond one the right-hand side
automatically saturates at one.

## Main results

* `monotoneOn_fabiusIntervalMass_firstHalf` and
  `antitoneOn_fabiusIntervalMass_secondHalf` give the complete global unimodal
  shape of a fixed-length CDF increment.
* `fabiusReal_sub_le_sub` is the least-mass endpoint inequality.
* `fabiusReal_add_le` and `fabiusInv_add_le` expose the resulting constrained
  superadditivity of `F` and global subadditivity of its clamped inverse.
* `fabiusInv_sub_le_sub_of_le` and `abs_fabiusInv_sub_le` are the ordered and
  symmetric sharp inverse-gap bounds on all of `ℝ`.
* `isGreatest_abs_fabiusInv_sub` and
  `isGreatest_abs_fabiusInv_sub_Icc` say that the sharp bounds are attained;
  `sSup_abs_fabiusInv_sub_eq` and `sSup_abs_fabiusInv_sub_Icc_eq` are their
  exact-modulus corollaries.
* `abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal` is the effective-injectivity
  form used by certified inversion algorithms, and
  `forall_abs_fabiusInv_sub_lt_iff` characterizes its optimal threshold.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- The CDF increment `F (x+h) - F x`.  For the atomless Fabius probability
law this is the mass of `(x, x+h]`, equivalently of `[x, x+h]`. -/
def fabiusIntervalMass (F : BoundedFabius) (h x : ℝ) : ℝ :=
  fabiusReal F (x + h) - fabiusReal F x

/-- Reflecting an interval about `1 / 2` preserves its Fabius mass. -/
theorem fabiusIntervalMass_reflect (F : BoundedFabius) (hF : IsFabius F)
    (h x : ℝ) :
    fabiusIntervalMass F h (1 - h - x) = fabiusIntervalMass F h x := by
  rw [fabiusIntervalMass, fabiusIntervalMass,
    show 1 - h - x + h = 1 - x by ring,
    show 1 - h - x = 1 - (x + h) by ring,
    hF.symmetry_all x, hF.symmetry_all (x + h)]
  ring

private theorem fabiusIntervalMass_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (h x : ℝ) :
    HasDerivAt (fabiusIntervalMass F h)
      (deriv (fabiusReal F) (x + h) - deriv (fabiusReal F) x) x := by
  have hshift : HasDerivAt (fun t => fabiusReal F (t + h))
      (deriv (fabiusReal F) (x + h)) x := by
    exact HasDerivAt.comp_add_const x h
      (fabius_differentiable F hF (x + h)).hasDerivAt
  exact hshift.sub (fabius_differentiable F hF x).hasDerivAt

private theorem deriv_fabiusReal_le_shift_of_le_center
    (F : BoundedFabius) (hF : IsFabius F) {h x : ℝ}
    (hh : 0 ≤ h) (hcenter : x ≤ (1 - h) / 2) :
    deriv (fabiusReal F) x ≤ deriv (fabiusReal F) (x + h) := by
  have hxhalf : x ≤ 1 / 2 := by nlinarith [hcenter, hh]
  have horder : x ≤ 1 - (x + h) := by nlinarith [hcenter]
  by_cases hleft : x + h ≤ 1 / 2
  · exact monotoneOn_deriv_fabiusReal F hF
      (show x ∈ Iic (1 / 2 : ℝ) from hxhalf)
      (show x + h ∈ Iic (1 / 2 : ℝ) from hleft)
      (by linarith [hh])
  · rw [← deriv_fabiusReal_one_sub F hF (x + h)]
    have hxright : (1 : ℝ) / 2 < x + h := lt_of_not_ge hleft
    exact monotoneOn_deriv_fabiusReal F hF
      (show x ∈ Iic (1 / 2 : ℝ) from hxhalf)
      (show 1 - (x + h) ∈ Iic (1 / 2 : ℝ) by
        exact (calc
          1 - (x + h) < 1 - (1 : ℝ) / 2 := sub_lt_sub_left hxright 1
          _ = (1 : ℝ) / 2 := by ring).le)
      horder

/-- For a nonnegative length `h`, the fixed-length CDF increment increases
while its centre approaches `1/2` from the left.  The statement is global in
the starting point, including intervals meeting the constant tails. -/
theorem monotoneOn_fabiusIntervalMass_firstHalf
    (F : BoundedFabius) (hF : IsFabius F) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn (fabiusIntervalMass F h) (Iic ((1 - h) / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iic ((1 - h) / 2))
  · exact ((hF.contDiff.continuous.comp
      (continuous_id.add continuous_const)).sub hF.contDiff.continuous).continuousOn
  · intro x _hx
    exact (fabiusIntervalMass_hasDerivAt F hF h x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(fabiusIntervalMass_hasDerivAt F hF h x).deriv]
    have hxIic : x ∈ Iic ((1 - h) / 2) :=
      (interior_subset : interior (Iic ((1 - h) / 2)) ⊆ Iic ((1 - h) / 2)) hx
    exact sub_nonneg.mpr <| deriv_fabiusReal_le_shift_of_le_center F hF hh
      hxIic

/-- For a nonnegative length `h`, the fixed-length CDF increment decreases
after its centre passes `1/2`.  This is the reflected form of
`monotoneOn_fabiusIntervalMass_firstHalf`. -/
theorem antitoneOn_fabiusIntervalMass_secondHalf
    (F : BoundedFabius) (hF : IsFabius F) {h : ℝ}
    (hh0 : 0 ≤ h) :
    AntitoneOn (fabiusIntervalMass F h) (Ici ((1 - h) / 2)) := by
  intro x hx y hy hxy
  have hmono := monotoneOn_fabiusIntervalMass_firstHalf F hF hh0
  have hyc : (1 - h) / 2 ≤ y := hy
  have hxc : (1 - h) / 2 ≤ x := hx
  have hy' : 1 - h - y ∈ Iic ((1 - h) / 2) := by
    show 1 - h - y ≤ (1 - h) / 2
    linarith
  have hx' : 1 - h - x ∈ Iic ((1 - h) / 2) := by
    show 1 - h - x ≤ (1 - h) / 2
    linarith
  have hreflected := hmono hy' hx' (by linarith)
  rwa [fabiusIntervalMass_reflect F hF h y,
    fabiusIntervalMass_reflect F hF h x] at hreflected

/-- **Least-mass interval inequality.**  Among all subintervals of `[0,1]`
with length `b-a`, an endpoint interval has the least Fabius mass:

`F (b-a) ≤ F b - F a`.

The proof is denominator-free and uses only the symmetry and single-peaked
derivative of the bounded Fabius function. -/
theorem fabiusReal_sub_le_sub (F : BoundedFabius) (hF : IsFabius F)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a ≤ b) :
    fabiusReal F (b - a) ≤ fabiusReal F b - fabiusReal F a := by
  let h : ℝ := b - a
  have hh0 : 0 ≤ h := by dsimp [h]; linarith
  have hh1 : h ≤ 1 := by dsimp [h]; linarith [ha.1, hb.2]
  have hzero : fabiusIntervalMass F h 0 = fabiusReal F h := by
    simp [fabiusIntervalMass, hF.zero_of_nonpos]
  have hfinish : fabiusIntervalMass F h a =
      fabiusReal F b - fabiusReal F a := by
    unfold fabiusIntervalMass
    rw [show a + h = b by dsimp [h]; linarith]
  have hmono := monotoneOn_fabiusIntervalMass_firstHalf F hF hh0
  by_cases hleft : a ≤ (1 - h) / 2
  · have hcenter0 : 0 ∈ Iic ((1 - h) / 2) := by
      show 0 ≤ (1 - h) / 2
      nlinarith [hh1]
    have ha' : a ∈ Iic ((1 - h) / 2) := by
      show a ≤ (1 - h) / 2
      exact hleft
    calc
      fabiusReal F h = fabiusIntervalMass F h 0 := hzero.symm
      _ ≤ fabiusIntervalMass F h a := hmono hcenter0 ha' ha.1
      _ = fabiusReal F b - fabiusReal F a := hfinish

  · let a' : ℝ := 1 - b
    have ha' : a' ∈ Iic ((1 - h) / 2) := by
      show a' ≤ (1 - h) / 2
      have hright : (1 - h) / 2 < a := lt_of_not_ge hleft
      dsimp [a', h] at hright ⊢
      linarith
    have ha'0 : 0 ≤ a' := by
      dsimp [a']
      linarith [hb.2]
    have hcenter0 : 0 ∈ Iic ((1 - h) / 2) := by
      show 0 ≤ (1 - h) / 2
      nlinarith [hh1]
    have hreflect : fabiusIntervalMass F h a' = fabiusIntervalMass F h a := by
      rw [show a' = 1 - h - a by dsimp [a', h]; ring,
        fabiusIntervalMass_reflect F hF h a]
    calc
      fabiusReal F h = fabiusIntervalMass F h 0 := hzero.symm
      _ ≤ fabiusIntervalMass F h a' := hmono hcenter0 ha' ha'0
      _ = fabiusIntervalMass F h a := hreflect
      _ = fabiusReal F b - fabiusReal F a := hfinish

/-- **Constrained superadditivity of the Fabius CDF.**  Nonnegative arguments
whose sum lies in `[0,1]` satisfy `F a + F b ≤ F (a+b)`. -/
theorem fabiusReal_add_le (F : BoundedFabius) (hF : IsFabius F)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    fabiusReal F a + fabiusReal F b ≤ fabiusReal F (a + b) := by
  have hgap := fabiusReal_sub_le_sub F hF
    (show a ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    (show a + b ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    (by linarith)
  rw [show a + b - a = b by ring] at hgap
  linarith

/-- On the unit interval, inverse increments are bounded by the inverse of
the input increment. -/
theorem fabiusInv_sub_le_sub_of_mem_Icc
    (F : BoundedFabius) (hF : IsFabius F) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) :
    fabiusInv F hF v - fabiusInv F hF u ≤ fabiusInv F hF (v - u) := by
  have hGu := fabiusInv_mem_Icc F hF u
  have hGv := fabiusInv_mem_Icc F hF v
  have hGuv : fabiusInv F hF u ≤ fabiusInv F hF v :=
    monotone_fabiusInv F hF huv
  have hmass := fabiusReal_sub_le_sub F hF hGu hGv hGuv
  rw [fabiusReal_fabiusInv F hF hv, fabiusReal_fabiusInv F hF hu] at hmass
  have hdiff : fabiusInv F hF v - fabiusInv F hF u ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hGu.1, hGu.2, hGv.1, hGv.2]
  have huvDiff : v - u ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hv.2]
  exact (fabiusReal_le_iff_le_fabiusInv F hF hdiff huvDiff).mp hmass

/-- **Ordered sharp modulus bound on the totalized inverse.**  For arbitrary
real inputs `u ≤ v`, including the clamped tails,

`G v - G u ≤ G (v-u)`. -/
theorem fabiusInv_sub_le_sub_of_le
    (F : BoundedFabius) (hF : IsFabius F) {u v : ℝ} (huv : u ≤ v) :
    fabiusInv F hF v - fabiusInv F hF u ≤ fabiusInv F hF (v - u) := by
  by_cases hv0 : v ≤ 0
  · rw [fabiusInv_eq_zero_of_nonpos F hF hv0,
      fabiusInv_eq_zero_of_nonpos F hF (huv.trans hv0), sub_self]
    exact fabiusInv_nonneg F hF (v - u)
  · by_cases hu0 : u ≤ 0
    · rw [fabiusInv_eq_zero_of_nonpos F hF hu0, sub_zero]
      exact monotone_fabiusInv F hF (by linarith)
    · by_cases hu1 : 1 ≤ u
      · rw [fabiusInv_eq_one_of_one_le F hF hu1,
          fabiusInv_eq_one_of_one_le F hF (hu1.trans huv), sub_self]
        exact fabiusInv_nonneg F hF (v - u)
      · by_cases hv1 : 1 ≤ v
        · rw [fabiusInv_eq_one_of_one_le F hF hv1,
            ← fabiusInv_one_sub F hF u]
          exact monotone_fabiusInv F hF (by linarith)
        · exact fabiusInv_sub_le_sub_of_mem_Icc F hF
            ⟨le_of_not_ge hu0, le_of_not_ge hu1⟩
            ⟨le_of_not_ge hv0, le_of_not_ge hv1⟩ huv

/-- **Order-free inverse-gap inequality.**  The ordered theorem remains true
without an order hypothesis: when `v < u`, its left side is nonpositive and
its right side is nonnegative. -/
theorem fabiusInv_sub_le_sub
    (F : BoundedFabius) (hF : IsFabius F) (u v : ℝ) :
    fabiusInv F hF v - fabiusInv F hF u ≤ fabiusInv F hF (v - u) := by
  rcases le_total u v with huv | hvu
  · exact fabiusInv_sub_le_sub_of_le F hF huv
  · exact (sub_nonpos.mpr (monotone_fabiusInv F hF hvu)).trans
      (fabiusInv_nonneg F hF (v - u))

/-- **Global subadditivity of the totalized inverse.**  The clamped inverse
satisfies `G (x+y) ≤ G x + G y` for every pair of real arguments. -/
theorem fabiusInv_add_le
    (F : BoundedFabius) (hF : IsFabius F) (x y : ℝ) :
    fabiusInv F hF (x + y) ≤ fabiusInv F hF x + fabiusInv F hF y := by
  have hgap := fabiusInv_sub_le_sub F hF x (x + y)
  rw [show x + y - x = y by ring] at hgap
  linarith

/-- **Exact pointwise modulus of the totalized inverse.**  For all real
inputs,

`|G u - G v| ≤ G |u-v|`.

The right-hand side is sharp: equality holds for the pair `0, |u-v|`. -/
theorem abs_fabiusInv_sub_le
    (F : BoundedFabius) (hF : IsFabius F) (u v : ℝ) :
    |fabiusInv F hF u - fabiusInv F hF v| ≤ fabiusInv F hF |u - v| := by
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonpos (sub_nonpos.mpr (monotone_fabiusInv F hF huv)),
      abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using fabiusInv_sub_le_sub_of_le F hF huv
  · rw [abs_of_nonneg (sub_nonneg.mpr (monotone_fabiusInv F hF hvu)),
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact fabiusInv_sub_le_sub_of_le F hF hvu

/-- Metric-native spelling of `abs_fabiusInv_sub_le`. -/
theorem dist_fabiusInv_le
    (F : BoundedFabius) (hF : IsFabius F) (u v : ℝ) :
    dist (fabiusInv F hF u) (fabiusInv F hF v) ≤
      fabiusInv F hF (dist u v) := by
  simpa only [Real.dist_eq] using abs_fabiusInv_sub_le F hF u v

/-- The explicit saturation identity matching the manuscript notation: the
clamped inverse has the same value at `min η 1` and `η`. -/
theorem fabiusInv_min_one
    (F : BoundedFabius) (hF : IsFabius F) (η : ℝ) :
    fabiusInv F hF (min η 1) = fabiusInv F hF η := by
  by_cases hη1 : η ≤ 1
  · rw [min_eq_left hη1]
  · have h1η : 1 ≤ η := le_of_not_ge hη1
    rw [min_eq_right h1η, fabiusInv_one F hF,
      fabiusInv_eq_one_of_one_le F hF h1η]

/-- **Attained exact modulus on all real inputs.**  For every `η ≥ 0`, `G η`
is the greatest inverse output gap among input pairs at distance at most `η`.
The extremizing pair is `(0, η)`. -/
theorem isGreatest_abs_fabiusInv_sub
    (F : BoundedFabius) (hF : IsFabius F) {η : ℝ} (hη : 0 ≤ η) :
    IsGreatest {z : ℝ | ∃ u v : ℝ, |u - v| ≤ η ∧
      z = |fabiusInv F hF u - fabiusInv F hF v|} (fabiusInv F hF η) := by
  let S : Set ℝ := {z : ℝ | ∃ u v : ℝ, |u - v| ≤ η ∧
    z = |fabiusInv F hF u - fabiusInv F hF v|}
  change IsGreatest S (fabiusInv F hF η)
  have hattain : fabiusInv F hF η ∈ S := by
    refine ⟨0, η, ?_, ?_⟩
    · simp [abs_of_nonneg hη]
    · rw [fabiusInv_zero F hF, zero_sub, abs_neg,
        abs_of_nonneg (fabiusInv_nonneg F hF η)]
  refine ⟨hattain, ?_⟩
  intro z hz
  rcases hz with ⟨u, v, huv, rfl⟩
  exact (abs_fabiusInv_sub_le F hF u v).trans
    (monotone_fabiusInv F hF huv)

/-- **Exact modulus on all real inputs.**  For every `η ≥ 0`, the supremum of
inverse output gaps over all input pairs at distance at most `η` is exactly
`G η`.  Since `G` is clamped, this is equivalently `G (min η 1)`. -/
theorem sSup_abs_fabiusInv_sub_eq
    (F : BoundedFabius) (hF : IsFabius F) {η : ℝ} (hη : 0 ≤ η) :
    sSup {z : ℝ | ∃ u v : ℝ, |u - v| ≤ η ∧
      z = |fabiusInv F hF u - fabiusInv F hF v|} = fabiusInv F hF η :=
  (isGreatest_abs_fabiusInv_sub F hF hη).csSup_eq

/-- **Attained exact modulus on the unit interval.**  For every `η ≥ 0`,
restricting both inputs to `[0,1]` leaves the exact modulus equal to `G η`.
For `η ≤ 1` the extremizer is `(0, η)`; after saturation it is `(0, 1)`. -/
theorem isGreatest_abs_fabiusInv_sub_Icc
    (F : BoundedFabius) (hF : IsFabius F) {η : ℝ} (hη : 0 ≤ η) :
    IsGreatest {z : ℝ | ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
      |u - v| ≤ η ∧ z = |fabiusInv F hF u - fabiusInv F hF v|}
      (fabiusInv F hF η) := by
  let S : Set ℝ := {z : ℝ | ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
    |u - v| ≤ η ∧ z = |fabiusInv F hF u - fabiusInv F hF v|}
  change IsGreatest S (fabiusInv F hF η)
  have hattain : fabiusInv F hF η ∈ S := by
    by_cases hη1 : η ≤ 1
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, η, ⟨hη, hη1⟩, ?_, ?_⟩
      · simp [abs_of_nonneg hη]
      · rw [fabiusInv_zero F hF, zero_sub, abs_neg,
          abs_of_nonneg (fabiusInv_nonneg F hF η)]
    · have h1η : 1 ≤ η := le_of_not_ge hη1
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, 1, ⟨zero_le_one, le_rfl⟩, ?_, ?_⟩
      · simpa using h1η
      · rw [fabiusInv_zero F hF, fabiusInv_one F hF, zero_sub, abs_neg,
          abs_one, fabiusInv_eq_one_of_one_le F hF h1η]
  refine ⟨hattain, ?_⟩
  intro z hz
  rcases hz with ⟨u, _hu, v, _hv, huv, rfl⟩
  exact (abs_fabiusInv_sub_le F hF u v).trans
    (monotone_fabiusInv F hF huv)

/-- **Exact modulus on the unit interval.**  At every nonnegative radius, the
supremum of inverse output gaps between unit-interval inputs is `G η`. -/
theorem sSup_abs_fabiusInv_sub_Icc_eq
    (F : BoundedFabius) (hF : IsFabius F) {η : ℝ} (hη : 0 ≤ η) :
    sSup {z : ℝ | ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
      |u - v| ≤ η ∧ z = |fabiusInv F hF u - fabiusInv F hF v|} =
      fabiusInv F hF η :=
  (isGreatest_abs_fabiusInv_sub_Icc F hF hη).csSup_eq

/-- **Effective injectivity.**  If `0 ≤ h ≤ 1` and two inputs are closer than
the endpoint mass `F h`, then their totalized inverse images are closer than
`h`.  The threshold is optimal, attained by `0` and `F h`. -/
theorem abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) {h u v : ℝ}
    (hh : h ∈ Icc (0 : ℝ) 1) (huv : |u - v| < fabiusReal F h) :
    |fabiusInv F hF u - fabiusInv F hF v| < h := by
  have huvIcc : |u - v| ∈ Icc (0 : ℝ) 1 :=
    ⟨abs_nonneg _, (le_of_lt huv).trans (fabiusReal_le_one F h)⟩
  have hinv : fabiusInv F hF |u - v| < h :=
    (fabiusInv_lt_iff_lt_fabiusReal F hF huvIcc hh).2 huv
  exact (abs_fabiusInv_sub_le F hF u v).trans_lt hinv

/-- Closed-threshold form of effective injectivity. -/
theorem abs_fabiusInv_sub_le_of_abs_sub_le_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) {h u v : ℝ}
    (hh : h ∈ Icc (0 : ℝ) 1) (huv : |u - v| ≤ fabiusReal F h) :
    |fabiusInv F hF u - fabiusInv F hF v| ≤ h := by
  calc
    |fabiusInv F hF u - fabiusInv F hF v| ≤ fabiusInv F hF |u - v| :=
      abs_fabiusInv_sub_le F hF u v
    _ ≤ fabiusInv F hF (fabiusReal F h) := monotone_fabiusInv F hF huv
    _ = h := fabiusInv_fabiusReal F hF hh

/-- Contrapositive separation form: an inverse-output gap of at least `h`
forces an input gap of at least the sharp threshold `F h`. -/
theorem fabiusReal_le_abs_sub_of_le_abs_fabiusInv_sub
    (F : BoundedFabius) (hF : IsFabius F) {h u v : ℝ}
    (hh : h ∈ Icc (0 : ℝ) 1)
    (huv : h ≤ |fabiusInv F hF u - fabiusInv F hF v|) :
    fabiusReal F h ≤ |u - v| := by
  by_contra hnot
  exact (not_lt_of_ge huv)
    (abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal F hF hh
      (lt_of_not_ge hnot))

/-- **The exact strict uniform threshold.**  For `0 ≤ h ≤ 1`, a radius `δ`
uniformly forces every inverse-output gap below `h` exactly when
`δ ≤ F h`.  No sign hypothesis on `δ` is needed: nonpositive radii make the
left-hand implication vacuous and automatically satisfy the right side. -/
theorem forall_abs_fabiusInv_sub_lt_iff
    (F : BoundedFabius) (hF : IsFabius F) {h δ : ℝ}
    (hh : h ∈ Icc (0 : ℝ) 1) :
    (∀ u v : ℝ, |u - v| < δ →
      |fabiusInv F hF u - fabiusInv F hF v| < h) ↔
      δ ≤ fabiusReal F h := by
  constructor
  · intro H
    by_contra hnot
    have hlt : fabiusReal F h < δ := lt_of_not_ge hnot
    have hw := H 0 (fabiusReal F h) (by
      simpa [abs_of_nonneg (fabiusReal_nonneg F h)] using hlt)
    rw [fabiusInv_zero F hF, fabiusInv_fabiusReal F hF hh,
      zero_sub, abs_neg, abs_of_nonneg hh.1] at hw
    exact (lt_irrefl h) hw
  · intro hδ u v huv
    exact abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal F hF hh
      (huv.trans_le hδ)

end Fabius
