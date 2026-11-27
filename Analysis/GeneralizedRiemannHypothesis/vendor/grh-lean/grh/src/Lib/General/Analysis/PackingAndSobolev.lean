import Lib.General.Measure.IntegralOperators

/-!
# Packing bounds for separated points and Sobolev trace inequalities
The first results count and sum over points `f i` of a finite-dimensional real normed space `V` at
mutual distance at least `m > 0`. Here `d = finrank ℝ V`. The remaining results bound the value of a
function at a point by `L²` norms of the function and of its derivatives, first on an interval and
then at the corner of a cube.

## Main definitions and results

* `New.encard_le_of_separated`: at most `(1 + 2R/m)^d` such points lie in the ball `‖x‖ ≤ R`,
  where `R ≥ 0`, by comparing volumes.
* `New.tsum_le_of_separated`: if `u i ≥ 1`, `‖f i‖ ≤ R * u i`, `R ≥ 0`, `d < A` and
  `A ≤ c (A - d)`, then `∑ u i ^ (-A) ≤ (1 + 2R/m)^d * c`, by the layer bound
  `New.DiscreteSeries.integral_rpow_neg_le_of_measure_le`.
* `New.tsum_inv_pow_le_of_separated`: if the points satisfy `‖f i‖ ≥ m` and `n ≥ d + 2`, then
  `∑ ‖f i‖⁻¹ ^ n ≤ (5/m)^n`.
* `New.sobolev_trace`: if `‖g'‖ ≤ b` pointwise on `[0, ε]`, where `0 < ε ≤ 1`, then
  `‖g 0‖² ≤ ∫₀^ε (2/ε) (‖g‖² + b²)`.
* `New.sobolev_trace_cube`: its iteration over the coordinates of a cube `[0, ε] ^ D` and a
  parameter space, for functions `f i` indexed by the words `i` in a finite alphabet, where the
  norms of the partial derivatives of `f i` are bounded by `Λ ∑ l, ‖f (l :: i)‖`, the sum over the
  letters `l`.
-/

/-! ## Packing bounds and sums over separated points -/

section Packing

open Module MeasureTheory Measure Metric

namespace New

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {f : I → V} {m R A c : ℝ}

/-- Packing bound: in a finite-dimensional real normed space `V`, if the points `f i`, for `i` in
`S`, have pairwise distances at least `m > 0` and norms at most `R`, with `R ≥ 0`, then `S` has
at most `(1 + 2R/m) ^ finrank ℝ V` elements. -/
lemma encard_le_of_separated (hm : 0 < m) (hR : 0 ≤ R) {S : Set I}
    (hf : S.Pairwise fun i j : I ↦ m ≤ ‖f i - f j‖) (hf_le : ∀ i ∈ S, ‖f i‖ ≤ R) :
    S.encard ≤ ENNReal.ofReal ((1 + 2 * R / m) ^ finrank ℝ V) := by
  -- Volume count: the balls of radius `m / 2` around the points are disjoint and lie in the ball of
  -- radius `R + m / 2 = (1 + 2 * R / m) * (m / 2)` around `0`.
  borelize V
  have h_disj : Pairwise (Function.onFun Disjoint fun i : S ↦ ball (f i) (m / 2)) :=
    hf.subtype.mono fun i j hij ↦ ball_disjoint_ball (by simpa [dist_eq_norm] using hij)
  rw [← ENNReal.mul_le_mul_iff_left (measure_ball_pos addHaar (0 : V) (half_pos hm)).ne'
    measure_ball_ne_top]
  calc
    S.encard * addHaar (ball (0 : V) (m / 2)) = ∑' i : S, addHaar (ball (f i) (m / 2)) := by
      simp [addHaar_ball_center]
    _ ≤ addHaar (⋃ i : S, ball (f i) (m / 2)) :=
      tsum_meas_le_meas_iUnion_of_disjoint _ (by measurability) h_disj
    _ ≤ addHaar (ball (0 : V) ((1 + 2 * R / m) * (m / 2))) := measure_mono <|
      Set.iUnion_subset fun i : S ↦ ball_subset (by simpa [field] using hf_le i i.prop)
    _ = _ := addHaar.addHaar_ball_mul_of_pos 0 (by positivity) (m / 2)

/-- Let points `f i` of a real normed space of finite dimension `d` have mutual distances at least
`m > 0`, with `‖f i‖ ≤ R * u i`, `u i ≥ 1` and `R ≥ 0`. If `A > d` and `A ≤ c (A - d)`, then
`∑ u i ^ (-A)` converges and is at most `(1 + 2R/m) ^ d * c`. -/
lemma tsum_le_of_separated (hm : 0 < m) (hR : 0 ≤ R)
    (hf : Pairwise fun i j : I ↦ m ≤ ‖f i - f j‖) {u : I → ℝ} (hu_one : ∀ i : I, 1 ≤ u i)
    (hu : ∀ i : I, ‖f i‖ ≤ R * u i) (hA : finrank ℝ V < A) (hc : A ≤ c * (A - finrank ℝ V)) :
    Summable (fun i : I ↦ u i ^ (-A)) ∧
    ∑' i : I, u i ^ (-A) ≤ (1 + 2 * R / m) ^ finrank ℝ V * c := by
  -- Apply `integral_rpow_neg_le_of_measure_le` to `u ≥ 1` and the counting measure on `I`: if
  -- `ν {u ≤ r} ≤ (K r ^ e) ^ d * v` for all `r ≥ 1`, `e d < A` and `A ≤ c (A - e d)`, then
  -- `∫ u ^ (-A) dν ≤ K ^ d * c * v`. Here `K = 1 + 2 * R / m`, `d = finrank ℝ V`, `e = v = 1`.
  let : MeasurableSpace I := ⊤
  -- The points with `u i ≤ r` lie in the ball of radius `R * r`, so packing bounds their number.
  have h_count (r : ℝ) (hr : r ≥ 1) :
      count {i : I | u i ≤ r} ≤ .ofReal (((1 + 2 * R / m) * r ^ 1) ^ finrank ℝ V) * 1 := by
    have h_ball (i : I) (hi : i ∈ {i : I | u i ≤ r}) : ‖f i‖ ≤ R * r := by grw [hu, hi.out]
    have h_radius : 1 + 2 * (R * r) / m ≤ (1 + 2 * R / m) * r := by grind
    grw [count_apply .of_discrete, mul_one, pow_one,
      encard_le_of_separated hm (by positivity) (hf.set_pairwise _) h_ball, h_radius]
  obtain ⟨h_int, h_le⟩ := DiscreteSeries.integral_rpow_neg_le_of_measure_le measurable_from_top
    hu_one
    (by positivity) ENNReal.one_ne_top h_count (by simpa using hA) (by simpa using hc)
  exact ⟨(integrable_count_iff.1 h_int).of_norm,
    by simpa [count, integral_sum_measure h_int] using h_le⟩

/-- Let points `f i` of a real normed space of finite dimension `d` have norms and mutual
distances at least `m > 0`. For a natural number `n ≥ d + 2`, `∑ ‖f i‖⁻¹ ^ n` converges and is
at most `(5/m) ^ n`. -/
lemma tsum_inv_pow_le_of_separated (hm : 0 < m) (hf : Pairwise fun i j : I ↦ m ≤ ‖f i - f j‖)
    (hf_ge : ∀ i : I, m ≤ ‖f i‖) {n : ℕ} (hn : finrank ℝ V + 2 ≤ n) :
    Summable (fun i : I ↦ ‖f i‖⁻¹ ^ n) ∧ ∑' i : I, ‖f i‖⁻¹ ^ n ≤ (5 / m) ^ n := by
  -- Take `u i = ‖f i‖ / m`, `R = m`, `A = n` and `c = 1 + n / 2` in `tsum_le_of_separated`.
  have hc : (n : ℝ) ≤ (1 + n * 2⁻¹) * (n - finrank ℝ V) := by
    nlinarith [show (finrank ℝ V : ℝ) + 2 ≤ n from mod_cast hn]
  obtain ⟨h_summable, h_le⟩ := tsum_le_of_separated (u := fun i ↦ m⁻¹ * ‖f i‖) hm hm.le hf
    (fun i ↦ (one_le_inv_mul₀ hm).2 (hf_ge i)) (fun i ↦ by simp [field]) (mod_cast by lia) hc
  have h_scale (i : I) : (m⁻¹ * ‖f i‖) ^ (-(n : ℝ)) = m ^ n * ‖f i‖⁻¹ ^ n := by
    simp [mul_pow, mul_comm]
  -- Pull `m ^ n` out of the sum; the factor `1 + 2 * m / m` is `1 + 2`.
  simp only [h_scale, tsum_mul_left, mul_div_cancel_right₀ _ hm.ne'] at h_summable h_le
  refine ⟨(summable_mul_left_iff (pow_ne_zero n hm.ne')).1 h_summable, ?_⟩
  rw [div_pow, le_div_iff₀' (by positivity)]
  -- Bernoulli's inequality gives `1 + n / 2 ≤ (3 / 2) ^ n`, and `3 * (3 / 2) ≤ 5`.
  calc m ^ n * ∑' i : I, ‖f i‖⁻¹ ^ n ≤ (1 + 2) ^ finrank ℝ V * (1 + n * 2⁻¹ : ℝ) := h_le
    _ ≤ (1 + 2) ^ n * (1 + 2⁻¹) ^ n := by
      grw [one_add_mul_le_pow (by norm_num) n, show finrank ℝ V ≤ n by lia]
      norm_num
    _ ≤ 5 ^ n := by grw [← mul_pow, show ((1 + 2) * (1 + 2⁻¹) : ℝ) ≤ 5 by norm_num]

end New

end Packing

/-! ## Sobolev trace inequality on an interval and at the corner of a cube -/

section SobolevChain

open MeasureTheory Function Set ENNReal Fintype Measure

/-- One-dimensional Sobolev trace inequality: let `g` take values in a real inner product space,
let `0 < ε ≤ 1`, and suppose that at every `t ∈ [0, ε]` it has a derivative of norm at most `b t`.
Then `‖g 0‖² ≤ ∫₀^ε (2/ε) (‖g t‖² + (b t)²) dt`. -/
lemma New.sobolev_trace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {g : ℝ → E}
    {b : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1)
    (h_deriv : ∀ t ∈ Icc 0 ε, ∃ c : E, HasDerivAt g c t ∧ ‖c‖ ≤ b t) :
    ‖g 0‖ₑ ^ 2 ≤ ∫⁻ t : ℝ in Icc 0 ε, ENNReal.ofReal (2 / ε * (‖g t‖ ^ 2 + b t ^ 2)) := by
  -- The function `φ t = ‖g t‖ ^ 2 * (t - ε) / ε` goes from `-‖g 0‖ ^ 2` to `0`, so `‖g 0‖ ^ 2`
  -- is at most the length of the image of `[0, ε]`, hence at most `∫ |φ'|`.
  choose! g' hg' norm_g'_le using h_deriv
  let φ (t : ℝ) : ℝ := ‖g t‖ ^ 2 * (t - ε) * ε⁻¹
  let φ' (t : ℝ) : ℝ := (2 * inner ℝ (g t) (g' t) * (t - ε) + ‖g t‖ ^ 2 * 1) * ε⁻¹
  have φ_deriv (t : ℝ) (ht : t ∈ Icc 0 ε) : HasDerivWithinAt φ (φ' t) (Icc 0 ε) t :=
    (((hg' t ht).norm_sq.mul ((hasDerivAt_id t).sub_const ε)).mul_const ε⁻¹).hasDerivWithinAt
  have φ'_le (t : ℝ) (ht : t ∈ Icc 0 ε) : |φ' t| ≤ 2 / ε * (‖g t‖ ^ 2 + b t ^ 2) := by
    -- Cauchy–Schwarz and `|t - ε| ≤ ε ≤ 1` bound the numerator; then `(u + v)² ≤ 2 (u² + v²)`.
    have numerator_le :
        |2 * inner ℝ (g t) (g' t) * (t - ε) + ‖g t‖ ^ 2| ≤ (‖g t‖ + ‖g' t‖) ^ 2 :=
      calc _ ≤ 2 * |inner ℝ (g t) (g' t)| * |t - ε| + ‖g t‖ ^ 2 :=
            (abs_add_le ..).trans (by simp [abs_mul])
        _ ≤ 2 * (‖g t‖ * ‖g' t‖) * 1 + ‖g t‖ ^ 2 := by
          grw [abs_real_inner_le_norm, show |t - ε| ≤ 1 by grind]
        _ ≤ (‖g t‖ + ‖g' t‖) ^ 2 := by nlinarith [sq_nonneg ‖g' t‖]
    calc |φ' t| = |2 * inner ℝ (g t) (g' t) * (t - ε) + ‖g t‖ ^ 2| / ε := by
          simp [φ', abs_mul, abs_of_pos hε, div_eq_mul_inv]
      _ ≤ 2 * (‖g t‖ ^ 2 + b t ^ 2) / ε := by grw [numerator_le, add_sq_le, norm_g'_le t ht]
      _ = 2 / ε * (‖g t‖ ^ 2 + b t ^ 2) := by ring
  calc ‖g 0‖ₑ ^ 2 = volume (Icc (φ 0) (φ ε)) := by simp [φ, hε.ne']
    _ ≤ volume (φ '' Icc 0 ε) :=
      measure_mono (intermediate_value_Icc hε.le (HasDerivWithinAt.continuousOn φ_deriv))
    _ ≤ ∫⁻ t in Icc 0 ε, .ofReal |φ' t| := by
      simpa using addHaar_image_le_lintegral_abs_det_fderiv volume measurableSet_Icc φ_deriv
    _ ≤ _ := setLIntegral_mono' measurableSet_Icc fun t ht ↦ ofReal_mono (φ'_le t ht)

/-- The trace inequality integrated over a parameter `ω` with a measure `σ`: let `g t ω` and the
`h l t ω`, for `l` in a finite type `L`, take values in `ℂ ^ I` and be measurable in `(t, ω)`, let
`0 < ε ≤ 1`, and suppose that, for almost all `ω`, the function `t ↦ g t ω` has at every point `t`
of `[0, ε]` a derivative of norm at most `Λ ∑ l, ‖h l t ω‖`. Then
`∫ ‖g 0 ω‖² dω ≤ ∫₀^ε (2/ε) (∫ ‖g t ω‖² dω + |L| Λ² ∑ l, ∫ ‖h l t ω‖² dω) dt`. -/
lemma New.lintegral_sobolev_trace {Ω I L : Type*} [MeasurableSpace Ω] {σ : Measure Ω} [SFinite σ]
    [Fintype L] [Fintype I] {g : ℝ → Ω → EuclideanSpace ℂ I}
    {h : L → ℝ → Ω → EuclideanSpace ℂ I} (hg : Measurable ↿g) (hh : ∀ l : L, Measurable ↿(h l))
    {ε Λ : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1)
    (h_deriv : ∀ᵐ ω : Ω ∂σ, ∀ t ∈ Icc 0 ε, ∃ c : EuclideanSpace ℂ I,
      HasDerivAt (fun s : ℝ ↦ g s ω) c t ∧ ‖c‖ ≤ ∑ l : L, Λ * ‖h l t ω‖) :
    ∫⁻ ω : Ω, ‖g 0 ω‖ₑ ^ 2 ∂σ ≤ ∫⁻ t : ℝ in Icc 0 ε, ENNReal.ofReal (2 / ε) *
      (∫⁻ ω : Ω, ‖g t ω‖ₑ ^ 2 ∂σ +
        ENNReal.ofReal (card L * Λ ^ 2) * ∑ l : L, ∫⁻ ω : Ω, ‖h l t ω‖ₑ ^ 2 ∂σ) := by
  have g_meas (t : ℝ) : Measurable (g t) := hg.comp measurable_prodMk_left
  have h_meas (l : L) (t : ℝ) : Measurable (h l t) := (hh l).comp measurable_prodMk_left
  calc ∫⁻ ω : Ω, ‖g 0 ω‖ₑ ^ 2 ∂σ
    _ ≤ ∫⁻ ω, (∫⁻ t in Icc 0 ε,
        .ofReal (2 / ε * (‖g t ω‖ ^ 2 + (∑ l, Λ * ‖h l t ω‖) ^ 2))) ∂σ :=
      lintegral_mono_ae (h_deriv.mono fun ω hω ↦ sobolev_trace hε hε_le hω)
    _ ≤ ∫⁻ t in Icc 0 ε, (∫⁻ ω,
        .ofReal (2 / ε * (‖g t ω‖ ^ 2 + card L * ∑ l, (Λ * ‖h l t ω‖) ^ 2)) ∂σ) := by
      grw [lintegral_lintegral_swap (by fun_prop), sq_sum_le_card_mul_sum_sq, Finset.card_univ]
    _ = _ := by
      -- Distribute the integral over `ω` over the sums.
      simp (disch := intros; first | positivity | fun_prop) [mul_pow, lintegral_finsetSum,
        ofReal_add, ofReal_sum_of_nonneg, Finset.mul_sum, mul_assoc]

/-- Sobolev trace at the corner of a cube. Let `D` and `L` be finite types and, for every word
(list) `i` in the alphabet `L`, let `f i x ω` be measurable in `x ∈ ℝ ^ D` and a parameter `ω`.
Let `0 < ε ≤ 1`. Assume that for almost all `ω` every partial derivative of `f i` on the cube
`[0, ε] ^ D` exists and has norm at most `Λ ∑ l, ‖f (l :: i)‖` (here `update x d t` is the point
`x` with its coordinate `d` changed to `t`), and that the integral of `‖f i‖²` over the cube and
`ω` is at most `K` for all words `i` of length at most `|D|`. Then, for the empty word `[]`,
`∫ ‖f [] 0 ω‖² dω ≤ (2 (1 + (|L| Λ)²) / ε) ^ |D| * K`. -/
lemma New.sobolev_trace_cube {Ω I L D : Type*} [MeasurableSpace Ω] {σ : Measure Ω} [SFinite σ]
    [Fintype L] [Fintype I] [Fintype D] [DecidableEq D]
    (f : List L → (D → ℝ) → Ω → EuclideanSpace ℂ I) (h_meas : ∀ i : List L, Measurable ↿(f i))
    {ε Λ : ℝ} {K : ℝ≥0∞} (hε : 0 < ε) (hε_le : ε ≤ 1)
    (h_deriv : ∀ᵐ ω : Ω ∂σ, ∀ (i : List L) (d : D) (x : D → ℝ) (t : ℝ),
      update x d t ∈ Icc 0 (fun _ : D ↦ ε) →
      ∃ f' : EuclideanSpace ℂ I,
        HasDerivAt (fun s : ℝ ↦ f i (update x d s) ω) f' t ∧
        ‖f'‖ ≤ ∑ l : L, Λ * ‖f (l :: i) (update x d t) ω‖)
    (h_cube : ∀ i : List L, i.length ≤ card D →
      ∫⁻ x : D → ℝ in Icc 0 fun _ : D ↦ ε, ∫⁻ ω : Ω, ‖f i x ω‖ₑ ^ 2 ∂σ ≤ K) :
    ∫⁻ ω : Ω, ‖f [] 0 ω‖ₑ ^ 2 ∂σ ≤
      ENNReal.ofReal ((2 / ε * (1 + (card L * Λ) ^ 2)) ^ card D) * K := by
  -- Remove the variable coordinates one at a time: induction on the set `s` of coordinates
  -- integrated over, the others being `0`. Each coordinate costs the factor `c` by
  -- `New.lintegral_sobolev_trace`.
  set c : ℝ := 2 / ε * (1 + (card L * Λ) ^ 2)
  let normSq (i : List L) (x : D → ℝ) : ℝ≥0∞ := ∫⁻ ω, ‖f i x ω‖ₑ ^ 2 ∂σ
  let μ (_ : D) : Measure ℝ := volume.restrict (Icc 0 ε)
  have normSq_meas (i : List L) : Measurable (normSq i) := by fun_prop
  let bound (i : List L) (d : D) (x : D → ℝ) : ℝ≥0∞ := ∫⁻ t, .ofReal (2 / ε) *
    (normSq i (update x d t) +
      .ofReal (card L * Λ ^ 2) * ∑ l, normSq (l :: i) (update x d t)) ∂μ d
  -- The trace inequality for the slice of `f i` through `x` in the direction `d`.
  have trace (i : List L) (d : D) (x : D → ℝ) (hx : x ∈ Icc 0 fun _ : D ↦ ε) (hxd : x d = 0) :
      normSq i x ≤ bound i d x := by
    have in_cube (t : ℝ) (ht : t ∈ Icc 0 ε) : update x d t ∈ Icc 0 fun _ : D ↦ ε :=
      ⟨le_update_iff.2 ⟨ht.1, fun j _ ↦ hx.1 j⟩, update_le_iff.2 ⟨ht.2, fun j _ ↦ hx.2 j⟩⟩
    have h_zero : update x d 0 = x := update_eq_self_iff.2 hxd.symm
    simpa [normSq, bound, μ, h_zero] using lintegral_sobolev_trace
      (g := fun t ↦ f i (update x d t)) (h := fun l t ↦ f (l :: i) (update x d t))
      (by fun_prop) (fun l ↦ by fun_prop) hε hε_le
      (h_deriv.mono fun ω hω t ht ↦ hω i d x t (in_cube t ht))
  -- `(∫⋯∫⁻_s, normSq i ∂μ) 0` integrates `normSq i` over the coordinates in `s`, the others
  -- being `0`.
  suffices h_induction : ∀ (s : Finset D) (M : ℝ≥0∞),
      (∀ i : List L, i.length ≤ s.card → (∫⋯∫⁻_s, normSq i ∂μ) 0 ≤ M) →
      normSq [] 0 ≤ .ofReal (c ^ s.card) * M by
    simp_rw [volume_pi, ← pi_univ_Icc, restrict_pi_pi, lintegral_eq_lmarginal_univ 0] at h_cube
    exact h_induction .univ K h_cube
  intro s
  induction s using Finset.induction with
  | empty => simp
  | insert d s hd_notMem ih =>
    intro M hM
    rw [s.card_insert_of_notMem hd_notMem] at hM ⊢
    rw [pow_succ, ofReal_mul (by positivity), mul_assoc]
    -- Apply the induction hypothesis with `c * M` in place of `M`; `hM` covers both `i` and the
    -- longer words `l :: i`.
    refine ih _ fun i hi ↦ ?_
    simp_rw [lmarginal_insert' _ (normSq_meas _) hd_notMem] at hM
    have slice_meas (j : List L) :
        Measurable fun y : s → ℝ ↦ ∫⁻ t, normSq j (update (updateFinset 0 s y) d t) ∂μ d :=
      ((normSq_meas j).comp measurable_update').lintegral_prod_right'.comp measurable_updateFinset
    calc (∫⋯∫⁻_s, normSq i ∂μ) 0
      _ ≤ (∫⋯∫⁻_s, bound i d ∂μ) 0 := by
        simp_rw [lmarginal, μ, ← restrict_pi_pi]
        refine setLIntegral_mono' (by measurability) fun y hy ↦ trace i d _ ?_ ?_
        · simp only [← pi_univ_Icc, mem_univ_pi] at hy ⊢
          intro j
          by_cases hj : j ∈ s <;> simp_all [updateFinset, hε.le]
        · simp [updateFinset, hd_notMem]
      _ = .ofReal (2 / ε) * ((∫⋯∫⁻_s, (fun x ↦ ∫⁻ t, normSq i (update x d t) ∂μ d) ∂μ) 0 +
          .ofReal (card L * Λ ^ 2) *
            ∑ l, (∫⋯∫⁻_s, (fun x ↦ ∫⁻ t, normSq (l :: i) (update x d t) ∂μ d) ∂μ) 0) := by
        simp (disch := intros; fun_prop) only [bound, lmarginal, lintegral_const_mul,
          lintegral_add_left, lintegral_finsetSum]
      _ ≤ .ofReal (2 / ε) * (M + .ofReal (card L * Λ ^ 2) * ∑ l : L, M) := by
        gcongr with l
        · exact hM i (by lia)
        · exact hM (l :: i) (by simpa)
      _ = .ofReal c * M := by simp (disch := positivity) [c, ofReal_add, ofReal_mul, mul_pow]; ring

end SobolevChain
