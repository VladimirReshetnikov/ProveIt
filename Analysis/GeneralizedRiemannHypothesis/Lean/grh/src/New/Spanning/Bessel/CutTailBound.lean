import New.Spanning.Bessel.LargeFunction

/-!
# The Bessel function at a real place: decay and cut

The file concerns Bessel functions (`New.IsBesselFunction`) on the real unitary group
G₁ = `New.Shape.G₁`: bounded functions to ℂ^I that transform on the left by a character of the
unipotent group 𝖴 = `New.Shape.Form.besselU` and by `rep` under H = U(κ). Throughout, p is a unitary
frame that diagonalises the form, c_λ = `New.HCParam.dsCoeffInFrame` is the discrete series
coefficient of a parameter l = 2λ with large gap (`New.HCParam.HasLargeGap`), v is a unit vector of
ℂ^I, and e = deg·c_λ with deg = `New.HCParam.formalDegree`. F is reproduced by e if F * e = F for
the convolution `New.convolve`: (F * e)(y) = ∫ e(a⁻¹) F(ya) da. The measure of 𝖴∖G₁ is
`New.besselQuotMeasure`. G₁ consists of r × r matrices with r = `𝔰.r`, ‖g‖ is the operator norm, and
n = `𝔰.n` = ϱ + 1 with ϱ the number of hyperbolic planes of the form.
* `New.exists_isDecayMajorant_besselAverage`: the normalised average of c_λ over the Bessel subgroup
  decays in the length, below a bounded integrable weight (`New.IsDecayMajorant`).
* `New.besselCut`: the cut of a function at length b^(6n+2); it is close to the function in L²
  (`New.IsDecayMajorant.lintegral_sq_besselCut_sub_le`).
* `New.exists_isCutPair_besselAverage`: a multiple of the average is reproduced by e and forms a cut
  pair (`New.IsCutPair`) with its cut.

Notions from other files:
* `New.besselLength`: for y in G₁, the infimum of ‖sy‖ + 1 over s in the Bessel subgroup S = 𝖴H
  (`New.Shape.Form.besselS`).
* `New.Shape.besselGraph`: the group 𝖴H as a graph, the pairs (g, k) in G₁ × U(κ) with k⁻¹g in 𝖴.
* `New.DiscreteSeries.besselAverage`: the function y ↦ ∫_S c_λ(x⁻¹ s y) π(s)⁻¹ v ds, where π is the
  character on 𝖴 and `rep` on H.
* `New.scaledBesselLength`: the larger of 1 and the length divided by b^(6n).

## Relation to the literature

A Bessel function at a real place, an average of a discrete series coefficient with a large period
integral, inherits the coefficient's decay. Normalised and multiplied by a scalar cut-off, it gives
a continuous approximant, close in L² and compactly supported modulo the unipotent group, with an
explicit tail bound. Related work: Muić, Fourier coefficients of automorphic forms and integrable
discrete series, 2015; Miličić, Asymptotic behavior of matrix coefficients of the discrete series,
1977; Wallach, Real Reductive Groups II, 1992.

See `New.Spanning.Bessel.FillingData` for related work.
-/

namespace New

open Matrix MeasureTheory ENNReal Norms.L2Operator Fintype CStarRing Set DiscreteSeries

variable {𝔰 : Shape} {I : Type} {ε : 𝔰.BesselIndex → ℤˣ} [Fintype I] [DecidableEq I]
  [p : UnitarySignFrame 𝔰 ε] {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {l : HCParam ε}
  {A L : ℕ}

/-- The frame is unitary, so passing to it by `frameEquiv` (g ↦ p⁻¹ g p) keeps the operator
norm. -/
lemma norm_frameEquiv (g : 𝔰.G₁) : ‖(DiscreteSeries.frameEquiv g).val.val‖ = ‖g.val.val‖ := by
  have hp : p.matrix.val ∈ unitary (Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) := p.mem_unitary
  simp [DiscreteSeries.frameEquiv, U.conj, inv_eq_left_inv (Unitary.star_mul_self_of_mem hp), hp,
    norm_mul_mem_unitary, norm_mem_unitary_mul]

/-- Let `G₁` be the unitary group of `r × r` matrices of the shape `𝔰`, and `l` a discrete series
parameter of gap `500 r ^ 3 + A`, with entries bounded by `L` and formal degree `deg`. For a natural
number `M > 8 r ^ 2`, `b ≥ 2000` and `r + L + 1 ≤ b ^ 4`, the integral of `deg * (2 / ‖g‖) ^ M`
(operator norm) over `g` in `G₁` is at most `b ^ (50 r ^ 2 + 1) * 2 ^ M`. -/
lemma lintegral_formalDegree_mul_decay_le (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) {b : ℝ} (hb_large : 2000 ≤ b)
    (hL_le : 𝔰.r + L + 1 ≤ b ^ 4) {M : ℕ} (hM : 8 * 𝔰.r ^ 2 < M) :
    ∫⁻ g : 𝔰.G₁, ENNReal.ofReal (l.formalDegree * (2 / ‖g.val.val‖) ^ M) ≤
      ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1) * 2 ^ M) := by
  -- Transport `integral_tail_le` to G₁ by the frame; then `8` and `2000` are at most `b`.
  have h_deg : 0 < l.formalDegree := formalDegree_pos h_gap
  have hb8 : 8 ≤ b := by linarith
  obtain ⟨h_int, h_le⟩ := integral_tail_le hL M hM
  calc _ = ∫⁻ g : USign ε, ENNReal.ofReal (l.formalDegree * (2 / ‖g.val.val‖) ^ M) := by
        simp_rw [← norm_frameEquiv]
        exact measurePreserving_frameEquiv.lintegral_comp
          (f := fun g ↦ .ofReal (l.formalDegree * (2 / ‖g.val.val‖) ^ M)) (by fun_prop)
    _ = ENNReal.ofReal (∫ g : USign ε, l.formalDegree * (2 / ‖g.val.val‖) ^ M) :=
        (ofReal_integral_eq_lintegral_ofReal h_int (.of_forall fun _ ↦ by positivity)).symm
    _ ≤ ENNReal.ofReal (b * (b * (b ^ 4) ^ 6) ^ (2 * 𝔰.r ^ 2) * 2 ^ M) := by
        grw [h_le, hL_le, hb_large, hb8]
    _ ≤ ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1) * 2 ^ M) := by
        simp only [← pow_mul, ← pow_succ']
        exact ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by lia)) (by positivity))

/-- Let `G₁` be the unitary group of `r × r` matrices of the shape `𝔰`, and `l` a discrete series
parameter of gap `500 r ^ 3 + A`, with entries bounded by `L` and formal degree `deg`. For
`M = 9 r ^ 2`, `b ≥ 2000` and `r + L + 1 ≤ b ^ 4`, the product of `deg`, the integral of
`(2 / ‖g‖) ^ M` (operator norm) over `g` in `G₁`, and `16 ^ M` is at most `b ^ (99 r ^ 2)`. -/
lemma formalDegree_mul_lintegral_decay_le (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) {b : ℝ} (hb_large : 2000 ≤ b)
    (hL_le : 𝔰.r + L + 1 ≤ b ^ 4) {M : ℕ} (hM : M = 9 * 𝔰.r ^ 2) :
    ENNReal.ofReal l.formalDegree * (∫⁻ g : 𝔰.G₁, ENNReal.ofReal ((2 / ‖g.val.val‖) ^ M)) *
        ENNReal.ofReal (16 ^ M) ≤
      ENNReal.ofReal (b ^ (99 * 𝔰.r ^ 2)) := by
  obtain ⟨hb1, hb2, hb16⟩ : 1 ≤ b ∧ 2 ≤ b ∧ 16 ≤ b := by bound
  have hr : 0 < 𝔰.r ^ 2 := by positivity
  calc _ ≤ ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1) * 2 ^ M) * ENNReal.ofReal (16 ^ M) := by
        grw [lintegral_const_mul_le]
        simp_rw [← ofReal_mul (formalDegree_pos h_gap).le]
        grw [lintegral_formalDegree_mul_decay_le h_gap hL hb_large hL_le (by lia)]
    _ ≤ ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1 + M + M)) := by
        grw [← ofReal_mul (by positivity), hb2, hb16, ← pow_add, ← pow_add]
    _ ≤ ENNReal.ofReal (b ^ (99 * 𝔰.r ^ 2)) :=
        ofReal_le_ofReal (pow_le_pow_right₀ hb1 (by lia))

/-- Let `G₁` be the unitary group of `r × r` matrices of the shape `𝔰`, and `l` a discrete series
parameter of gap `500 r ^ 3 + A`, with entries bounded by `L` and formal degree `deg`. If
`b ≥ 2000`, `r + L + 1 ≤ b ^ 4` and `T ≥ 1`, the set of `g` in `G₁` of operator norm at most `T` has
volume at most `T ^ (9 r ^ 2) * b ^ (99 r ^ 2) / deg`. -/
lemma formalDegree_mul_volume_ball_le (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) {b : ℝ}
    (hb_large : 2000 ≤ b) (hL_le : 𝔰.r + L + 1 ≤ b ^ 4) {T : ℝ} (hT : 1 ≤ T) :
    ENNReal.ofReal l.formalDegree * volume {g : 𝔰.G₁ | ‖g.val.val‖ ≤ T} ≤
      ENNReal.ofReal (T ^ (9 * 𝔰.r ^ 2) * b ^ (99 * 𝔰.r ^ 2)) := by
  -- Chebyshev's inequality with `M = 9 r ^ 2`: on the ball `deg ≤ (T / 2) ^ M * φ g` for
  -- `φ g = deg * (2 / ‖g‖) ^ M`.
  have hb1 : 1 ≤ b := by linarith
  have hr : 0 < 𝔰.r ^ 2 := by positivity
  have h_deg : 0 < l.formalDegree := formalDegree_pos h_gap
  let M : ℕ := 9 * 𝔰.r ^ 2
  let φ (g : 𝔰.G₁) : ℝ≥0∞ := .ofReal (l.formalDegree * (2 / ‖g.val.val‖) ^ M)
  have h_tail : ∫⁻ g : 𝔰.G₁, φ g ≤ .ofReal (b ^ (99 * 𝔰.r ^ 2) * 2 ^ M) := by
    grw [lintegral_formalDegree_mul_decay_le h_gap hL hb_large hL_le (by lia),
      show 50 * 𝔰.r ^ 2 + 1 ≤ 99 * 𝔰.r ^ 2 by lia]
  have h_point (g : 𝔰.G₁) (hg_mem : g ∈ {g : 𝔰.G₁ | ‖g.val.val‖ ≤ T}) :
      .ofReal l.formalDegree ≤ .ofReal ((T / 2) ^ M) * φ g := by
    grw [← ofReal_mul (by positivity), mul_left_comm, ← mul_pow,
      div_mul_div_cancel₀ two_ne_zero, ← (one_le_div (one_pos.trans_le (U.one_le_norm g))).2 hg_mem,
      one_pow, mul_one]
  calc _ ≤ ∫⁻ g : 𝔰.G₁, .ofReal ((T / 2) ^ M) * φ g := by
        grw [← setLIntegral_const, setLIntegral_mono (by fun_prop) h_point,
          setLIntegral_le_lintegral]
    _ ≤ .ofReal ((T / 2) ^ M) * .ofReal (b ^ (99 * 𝔰.r ^ 2) * 2 ^ M) := by
        grw [lintegral_const_mul' _ _ ofReal_ne_top, h_tail]
    _ = ENNReal.ofReal (T ^ M * b ^ (99 * 𝔰.r ^ 2)) := by
        rw [← ofReal_mul (by positivity), mul_left_comm, ← mul_pow,
          div_mul_cancel₀ _ two_ne_zero, mul_comm]

/-- Let `s` be in the Bessel subgroup 𝖴H of `G₁` (the first component of a pair in `besselGraph`).
If `b ≥ 2` and the length `besselLength x` is at most `b ^ (5 n)`, with `n = ϱ + 1`, then the length
of `y` divided by `b ^ (6 n)` is at most `‖x⁻¹ s y‖ / 2`. -/
lemma besselLength_div_le_half_norm {b : ℝ} {x : 𝔰.G₁} (hb : 2 ≤ b)
    (hx : besselLength x ≤ b ^ (5 * 𝔰.n)) (s : 𝔰.besselGraph) (y : 𝔰.G₁) :
    besselLength y / b ^ (6 * 𝔰.n) ≤ ‖(x⁻¹ * (s.val.fst * y)).val.val‖ / 2 := by
  have h_pow : b ^ (5 * 𝔰.n + 1) ≤ b ^ (6 * 𝔰.n) := pow_le_pow_right₀ (by linarith) (by lia)
  set g : 𝔰.G₁ := x⁻¹ * (s.val.fst * y)
  rw [div_le_div_iff₀ (by positivity) two_pos]
  calc _ = besselLength (s.val.fst * y) * 2 := by
        rw [besselLength_besselS_mul (besselGraph_fst_mem_besselS s)]
    _ ≤ ‖g.val.val‖ * b ^ (5 * 𝔰.n) * b := by
      grw [besselLength_le_norm_inv_mul_mul_besselLength x, hx, hb]
    _ ≤ ‖g.val.val‖ * b ^ (6 * 𝔰.n) := by grw [mul_assoc, ← pow_succ, h_pow]

/-- Decay of `W = besselAverage l rep x v`, the average `W y = ∫ c_λ(x⁻¹ s y) π(s)⁻¹ v ds` of the
discrete series coefficient of `l = 2λ` over the Bessel subgroup 𝖴H of `G₁`, where π is a character
on 𝖴 and `rep` on H = U(κ). The integrals run over `besselGraph`, the pairs `(s, k)` of an element
`s` of 𝖴H and its component `k` in H. Let `r` be the size of the matrices of `G₁` and `n = ϱ + 1`.
Suppose `l` has gap `500 r ^ 3 + A`, `v` is a unit vector, `b ≥ 2`, `besselLength x ≤ b ^ (5 n)` and
`i ≤ A`. Then `‖W y‖` times the `i`-th power of `max 1 (besselLength y / b ^ (6 n))` (this is
`scaledBesselLength y b`) is at most `∫ (2 / ‖x⁻¹ s y‖) ^ (9 r ^ 2) ds`. -/
lemma scaledBesselLength_pow_mul_enorm_besselAverage_le (h_gap : l.HasLargeGap A) {b : ℝ} {x : 𝔰.G₁}
    {v : EuclideanSpace ℂ I} (hv : ‖v‖ = 1) (hb : 2 ≤ b) (hx : besselLength x ≤ b ^ (5 * 𝔰.n))
    {i : ℕ} (hi : i ≤ A) (y : 𝔰.G₁) :
    ENNReal.ofReal (scaledBesselLength y b ^ i) * ‖besselAverage l rep x v y‖ₑ ≤
      ∫⁻ s : 𝔰.besselGraph,
        ENNReal.ofReal ((2 / ‖(x⁻¹ * (s.val.fst * y)).val.val‖) ^ (9 * 𝔰.r ^ 2))
        ∂𝔰.besselGraphMeasure := by
  grw [enorm_besselAverage_le x hv, lintegral_const_mul_le]
  refine lintegral_mono fun s ↦ ?_
  set g : 𝔰.G₁ := x⁻¹ * (s.val.fst * y)
  have h_decay (j : ℕ) (hj : j ≤ A) :
      ‖l.dsCoeffInFrame g‖ ≤ (2 / ‖g.val.val‖) ^ j * (2 / ‖g.val.val‖) ^ (9 * 𝔰.r ^ 2) := by
    rw [← pow_add, ← norm_frameEquiv g]
    exact norm_dsCoeffInFrame_le h_gap hj g
  -- The length of `y` is that of `x g`, at most `‖g‖ b ^ (5 n) ≤ ‖g‖ b ^ (6 n) / 2`.
  have h_size : besselLength y / b ^ (6 * 𝔰.n) ≤ ‖g.val.val‖ / 2 :=
    besselLength_div_le_half_norm hb hx s y
  rw [← ofReal_norm, ← ofReal_mul (pow_nonneg (zero_le_one.trans (one_le_scaledBesselLength ..)) i)]
  refine ofReal_le_ofReal ?_
  obtain h_small | h_large := le_total (besselLength y / b ^ (6 * 𝔰.n)) 1
  · simpa [scaledBesselLength, h_small] using h_decay 0 (Nat.zero_le A)
  · grw [scaledBesselLength, max_eq_right h_large, h_size, h_decay i hi, ← mul_assoc, ← mul_pow]
    simp [(one_pos.trans_le (U.one_le_norm g)).ne']

/-- A Bessel function `Y` for `rep` is a bounded measurable function with `Y (n y) = ψ(n) Y y` for
`n` in `besselU` and `Y (h y) = rep h (Y y)` for `h` in `U(κ)`. If such `Y` is continuous, and `a`
is a continuous real function with `|a y| ≤ K` that is left invariant under the Bessel subgroup
`besselS`, then `a • Y` is a Bessel function for `rep`. -/
lemma IsBesselFunction.smul_of_invariant {Y : 𝔰.G₁ → EuclideanSpace ℂ I}
    (hY : IsBesselFunction rep Y) (hY_cont : Continuous Y)
    {a : 𝔰.G₁ → ℝ} (ha_cont : Continuous a) {K : ℝ} (ha_le : ∀ y : 𝔰.G₁, |a y| ≤ K)
    (ha_inv : ∀ s ∈ besselS, ∀ y : 𝔰.G₁, a (s * y) = a y) :
    IsBesselFunction rep fun y : 𝔰.G₁ ↦ a y • Y y := by
  obtain ⟨K', hK'⟩ := hY.bounded
  have h_bound (y : 𝔰.G₁) : ‖a y • Y y‖ ≤ K * K' := by
    grw [norm_smul, Real.norm_eq_abs, ha_le, hK']
    exact (abs_nonneg _).trans (ha_le y)
  refine ⟨.of_continuous ⟨K * K', h_bound⟩, fun s hs y ↦ ?_, fun h y ↦ ?_⟩
  · rw [ha_inv s (mem_partialUnitriangularGroup_of_mem_besselU hs), hY.map_unipotent_mul s hs,
    smul_comm]
  · simp [ha_inv (RealPlace.embedH h) (mem_partialUnitriangularGroup_of_mem_floorGroup
    (toBesselH_mem _)),
      hY.map_unitary_mul]

/-- A finite nonzero `q` can be scaled to any natural number by the square of a real number. -/
lemma exists_enorm_sq_mul_eq {q : ℝ≥0∞} (hq_ne : q ≠ 0) (hq_fin : q ≠ ⊤) (k : ℕ) :
    ∃ c : ℝ, ‖c‖ₑ ^ 2 * q = k := by
  have hq_pos : 0 < q.toReal := toReal_pos hq_ne hq_fin
  use √(k / q.toReal)
  rw [← ofReal_norm, ← ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity), ofReal_div_of_pos hq_pos, ofReal_natCast, ofReal_toReal hq_fin,
    ENNReal.div_mul_cancel hq_ne hq_fin]

/-- The cutoff of radius `R > 0`: it is `1` up to `R / 2`, `0` from `R` on, and linear in
between. -/
noncomputable def besselCutoff (R t : ℝ) : ℝ := max 0 (min 1 (2 - 2 * t / R))

lemma besselCutoff_mem_Icc (R t : ℝ) : besselCutoff R t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left .., max_le zero_le_one (min_le_left ..)⟩

lemma besselCutoff_eq_one {R t : ℝ} (hR : 0 < R) (ht : t ≤ R / 2) : besselCutoff R t = 1 := by
  have h_le : 2 * t / R ≤ 1 := (div_le_one hR).2 (by linarith)
  rw [besselCutoff, min_eq_left (by linarith), max_eq_right zero_le_one]

lemma besselCutoff_eq_zero {R t : ℝ} (hR : 0 < R) (ht : R ≤ t) : besselCutoff R t = 0 := by
  have h_ge : 2 ≤ 2 * t / R := (le_div_iff₀ hR).2 (by linarith)
  exact max_eq_left (min_le_of_right_le (by linarith))

/-- The cut `F♭` of `F`: the product of `F y` with the cutoff of radius `b ^ (6 n + 2)` evaluated at
the length `besselLength y`, where `n = ϱ + 1`. -/
noncomputable def besselCut (b : ℝ) (F : C(𝔰.G₁, EuclideanSpace ℂ I)) :
    C(𝔰.G₁, EuclideanSpace ℂ I) where
  toFun y := besselCutoff (b ^ (6 * 𝔰.n + 2)) (besselLength y) • F y
  continuous_toFun := by fun_prop [besselCutoff]

section Cut

variable {b : ℝ} {F : C(𝔰.G₁, EuclideanSpace ℂ I)}

section

omit [DecidableEq I]

lemma besselCut_apply (y : 𝔰.G₁) :
    besselCut b F y = besselCutoff (b ^ (6 * 𝔰.n + 2)) (besselLength y) • F y := rfl

/-- `besselCut b F y` is `F y` multiplied by a number in `[0, 1]`, so its norm is at most
`‖F y‖`. -/
lemma enorm_besselCut_le (y : 𝔰.G₁) : ‖besselCut b F y‖ₑ ≤ ‖F y‖ₑ := by
  obtain ⟨h_nonneg, h_le⟩ := besselCutoff_mem_Icc (b ^ (6 * 𝔰.n + 2)) (besselLength y)
  rw [besselCut_apply, enorm_le_iff_norm_le, norm_smul, Real.norm_of_nonneg h_nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) h_le

/-- `besselCut b F y` is `F y` multiplied by a number in `[0, 1]` (a cutoff evaluated at
`besselLength y`), so it differs from `F y` by at most `‖F y‖`. -/
lemma enorm_besselCut_sub_le (y : 𝔰.G₁) : ‖besselCut b F y - F y‖ₑ ≤ ‖F y‖ₑ := by
  obtain ⟨h_nonneg, h_le⟩ := besselCutoff_mem_Icc (b ^ (6 * 𝔰.n + 2)) (besselLength y)
  nth_rw 1 [← one_smul ℝ (F y)]
  rw [besselCut_apply, ← sub_smul, enorm_le_iff_norm_le, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.2 ⟨by linarith, by linarith⟩)

/-- Where the cut of `F` is nonzero, the length is at most `b ^ (6 n + 2)` (`InCut`). -/
lemma inCut_of_besselCut_ne_zero (hb : 0 < b) {y : 𝔰.G₁} (hy : besselCut b F y ≠ 0) :
    InCut y b := by
  contrapose! hy with h_large
  rw [besselCut_apply, besselCutoff_eq_zero (by positivity) h_large.le, zero_smul]

/-- Where the cut of `F` differs from `F`, the length exceeds `b ^ (6 n + 2) / 2`. -/
lemma lt_besselLength_of_besselCut_ne (hb : 0 < b) {y : 𝔰.G₁} (hy : besselCut b F y ≠ F y) :
    b ^ (6 * 𝔰.n + 2) / 2 < besselLength y := by
  contrapose! hy with h_small
  rw [besselCut_apply, besselCutoff_eq_one (by positivity) h_small, one_smul]

end

/-- The cut of a continuous Bessel function is a Bessel function, as the length is left invariant
under `besselS`. -/
lemma IsBesselFunction.besselCut (hF : IsBesselFunction rep F) :
    IsBesselFunction rep (besselCut b F) := by
  exact hF.smul_of_invariant F.continuous (by fun_prop [besselCutoff]) (K := 1)
    (fun y ↦ by simp [besselCutoff, abs_le]) fun s hs y ↦ by rw [besselLength_besselS_mul hs]

omit [DecidableEq I] in
/-- Let `F♭ = besselCut b F` be the product of `F : G₁ → ℂ^I` with a cutoff of the length
`besselLength` that is `1` up to `b ^ (6 n + 2) / 2`, where `n = ϱ + 1`, and let `r` be the size of
the matrices of `G₁`. Let `w ≤ a` be a decay majorant (`IsDecayMajorant`) of the pair `F`, `F♭`
(formed by `FullOrCut.select`): `‖F y‖` and `‖F♭ y‖`, each multiplied by
`max 1 (besselLength y / b ^ (6 n)) ^ (3 r ^ 3 f)`, are at most `w y`, and `a ∫ w` is at most
`b ^ (400 r ^ 2) * card I`. If `b ≥ 2`, `r ≥ 100` and `f ≠ 0`, then `‖F♭ - F‖₂ ^ 2` is at most
`b ^ (-2 r ^ 3 f) * card I`. The integrals are over 𝖴∖G₁. -/
lemma IsDecayMajorant.lintegral_sq_besselCut_sub_le {f : ℕ} [NeZero f] {w : 𝔰.G₁ → ℝ≥0∞}
    {a : ℝ≥0∞} (hw : IsDecayMajorant b f (FullOrCut.select F (besselCut b F)) w a)
    (hb : 2 ≤ b) (hr : 100 ≤ 𝔰.r) :
    ∫⁻ y : 𝔰.G₁, ‖besselCut b F y - F y‖ₑ ^ 2 ∂besselQuotMeasure ≤
      .ofReal (b⁻¹ ^ (𝔰.r ^ 3 * f)) ^ 2 * card I := by
  -- Where the cut acts the scaled length is at least `b`, so `b ^ (3 r ^ 3 f) ‖F♭ - F‖ ≤ w ≤ a`.
  -- Multiply the two bounds and integrate.
  have h_point (y : 𝔰.G₁) :
      .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2 * ‖besselCut b F y - F y‖ₑ ^ 2 ≤ a * w y := by
    obtain h_eq | h_ne := eq_or_ne (besselCut b F y) (F y)
    · simp [h_eq]
    have h_gain : .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) * ‖besselCut b F y - F y‖ₑ ≤ w y := by
      grw [enorm_besselCut_sub_le,
        le_scaledBesselLength hb (lt_besselLength_of_besselCut_ne (by positivity) h_ne)]
      exact hw.pow_mul_enorm_le .full y
    rw [← mul_pow, sq]
    exact mul_le_mul' (h_gain.trans (hw.le_bound y)) h_gain
  -- Exponents: `400 r ^ 2 + 2 r ^ 3 f ≤ 6 r ^ 3 f`, as `100 r ^ 2 ≤ r ^ 3 ≤ r ^ 3 f`.
  have h_exponent : 100 * 𝔰.r ^ 2 ≤ 𝔰.r ^ 3 * f := by
    grw [hr, ← pow_succ']
    exact Nat.le_mul_of_pos_right _ (NeZero.pos f)
  have h_power : b ^ (400 * 𝔰.r ^ 2) ≤ (b ^ (3 * 𝔰.r ^ 3 * f) * b⁻¹ ^ (𝔰.r ^ 3 * f)) ^ 2 := by
    simp only [inv_pow, fieldLe, ← pow_mul, ← pow_add] -- clears the negative power
    exact pow_le_pow_right₀ (by linarith) (by linarith)
  rw [← ENNReal.mul_le_mul_iff_right (a := .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2) (by positivity)
    (pow_ne_top ofReal_ne_top)]
  calc .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2 * ∫⁻ y, ‖besselCut b F y - F y‖ₑ ^ 2 ∂besselQuotMeasure
      ≤ ∫⁻ y, a * w y ∂besselQuotMeasure :=
        (lintegral_const_mul_le ..).trans (lintegral_mono h_point)
    _ ≤ .ofReal (b ^ (400 * 𝔰.r ^ 2)) * card I :=
        (lintegral_const_mul _ hw.measurable).trans_le hw.bound_mul_lintegral_le
    _ ≤ .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2 * (.ofReal (b⁻¹ ^ (𝔰.r ^ 3 * f)) ^ 2 * card I) := by
        grw [h_power, ofReal_pow (by positivity), ofReal_mul (by positivity), mul_pow, mul_assoc]

end Cut

/-- For `t` in the Bessel subgroup `besselS`, the integral of `φ (x⁻¹ s y)` over `s` in that
subgroup does not change when `y` is replaced by `t y`, as the measure on `besselGraph` is right
invariant. -/
lemma lintegral_besselGraph_mul_eq {x : 𝔰.G₁} (φ : 𝔰.G₁ → ℝ≥0∞) {t : 𝔰.G₁} (ht : t ∈ besselS)
    (y : 𝔰.G₁) :
    ∫⁻ s : 𝔰.besselGraph, φ (x⁻¹ * (s.val.fst * (t * y))) ∂𝔰.besselGraphMeasure =
      ∫⁻ s : 𝔰.besselGraph, φ (x⁻¹ * (s.val.fst * y)) ∂𝔰.besselGraphMeasure := by
  obtain ⟨u, hu, k, rfl⟩ := exists_besselU_mul_toBesselH ht isUnit_one
  have h_mem : (u * toBesselH 𝔰 1 k, k) ∈ 𝔰.besselGraph :=
    Shape.mem_besselGraph_iff_mul_inv_mem.2 (by simpa using hu)
  simpa [mul_assoc] using lintegral_mul_right_eq_self (μ := 𝔰.besselGraphMeasure)
    (fun s ↦ φ (x⁻¹ * (s.val.fst * y))) ⟨_, h_mem⟩

/-- Let `r` be the size of the matrices of `G₁`, `n = ϱ + 1`, and `l = 2λ` a discrete series
parameter of gap `500 r ^ 3 + A`, with entries bounded by `L` and formal degree `deg`. Let
`W = besselAverage l rep x v` be the average of its coefficient `c_λ` over the Bessel subgroup 𝖴H at
a unit vector `v` and a point `x` with `besselLength x ≤ b ^ (5 n)`. Suppose that
`b ^ m * deg * ‖W‖₂ ^ 2` is at least `besselBallVolume x` (the volume of the `s` in 𝖴H with
`‖x⁻¹ s x - 1‖ ≤ 1`), that `F = c W` has `‖F‖₂ ^ 2 = card I`, and that `b ≥ 2000`,
`r + L + 1 ≤ b ^ 4`, `m ≤ 301 r ^ 2` and `3 r ^ 3 f ≤ A`. Then `F` and its cut `F♭ = besselCut b F`
have a decay majorant (`IsDecayMajorant`): a left 𝖴H-invariant function `w ≤ a < ∞` such that
`‖F y‖` and `‖F♭ y‖`, each multiplied by `max 1 (besselLength y / b ^ (6 n)) ^ (3 r ^ 3 f)`, are at
most `w y`, and `a ∫ w ≤ b ^ (400 r ^ 2) * card I`. -/
lemma exists_isDecayMajorant_besselAverage {f m : ℕ} {b : ℝ} {x : 𝔰.G₁} {v : EuclideanSpace ℂ I}
    (h_gap : l.HasLargeGap A) (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) (hv : ‖v‖ = 1)
    (h_volume : besselBallVolume (ε := ε) x ≤ ENNReal.ofReal (b ^ m) *
      (ENNReal.ofReal l.formalDegree *
        ∫⁻ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure))
    (hx : besselLength x ≤ b ^ (5 * 𝔰.n)) (hb_large : 2000 ≤ b)
    (hm : m + 99 * 𝔰.r ^ 2 ≤ 400 * 𝔰.r ^ 2) (hL_le : 𝔰.r + L + 1 ≤ b ^ 4)
    (hf : 3 * 𝔰.r ^ 3 * f ≤ A) {c : ℝ} {F : C(𝔰.G₁, EuclideanSpace ℂ I)}
    (hF : ∀ y : 𝔰.G₁, F y = c • besselAverage l rep x v y)
    (hc : ‖c‖ₑ ^ 2 * ∫⁻ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure = card I) :
    ∃ (w : 𝔰.G₁ → ℝ≥0∞) (a : ℝ≥0∞),
      IsDecayMajorant b f (FullOrCut.select F (besselCut b F)) w a := by
  -- With `φ g = (2 / ‖g‖) ^ M` and `Φ y = ∫ φ (x⁻¹ s y) ds`, the majorant is `|c| Φ`. It is bounded
  -- by `lintegral_decay_le_besselBallVolume`, and unfolding gives its integral; the volume of the
  -- ball cancels against the norm of `W`.
  obtain ⟨hb_one, hb_two⟩ : 1 ≤ b ∧ 2 ≤ b := ⟨by linarith, by linarith⟩
  let M : ℕ := 9 * 𝔰.r ^ 2
  let φ (g : 𝔰.G₁) : ℝ≥0∞ := .ofReal ((2 / ‖g.val.val‖) ^ M)
  let Φ (y : 𝔰.G₁) : ℝ≥0∞ := ∫⁻ s, φ (x⁻¹ * (s.val.fst * y)) ∂𝔰.besselGraphMeasure
  let a : ℝ≥0∞ := ‖c‖ₑ * (.ofReal (16 ^ M) * besselBallVolume (ε := ε) x)
  have h_decay (y : 𝔰.G₁) :
      .ofReal (scaledBesselLength y b ^ (3 * 𝔰.r ^ 3 * f)) * ‖F y‖ₑ ≤ ‖c‖ₑ * Φ y := by
    grw [hF, enorm_smul, mul_left_comm,
      scaledBesselLength_pow_mul_enorm_besselAverage_le h_gap hv hb_two hx hf]
  have h_bound (y : 𝔰.G₁) : Φ y ≤ .ofReal (16 ^ M) * besselBallVolume (ε := ε) x := by
    simpa only [norm_frameEquiv] using lintegral_decay_le_besselBallVolume x y
  have h_integral : a * ∫⁻ y, ‖c‖ₑ * Φ y ∂besselQuotMeasure ≤
      .ofReal (b ^ (400 * 𝔰.r ^ 2)) * card I :=
    calc _ = ‖c‖ₑ ^ 2 * (.ofReal (16 ^ M) * besselBallVolume (ε := ε) x) * ∫⁻ g, φ g := by
          rw [lintegral_const_mul' _ _ enorm_ne_top,
            lintegral_unfold_besselGraphMeasure (x := x⁻¹) φ (by fun_prop)]
          simp only [a]
          ring
      _ ≤ .ofReal (b ^ m) * (.ofReal l.formalDegree * (∫⁻ g, φ g) * .ofReal (16 ^ M)) *
            (‖c‖ₑ ^ 2 * ∫⁻ y, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure) := by
          grw [h_volume]
          exact le_of_eq (by ring)
      _ ≤ .ofReal (b ^ (400 * 𝔰.r ^ 2)) * card I := by
          grw [hc, formalDegree_mul_lintegral_decay_le h_gap hL hb_large hL_le rfl,
            ← ofReal_mul (by positivity), ← pow_add, hm]
  exact ⟨fun y ↦ ‖c‖ₑ * Φ y, a,
    { measurable := by fun_prop
      fixesLeft s hs y := congrArg (‖c‖ₑ * ·) (lintegral_besselGraph_mul_eq φ hs y)
      pow_mul_enorm_le
        | .full, y => h_decay y
        | .cut, y => (mul_le_mul_right (enorm_besselCut_le y) _).trans (h_decay y)
      le_bound y := mul_le_mul_right (h_bound y) _
      bound_ne_top := by finiteness [besselBallVolume_ne_top (ε := ε) x]
      bound_mul_lintegral_le := h_integral }⟩

/-- The Bessel function and its cut. Fix a unitary matrix that takes the form of G₁ to the diagonal
form with signs `ε` (the instance `UnitarySignFrame 𝔰 ε`). Let `l = 2λ` be a parameter for `ε` of
gap `500 r ^ 3 + A` with entries bounded by `L`. Let `c_λ = l.dsCoeffInFrame` be its discrete series
coefficient in this frame, and `deg = l.formalDegree`. Let `rep` be a continuous unitary
representation of U(κ) on ℂ^I, where κ indexes the summand X₀. Let `W = besselAverage l rep x v` be
the average of `c_λ` over the Bessel subgroup at a unit vector `v` and a point `x` with
`besselLength x ≤ b ^ (5 n)`. Assume `deg ‖W‖₂ ^ 2` is at least `b ^ (-m)` times
`besselBallVolume x`. Suppose `b ≥ 2000`, `r + L + 1 ≤ b ^ 4`, `r ≥ 100`, `f ≠ 0`, `m ≤ 301 r ^ 2`
and `3 r ^ 3 f ≤ A`. Then a real multiple `F` of `W` is fixed by convolution with `deg * c_λ`. It
also forms a cut pair with its cut `besselCut b F`. Here `IsCutPair` means Bessel functions, the
first normalised, close in L², with a decay majorant. Here `r` is the size of the matrices of G₁,
`n = ϱ + 1` with ϱ the number of hyperbolic planes, and `‖·‖₂` is the norm of L²(𝖴∖G₁), 𝖴 the Bessel
unipotent group. -/
lemma exists_isCutPair_besselAverage {m : ℕ} {b : ℝ} {x : 𝔰.G₁} {v : EuclideanSpace ℂ I}
    (h_gap : l.HasLargeGap A) (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) (f : ℕ) [NeZero f]
    (h_cont : Continuous rep) (hv : ‖v‖ = 1)
    (h_volume : besselBallVolume (ε := ε) x ≤ ENNReal.ofReal (b ^ m) *
      (ENNReal.ofReal l.formalDegree *
        ∫⁻ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure))
    (hx : besselLength x ≤ b ^ (5 * 𝔰.n)) (hb_large : 2000 ≤ b) (hr : 100 ≤ 𝔰.r)
    (hm : m + 99 * 𝔰.r ^ 2 ≤ 400 * 𝔰.r ^ 2) (hL_le : 𝔰.r + L + 1 ≤ b ^ 4)
    (hf : 3 * 𝔰.r ^ 3 * f ≤ A) :
    ∃ (c : ℝ) (F : C(𝔰.G₁, EuclideanSpace ℂ I)),
      (∀ y : 𝔰.G₁, F y = c • besselAverage l rep x v y) ∧
      convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F ∧
      IsCutPair b f rep (FullOrCut.select F (besselCut b F)) := by
  set W : 𝔰.G₁ → EuclideanSpace ℂ I := besselAverage l rep x v
  set e : 𝔰.G₁ → ℂ := fun g ↦ l.formalDegree * l.dsCoeffInFrame g
  have hW : IsBesselFunction rep W := isBesselFunction_besselAverage x h_cont hv h_gap
  have h_repr : convolve W e = W := convolve_besselAverage x h_cont hv h_gap
  have hW_cont : Continuous W := by
    rw [← h_repr]
    exact hW.continuous_convolve (isIdempotentKernel_dsCoeffInFrame h_gap).integrable
  have hW_int : Integrable W besselQuotMeasure := integrable_besselAverage x h_cont hv h_gap
  -- Normalisation: `W` is not zero in L², because the ball has positive volume.
  have h_ne_zero : ∫⁻ y, ‖W y‖ₑ ^ 2 ∂besselQuotMeasure ≠ 0 :=
    fun h ↦ besselBallVolume_ne_zero x (by simpa [h] using h_volume)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ‖c‖ₑ ^ 2 * ∫⁻ y, ‖W y‖ₑ ^ 2 ∂besselQuotMeasure = card I :=
    exists_enorm_sq_mul_eq h_ne_zero
      ((lintegral_enorm_sq hW_int hW.memLp_top).trans_ne ofReal_ne_top) (card I)
  let F : C(𝔰.G₁, EuclideanSpace ℂ I) := .mk fun y ↦ c • W y
  have hF : IsBesselFunction rep F :=
    hW.smul_of_invariant hW_cont continuous_const (K := |c|) (fun _ ↦ le_rfl) fun _ _ _ ↦ rfl
  have hF_norm : ∫⁻ y, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure = card I := by
    simp [F, enorm_smul, mul_pow, lintegral_const_mul', ← hc]
  have hF_repr : convolve F e = F := by
    funext y
    calc convolve F e y = c • convolve W e y := by
          simp [F, convolve, smul_comm _ c, integral_smul]
      _ = c • W y := by rw [h_repr]
  obtain ⟨w, a, hw⟩ : ∃ (w : 𝔰.G₁ → ℝ≥0∞) (a : ℝ≥0∞),
      IsDecayMajorant b f (FullOrCut.select F (besselCut b F)) w a :=
    exists_isDecayMajorant_besselAverage h_gap hL hv h_volume hx hb_large hm hL_le hf
      (fun _ ↦ rfl) hc
  exact ⟨c, F, fun _ ↦ rfl, hF_repr,
    { isBesselFunction
        | .full => hF
        | .cut => hF.besselCut
      integrable := hW_int.smul c
      lintegral_sq_full_eq := hF_norm
      lintegral_sq_cut_le :=
        (lintegral_mono fun y ↦ pow_le_pow_left' (enorm_besselCut_le y) 2).trans_eq hF_norm
      inCut_of_ne_zero y := inCut_of_besselCut_ne_zero (by positivity)
      lintegral_sq_sub_le := hw.lintegral_sq_besselCut_sub_le (by linarith) hr
      lt_besselLength_of_ne y := lt_besselLength_of_besselCut_ne (by positivity)
      exists_majorant := ⟨w, a, hw⟩ }⟩

end New
