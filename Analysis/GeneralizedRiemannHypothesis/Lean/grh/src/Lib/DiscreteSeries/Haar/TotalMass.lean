import Lib.Adelic.Witt.WittTheorem
import Lib.DiscreteSeries.Haar.GramPolar
import Lib.General.Analysis.PackingAndSobolev

/-!
# Haar measure on U(J): U(n) has mass one, covering bounds for norm balls

The measure `volume` on `U J` is the compact dual measure `New.haarU J`, normalised by
`New.volU n = ∏ i < n, 2 π ^ (i + 1) / i!`, the product of the areas of the unit spheres of
`ℂ, …, ℂ ^ n`. The first part shows that U(n) has mass one, by computing the image of Lebesgue
measure under the Gram map in two ways. For the second part let `J` be a hermitian involution of
size `n`, `j : S →* U J` a proper homomorphism, and `ν` a right invariant measure on `S` that is
finite on compact sets. Then norm balls are compared by a covering argument, with operator norms
throughout.

## Main definitions and results

* `New.exists_hasGramDensity`: near the identity, the image of Lebesgue measure under the
  Gram map `Y ↦ Yᴴ Y` of square matrices is `volU n / 2 ^ n` times Lebesgue measure. One column
  ranges over a sphere, and the parts of the other columns orthogonal to it form a square matrix of
  size `n - 1`.
* `New.isProbabilityMeasure_haarU`: for `J = 1` the measure has mass one, by comparison with the
  polar formula `New.IsGramSection.lintegral_eq`. The same holds for the sign matrix with all signs
  equal to 1.
* `New.DiscreteSeries.measure_ball_le_covering`: for `D, R ≥ 1` the set `‖j s * y‖ ≤ R` has at most
  `(3 D R²) ^ (2 n²)` times the measure of the ball `‖j s - 1‖ ≤ 1 / D`.
* `New.DiscreteSeries.integral_decay_le`, `New.DiscreteSeries.lintegral_decay_le`: for `n ≥ 1` and a
  natural number `c > 8 n²` the function `(2 / ‖j s * y‖) ^ c` is integrable, with integral at most
  `16 ^ c` times the measure of `‖j s - 1‖ ≤ 1`.

Notions from other files:
* `New.gramCoords J Y`: the real coordinates `skewCoords (I • (Yᴴ J Y))` of the hermitian matrix
  `Yᴴ J Y`: with `x = I • (Yᴴ J Y)` they are `(x a b).re + (x a b).im`, divided by `√2` for `a ≠ b`.
* `New.U J`: the group of matrices `g` with `gᴴ J g = J`; thus `U 1` is the unitary group.
* `New.sphereDensity k r`: the number `2 π ^ k r ^ (k - 1) / (k - 1)!`.

## Relation to the literature

Known result: volume of U(n), polynomial volume growth of U(J).
Here J is any hermitian matrix with J² = 1, and the measure is normalised so that U(n) has mass one.
The covering bound for norm balls holds for any group with a right invariant measure and a
homomorphism to U(J), with an explicit crude constant. Source: L. K. Hua, Harmonic Analysis of
Functions of Several Complex Variables in the Classical Domains (1963), ch. III; I. G. Macdonald,
The volume of a compact Lie group, Invent. Math. 56 (1980); B. Gross, On the motive of a reductive
group, Invent. Math. 130 (1997).
-/

/-! ## U(n) has mass one -/

namespace New

open Matrix MeasureTheory Measure Fintype Real Complex Set ComplexOrder

variable {κ n n' : Type} [Fintype κ] [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']

/-- The unitary group of `ℂ^κ` takes a vector to any vector of the same norm. -/
lemma exists_unitary_mulVec_eq [DecidableEq κ]
    (ω : κ → ℂ) {v : κ → ℂ} (h_norm : star ω ⬝ᵥ ω = star v ⬝ᵥ v) :
    ∃ u : U (1 : Matrix κ κ ℂ), (u : Matrix κ κ ℂ) *ᵥ ω = v := by
  obtain rfl | hω := eq_or_ne ω 0
  · exact ⟨1, by simpa [eq_comm (b := v)] using h_norm.symm⟩
  -- Witt's theorem for the one-column matrices of `ω` and `v`
  have hv : v ≠ 0 := fun hv ↦ hω (by simpa [hv] using h_norm)
  obtain ⟨u, hu⟩ : ∃ u : U (1 : Matrix κ κ ℂ),
      (u : Matrix κ κ ℂ) * replicateCol Unit ω = replicateCol Unit v :=
    witt ⟨I, by simp⟩ conjTranspose_one isUnit_one (.of_ne_zero hω) (.of_ne_zero hv)
      (by simpa [← ext_iff, mul_apply, dotProduct] using h_norm)
  exact ⟨u, by rwa [← replicateCol_mulVec, replicateCol_inj] at hu⟩

/-- For nonempty `κ` with `k` elements, the set `|ω|² < a` in `ℂ ^ κ` is the ball of radius `√a`, of
volume `(√a) ^ (2 k) π ^ k / k!`. -/
lemma volume_map_normSq_Iio [Nonempty κ] (a : ℝ) :
    volume.map (fun ω : κ → ℂ ↦ ‖star ω ⬝ᵥ ω‖) (Iio a) =
      ENNReal.ofReal √a ^ (2 * card κ) * ENNReal.ofReal (π ^ card κ / (card κ).factorial) := by
  have h_volume : volume {ω : κ → ℂ | (∑ i : κ, ‖ω i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < √a} =
      ENNReal.ofReal √a ^ (2 * card κ) * ENNReal.ofReal (π ^ card κ / (card κ).factorial) := by
    rw [Complex.volume_sum_rpow_lt κ one_le_two √a]
    simp [Real.Gamma_nat_eq_factorial, one_add_one_eq_two]
  rw [← h_volume]
  -- ↓ keeps simp from rewriting inside the square root and the dot product first
  simp (disch := first | positivity | measurability) [preimage, ↓← sqrt_eq_rpow,
    ↓Fock.star_dotProduct_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]

/-- For `k > 0` the integral of `sphereDensity k r / 2` over `[0, a]` is `a ^ k π ^ k / k!`. -/
lemma integral_sphereDensity_div_two {k : ℕ} (hk : 0 < k) (a : ℝ) :
    ∫ r : ℝ in 0..a, sphereDensity k r / 2 = a ^ k * (π ^ k / k.factorial) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp [Nat.factorial_succ, field]

/-- For nonempty `κ` with `k` elements, the map `ω ↦ |ω|²` carries Lebesgue measure on `ℂ ^ κ` to
the measure on `r > 0` with density `sphereDensity k r / 2 = π ^ k r ^ (k - 1) / (k - 1)!`. -/
lemma measurePreserving_normSq_sphereDensity [Nonempty κ] :
    MeasurePreserving (fun ω : κ → ℂ ↦ ‖star ω ⬝ᵥ ω‖) volume
      ((volume.restrict (Ioi 0)).withDensity fun r : ℝ ↦
        ENNReal.ofReal (sphereDensity (card κ) r / 2)) := by
  -- Both measures give the half-line `Iio a` the volume of the ball of radius `√a`.
  refine ⟨by fun_prop, ext_of_generateFrom_of_iUnion _ (fun n : ℕ ↦ Iio (n : ℝ))
    (borel_eq_generateFrom_Iio ℝ) isPiSystem_Iio (iUnion_eq_univ_iff.2 exists_nat_gt) (by simp)
    (fun n ↦ ?_) (forall_mem_range.2 fun a ↦ ?_)⟩
  · rw [volume_map_normSq_Iio]
    finiteness
  have h_inter : Iio a ∩ Ioi 0 = Ioo 0 (√a ^ 2) := by grind
  have h_nonneg : ∀ᵐ r : ℝ ∂volume.restrict (Ioc 0 (√a ^ 2)), 0 ≤ sphereDensity (card κ) r / 2 :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun r ⟨_, _⟩ ↦ by positivity
  rw [volume_map_normSq_Iio, withDensity_apply', restrict_restrict measurableSet_Iio, h_inter,
    restrict_Ioo_eq_restrict_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Ioc (by fun_prop)) h_nonneg,
    ← intervalIntegral.integral_of_le (sq_nonneg _), integral_sphereDensity_div_two card_pos,
    ENNReal.ofReal_mul (by positivity), ← pow_mul, ENNReal.ofReal_pow (by positivity)]

/-- The real coordinates of the hermitian matrix `w wᴴ` of rank at most one, in the same convention
as `New.gramCoords`. -/
noncomputable def outerCoords (w : n → ℂ) : Matrix n n ℝ := skewCoords (I • vecMulVec w (star w))

@[fun_prop]
theorem continuous_outerCoords : Continuous (outerCoords : (n → ℂ) → Matrix n n ℝ) :=
  skewCoords.continuous_of_finiteDimensional.comp (by fun_prop)

/-- The Gram map `Y ↦ gramCoords 1 Y`, the real coordinates of `Yᴴ Y` for square matrices `Y`, has
density `c` on the set `W` of real matrices: on `W` it carries Lebesgue measure to `c` times
Lebesgue measure. -/
def HasGramDensity (W : Set (Matrix n n ℝ)) (c : ENNReal) : Prop :=
  ∀ G : Matrix n n ℝ → ENNReal, Measurable G → G.support ⊆ W →
    ∫⁻ Y : Matrix n n ℂ, G (gramCoords 1 Y) = c * ∫⁻ t : Matrix n n ℝ, G t

/-- Let the index set `n` consist of `n'` and one further index, fix a vector `v` of squared norm
`r > 0` in `ℂ ^ n`, and let the Gram map in size `n'` have the density `c` on `W`. Let `k` be the
number of elements of `n'`. The map that sends `k` vectors `Y` of `ℂ ^ n` to the coordinates `t` of
their Gram matrix and their products `w` with `v` carries Lebesgue measure to `c / r ^ k` times
Lebesgue measure, on the set where `t - outerCoords w / r`, the coordinates of the Gram matrix
minus `w wᴴ / r`, lies in `W`. -/
theorem HasGramDensity.lintegral_conjTranspose_mulVec {W : Set (Matrix n' n' ℝ)} {c : ENNReal}
    (hW : HasGramDensity W c) (e : n' ⊕ Unit ≃ n) {v : n → ℂ} {r : ℝ} (hr : 0 < r)
    (hv : star v ⬝ᵥ v = r) {F : Matrix n' n' ℝ × (n' → ℂ) → ENNReal} (hF : Measurable F)
    (h_supp : ∀ p ∈ F.support, p.1 - r⁻¹ • outerCoords p.2 ∈ W) :
    ENNReal.ofReal (r ^ card n') * ∫⁻ Y : Matrix n n' ℂ, F (gramCoords 1 Y, Yᴴ *ᵥ v) =
      c * ∫⁻ p : Matrix n' n' ℝ × (n' → ℂ), F p := by
  -- Rotate `v` to `√r` times a basis vector. Then `Y` consists of a square matrix `X` and a row
  -- `wᴴ`; its Gram matrix is `Xᴴ X + w wᴴ` and its products with `v` are `√r w`.
  let v₀ : n → ℂ := √r • Pi.single (e (.inr ())) 1
  obtain ⟨u, hu⟩ : ∃ u : U (1 : Matrix n n ℂ), (u : Matrix n n ℂ) *ᵥ v₀ = v :=
    exists_unitary_mulVec_eq v₀ (by simp [v₀, hv, star_trivial, ← ofReal_mul, hr.le])
  let rows : Matrix n' n' ℂ × (n' → ℂ) → Matrix n n' ℂ := fun (X, w) ↦ (joinCol e (Xᴴ, w))ᴴ
  have h_rows : MeasurePreserving fun p ↦ (u : Matrix n n ℂ) * rows p :=
    (measurePreserving_U_mul u).comp <| measurePreserving_conjTranspose.comp <|
      (measurePreserving_joinCol e).comp (measurePreserving_conjTranspose.prod (.id _))
  have h_gram (X : Matrix n' n' ℂ) (w : n' → ℂ) :
      gramCoords 1 ((u : Matrix n n ℂ) * rows (X, w)) = gramCoords 1 X + outerCoords w := by
    have h_sum : (rows (X, w))ᴴ * rows (X, w) = Xᴴ * X + vecMulVec w (star w) := by
      simp [← ext_iff, rows, mul_apply, ← e.sum_comp, vecMulVec_apply]
    rw [gramCoords_U_mul]
    simp [gramCoords, outerCoords, h_sum]
  have h_prod (X : Matrix n' n' ℂ) (w : n' → ℂ) :
      ((u : Matrix n n ℂ) * rows (X, w))ᴴ *ᵥ v = √r • w := by
    have h_unitary : (u : Matrix n n ℂ)ᴴ * u = 1 := by simpa using mem_U.1 u.property
    rw [← hu, mulVec_mulVec, conjTranspose_mul, Matrix.mul_assoc, h_unitary]
    simp [funext_iff, v₀, rows, mulVec_smul]
  have h_outer (w : n' → ℂ) : r⁻¹ • outerCoords (√r • w) = outerCoords w := by
    simp [outerCoords, star_trivial, smul_comm I, smul_smul, hr.le, hr.ne']
  -- For fixed `w`, the translate of `F` by `outerCoords w` is supported in `W`.
  have h_inner (w : n' → ℂ) : ∫⁻ X : Matrix n' n' ℂ, F (gramCoords 1 X + outerCoords w, √r • w) =
      c * ∫⁻ t, F (t, √r • w) := by
    rw [hW (fun t ↦ F (t + outerCoords w, √r • w)) (by fun_prop)
        fun t ht ↦ by simpa [h_outer] using h_supp _ ht,
      lintegral_add_right_eq_self fun t ↦ F (t, √r • w)]
  let T : (n' → ℂ) →ₗ[ℝ] n' → ℂ := √r • .id
  have hT : T.det = r ^ card n' := by simp [T, Module.finrank_pi_fintype, pow_mul', hr.le]
  calc _ = ENNReal.ofReal (r ^ card n') *
          ∫⁻ w, ∫⁻ X : Matrix n' n' ℂ, F (gramCoords 1 X + outerCoords w, √r • w) := by
        rw [← h_rows.lintegral_comp (hF.fun_comp (Continuous.measurable (by fun_prop)))]
        simp only [h_gram, h_prod]
        rw [volume_eq_prod, lintegral_prod_symm' _ (by fun_prop)]
    _ = ENNReal.ofReal (r ^ card n') * ∫⁻ w, c * ∫⁻ t, F (t, √r • w) := by simp only [h_inner]
    _ = ∫⁻ w, c * ∫⁻ t, F (t, w) := by
        rw [eq_comm, lintegral_eq_abs_det_mul_comp volume (hT.trans_ne (by positivity))
          (by fun_prop), hT]
        simp [T, abs_of_pos hr]
    _ = c * ∫⁻ p, F p := by
        rw [volume_eq_prod, lintegral_prod_symm' _ hF, lintegral_const_mul c (by fun_prop)]

/-- The step from size `n'` to size `n`, one more than `n'`. Let `φ` be a volume-preserving
homeomorphism that splits the coordinates of the Gram matrix of the columns `(Y, v)` (joined by
`joinCol e`, which puts column `a` of `Y` at index `e (.inl a)` and `v` at index `e (.inr ())`) into
the block `t = gramCoords 1 Y`, the column `w = Yᴴ v` and the corner `r = |v|²`. Suppose the Gram
map `Y ↦ gramCoords 1 Y` (real coordinates of `Yᴴ Y`) carries Lebesgue measure on `W` to `c` times
Lebesgue measure in size `n'`. Then in size `n` it does so with constant `sphereDensity (card n)
1 / 2 * c = (π^k / (k−1)!) c`, where `k = card n`, on the set where `r > 0` and
`t - outerCoords w / r` lies in `W`; here `outerCoords w` is the real coordinates of `w wᴴ`. -/
theorem HasGramDensity.succ {W : Set (Matrix n' n' ℝ)} {c : ENNReal} (hW : HasGramDensity W c)
    (e : n' ⊕ Unit ≃ n) {φ : Matrix n n ℝ ≃ₜ Matrix n' n' ℝ × (n' → ℂ) × ℝ}
    (φ_vol : MeasurePreserving φ)
    (φ_gram : ∀ (Y : Matrix n n' ℂ) (v : n → ℂ),
      φ (gramCoords 1 (joinCol e (Y, v))) = (gramCoords 1 Y, Yᴴ *ᵥ v, ‖star v ⬝ᵥ v‖)) :
    HasGramDensity (φ ⁻¹' {p : Matrix n' n' ℝ × (n' → ℂ) × ℝ |
        0 < p.2.2 ∧ p.1 - p.2.2⁻¹ • outerCoords p.2.1 ∈ W})
      (ENNReal.ofReal (sphereDensity (card n) 1 / 2) * c) := by
  -- Let `m = card n'`. One column `v` ranges over the sphere `|v|² = r`, whose mass
  -- `π ^ (m + 1) r ^ m / m!` cancels the power of `r` that comes from the other `m` columns.
  intro G hG h_supp
  have : Nonempty n := ⟨e (.inr ())⟩
  let F (r : ℝ) (p : Matrix n' n' ℝ × (n' → ℂ)) : ENNReal := G (φ.symm (p.1, p.2, r))
  have hF_supp (r : ℝ) (p : Matrix n' n' ℝ × (n' → ℂ)) (hp : F r p ≠ 0) :
      0 < r ∧ p.1 - r⁻¹ • outerCoords p.2 ∈ W := by simpa using h_supp hp
  let H (r : ℝ) : ENNReal := ENNReal.ofReal (r ^ card n')⁻¹ * (c * ∫⁻ p, F r p)
  have h_column (v : n → ℂ) (hv : v ≠ 0) :
      ∫⁻ Y : Matrix n n' ℂ, G (gramCoords 1 (joinCol e (Y, v))) = H ‖star v ⬝ᵥ v‖ := by
    have hr : 0 < ‖star v ⬝ᵥ v‖ := by simpa using hv
    simp only [H]
    rw [← hW.lintegral_conjTranspose_mulVec e hr
      (norm_of_nonneg' (dotProduct_star_self_nonneg v)).symm (by fun_prop)
      fun p hp ↦ (hF_supp _ p hp).right, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    simp [F, ← φ_gram, hv]
  have h_mass (r : ℝ) (hr : 0 < r) :
      sphereDensity (card n) r / 2 * (r ^ card n')⁻¹ = sphereDensity (card n) 1 / 2 := by
    simp [← card_congr e, field]
  have hF_subset : (fun r : ℝ ↦ ∫⁻ p, F r p).support ⊆ Ioi 0 := fun r hr ↦ by
    obtain ⟨p, hp⟩ : ∃ p, F r p ≠ 0 := by_contra fun h ↦ hr (by simp_all)
    exact (hF_supp r p hp).left
  calc ∫⁻ Y, G (gramCoords 1 Y) = ∫⁻ v : n → ℂ, H ‖star v ⬝ᵥ v‖ := by
        rw [← (measurePreserving_joinCol e).lintegral_comp (by fun_prop), volume_eq_prod,
          lintegral_prod_symm' _ (by fun_prop)]
        exact lintegral_congr_ae ((ae_ne volume 0).mono h_column)
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (sphereDensity (card n) r / 2) * H r := by
        rw [measurePreserving_normSq_sphereDensity.lintegral_comp (by fun_prop)]
        exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (sphereDensity (card n) 1 / 2) * c * ∫⁻ p, F r p := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        simp (disch := positivity) only [H, ← h_mass r hr, ENNReal.ofReal_mul, mul_assoc]
    _ = ENNReal.ofReal (sphereDensity (card n) 1 / 2) * c * ∫⁻ r, ∫⁻ p, F r p := by
        rw [lintegral_const_mul _ (by fun_prop), setLIntegral_eq_of_support_subset hF_subset]
    _ = ENNReal.ofReal (sphereDensity (card n) 1 / 2) * c * ∫⁻ t : Matrix n n ℝ, G t := by
        rw [← (φ_vol.symm φ.toMeasurableEquiv).lintegral_comp hG,
          ← volume_preserving_prodAssoc.lintegral_comp (by fun_prop), volume_eq_prod _ ℝ,
          lintegral_prod_symm' _ (by fun_prop)]
        rfl

omit [Fintype n'] in
/-- The Gram matrix of columns `(Y, v)`, joined by `joinCol e`, in the coordinates `φ` of block,
column and corner, where the column entries are read from `hermOfReal t`, the hermitian matrix with
real coordinates `t`: they are `gramCoords 1 Y`, `Yᴴ v` and `|v|²`. -/
lemma apply_gramCoords_joinCol (e : n' ⊕ Unit ≃ n)
    {φ : Matrix n n ℝ ≃ₜ Matrix n' n' ℝ × (n' → ℂ) × ℝ}
    (φ_apply : ∀ t : Matrix n n ℝ, φ t = (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
      fun a : n' ↦ hermOfReal t (e (.inl a)) (e (.inr ())), t (e (.inr ())) (e (.inr ()))))
    (Y : Matrix n n' ℂ) (v : n → ℂ) :
    φ (gramCoords 1 (joinCol e (Y, v))) = (gramCoords 1 Y, Yᴴ *ᵥ v, ‖star v ⬝ᵥ v‖) := by
  have h_corner : ((joinCol e (Y, v))ᴴ * joinCol e (Y, v)) (e (.inr ())) (e (.inr ())) =
      ‖star v ⬝ᵥ v‖ := by
    rw [norm_of_nonneg' (dotProduct_star_self_nonneg v)]
    simp [mul_apply, dotProduct]
  rw [φ_apply, hermOfReal_gramCoords isHermitian_one]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [← ext_iff, gramCoords, skewCoords, mul_apply]
  · simp [funext_iff, mul_apply, mulVec, dotProduct]
  · simp [gramCoords, skewCoords, h_corner]

/-- There is an open set `W` of real `n × n` matrices containing `gramCoords 1 1` on which the Gram
map `Y ↦ gramCoords 1 Y` has density `volU (card n) / 2 ^ card n`. Here `gramCoords 1 Y` is the
vector of real coordinates, in the sense of `hermOfReal` (which takes real coordinates back to the
hermitian matrix), of `Yᴴ Y` for complex square matrices `Y`. Having this density means that on `W`
the map carries Lebesgue measure to that constant times Lebesgue measure, where
`volU j = ∏ i < j, 2 π ^ (i + 1) / i!`. -/
theorem exists_hasGramDensity :
    ∃ W : Set (Matrix n n ℝ), IsOpen W ∧ gramCoords 1 (1 : Matrix n n ℂ) ∈ W ∧
      HasGramDensity W (ENNReal.ofReal (volU (card n) / 2 ^ card n)) := by
  induction hk : card n generalizing n with
  | zero =>
    rw [card_eq_zero_iff] at hk
    refine ⟨univ, isOpen_univ, trivial, fun G hG _ ↦ ?_⟩
    simp [volU, volume_eq_dirac_of_isEmpty (1 : Matrix n n ℂ),
      volume_eq_dirac_of_isEmpty (gramCoords 1 (1 : Matrix n n ℂ))]
  | succ k ih =>
    obtain ⟨k₀⟩ : Nonempty n := card_pos_iff.1 (by lia)
    let n' : Type := {a : n // a ≠ k₀}
    let e : n' ⊕ Unit ≃ n := (Equiv.optionEquivSumPUnit n').symm.trans (Equiv.optionSubtypeNe k₀)
    obtain ⟨W, hW_open, hW_one, hW⟩ := ih (n := n') (by simp [n', hk])
    -- `φ` splits the coordinates of a hermitian matrix into block, column and corner.
    obtain ⟨φ, φ_vol, φ_apply⟩ := exists_measurePreserving_hermCorner e
    have h_const : ENNReal.ofReal (volU (k + 1) / 2 ^ (k + 1)) =
        ENNReal.ofReal (sphereDensity (card n) 1 / 2) * ENNReal.ofReal (volU k / 2 ^ k) := by
      rw [← ENNReal.ofReal_mul (by positivity), hk, volU, Finset.prod_range_succ_comm, ← volU,
        pow_succ', mul_div_mul_comm]
    have h_open : IsOpen {p : Matrix n' n' ℝ × (n' → ℂ) × ℝ |
        0 < p.2.2 ∧ p.1 - p.2.2⁻¹ • outerCoords p.2.1 ∈ W} := by
      refine ContinuousOn.isOpen_inter_preimage (fun p hp ↦ ContinuousAt.continuousWithinAt ?_)
        (isOpen_Ioi.preimage continuous_snd.snd) hW_open
      fun_prop (disch := exact ne_of_gt hp)
    have h_one : φ (gramCoords 1 (1 : Matrix n n ℂ)) =
        (gramCoords 1 (1 : Matrix n' n' ℂ), 0, 1) := by
      rw [φ_apply, hermOfReal_gramCoords isHermitian_one]
      simp [← ext_iff, funext_iff, gramCoords, skewCoords, one_apply]
    exact ⟨_, h_open.preimage φ.continuous, by simpa [h_one, outerCoords] using hW_one,
      by simpa only [h_const] using hW.succ e φ_vol (apply_gramCoords_joinCol e φ_apply)⟩

/-- The compact unitary group `U(n)` has total mass one for the measure `New.haarU 1`, which is
the `volume` of `U 1`. -/
instance isProbabilityMeasure_haarU :
    IsProbabilityMeasure (volume : Measure (U (1 : Matrix n n ℂ))) where
  measure_univ := by
    -- Compute the volume of the matrices with Gram matrix in a small open set `S` in two ways: by
    -- the polar formula over a section `σ`, and by the density of the Gram map near the identity.
    obtain ⟨W, hW_open, hW_one, hW⟩ := exists_hasGramDensity (n := n)
    obtain ⟨V, σ, hσ, hV_one, -⟩ := exists_isGramSection (1 : Matrix n n ℂ)
    obtain ⟨O, hO_one, hO_open, hO_fin⟩ :=
      exists_isOpen_measure_lt_top volume (gramCoords 1 (1 : Matrix n n ℂ))
    let S : Set (Matrix n n ℝ) := V ∩ W ∩ O
    have hS : IsOpen S := (hσ.isOpen.inter hW_open).inter hO_open
    have hS_pos : volume S ≠ 0 := hS.measure_ne_zero volume ⟨_, ⟨hV_one, hW_one⟩, hO_one⟩
    have hS_fin : volume S ≠ ⊤ := ((measure_mono inter_subset_right).trans_lt hO_fin).ne
    set c : ENNReal := ENNReal.ofReal (volU (card n) / 2 ^ card n)
    have hc : c ≠ 0 := by simp [c, volU_pos]
    rw [← ENNReal.mul_left_inj hS_pos hS_fin, ← ENNReal.mul_right_inj hc ENNReal.ofReal_ne_top]
    calc c * (volume (univ : Set (U (1 : Matrix n n ℂ))) * volume S)
        = c * ∫⁻ t : Matrix n n ℝ in S, ∫⁻ g : U (1 : Matrix n n ℂ), 1 := by simp
      _ = ∫⁻ Y : Matrix n n ℂ in gramCoords 1 ⁻¹' S, 1 :=
          ((hσ.mono hS (by grind)).lintegral_eq measurable_const).symm
      _ = ∫⁻ Y : Matrix n n ℂ, S.indicator 1 (gramCoords 1 Y) :=
          (lintegral_indicator ((continuous_gramCoords 1).measurable hS.measurableSet) _).symm
      _ = c * (1 * volume S) := by
          simpa [hS.measurableSet] using hW _ (measurable_one.indicator hS.measurableSet)
            (support_indicator_subset.trans (by grind))

/-- For all signs equal to one, the unitary group of the sign matrix `signMatrix 1`, which equals
`1` by `signMatrix_one`, has total mass one. -/
instance : IsProbabilityMeasure (α := U (signMatrix (n := n) 1)) volume := by
  rw! [signMatrix_one]
  infer_instance

end New

/-!
## Covering bounds for norm balls in U(J) and integrals of (2/‖j s y‖)^c

The covering bound compares volumes of balls in the real space of matrices, of dimension `2 n²`. The
integral bound integrates it over the level sets of the norm.
-/

section HaarCovering

open New U MeasureTheory ENNReal Fintype Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} [IsHermitianInvolution J]
  {S : Type} [Group S] [MeasurableSpace S]

omit [IsHermitianInvolution J] in
theorem IsProperMap.monoidHom_id : IsProperMap (MonoidHom.id (U J)) := by simp

/-- The distance on `U J` is the operator norm of the difference of matrices. -/
noncomputable instance : MetricSpace (U J) := isClosedEmbedding_U.toIsEmbedding.comapMetricSpace _

/-- Closed balls of `U J` are compact, as `U J` is a closed set of matrices. -/
instance : ProperSpace (U J) where
  isCompact_closedBall x r :=
    isClosedEmbedding_U.isCompact_preimage (isCompact_closedBall (x : Matrix n n ℂ) r)

theorem New.isCompact_U_norm_le (T : ℝ) : IsCompact {y : U J | ‖(y : Matrix n n ℂ)‖ ≤ T} := by
  simpa [Set.preimage] using
    isClosedEmbedding_U.isCompact_preimage (isCompact_closedBall (0 : Matrix n n ℂ) T)

/-- The sublevel set `{s | f s ≤ r}` of a continuous function `f` has nonzero measure when
`f 1 < r`, for a measure `ν` that is positive on nonempty open sets. -/
lemma New.measure_sublevel_ne_zero (ν : Measure S) [TopologicalSpace S] [ν.IsOpenPosMeasure]
    {f : S → ℝ} {r : ℝ} (h_one : f 1 < r := by simp) (hf : Continuous f := by fun_prop) :
    ν {s : S | f s ≤ r} ≠ 0 :=
  (ν.measure_pos_of_mem_nhds (hf.tendsto 1 (ge_mem_nhds h_one))).ne'

namespace New.DiscreteSeries

/-- Covering bound. For `D, R ≥ 1` and `3 D R² ≤ K`, the set where `‖j s * y‖ ≤ R` has measure
at most `K ^ (2 n²)` times the measure of the set where `‖j s - 1‖ ≤ 1 / D`. Here `ν` is a
right invariant measure on `S`, `j` is a homomorphism to the unitary group `U J` of a hermitian
involution `J` of size `n`, and the norms are operator norms. -/
theorem measure_ball_le_covering (ν : Measure S) [MeasurableMul S] [ν.IsMulRightInvariant]
    (j : S →* U J) (y : U J) {D R K : ℝ} (hD : 1 ≤ D) (hR : 1 ≤ R) (hK : 3 * D * R ^ 2 ≤ K) :
    ν {s : S | ‖((j s * y : U J) : Matrix n n ℂ)‖ ≤ R} ≤
      ENNReal.ofReal (K ^ (2 * card n ^ 2)) * ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ D⁻¹} := by
  -- Among the `s` with `‖j s * y‖ ≤ R` take a maximal family `M` whose matrices `j s * y` are
  -- `1 / (D R)`-separated. The packing bound counts `M`, and by maximality the right translates
  -- of the small ball `B` by the points of `M` cover the set on the left.
  let f (s : S) : Matrix n n ℂ := ((j s * y : U J) : Matrix n n ℂ)
  set B : Set S := {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ D⁻¹}
  let IsFar (s t : {s : S // ‖f s‖ ≤ R}) : Prop := D⁻¹ / R ≤ ‖f s - f t‖
  obtain ⟨M, h_sep, h_max⟩ : ∃ M, IsMaxChain IsFar M := ⟨maxChain IsFar, maxChain_spec⟩
  have h_card : M.encard ≤ ENNReal.ofReal (K ^ (2 * card n ^ 2)) := by
    have h_pairwise : M.Pairwise IsFar := by simpa [IsChain, IsFar, norm_sub_rev] using h_sep
    have h_base : 1 + 2 * R / (D⁻¹ / R) ≤ K :=
      calc _ = 1 + 2 * D * R ^ 2 := by field
        _ ≤ K := by linarith [show 1 ≤ D * R ^ 2 by bound]
    calc _ ≤ ENNReal.ofReal ((1 + 2 * R / (D⁻¹ / R)) ^ Module.finrank ℝ (Matrix n n ℂ)) :=
          encard_le_of_separated (by positivity) (by positivity) h_pairwise fun s _ ↦ s.property
      _ ≤ ENNReal.ofReal (K ^ Module.finrank ℝ (Matrix n n ℂ)) := by gcongr
      _ = _ := by simp [Module.finrank_matrix, ← sq, mul_comm 2]
  have : Finite M := Set.Finite.to_subtype (by simpa using h_card.trans_lt ofReal_lt_top)
  have h_cover : {s : S | ‖f s‖ ≤ R} ⊆ ⋃ k : M, (· * (k : S)⁻¹) ⁻¹' B := by
    intro g hg
    by_contra! h_not_mem
    -- Otherwise `g` is far from all of `M`: `j (g k⁻¹) - 1 = (f g - f k) (j k * y)⁻¹`, and an
    -- element of `U J` has the norm of its inverse.
    have h_far (k : M) : IsFar ⟨g, hg⟩ k := (div_le_iff₀ (by positivity)).2 <|
      calc D⁻¹ ≤ ‖(j (g * (k : S)⁻¹) : Matrix n n ℂ) - 1‖ :=
          le_of_not_ge fun h ↦ h_not_mem (Set.mem_iUnion.2 ⟨k, h⟩)
        _ = ‖(f g - f k) * (((j k * y)⁻¹ : U J) : Matrix n n ℂ)‖ := by simp [f, sub_mul, mul_assoc]
        _ ≤ ‖f g - f k‖ * R := by grw [norm_mul_le, U.norm_inv, k.val.property]
    -- Maximality puts `g` into `M`, so `g` is far from itself.
    have h_mem : ⟨g, hg⟩ ∈ M := Set.insert_eq_self.1
      (h_max (h_sep.insert fun k hk _ ↦ .inl (h_far ⟨k, hk⟩)) (Set.subset_insert ..)).symm
    have h_self : D⁻¹ / R ≤ 0 := by simpa [IsFar] using h_far ⟨_, h_mem⟩
    exact h_self.not_gt (by positivity)
  calc ν {s : S | ‖f s‖ ≤ R} ≤ ∑' k : M, ν ((· * (k : S)⁻¹) ⁻¹' B) :=
        (measure_mono h_cover).trans (measure_iUnion_le _)
    _ = M.encard * ν B := by simp only [measure_preimage_mul_right, tsum_set_const]
    _ ≤ ENNReal.ofReal (K ^ (2 * card n ^ 2)) * ν B := by gcongr

/-- For a proper homomorphism `j` to `U J` and a measure `ν` that is finite on compact sets, the
ball `‖j s - 1‖ ≤ R` in the operator norm has finite measure. -/
lemma measure_ball_ne_top_of_isProperMap (ν : Measure S) [MeasurableMul S]
    [ν.IsMulRightInvariant] {j : S →* U J} [TopologicalSpace S] [IsFiniteMeasureOnCompacts ν]
    (hj : IsProperMap j) (R : ℝ) : ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ R} ≠ ⊤ := by
  have h_eq : {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ R} = j ⁻¹' Metric.closedBall 1 R :=
    Set.ext fun s ↦ (mem_closedBall_iff_norm (b := (j s : Matrix n n ℂ))).symm
  simpa only [h_eq] using (hj.isCompact_preimage (isCompact_closedBall 1 R)).measure_ne_top

/-- Let `J` be a hermitian involution of size `n ≥ 1`, let `j : S →* U J` be proper, let `ν` be
right invariant and finite on compact sets, and let `c > 8 n²` be a natural number. Then
`s ↦ (2 / ‖j s * y‖) ^ c` is integrable, and its integral is at most `16 ^ c` times the measure of
the set where `‖j s - 1‖ ≤ 1` (operator norms). The bound does not depend on `y`. -/
theorem integral_decay_le (ν : Measure S) [MeasurableMul S] [ν.IsMulRightInvariant]
    {j : S →* U J} [TopologicalSpace S] [IsFiniteMeasureOnCompacts ν] [BorelSpace S] [Nonempty n]
    (hj : IsProperMap j) {c : ℕ} (hc : 8 * card n ^ 2 < c) (y : U J) :
    Integrable (fun s : S ↦ (2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c) ν ∧
      ∫ s : S, (2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c ∂ν ≤
        16 ^ c * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by
  -- By `measure_ball_le_covering` with `D = 1`, the set `‖j s * y‖ ≤ R` has measure at most
  -- `(3 R²) ^ (2 n²)` times that of `‖j s - 1‖ ≤ 1`. As `‖j s * y‖ ≥ 1` and `c ≤ 3 (c - 4 n²)`,
  -- integration by layers gives the factor `3 ^ (2 n²) * 3`.
  let N (s : S) : ℝ := ‖((j s * y : U J) : Matrix n n ℂ)‖
  have h_layers (R : ℝ) (hR : 1 ≤ R) : ν {s : S | N s ≤ R} ≤
      ENNReal.ofReal ((3 * 1 * R ^ 2) ^ (2 * card n ^ 2)) *
        ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1⁻¹} :=
    measure_ball_le_covering ν j y le_rfl hR le_rfl
  have hc_real : 8 * (card n : ℝ) ^ 2 < c := mod_cast hc
  have h_exp : (2 : ℕ) * (2 * card n ^ 2 : ℕ) < (c : ℝ) := mod_cast by lia
  have h_factor : (c : ℝ) ≤ 3 * (c - (2 : ℕ) * (2 * card n ^ 2 : ℕ)) := by grind
  obtain ⟨h_int, h_le⟩ : Integrable (fun s : S ↦ N s ^ (-c : ℝ)) ν ∧
      ∫ s : S, N s ^ (-c : ℝ) ∂ν ≤
        (3 * 1) ^ (2 * card n ^ 2) * 3 * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1⁻¹} :=
    integral_rpow_neg_le_of_measure_le (Continuous.measurable (by fun_prop)) (fun _ ↦ one_le_norm _)
      (by norm_num) (measure_ball_ne_top_of_isProperMap ν hj 1⁻¹) h_layers h_exp h_factor
  have h_split (s : S) :
      (2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c = 2 ^ c * N s ^ (-c : ℝ) := by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, div_pow, div_eq_mul_inv]
  have h_const : (2 : ℝ) ^ c * (3 ^ (2 * card n ^ 2) * 3) ≤ 16 ^ c :=
    calc _ ≤ (2 : ℝ) ^ c * 3 ^ c := by
          grw [← pow_succ, pow_le_pow_right₀ (by norm_num) (show 2 * card n ^ 2 + 1 ≤ c by lia)]
      _ ≤ 16 ^ c := by grw [← mul_pow, show (2 * 3 : ℝ) ≤ 16 by norm_num]
  simp only [h_split]
  refine ⟨h_int.const_mul _, ?_⟩
  calc ∫ s : S, 2 ^ c * N s ^ (-c : ℝ) ∂ν
      ≤ 2 ^ c * (3 ^ (2 * card n ^ 2) * 3) * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by
        grw [integral_const_mul, h_le, mul_one, inv_one, ← mul_assoc]
    _ ≤ 16 ^ c * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by gcongr

/-- The bound of `integral_decay_le` for the lower Lebesgue integral: for a proper `j : S →* U J`,
`ν` right invariant and finite on compact sets, `n ≥ 1` and `c > 8 n²`, the integral of
`(2 / ‖j s * y‖) ^ c` is at most `16 ^ c` times the measure of the set where `‖j s - 1‖ ≤ 1`. -/
theorem lintegral_decay_le (ν : Measure S) [MeasurableMul S] [ν.IsMulRightInvariant]
    {j : S →* U J} [TopologicalSpace S] [IsFiniteMeasureOnCompacts ν] [BorelSpace S] [Nonempty n]
    (hj : IsProperMap j) {c : ℕ} (hc : 8 * card n ^ 2 < c) (y : U J) :
    ∫⁻ s : S, ENNReal.ofReal ((2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c) ∂ν ≤
      ENNReal.ofReal (16 ^ c) * ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by
  obtain ⟨h_int, h_le⟩ := integral_decay_le ν hj hc y
  calc _ = ENNReal.ofReal (∫ s : S, (2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal h_int (.of_forall fun s ↦ by positivity)).symm
    _ ≤ ENNReal.ofReal (16 ^ c * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1}) :=
        ENNReal.ofReal_le_ofReal h_le
    _ = ENNReal.ofReal (16 ^ c) * ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by
        rw [ENNReal.ofReal_mul (by positivity),
          ofReal_measureReal (measure_ball_ne_top_of_isProperMap ν hj 1)]

end New.DiscreteSeries

end HaarCovering
