import New.Spanning.Bessel.Orthonormality
import New.Spanning.Frames.RealPlaceGauge
import New.Spanning.Frames.Shells

/-!
# Cut Bessel functions at ℂ: integration of the local estimates over shells

This file integrates pointwise local estimates for Bessel functions at the place ℂ over the group.
Every position lies in a dyadic shell, and the positions outside the position ball at a scale are
the remote positions. The place ℂ lies over a real place of the totally real subfield, and the
docstrings call it a real place. The results are the absolute convergence of the forms, an
integrated bound, and a bound for the form of each floor.

Throughout k = card κ and n = ϱ + 1 (`New.Shape.n`), as in the exponents.
`New.Floors.RealPlaceSizes.complexData` is the place datum at ℂ: box ‖x‖ ≤ ρ, Haar measure
`New.Floors.PlaceData.groupMeasure`. `New.Floors.RealPlaceSizes.gauge` measures sizes by powers of
L. A list p is a head of length j (`New.Floors.Size.IsHead`) if the inverses of p₀ ⋯ p_{l-1}, l ≤ j,
have modulus at most L. `New.Floors.PlaceData.floorForm` is the form of floor j.
`New.Floors.PlaceData.formIntegrandL1Norm` and `New.Floors.PlaceData.formMajorant` bound its
integrand at a position x. `New.Floors.Gauge.weightedSquareProduct` is the weighted product of norms
that their squares are compared to.

## Main definitions and results

* `New.Floors.IsCutBessel`: the cut, at size ρ, of a normalised Bessel function (`New.IsCutPair`) of
  irreducible type, with the numerical constraints.
* `New.Floors.IsCutBessel.lintegral_formMajorant_ne_top`: the forms converge absolutely.
* `New.Floors.IsCutBessel.norm_floorForm_le`: a local bound with gain (π / |y|) ^ (2 (k - 5)) gives
  a bound for the form.

Notions from other files:
* `New.Floors.complexPlace`: The place `ℂ`: `τ = 1/2`, `δ = i/2`, `ν` the image of Lebesgue measure
  under `r ↦ r i`, modulus `‖x‖ ^ 2`, character `x ↦ exp (x - x̄)` and constant
  `kernelBound = π ^ 2`.
* `New.IsCutPair`: Two Bessel functions, full and cut (`New.FullOrCut.select`), with base b and
  degree f. The cut one vanishes where `New.besselLength` exceeds b ^ (6 n + 2), n = ϱ + 1. Their L²
  distance is at most b ^ (-r³ f) √(card I), and f also sets their decay.
* `New.Floors.RealPlaceSizes`: The box radius is ρ = b ^ (6 n + 2) ≥ 8 r with b ≥ 2, the exponent
  s > 10⁹ n³ is fixed by k = s + 3 n + 6, and k ≥ n⁷, ϱ ≥ 10⁸.
* `New.headWeight`: The product of max(1, |δ|⁻¹) ^ K over the products δ = p₀ ⋯ p_l, l < j, if these
  have modulus at most R, and 0 otherwise. `New.dampedPower`: The gain r ^ K min(1, r)⁶.
* `weylElem j p`: The Weyl element w_p, with e_a ↦ p_a e*_a and e*_a ↦ e_a / p̄_a for a < j.
  `New.Floors.PlaceData.IsNear`: g is near at j if the coset `partialUnitriangularGroup j` · g meets
  the box. The frame is (e₀, …, e_{ϱ-1}, z), where e_a, e*_a are the hyperbolic pairs of basis
  vectors, and `New.Shape.top` is the position of z. `New.realFrameGram` x is the matrix of the
  products h(f_a, x f_b) of the frame vectors f_a; its entries are the frame entries of x.
* `New.Shape.scaledVolumeRatio`: The constant π ^ ((2ϱ + 1) k) · vol U(k) / vol U(r), where k = card
  κ and r is the rank of G₁. `New.Floors.PlaceData.headDensity`: A product of powers of |p_a q_a|,
  a < j. A normalised integral is an integral over G₁ times this density and
  `New.Floors.IsCutBessel.formConst`.
-/

noncomputable section

namespace New.Floors

section ComplexShells

open MeasureTheory Size Fintype Real PlaceData Shape ENNReal Finset Gauge RealPlaceSizes

variable {j s : ℕ} {𝔰 : Shape} {I : Type} [Fintype I] [DecidableEq I]
  {F : C(𝔰.G₁, EuclideanSpace ℂ I)} {p q : ℕ → ℂˣ} {ρ L t b : ℝ}
  {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* Matrix.unitaryGroup I ℂ} {F₀ : C(𝔰.G₁, EuclideanSpace ℂ I)}
  {f : ℕ}

/-! ### Cut Bessel functions and their gauges -/

/-- `F` is the cut of the normalised Bessel function `F₀` of irreducible type `rep`: the two form a
cut pair (`New.IsCutPair`) with base `b` and decay rate `f`, and the box radius `ρ`, the exponent
`s` and `b` satisfy the numerical hypotheses `New.Floors.RealPlaceSizes`. -/
structure IsCutBessel (F : C(𝔰.G₁, EuclideanSpace ℂ I))
    (rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* Matrix.unitaryGroup I ℂ) (ρ : ℝ) (s : ℕ) (b : ℝ)
    (F₀ : C(𝔰.G₁, EuclideanSpace ℂ I)) (f : ℕ) : Prop extends
    IsCutPair b f rep (FullOrCut.select F₀ F), RealPlaceSizes 𝔰 ρ s b where
  /-- Every matrix that commutes with all `rep h` is scalar. -/
  irreducible (M : Matrix I I ℂ) :
    (∀ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), Commute M (rep h : Matrix I I ℂ)) →
      M ∈ Set.range (Matrix.scalar I)

/-- The position ball at scale `T`: the entries of `x - 1` have modulus at most `T ^ (99 n)`. -/
def positionBall (𝔰 : Shape) (T : ℝ) : Set 𝔰.G₁ :=
  {x | ∀ a c : 𝔰.BesselIndex, ‖(x.val.val - 1) a c‖ ≤ T ^ (99 * 𝔰.n)}

lemma measurableSet_positionBall (T : ℝ) : MeasurableSet (positionBall 𝔰 T) := by
  simp only [positionBall, Set.ofPred_forall]
  exact .iInter fun a ↦ .iInter fun c ↦ measurableSet_le (by fun_prop) measurable_const

/-- The shell of height `2 ^ i`: the positions `x` for which `2 ^ i` is the least of `1, 2, 4, …`
that bounds the moduli of the entries of `x - 1`. -/
def dyadicShell (𝔰 : Shape) (i : ℕ) : Set 𝔰.G₁ :=
  {x | IsLeast {l : ℕ | ∀ a c : 𝔰.BesselIndex, ‖(x.val.val - 1) a c‖ ≤ 2 ^ l} i}

/-- Every position lies in a dyadic shell. -/
lemma exists_mem_dyadicShell (x : 𝔰.G₁) : ∃ i : ℕ, x ∈ dyadicShell 𝔰 i := by
  let X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := x - 1
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ a c : 𝔰.BesselIndex, ‖X a c‖ ≤ B :=
    ⟨_, fun a c ↦ norm_apply_le_l2_opNorm ..⟩
  obtain ⟨l, hl⟩ : ∃ l : ℕ, B < 2 ^ l := pow_unbounded_of_one_lt B _root_.one_lt_two
  have h_bound : ∃ l : ℕ, ∀ a c : 𝔰.BesselIndex, ‖X a c‖ ≤ 2 ^ l :=
    ⟨l, fun a c ↦ (hB a c).trans hl.le⟩
  exact ⟨Nat.find h_bound, Nat.isLeast_find h_bound⟩

/-- A position `x` in the dyadic shell `dyadicShell 𝔰 i` of height `2 ^ i` is not in
`positionBall 𝔰 T` for a scale `T ≥ 1` with `2 * T ^ (99 * 𝔰.n) ≤ 2 ^ i`. -/
lemma notMem_positionBall_of_mem_dyadicShell {i : ℕ} {x : 𝔰.G₁} (hx : x ∈ dyadicShell 𝔰 i)
    {T : ℝ} (one_le_T : 1 ≤ T) (h_half : 2 * T ^ (99 * 𝔰.n) ≤ 2 ^ i) :
    x ∉ positionBall 𝔰 T := by
  intro h_close
  obtain ⟨-, h_least⟩ := hx
  cases i with
  | zero => linarith [one_le_pow₀ one_le_T (n := 99 * 𝔰.n)]
  | succ i =>
    -- `2 ^ i` would bound the entries of `x - 1`, against the minimality of `i + 1`.
    have pow_le : T ^ (99 * 𝔰.n) ≤ 2 ^ i := by linarith [pow_succ' (2 : ℝ) i]
    exact i.not_succ_le_self (h_least fun a c ↦ (h_close a c).trans pow_le)

namespace IsCutBessel

/-- The normalising constant vol U(k) / vol U(r) / (λ · card I)² of the forms, where k = card κ, r
is the rank of the group and λ = `New.Floors.RealPlaceSizes.haarRatio` is the ratio of the two Haar
measures. -/
def formConst (hF : IsCutBessel F rep ρ s b F₀ f) : ℝ :=
  volU 𝔰.k / volU 𝔰.r / (hF.haarRatio.toReal * card I) ^ 2

section

/-- A cut Bessel function `F` is cut for the place datum at ℂ: it is a Bessel function of frequency
`1` and vanishes off the translates of the box `‖x‖ ≤ ρ` by the Bessel unipotent group. -/
lemma isCut_complexData (hF : IsCutBessel F rep ρ s b F₀ f) : hF.complexData.IsCut F := by
  have h_bes : IsBesselFunction rep F := hF.isBesselFunction .cut
  refine ⟨⟨h_bes.toIsBoundedMeasurable, by simpa using h_bes.map_unipotent_mul⟩,
    fun {x} hx ↦ ?_⟩
  have h_size : besselLength x ≤ ρ := hF.rho_eq.ge.trans' (hF.inCut_of_ne_zero x hx)
  exact RealPlace.exists_norm_le_of_besselLength_le h_size

/-- For the gauge of size `L`, a number has size `i` if its modulus is at most `L ^ i`. -/
lemma mem_ofSize_gauge (hF : IsCutBessel F rep ρ s b F₀ f) (hL : ρ ≤ L) {i : ℕ} {z : ℂ} :
    z ∈ (hF.gauge hL).ofSize i ↔ ‖z‖ ≤ L ^ i :=
  Iff.rfl

/-- For the gauge of size `L`, the list `p` is a head of length `j` if the products of its first
`l ≤ j` entries have inverse modulus at most `L`. -/
lemma isHead_gauge_iff (hF : IsCutBessel F rep ρ s b F₀ f) (hL : ρ ≤ L) :
    (hF.gauge hL).IsHead j p ↔ ∀ l ≤ j, ‖(∏ a ∈ range l, p a).val‖⁻¹ ≤ L := by
  simp only [IsHead, hF.mem_ofSize_gauge, Units.val_inv_eq_inv_val, norm_inv, pow_one]

/-- If the orbital integral J(γ) = ∫ F(y) ⊗ F(γ⁻¹y)^* dy of a cut Bessel function `F` of box size
`ρ` is not zero, then all leading minors of the matrix `realFrameGram γ` of the products
`h(f_a, γ f_b)` have modulus at most `ρ ^ (9 * 𝔰.n)`, where f is the frame (e₀, …, e_{ϱ-1}, z).
-/
theorem norm_leadingMinor_le_of_besselOrbitalIntegral_ne_zero (hF : IsCutBessel F rep ρ s b F₀ f)
    {γ : 𝔰.G₁} (hγ : besselOrbitalIntegral volume F γ ≠ 0) (j : Fin (𝔰.n + 1)) :
    ‖leadingMinor (realFrameGram γ) j‖ ≤ ρ ^ (9 * 𝔰.n) :=
  hF.mem_ofSize_gauge le_rfl |>.1 <|
    (hF.gauge le_rfl).leadingMinor_mem_ofSize_of_besselOrbitalIntegral_ne_zero
      hF.isCut_complexData hγ j

/-- The exponent `s` is at least `10 ^ 10 * 𝔰.n ^ 4`, since the hypotheses carried by `hF` give
`s + 3 𝔰.n + 6 ≥ 𝔰.n ^ 7` and `𝔰.n > 10 ^ 8`. -/
lemma mul_pow_four_le_s (hF : IsCutBessel F rep ρ s b F₀ f) : 10 ^ 10 * 𝔰.n ^ 4 ≤ s := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 𝔰.k = 𝔰.n ^ 7 + K := exists_add_of_le hF.pow_seven_le_k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 𝔰.ϱ = 10 ^ 8 + N := exists_add_of_le hF.ten_pow_le_varrho
  simp only [hF.k_eq, Shape.n, hN] at hK ⊢
  lia

/-- The exponent in the weight of the place datum at ℂ is `s`, since `k = s + 3 n + 6`. -/
lemma volumeExponent_eq (hF : IsCutBessel F rep ρ s b F₀ f) :
    hF.complexData.volumeExponent = s := by
  simp [PlaceData.volumeExponent, PlaceData.blockRank, hF.k_eq]

end

/-- If `1 ≤ L` and `L ^ K ≤ B`, then `max L x ^ K ≤ B * max 1 x ^ K`: replacing `L` by `max L x`
costs at most the factor `max 1 x ^ K`. -/
lemma max_pow_le_mul_max_one_pow {K : ℕ} {L B x : ℝ} (hB : L ^ K ≤ B) (hL : 1 ≤ L) :
    max L x ^ K ≤ B * max 1 x ^ K := by
  have h_max : max L x ≤ L * max 1 x :=
    max_le (le_mul_of_one_le_right (by positivity) (le_max_left 1 x))
      ((le_max_right 1 x).trans (le_mul_of_one_le_left (by positivity) hL))
  grw [h_max, mul_pow, hB]

/-- If the product δ of the first `j + 1` entries of `p` has modulus at most `R`, the weight
`New.headWeight` gains the factor `max 1 ‖δ‖⁻¹ ^ K` from length `j` to length `j + 1`. -/
lemma headWeight_succ_of_le {R : ℝ} (K : ℕ) (h_le : ‖(∏ a ∈ range (j + 1), p a).val‖ ≤ R) :
    headWeight R K (j + 1) p =
      headWeight R K j p * max 1 ‖(∏ a ∈ range (j + 1), p a).val‖⁻¹ ^ K := by
  rw [Units.coe_prod] at h_le ⊢
  rw [headWeight, prod_range_succ, ite_eq_left h_le, headWeight]

/-- For a cut Bessel function `F` of box radius ρ and lists p, q there is L ≥ ρ such that (a) p and
q are heads of length j for the gauge of size L: the products of their first l terms, l ≤ j, have
inverse modulus at most L; (b) L ^ K ≤ ρ ^ K times the weights `New.headWeight` R K j of p and q,
for every R that bounds the moduli of these products. -/
lemma exists_gauge_isHead (hF : IsCutBessel F rep ρ s b F₀ f) (j : ℕ) (p q : ℕ → ℂˣ) (K : ℕ) :
    ∃ L : ℝ, ∃ hL : ρ ≤ L,
      (hF.gauge hL).IsHead j p ∧
      (hF.gauge hL).IsHead j q ∧
      ∀ R : ℝ, (∀ l ≤ j, ‖(∏ a ∈ range l, p a).val‖ ≤ R ∧ ‖(∏ a ∈ range l, q a).val‖ ≤ R) →
        L ^ K ≤ ρ ^ K * (headWeight R K j p * headWeight R K j q) := by
  -- Induction on `j`: `L` is the largest of `ρ` and the inverse norms of the partial products.
  -- Each step enlarges `L` once for `p` and once for `q` (`max_pow_le_mul_max_one_pow`).
  have one_le_ρ : 1 ≤ ρ := by linarith [hF.four_le]
  simp only [hF.isHead_gauge_iff, exists_prop]
  induction j with
  | zero => exact ⟨ρ, le_rfl, by simpa, by simpa, fun R _ ↦ by simp [headWeight]⟩
  | succ j ih =>
    obtain ⟨L, hL, head_p, head_q, h_weight⟩ := ih
    let x : ℂˣ := ∏ a ∈ range (j + 1), p a
    let y : ℂˣ := ∏ a ∈ range (j + 1), q a
    let L' : ℝ := max (max L ‖x.val‖⁻¹) ‖y.val‖⁻¹
    have L_le : L ≤ L' := le_max_of_le_left (le_max_left ..)
    have head_p' : ∀ l ≤ j + 1, ‖(∏ a ∈ range l, p a).val‖⁻¹ ≤ L' := by grind
    have head_q' : ∀ l ≤ j + 1, ‖(∏ a ∈ range l, q a).val‖⁻¹ ≤ L' := by grind
    refine ⟨L', hL.trans L_le, head_p', head_q', fun R h_le ↦ ?_⟩
    have ⟨hx, hy⟩ : ‖x.val‖ ≤ R ∧ ‖y.val‖ ≤ R := h_le (j + 1) le_rfl
    have one_le_L : 1 ≤ L := one_le_ρ.trans hL
    let B : ℝ := ρ ^ K * (headWeight R K j p * headWeight R K j q)
    have step_x : max L ‖x.val‖⁻¹ ^ K ≤ B * max 1 ‖x.val‖⁻¹ ^ K :=
      max_pow_le_mul_max_one_pow (h_weight R fun l hl ↦ h_le l (by lia)) one_le_L
    calc L' ^ K ≤ B * max 1 ‖x.val‖⁻¹ ^ K * max 1 ‖y.val‖⁻¹ ^ K :=
          max_pow_le_mul_max_one_pow step_x (le_max_of_le_left one_le_L)
      _ = ρ ^ K * (headWeight R K (j + 1) p * headWeight R K (j + 1) q) := by
        rw [headWeight_succ_of_le K hx, headWeight_succ_of_le K hy]
        ring

/-- For a cut Bessel function `F`, the integral `pairingNormSq` of `|⟪F x, F y⟫| ^ 2` over two
points of the quotient by the Bessel unipotent group is at most λ² · card I, where λ = `haarRatio`
is the ratio of the two Haar measures. -/
lemma pairingNormSq_le [Nonempty I] (hF : IsCutBessel F rep ρ s b F₀ f) :
    hF.complexData.pairingNormSq F ≤ hF.haarRatio ^ 2 * card I := by
  -- The integral over `y` is at most `haarRatio * ‖F x‖ ^ 2`, as `∫ F ⊗ F^* ≤ 1` on the quotient.
  have h_cut : hF.complexData.IsCut F := hF.isCut_complexData
  have h_meas : Measurable fun g : 𝔰.G₁ ↦ ‖F g‖ₑ ^ 2 := h_cut.stronglyMeasurable.enorm.pow_const 2
  have h_inv : besselU.FixesLeft fun g : 𝔰.G₁ ↦ ‖F g‖ₑ ^ 2 := fun u hu g ↦ by
    simp [h_cut.map_unipotent_mul u hu, enorm_smul, ← ofReal_norm (wave _)]
  set μ : Measure 𝔰.G₁ := hF.complexData.quotientMeasureFrom 0
  -- `h_unfold` turns integrals of invariant functions against `quotientMeasureFrom 0` into
  -- `haarRatio` times integrals over the quotient.
  obtain ⟨-, -, h_unfold, -⟩ := hF.haarRatio_ne_zero_and_groupMeasure_eq_smul
  have h_norm : ∫⁻ g, ‖F g‖ₑ ^ 2 ∂μ ≤ hF.haarRatio * card I := by
    have h_quot : ∫⁻ g, ‖F g‖ₑ ^ 2 ∂besselQuotMeasure ≤ card I := hF.lintegral_sq_cut_le
    grw [h_unfold _ h_meas h_inv, h_quot]
  have h_inner (v : EuclideanSpace ℂ I) :
      ∫⁻ y, ‖inner ℂ v (F y)‖ₑ ^ 2 ∂μ ≤ hF.haarRatio * ‖v‖ₑ ^ 2 := by
    have h_meas_inner : Measurable fun y : 𝔰.G₁ ↦ ‖inner ℂ v (F y)‖ₑ ^ 2 := by fun_prop
    have h_inv_inner : besselU.FixesLeft fun y : 𝔰.G₁ ↦ ‖inner ℂ v (F y)‖ₑ ^ 2 := fun u hu g ↦ by
      simp [h_cut.map_unipotent_mul u hu, enorm_mul, ← ofReal_norm (wave _)]
    have h_quot : ∫⁻ y, ‖inner ℂ v (F y)‖ₑ ^ 2 ∂besselQuotMeasure ≤ ‖v‖ₑ ^ 2 :=
      hF.toIsCutPair.lintegral_sq_inner_cut_le hF.irreducible v
    grw [h_unfold _ h_meas_inner h_inv_inner, h_quot]
  calc hF.complexData.pairingNormSq F ≤ ∫⁻ x, hF.haarRatio * ‖F x‖ₑ ^ 2 ∂μ :=
        lintegral_mono fun x ↦ h_inner (F x)
    _ = hF.haarRatio * ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := lintegral_const_mul _ h_meas
    _ ≤ hF.haarRatio ^ 2 * card I := by grw [h_norm, sq, mul_assoc]

/-! ### Support of the forms -/

/-- Support: let `F` be a cut Bessel function and `l ≤ j ≤ ϱ`. If the product of the first `l`
entries of `p` or of `q` has modulus above `ρ ^ (9 n)`, then the majorant `formMajorant` of the form
of floor `j`, in which both correlations are replaced by their moduli, vanishes at every
position `x`. -/
lemma formMajorant_eq_zero_of_lt (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) {l : ℕ}
    (hl : l ≤ j) (h_big : ρ ^ (9 * 𝔰.n) < ‖(∏ a ∈ range l, p a).val‖ ∨
      ρ ^ (9 * 𝔰.n) < ‖(∏ a ∈ range l, q a).val‖) (x : 𝔰.G₁) :
    hF.complexData.formMajorant j p q F x = 0 := by
  -- An active point `y` (`IsActive`) would bound the products of the entries of both lists
  -- (`head_products_mem_ofSize`). There are none, so `formMajorant_sq_le` holds with the gain `0`.
  have h_cut : hF.complexData.IsCut F := hF.isCut_complexData
  obtain ⟨L, hL, hp, -⟩ := hF.exists_gauge_isHead j p q 0
  have h_small {r : ℕ → ℂˣ} {y : 𝔰.G₁} (hy : F y ≠ 0)
      (h_near : hF.complexData.IsNear j ((FloorGroups.weylElem j r)⁻¹ * y)) :
      ‖(∏ a ∈ range l, r a).val‖ ≤ ρ ^ (9 * 𝔰.n) := by
    obtain ⟨u, hu⟩ : hF.complexData.IsNear j y := h_cut.isNear_of_ne_zero hy
    exact (hF.mem_ofSize_gauge le_rfl).1
      (head_products_mem_ofSize (hF.gauge le_rfl).hasMatrixSize_boxSet hj h_near hu l hl)
  have no_active (y : 𝔰.G₁) : ¬ hF.complexData.IsActive j p q F x y := by
    rintro ⟨hy, near_p, near_q⟩
    rcases h_big with big_p | big_q
    · exact big_p.not_ge (h_small (fun h ↦ hy (by simp [h])) near_p)
    · exact big_q.not_ge (h_small (fun h ↦ hy (by simp [h])) near_q)
  have h_sq : hF.complexData.formMajorant j p q F x ^ 2 ≤
      0 ^ hF.complexData.volumeExponent * ∞ ^ 2 * (hF.gauge hL).weightedSquareProduct j p q F x :=
    formMajorant_sq_le (hF.gauge hL) h_cut hj hp (Set.mem_univ x) (fun _ ↦ le_top) le_top
      fun _ y h_active ↦ (no_active y h_active).elim
  simpa [hF.volumeExponent_eq, hF.mul_cube_lt_s.ne_zero] using h_sq

/-- Let `F` be a cut Bessel function (`hF`) and `l ≤ j ≤ 𝔰.ϱ`. If the product of the first `l`
entries of `p` or of `q` has modulus above `ρ ^ (9 * 𝔰.n)`, then the form `floorForm j p q F ω` of
floor `j` at the place datum `hF.complexData` is zero. This holds for every weight `ω` with
`‖ω x‖ ≤ 1` for all `x`. -/
lemma floorForm_eq_zero_of_lt (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) {l : ℕ}
    (hl : l ≤ j) (h_big : ρ ^ (9 * 𝔰.n) < ‖(∏ a ∈ range l, p a).val‖ ∨
      ρ ^ (9 * 𝔰.n) < ‖(∏ a ∈ range l, q a).val‖) {ω : 𝔰.G₁ → ℂ} (hω : ∀ x : 𝔰.G₁, ‖ω x‖ ≤ 1) :
    hF.complexData.floorForm j p q F ω = 0 := by
  have h_modulus (x : 𝔰.G₁) : hF.complexData.formIntegrandL1Norm j p q F x ω = 0 :=
    le_zero_iff.1 ((hF.isCut_complexData.formIntegrandL1Norm_le_formMajorant hω).trans_eq
      (hF.formMajorant_eq_zero_of_lt hj hl h_big x))
  have h_le : ‖hF.complexData.floorForm j p q F ω‖ₑ ≤ hF.complexData.headDensity j p q *
      ∫⁻ x, hF.complexData.formIntegrandL1Norm j p q F x ω ∂hF.complexData.groupMeasure :=
    enorm_floorForm_le ω
  simpa [h_modulus] using h_le

/-! ### Deep vectors and dyadic shells -/

/-- Let `F` be a cut Bessel function, `p`, `q` heads of length `j ≤ ϱ` for the gauge of size
`L ≥ ρ`, and `x` not in the position ball at a scale `T ≥ L ^ (11 n)`. Suppose `⟪F y, F (y x)⟫ ≠ 0`
and that `w_p⁻¹ y` and `w_q⁻¹ y x` are near at `j`, for the Weyl elements `weylElem j`. Then some
e_a, `a ≥ j`, has `realDepth` at least `T ^ 2`: the infimum of the sum of the squared lengths at `y`
and at `y x`, modulo the e_b with `b < a`, of the vectors ζ orthogonal to these e_b with h(e_a,
ζ) = 1. -/
lemma exists_sq_le_realDepth (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) {hL : ρ ≤ L}
    (hp : (hF.gauge hL).IsHead j p) (hq : (hF.gauge hL).IsHead j q) {T : ℝ}
    (hT : L ^ (11 * 𝔰.n) ≤ T) {x y : 𝔰.G₁} (hx : x ∉ positionBall 𝔰 T)
    (hy : inner ℂ (F y) (F (y * x)) ≠ 0)
    (near_p : hF.complexData.IsNear j ((FloorGroups.weylElem j p)⁻¹ * y))
    (near_q : hF.complexData.IsNear j ((FloorGroups.weylElem j q)⁻¹ * (y * x))) :
    ∃ a : Fin 𝔰.ϱ, j ≤ a ∧ T ^ 2 ≤ realDepth a y (y * x) := by
  -- Otherwise `T⁻¹` lies in each of the discs 𝔡_a = `stableProducts a y x`, `a ≥ j`, and
  -- `hasMatrixSize_sub_one_of_stableProducts`, in the gauge of size `T`, puts `x` in the position
  -- ball.
  have h_cut : hF.complexData.IsCut F := hF.isCut_complexData
  have one_le_L : 1 ≤ L := by linarith [hF.four_le]
  have pow_le (a : ℕ) (ha : a ≤ 11 * 𝔰.n) : L ^ a ≤ T := (pow_le_pow_right₀ one_le_L ha).trans hT
  have L_le : L ≤ T := by simpa using pow_le 1 (by lia)
  have T_pos : 0 < T := by linarith
  let Γ : Gauge hF.complexData := hF.gauge (hL.trans L_le)
  by_contra! h_shallow
  obtain ⟨u, hu, u_box⟩ := h_cut.exists_mul_mem_box (x := y) fun h ↦ hy (by simp [h])
  obtain ⟨v, hv, v_box⟩ := h_cut.exists_mul_mem_box (x := y * x) fun h ↦ hy (by simp [h])
  have h_level : ↑hF.complexData.levelUnit⁻¹ ∈ (hF.gauge hL).ofSize 1 := by
    simpa [hF.mem_ofSize_gauge] using one_le_L
  have h_subset : (hF.gauge hL).ofSize (10 * 𝔰.n) ⊆ Γ.ofSize 1 := fun c hc ↦ by
    simpa [Γ, hF.mem_ofSize_gauge] using
      ((hF.mem_ofSize_gauge hL).1 hc).trans (pow_le (10 * 𝔰.n) (by lia))
  have h_diff : Γ.HasMatrixSize 2
      (hF.complexData.levelUnit⁻¹.val • ((v * (y * x)).val.val - (u * y).val.val)) := by
    simpa using (Γ.hasMatrixSize_boxSet v_box).sub (Γ.hasMatrixSize_boxSet u_box)
  have h_disc (a : Fin 𝔰.ϱ) (ha : j ≤ a) :
      ∃ c : ℂˣ, ↑c ∈ hF.complexData.stableProducts a y x ∧ ↑c⁻¹ ∈ Γ.ofSize 1 := by
    refine ⟨(Units.mk0 (T : ℂ) (by simpa using T_pos.ne'))⁻¹, ?_,
      by simp [Γ, hF.mem_ofSize_gauge, abs_of_pos T_pos]⟩
    simpa [hF.stableProducts_eq, inv_mul_lt_one₀ (pow_pos T_pos 2)] using h_shallow a ha
  have h_size : Γ.HasMatrixSize (99 * 𝔰.n) (hF.complexData.levelUnit⁻¹.val • (x.val.val - 1)) :=
    Γ.hasMatrixSize_sub_one_of_stableProducts (hF.gauge hL) hj hp hq (fun _ ↦ h_level)
      (fun _ ↦ h_subset) ⟨u, hu, v, hv, u_box, v_box, h_diff⟩ near_p near_q h_disc
  exact hx fun a c ↦ by simpa [Γ, hF.mem_ofSize_gauge] using h_size a c

/-- Far means deep at a real place. Let `F` be a cut Bessel function and `p`, `q` heads of length
`j ≤ ϱ` for the gauge of size `L`. A point `y` is active if `⟪F y, F (y x)⟫ ≠ 0` and `w_p⁻¹ y`,
`w_q⁻¹ y x` are near at `j`. If `x` is not in `positionBall` at a scale `T ≥ L ^ (11 n)` and
`T⁻¹ ≤ τ / 2`, then every active point has a vector e_a, `a ≥ j`, whose depth, the inverse area of
the disc `stableProducts a`, is at least `τ⁻²`. -/
lemma hasDeepVector_of_notMem (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) {hL : ρ ≤ L}
    (hp : (hF.gauge hL).IsHead j p) (hq : (hF.gauge hL).IsHead j q) {T τ : ℝ}
    (hT : L ^ (11 * 𝔰.n) ≤ T) (hτ : T⁻¹ ≤ τ / 2) {x : 𝔰.G₁} (hx : x ∉ positionBall 𝔰 T) :
    hF.complexData.HasDeepVector j p q F x (.ofReal τ ^ 2)⁻¹ := by
  rintro y ⟨hy, near_p, near_q⟩
  obtain ⟨a, ha, h_depth⟩ : ∃ a : Fin 𝔰.ϱ, j ≤ a ∧ T ^ 2 ≤ realDepth a y (y * x) :=
    hF.exists_sq_le_realDepth hj hp hq hT hx hy near_p near_q
  have T_pos : 0 < T := (pow_pos (by linarith [hF.four_le]) _).trans_le hT
  have τ_pos : 0 < τ := by linarith [inv_pos.2 T_pos]
  have h_le : (τ ^ 2)⁻¹ ≤ realDepth a y (y * x) / π :=
    calc (τ ^ 2)⁻¹ ≤ ((2 * T⁻¹) ^ 2)⁻¹ := by
          gcongr
          linarith
      _ = T ^ 2 / 4 := by field
      _ ≤ realDepth a y (y * x) / π := div_le_div₀ realDepth_nonneg h_depth pi_pos pi_le_four
  refine ⟨a, ha, ?_⟩
  grw [hF.depth_eq, ← h_le, ← ofReal_pow τ_pos.le, ofReal_inv_of_pos (by positivity)]

/-- Let `F` be a cut Bessel function of box radius `ρ` and `j ≤ ϱ`. For every `g`, the set of `σ`
with `σ g` near at `j + 1` (`New.Floors.PlaceData.IsNear`) has measure at most
`(π ρ ^ 24) ^ k ρ ^ (9999 n)` for the measure `floorMeasure j` of floor `j`. This is `FloorMassLe`
for the weight `1`. -/
lemma floorMassLe (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) :
    hF.complexData.FloorMassLe j (.ofReal ((π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n))) 1 := by
  intro g
  have one_le_ρ : 1 ≤ ρ := by linarith [hF.four_le]
  have h_volume : (ρ ^ 24) ^ (𝔰.k - 5) ≤ (π * ρ ^ 24) ^ 𝔰.k := by
    grw [← one_le_two.trans two_le_pi, one_mul]
    exact pow_le_pow_right₀ (one_le_pow₀ one_le_ρ) (by lia)
  -- The bound of `floorMassLe_one` in the gauge of size `ρ`, whose `loss` is `ρ ^ 2`.
  have h_real : (ρ ^ 2) ^ (99 * 𝔰.n * 13) * ((ρ ^ 2) ^ 12) ^ (𝔰.k - 5) ≤
      (π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n) :=
    calc _ = (ρ ^ 24) ^ (𝔰.k - 5) * ρ ^ (2574 * 𝔰.n) := by ring
      _ ≤ _ := by
        gcongr
        lia
  grw [(hF.gauge le_rfl).floorMassLe_one ⟨j, by lia⟩ g, volume_ofSize_le]
  simpa (disch := finiteness) [RealPlaceSizes.gauge, ← toReal_le_toReal, PlaceData.blockRank,
    Nat.sub_sub] using h_real

/-- The bound `(π ρ ^ 24) ^ k ρ ^ (9999 n)` for the mass of a floor is at least 1. -/
lemma one_le_massBound (hF : IsCutBessel F rep ρ s b F₀ f) :
    1 ≤ ENNReal.ofReal ((π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n)) := by
  have one_le_ρ : 1 ≤ ρ := by linarith [hF.four_le]
  have one_le_π : 1 ≤ π := one_le_two.trans two_le_pi
  exact one_le_ofReal.2 (by bound)

/-- If `2 ≤ L`, `0 < τ ≤ 1`, `n ≠ 0` and `L ^ (2400 n²) ≤ τ ^ (400 n²) H`, then at the scale
`T = L ^ (11 n + 1) / τ` the number `T ^ (99 n)` is at most half of `H`. -/
lemma two_mul_div_pow_le_of_pow_le {n : ℕ} (hn : n ≠ 0) {L τ H : ℝ} (two_le_L : 2 ≤ L)
    (τ_pos : 0 < τ) (τ_le : τ ≤ 1) (h_le : L ^ (2400 * n ^ 2) ≤ τ ^ (400 * n ^ 2) * H) :
    2 * (L ^ (11 * n + 1) / τ) ^ (99 * n) ≤ H := by
  have one_le_L : 1 ≤ L := one_le_two.trans two_le_L
  have n_le : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  refine le_of_mul_le_mul_left ?_ (pow_pos τ_pos (400 * n ^ 2))
  calc τ ^ (400 * n ^ 2) * (2 * (L ^ (11 * n + 1) / τ) ^ (99 * n))
      ≤ τ ^ (99 * n) * (L * (L ^ (11 * n + 1) / τ) ^ (99 * n)) := by
        gcongr ?_ * (?_ * _)
        exact pow_le_pow_of_le_one τ_pos.le τ_le (by lia)
    _ = L ^ ((11 * n + 1) * (99 * n) + 1) := by
        rw [mul_left_comm, ← mul_pow, mul_div_cancel₀ _ τ_pos.ne', ← pow_mul, ← pow_succ']
    _ ≤ L ^ (2400 * n ^ 2) := pow_le_pow_right₀ one_le_L (by lia)
    _ ≤ τ ^ (400 * n ^ 2) * H := h_le

/-- Let `F` be a cut Bessel function and `p`, `q` heads of length `j ≤ ϱ` for the gauge of size `L`,
whose `loss` is L². The dyadic shell of index `i` is a shell of height H = `2 ^ i` for this gauge.
It is covered by the positions `x` with `x - 1` of size 1 for at most 2 H ^ (9 n) gauges of loss at
most L² H². If σ < 1 and L ^ (2400 n²) ≤ σ ^ (400 n²) H, then at each of its positions every active
point has a vector e_a, `a ≥ j`, of depth at least σ⁻². -/
lemma isShell_dyadicShell [Nonempty I]
    (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) {hL : ρ ≤ L}
    (hp : (hF.gauge hL).IsHead j p) (hq : (hF.gauge hL).IsHead j q) (i : ℕ) :
    (hF.gauge hL).IsShell j p q F (dyadicShell 𝔰 i) (2 ^ i) := by
  have two_le_L : 2 ≤ L := by linarith [hF.four_le]
  have one_le_L : 1 ≤ L := one_le_two.trans two_le_L
  refine ⟨one_le_pow₀ one_le_two, by finiteness, ?_, fun x hx σ hσ_lt hσ ↦ ?_⟩
  · -- One gauge, of size `L * 2 ^ i`, covers the shell.
    have ρ_le : ρ ≤ L * 2 ^ i :=
      hL.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ one_le_two))
    have h_cover : dyadicShell 𝔰 i ⊆ (hF.gauge ρ_le).positionsOfSize := by
      rintro x ⟨h_bound, -⟩
      refine ⟨Set.mem_univ x, fun a c ↦ ?_⟩
      simpa [hF.mem_ofSize_gauge] using
        (h_bound a c).trans (le_mul_of_one_le_left (by positivity) one_le_L)
    have h_scale : (hF.gauge ρ_le).loss ≤ (hF.gauge hL).loss * (2 ^ i) ^ 2 := by
      simp [RealPlaceSizes.gauge, ofReal_mul (zero_le_one.trans one_le_L), mul_pow]
    refine ⟨{hF.gauge ρ_le}, ?_, by simpa using h_cover, by simpa using h_scale⟩
    simpa using one_le_mul one_le_two (one_le_pow₀ (one_le_pow₀ one_le_two))
  -- Pass to real numbers: `L ^ (2400 n²) ≤ τ ^ (400 n²) 2 ^ i` with `0 < τ < 1`.
  lift σ to NNReal using hσ_lt.ne_top with τ
  have τ_lt : (τ : ℝ) < 1 := by exact_mod_cast hσ_lt
  have h_real : L ^ (2400 * 𝔰.n ^ 2) ≤ (τ : ℝ) ^ (400 * 𝔰.n ^ 2) * 2 ^ i :=
    calc L ^ (2400 * 𝔰.n ^ 2) = ((hF.gauge hL).loss ^ (1200 * 𝔰.n ^ 2)).toReal := by
          simp [RealPlaceSizes.gauge, ← pow_mul, zero_le_one.trans one_le_L, ← mul_assoc]
      _ ≤ ((τ : ℝ≥0∞) ^ (400 * 𝔰.n ^ 2) * 2 ^ i).toReal := toReal_mono (by finiteness) hσ
      _ = (τ : ℝ) ^ (400 * 𝔰.n ^ 2) * 2 ^ i := by simp
  have τ_pos : (0 : ℝ) < τ := τ.coe_nonneg.lt_of_ne fun h_zero ↦ by
    rw [← h_zero, zero_pow (by positivity), zero_mul] at h_real
    exact h_real.not_gt (by positivity)
  -- The position `x` is not in the position ball at the scale `T = L ^ (11 n + 1) / τ`.
  let T : ℝ := L ^ (11 * 𝔰.n + 1) / τ
  have h_scale : L ^ (11 * 𝔰.n + 1) ≤ T := le_div_self (by positivity) τ_pos τ_lt.le
  have h_far : x ∉ positionBall 𝔰 T :=
    notMem_positionBall_of_mem_dyadicShell hx ((one_le_pow₀ one_le_L).trans h_scale)
      (two_mul_div_pow_le_of_pow_le (by lia) two_le_L τ_pos τ_lt.le h_real)
  have h_radius : T⁻¹ ≤ τ / 2 := by
    rw [inv_div]
    gcongr
    exact two_le_L.trans (le_self_pow₀ one_le_L (by lia))
  have pow_le : L ^ (11 * 𝔰.n) ≤ T := (pow_le_pow_right₀ one_le_L (by lia)).trans h_scale
  simpa only [ofReal_coe_nnreal] using hF.hasDeepVector_of_notMem hj hp hq pow_le h_radius h_far

/-! ### Summation over the shells -/

/-- Let `F` be a cut Bessel function, `p`, `q` heads of length `j ≤ ϱ` for the gauge of size `L`,
and `1 ≤ t`. Let `φ` lie below the majorant of the form of floor `j` and, if `1 < t`, have a square
at most `((π ρ ^ 24) ^ k ρ ^ (9999 n) / t ^ s) ^ 2` times the product of norms. Then the normalised
integral of `φ`, times the dimension `card I` of the value space, is at most `scaledVolumeRatio * L
^ (10 ^ 9 n ^ 4) * ρ ^ (24 k) * t ^ (10 ^ 8 n ^ 4) / t ^ s`. -/
lemma formConst_mul_lintegral_le [Nonempty I]
    (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) {hL : ρ ≤ L}
    (hp : (hF.gauge hL).IsHead j p) (hq : (hF.gauge hL).IsHead j q) (ht : 1 ≤ t) {φ : 𝔰.G₁ → ℝ≥0∞}
    (hφ_le : φ ≤ hF.complexData.formMajorant j p q F)
    (hφ_gain : 1 < t → ∀ x : 𝔰.G₁, φ x ^ 2 ≤
      .ofReal ((π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n) / t ^ s) ^ 2 *
        (hF.gauge hL).weightedSquareProduct j p q F x) :
    card I * (‖(hF.formConst : ℂ)‖ₑ *
        (hF.complexData.headDensity j p q * ∫⁻ x, φ x ∂hF.complexData.groupMeasure)) ≤
      .ofReal (𝔰.scaledVolumeRatio * L ^ (10 ^ 9 * 𝔰.n ^ 4) * ρ ^ (24 * 𝔰.k) *
        t ^ (10 ^ 8 * 𝔰.n ^ 4) / t ^ s) := by
  -- Sum over the dyadic shells with the mass bound `V`, the gain `t⁻¹` and `r = s - 10 ^ 8 n ^ 4`.
  obtain ⟨one_le_ρ, one_le_L⟩ : 1 ≤ ρ ∧ 1 ≤ L := by grind [hF.four_le]
  have one_le_π : 1 ≤ π := one_le_two.trans two_le_pi
  obtain ⟨⟨ratio_ne_zero : hF.haarRatio ≠ 0, ratio_ne_top : hF.haarRatio ≠ ∞⟩, -⟩ :=
    hF.haarRatio_ne_zero_and_groupMeasure_eq_smul
  obtain ⟨r, hr⟩ : ∃ r : ℕ, s = 10 ^ 8 * 𝔰.n ^ 4 + r :=
    exists_add_of_le ((by lia : 10 ^ 8 * 𝔰.n ^ 4 ≤ 10 ^ 10 * 𝔰.n ^ 4).trans hF.mul_pow_four_le_s)
  let V : ℝ := (π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n)
  have h_cover : φ.support ⊆ ⋃ i, dyadicShell 𝔰 i := fun x _ ↦
    Set.mem_iUnion.2 (exists_mem_dyadicShell x)
  have h_gain (h_lt : ENNReal.ofReal t⁻¹ < 1) (x : 𝔰.G₁) (_ : x ∈ hF.complexData.positions) :
      φ x ^ 2 ≤ (.ofReal V * .ofReal t⁻¹ ^ hF.complexData.volumeExponent) ^ 2 *
        (hF.gauge hL).weightedSquareProduct j p q F x := by
    rw [hF.volumeExponent_eq, ← ofReal_pow (by positivity), ← ofReal_mul (by positivity), inv_pow]
    exact hφ_gain ((inv_lt_one₀ (by positivity)).1 (ofReal_lt_one.1 h_lt)) x
  have r_le : 9 * 10 ^ 7 * 𝔰.n ^ 4 + r ≤ hF.complexData.volumeExponent := by
    rw [hF.volumeExponent_eq]
    lia
  have h_shells : hF.complexData.headDensity j p q * ∫⁻ x, φ x ∂hF.complexData.groupMeasure ≤
      .ofReal V * min 1 (.ofReal t⁻¹) ^ r * (hF.gauge hL).loss ^ (4 * 10 ^ 8 * 𝔰.n ^ 4) *
        hF.complexData.shellNormalization F :=
    (hF.gauge hL).lintegral_le_of_shells (hF.isShell_dyadicShell hj hp hq) h_cover
      hF.isCut_complexData hj hp hq (hF.floorMassLe hj) hF.one_le_massBound hφ_le h_gain r_le
  -- At the place ℂ the level is `1`, `kernelBound` is `π ^ 2` and the `loss` is `L ^ 2`.
  have unit_le : hF.complexData.shellNormalization F ≤
      .ofReal (π ^ (2 * ((𝔰.k - 5) * 𝔰.ϱ))) * (hF.haarRatio ^ 2 * card I) := by
    grw [shellNormalization, hF.pairingNormSq_le]
    simp [floorModulus, PlaceData.blockRank, Nat.sub_sub, ← pow_mul, pi_pos.le]
  have scale_eq : (hF.gauge hL).loss = .ofReal L ^ 2 := by simp [RealPlaceSizes.gauge]
  grw [h_shells, min_le_right, unit_le, scale_eq]
  -- `haarRatio`, `card I` and the volumes cancel: it remains to compare powers of `π`, `ρ` and `L`.
  suffices h_powers :
      π ^ 𝔰.k * ρ ^ (9999 * 𝔰.n) * L ^ (2 * (400000000 * 𝔰.n ^ 4)) *
          π ^ (2 * ((𝔰.k - 5) * 𝔰.ϱ)) ≤
        π ^ ((2 * 𝔰.ϱ + 1) * 𝔰.k) * L ^ (1000000000 * 𝔰.n ^ 4) by
    have t_pow : t ^ s = t ^ (10 ^ 8 * 𝔰.n ^ 4) * t ^ r := by rw [← pow_add, ← hr]
    rw [t_pow]
    simpa (disch := finiteness) [V, ← toReal_le_toReal, toReal_ne_zero, ratio_ne_zero,
      ratio_ne_top, formConst, scaledVolumeRatio, volU, field, mul_pow, ← pow_mul, abs_of_nonneg]
      using h_powers
  calc
    _ ≤ π ^ 𝔰.k * L ^ (9999 * 𝔰.n) * L ^ (2 * (400000000 * 𝔰.n ^ 4)) *
        π ^ (2 * (𝔰.k * 𝔰.ϱ)) := by
      gcongr
      exact Nat.sub_le ..
    _ = π ^ ((2 * 𝔰.ϱ + 1) * 𝔰.k) * L ^ (9999 * 𝔰.n + 2 * (400000000 * 𝔰.n ^ 4)) := by ring
    _ ≤ π ^ ((2 * 𝔰.ϱ + 1) * 𝔰.k) * L ^ (1000000000 * 𝔰.n ^ 4) := by
      gcongr
      have n_le : 𝔰.n ≤ 𝔰.n ^ 4 := Nat.le_self_pow four_ne_zero 𝔰.n
      lia

/-- Remote positions. Let `F` be a cut Bessel function and `p`, `q` heads of length `j ≤ ϱ` for the
gauge of size `L ≥ ρ`. Let `1 ≤ t`. Integrate the majorant `formMajorant` over the positions `x`
that are not in `positionBall` at the scale `t L ^ (11 n)`, meaning some entry of `x - 1` has
modulus above that scale to the power `99 n`. This integral, times `formConst` and `headDensity`, is
at most `scaledVolumeRatio * L ^ (10 ^ 9 n ^ 4) * ρ ^ (24 k) * t ^ (10 ^ 8 n ^ 4) / t ^ s`. -/
lemma formConst_mul_setLIntegral_compl_positionBall_le [Nonempty I]
    (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ)
    {hL : ρ ≤ L} (hp : (hF.gauge hL).IsHead j p) (hq : (hF.gauge hL).IsHead j q) (ht : 1 ≤ t) :
    ‖(hF.formConst : ℂ)‖ₑ * (hF.complexData.headDensity j p q *
        ∫⁻ x in (positionBall 𝔰 (t * L ^ (11 * 𝔰.n)))ᶜ,
          hF.complexData.formMajorant j p q F x ∂hF.complexData.groupMeasure) ≤
      .ofReal (𝔰.scaledVolumeRatio * L ^ (10 ^ 9 * 𝔰.n ^ 4) * ρ ^ (24 * 𝔰.k) *
        t ^ (10 ^ 8 * 𝔰.n ^ 4) / t ^ s) := by
  -- These positions have a deep vector; apply the sum over all shells to the majorant on them.
  obtain ⟨two_le_L, one_le_L⟩ : 2 ≤ L ∧ 1 ≤ L := by grind [hF.four_le]
  have one_le_card : (1 : ℝ≥0∞) ≤ card I := mod_cast card_pos
  rw [← lintegral_indicator (measurableSet_positionBall _).compl]
  refine (le_mul_of_one_le_left' one_le_card).trans
    (hF.formConst_mul_lintegral_le hj hp hq ht (Set.indicator_le_self _ _) fun _ x ↦ ?_)
  by_cases hx : x ∈ positionBall 𝔰 (t * L ^ (11 * 𝔰.n))
  · simp [hx]
  have h_radius : (t * L ^ (11 * 𝔰.n))⁻¹ ≤ t⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]
    gcongr
    exact two_le_L.trans (le_self_pow₀ one_le_L (by lia))
  have h_deep : hF.complexData.HasDeepVector j p q F x (.ofReal t⁻¹ ^ 2)⁻¹ :=
    hF.hasDeepVector_of_notMem hj hp hq (le_mul_of_one_le_left (by positivity) ht) h_radius hx
  have ρ_pos : 0 < ρ := by linarith [hF.four_le]
  let V : ℝ := (π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n)
  rw [Set.indicator_of_mem hx]
  calc hF.complexData.formMajorant j p q F x ^ 2
      ≤ (.ofReal t⁻¹ ^ 2) ^ s * .ofReal V ^ 2 * (hF.gauge hL).weightedSquareProduct j p q F x := by
        simpa only [hF.volumeExponent_eq] using (hF.gauge hL).formMajorant_sq_le_of_hasDeepVector
          hF.isCut_complexData hj hp ⟨⟩ (hF.floorMassLe hj) hF.one_le_massBound h_deep
    _ = .ofReal (V / t ^ s) ^ 2 * (hF.gauge hL).weightedSquareProduct j p q F x := by
        rw [div_eq_mul_inv, ← inv_pow, ofReal_mul (q := t⁻¹ ^ s) (by positivity),
          ofReal_pow (by positivity) s]
        ring

/-- Absolute convergence: if `F` is a cut Bessel function (`hF`) and `j ≤ 𝔰.ϱ`, then the majorant
`formMajorant j p q F` of the form of floor `j` at the place datum `hF.complexData` has finite
integral over `(𝔰.middleGram 1).G` against `hF.complexData.groupMeasure`. -/
lemma lintegral_formMajorant_ne_top [Nonempty I]
    (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) :
    ∫⁻ x : (𝔰.middleGram (1 : ℂ)).G,
      hF.complexData.formMajorant j p q F x ∂hF.complexData.groupMeasure ≠ ∞ := by
  -- `formConst_mul_lintegral_le` with `t = 1` gives a finite bound for a nonzero multiple of it.
  obtain ⟨L, hL, hp, hq, -⟩ := hF.exists_gauge_isHead j p q 0
  have h_finite : card I * (‖(hF.formConst : ℂ)‖ₑ * (hF.complexData.headDensity j p q *
      ∫⁻ x, hF.complexData.formMajorant j p q F x ∂hF.complexData.groupMeasure)) ≠ ∞ :=
    ne_top_of_le_ne_top ofReal_ne_top
      (hF.formConst_mul_lintegral_le hj hp hq le_rfl le_rfl fun h ↦ absurd h (lt_irrefl 1))
  have h_factor : card I * ‖(hF.formConst : ℂ)‖ₑ * hF.complexData.headDensity j p q ≠ 0 := by
    simp [headDensity, formConst, prod_eq_zero_iff, toReal_ne_zero, ne_of_gt,
      haarRatio_ne_zero_and_groupMeasure_eq_smul]
  intro h_top
  rw [h_top, ← mul_assoc, ← mul_assoc, ENNReal.mul_top h_factor] at h_finite
  exact h_finite rfl

/-- Let `ρ`, `s`, `b` be the sizes of a cut Bessel function, `0 < r` and `1 ≤ L`, and let `H ≥ 0`
satisfy `L ^ n ^ 6 ≤ ρ ^ n ^ 6 * H`. At `t = max 1 (ρ ^ 24 * r)`, the bound for the sum over all
shells (`formConst_mul_lintegral_le`) is at most `scaledVolumeRatio * b ^ (2000 n ^ 9) * dampedPower
(k - n ^ 7) r⁻¹ * H`. -/
lemma shell_bound_le_dampedPower (hF : IsCutBessel F rep ρ s b F₀ f) {r H : ℝ} (r_pos : 0 < r)
    (one_le_L : 1 ≤ L) (H_nonneg : 0 ≤ H) (L_le : L ^ 𝔰.n ^ 6 ≤ ρ ^ 𝔰.n ^ 6 * H) :
    𝔰.scaledVolumeRatio * L ^ (10 ^ 9 * 𝔰.n ^ 4) * ρ ^ (24 * 𝔰.k) *
        max 1 (ρ ^ 24 * r) ^ (10 ^ 8 * 𝔰.n ^ 4) / max 1 (ρ ^ 24 * r) ^ s ≤
      𝔰.scaledVolumeRatio * b ^ (2000 * 𝔰.n ^ 9) * dampedPower (𝔰.k - 𝔰.n ^ 7) r⁻¹ * H := by
  have one_le_ρ : 1 ≤ ρ := by linarith [hF.four_le]
  have one_le_b : 1 ≤ b := one_le_two.trans hF.two_le_b
  have const_pos : 0 < 𝔰.scaledVolumeRatio := by
    unfold scaledVolumeRatio volU
    positivity
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 𝔰.k = 𝔰.n ^ 7 + K := exists_add_of_le hF.pow_seven_le_k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 𝔰.ϱ = 10 ^ 8 + N := exists_add_of_le hF.ten_pow_le_varrho
  -- The exponent bounds use `10 ^ 8 ≤ 𝔰.ϱ` and `𝔰.n ^ 7 + K = 𝔰.k = s + 3 * 𝔰.n + 6`.
  have exp_L : 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6 := by
    simp only [Shape.n, hN]
    lia
  have exp_t : 10 ^ 8 * 𝔰.n ^ 4 + (K + 6) ≤ s := by
    simp only [hF.k_eq, Shape.n, hN] at hK ⊢
    lia
  set t : ℝ := max 1 (ρ ^ 24 * r)
  have one_le_t : 1 ≤ t := le_max_left ..
  have mul_le_t : ρ ^ 24 * r ≤ t := le_max_right ..
  have const_le : ρ ^ 𝔰.n ^ 6 * ρ ^ (24 * 𝔰.n ^ 7) ≤ b ^ (2000 * 𝔰.n ^ 9) := by
    -- Both sides are powers of `b`, as `ρ = b ^ (6 * 𝔰.n + 2)`: compare exponents.
    simp only [hF.rho_eq, ← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ one_le_b (by lia)
  have div_le : ρ ^ 24 / t ≤ r⁻¹ := by
    rwa [div_le_iff₀ (by positivity), le_inv_mul_iff₀' r_pos]
  have inv_le : t⁻¹ ≤ min 1 r⁻¹ :=
    le_min (inv_le_one_of_one_le₀ one_le_t) (inv_anti₀ r_pos
      ((le_mul_of_one_le_left r_pos.le (one_le_pow₀ one_le_ρ)).trans mul_le_t))
  calc
    _ ≤ 𝔰.scaledVolumeRatio * (ρ ^ 𝔰.n ^ 6 * H) * ρ ^ (24 * 𝔰.k) *
        t ^ (10 ^ 8 * 𝔰.n ^ 4) / t ^ (10 ^ 8 * 𝔰.n ^ 4 + (K + 6)) := by
      grw [exp_L, L_le, ← exp_t]
    _ = 𝔰.scaledVolumeRatio * (ρ ^ 𝔰.n ^ 6 * ρ ^ (24 * 𝔰.n ^ 7)) *
        ((ρ ^ 24 / t) ^ K * t⁻¹ ^ 6) * H := by
      simp [hK, field, pow_add, div_pow, mul_add, pow_mul]
    _ ≤ 𝔰.scaledVolumeRatio * b ^ (2000 * 𝔰.n ^ 9) * (r⁻¹ ^ K * min 1 r⁻¹ ^ 6) * H := by
      grw [const_le, div_le, inv_le]
    _ = _ := by rw [dampedPower, hK, Nat.add_sub_cancel_left]

/-- For `1 ≤ ρ`, `0 < r`, `1 ≤ ρ ^ 24 * r` and `s ≤ m ≤ k`, the power `(π ^ 2 / r ^ 2) ^ m` is at
most the square of `(π ρ ^ 24) ^ k ρ ^ e / (ρ ^ 24 r) ^ s`. -/
lemma pi_sq_div_sq_pow_le {m k : ℕ} (e : ℕ) {r : ℝ} (one_le_ρ : 1 ≤ ρ) (r_pos : 0 < r)
    (one_le_mul : 1 ≤ ρ ^ 24 * r) (s_le : s ≤ m) (m_le : m ≤ k) :
    (π ^ 2 / r ^ 2) ^ m ≤ ((π * ρ ^ 24) ^ k * ρ ^ e / (ρ ^ 24 * r) ^ s) ^ 2 := by
  have one_le_base : 1 ≤ π * ρ ^ 24 :=
    one_le_mul_of_one_le_of_one_le (one_le_two.trans two_le_pi) (one_le_pow₀ one_le_ρ)
  have ratio_eq : π / r = π * ρ ^ 24 / (ρ ^ 24 * r) := by field
  calc (π ^ 2 / r ^ 2) ^ m = ((π * ρ ^ 24) ^ m * 1 / (ρ ^ 24 * r) ^ m) ^ 2 := by
        rw [mul_one, ← div_pow, ← div_pow, ← ratio_eq, pow_right_comm]
    _ ≤ ((π * ρ ^ 24) ^ k * ρ ^ e / (ρ ^ 24 * r) ^ s) ^ 2 := by
        gcongr
        exact one_le_pow₀ one_le_ρ

/-- Let `F` be a cut Bessel function with base `b`, let `j ≤ ϱ` be a floor, `p`, `q` lists of units,
`y` a unit and `ω` a weight of modulus at most one on G₁. At a position `x`, `formIntegrandL1Norm`
is the integral of the modulus of the integrand of the form `floorForm j p q F ω` of floor `j`, and
`Γ.weightedSquareProduct` is the product of the second moments of its two correlations, with the
constants of the gauge `Γ`. Suppose that for every gauge in which `p` is a head of length `j` the
square of the first is at most the second times `(π / ‖y‖) ^ (2 (k - 5))`, which is the value at the
place ℂ of the power in `h_local`. Then the modulus of the form, normalised by `formConst`, times
the dimension `card I` is at most `scaledVolumeRatio * b ^ (2000 n ^ 9)` times
`dampedPower (k - n ^ 7) ‖y‖⁻¹` times the weights `New.headWeight` of `p` and `q`. -/
lemma norm_floorForm_le [Nonempty I] (hF : IsCutBessel F rep ρ s b F₀ f) (hj : j ≤ 𝔰.ϱ) (y : ℂˣ)
    {ω : 𝔰.G₁ → ℂ} (hω : ∀ x : 𝔰.G₁, ‖ω x‖ ≤ 1)
    (h_local : ∀ Γ : Gauge hF.complexData, Γ.IsHead j p → ∀ {x : 𝔰.G₁},
      hF.complexData.formIntegrandL1Norm j p q F x ω ^ 2 ≤
        (complexPlace.kernelBound / complexPlace.modulus y) ^ card hF.complexData.FreeIndex *
          Γ.weightedSquareProduct j p q F x) :
    card I * ‖hF.formConst * hF.complexData.floorForm j p q F ω‖ ≤
      𝔰.scaledVolumeRatio * b ^ (2000 * 𝔰.n ^ 9) * dampedPower (𝔰.k - 𝔰.n ^ 7) ‖(y : ℂ)‖⁻¹ *
        (headWeight (b ^ (60 * 𝔰.n ^ 2)) (𝔰.n ^ 6) j p *
          headWeight (b ^ (60 * 𝔰.n ^ 2)) (𝔰.n ^ 6) j q) := by
  -- Apply `formConst_mul_lintegral_le` with `t = max 1 (ρ ^ 24 * ‖y‖)` in a gauge for both heads.
  -- The weights of the heads pay the size `L` of the gauge if their partial products are at most
  -- `R`; if not, the form is `0` (`floorForm_eq_zero_of_lt`).
  have one_le_ρ : 1 ≤ ρ := by linarith [hF.four_le]
  have one_le_b : 1 ≤ b := one_le_two.trans hF.two_le_b
  have y_pos : 0 < ‖(y : ℂ)‖ := y.norm_pos
  set R : ℝ := b ^ (60 * 𝔰.n ^ 2)
  set H : ℝ := headWeight R (𝔰.n ^ 6) j p * headWeight R (𝔰.n ^ 6) j q
  have H_nonneg : 0 ≤ H := mul_nonneg (headWeight_nonneg ..) (headWeight_nonneg ..)
  have bound_nonneg : 0 ≤ 𝔰.scaledVolumeRatio * b ^ (2000 * 𝔰.n ^ 9) *
      dampedPower (𝔰.k - 𝔰.n ^ 7) ‖(y : ℂ)‖⁻¹ * H := by
    unfold scaledVolumeRatio volU dampedPower
    positivity
  by_cases! h_minors :
      ∃ l ≤ j, R < ‖(∏ a ∈ range l, p a).val‖ ∨ R < ‖(∏ a ∈ range l, q a).val‖
  · obtain ⟨l, hl, h_big⟩ := h_minors
    have pow_le_R : ρ ^ (9 * 𝔰.n) ≤ R := by
      have three_le_n : 3 ≤ 𝔰.n := Nat.succ_le_succ (le_trans (by norm_num) hF.ten_pow_le_varrho)
      rw [hF.rho_eq, ← pow_mul]
      exact pow_le_pow_right₀ one_le_b (by nlinarith)
    have form_eq : hF.complexData.floorForm j p q F ω = 0 :=
      hF.floorForm_eq_zero_of_lt hj hl (h_big.imp pow_le_R.trans_lt pow_le_R.trans_lt) hω
    rwa [form_eq, mul_zero, norm_zero, mul_zero]
  obtain ⟨L, hL, hp, hq, h_pay⟩ : ∃ L : ℝ, ∃ hL : ρ ≤ L, (hF.gauge hL).IsHead j p ∧
      (hF.gauge hL).IsHead j q ∧
      ∀ R : ℝ, (∀ l ≤ j, ‖(∏ a ∈ range l, p a).val‖ ≤ R ∧ ‖(∏ a ∈ range l, q a).val‖ ≤ R) →
        L ^ 𝔰.n ^ 6 ≤ ρ ^ 𝔰.n ^ 6 * (headWeight R (𝔰.n ^ 6) j p * headWeight R (𝔰.n ^ 6) j q) :=
    hF.exists_gauge_isHead j p q (𝔰.n ^ 6)
  have L_le : L ^ 𝔰.n ^ 6 ≤ ρ ^ 𝔰.n ^ 6 * H := h_pay R h_minors
  let t : ℝ := max 1 (ρ ^ 24 * ‖(y : ℂ)‖)
  have one_le_t : 1 ≤ t := le_max_left ..
  have h_major (x : 𝔰.G₁) :
      hF.complexData.formIntegrandL1Norm j p q F x ω ≤ hF.complexData.formMajorant j p q F x :=
    hF.isCut_complexData.formIntegrandL1Norm_le_formMajorant hω
  -- For `1 < t` we have `t = ρ ^ 24 * ‖y‖`, and `h_local` gives the gain that
  -- `formConst_mul_lintegral_le` asks for.
  have h_gain (ht : 1 < t) (x : 𝔰.G₁) : hF.complexData.formIntegrandL1Norm j p q F x ω ^ 2 ≤
      .ofReal ((π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n) / t ^ s) ^ 2 *
        (hF.gauge hL).weightedSquareProduct j p q F x := by
    have exp_le : s ≤ 𝔰.k - 5 := by
      rw [hF.k_eq]
      lia
    have one_le_mul : 1 ≤ ρ ^ 24 * ‖(y : ℂ)‖ := ((lt_max_iff.1 ht).resolve_left (lt_irrefl 1)).le
    have t_eq : t = ρ ^ 24 * ‖(y : ℂ)‖ := max_eq_right one_le_mul
    have h_real : (π ^ 2 / ‖(y : ℂ)‖ ^ 2) ^ (𝔰.k - 5) ≤
        ((π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n) / (ρ ^ 24 * ‖(y : ℂ)‖) ^ s) ^ 2 :=
      pi_sq_div_sq_pow_le (9999 * 𝔰.n) one_le_ρ y_pos one_le_mul exp_le (Nat.sub_le ..)
    grw [h_local (hF.gauge hL) hp, t_eq]
    gcongr 1
    -- At the place ℂ, `kernelBound` is `π ^ 2` and the modulus of `y` is `‖y‖ ^ 2`.
    simpa (disch := finiteness) [← ofReal_norm, ← toReal_le_toReal, div_pow, field,
      PlaceData.blockRank, Nat.sub_sub] using h_real
  rw [← ofReal_le_ofReal_iff bound_nonneg]
  calc
    _ = card I * (‖(hF.formConst : ℂ)‖ₑ * ‖hF.complexData.floorForm j p q F ω‖ₑ) := by
      rw [ofReal_mul (Nat.cast_nonneg _), ofReal_natCast, ofReal_norm, enorm_mul]
    _ ≤ card I * (‖(hF.formConst : ℂ)‖ₑ * (hF.complexData.headDensity j p q *
        ∫⁻ x, hF.complexData.formIntegrandL1Norm j p q F x ω ∂hF.complexData.groupMeasure)) := by
      grw [enorm_floorForm_le]
    _ ≤ .ofReal (𝔰.scaledVolumeRatio * L ^ (10 ^ 9 * 𝔰.n ^ 4) * ρ ^ (24 * 𝔰.k) *
        t ^ (10 ^ 8 * 𝔰.n ^ 4) / t ^ s) := by
      grw [hF.formConst_mul_lintegral_le hj hp hq one_le_t h_major h_gain]
    _ ≤ .ofReal (𝔰.scaledVolumeRatio * b ^ (2000 * 𝔰.n ^ 9) *
        dampedPower (𝔰.k - 𝔰.n ^ 7) ‖(y : ℂ)‖⁻¹ * H) :=
      ofReal_le_ofReal (hF.shell_bound_le_dampedPower y_pos (one_le_ρ.trans hL) H_nonneg L_le)

end IsCutBessel

end ComplexShells

end New.Floors

end
