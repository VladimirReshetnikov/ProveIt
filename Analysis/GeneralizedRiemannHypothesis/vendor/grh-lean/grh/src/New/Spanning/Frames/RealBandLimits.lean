import Lib.Cohomology.Etale.Basic
import New.Spanning.Frames.RealShells

/-!
# The normalized cell integral Ξ and the local bounds at ℂ for cut Bessel functions

This file defines the normalized cell integral Ξ at the chart of the top floor, proves that it is
continuous, and gives the descent from each floor to the one below. It bounds the mass on the bottom
floor by the position ball and remote positions, and proves decay in the frequency and for unequal
last entries. At the end, a cut Bessel function `F` of a Bessel function `W` satisfies the local
bounds `New.HasLocalBounds` read by the sieve, given bounds on the matrix coefficient of `W` and on
volumes of balls. The place ℂ lies over a real place of the totally real subfield, and the
docstrings call it a real place.

`New.HasLocalBounds` asks for a system of forms `New.SieveSystem` on floors `0, …, ϱ + 1`, each
below the top an integral of the next one.

Throughout `F` is the cut of the Bessel function `W`, n = ϱ + 1, k = card κ and r is the rank of G₁.

## Main definitions and results

* `New.Floors.IsCutBessel.norm_floorForm_zero_le`: the mass at a real place, by the position ball
  and remote positions.
* `New.Floors.IsCutBessel.norm_floorForm_wave_le`, `New.Floors.IsCutBessel.norm_floorForm_heads_le`:
  decay in the frequency and for unequal last entries.
* `New.Floors.exists_hasLocalBounds_of_isCutBessel`: the local bounds.

Notions from other files:
* `New.Shape.G₁`: The unitary group of the complex hermitian form made of ϱ hyperbolic planes, the
  standard positive form on κ, and one vector z with h(z, z) = −1. `New.Shape.Form.besselU`: The
  unipotent group 𝖴 of block upper unitriangular elements with middle block 1.
  `New.besselQuotMeasure` computes integrals over 𝖴∖G₁. The frame is (e₀, …, e_{ϱ-1}, z), where e_a,
  e*_a are the hyperbolic pairs of basis vectors, and `New.Shape.top` is the position of z.
  `New.realFrameGram` x is the matrix of the products h(f_a, x f_b) of the frame vectors f_a; its
  entries are the frame entries of x.
* `weylElem j p`: The Weyl element w_p, with e_a ↦ p_a e*_a and e*_a ↦ e_a / p̄_a for a < j.
  `New.wave`: The character c ↦ exp (c - c̄) of ℂ. `New.unitOrOne`: c as a unit if c ≠ 0, and 1
  otherwise.
* `New.Shape.scaledVolumeRatio`: The constant π ^ ((2ϱ + 1) k) · vol U(k) / vol U(r), where k = card
  κ and r is the rank of G₁. `New.dampedPower`: The gain r ^ K min(1, r)⁶.
* `New.Floors.IsCutBessel` (in `New.Spanning.Frames.RealShells`): the cut, at size ρ, of a
  normalised Bessel function of irreducible type, with the numerical constraints.
* `New.Floors.IsCutBessel.formConst` (in `New.Spanning.Frames.RealShells`): the normalising constant
  vol U(k) / vol U(r) / (λ · card I)² of the forms.

## Relation to the literature

The estimates supply the local bounds of the Bessel systems built in
`New.Spanning.Bessel.FillingData`.
-/

noncomputable section

namespace New.Floors

/-!
## The normalized cell integral Ξ and the top floor
-/

section BandLimits

open Matrix MeasureTheory Measure Fintype RealPlace Real ENNReal InnerProductSpace Finset
  FloorGroups IsCutBessel Function Norms.L2Operator PlaceData Gauge

variable {𝔰 : Shape} {s : ℕ} {I : Type} [Fintype I] [DecidableEq I]
  {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
  {ρ b : ℝ} {f : ℕ} {F W : C(𝔰.G₁, EuclideanSpace ℂ I)}

variable (F) in
/-- The vector Ξ(p): the tensor J(w_p σ_p) times the real normalising factor of
`New.normalizedOrbitalIntegral`. Here J(γ) = ∫ F(y) ⊗ F(γ⁻¹y)^* dy, w_p is the Weyl element
`weylElem ϱ p`, and σ_p is the chart `New.Floors.cellChart` of floor ϱ at the last entry `p ϱ`. -/
noncomputable def normalizedCellIntegral (p : ℕ → ℂˣ) : EuclideanSpace ℂ (I × I) :=
  normalizedOrbitalIntegral (cellChart 𝔰 𝔰.ϱ (p 𝔰.ϱ)) F p

/-- The vector Ξ(p) = `normalizedCellIntegral F p` of a cut Bessel function `F` is continuous in the
list `p` of units. -/
lemma IsCutBessel.continuous_normalizedCellIntegral (hF : IsCutBessel F rep ρ s b W f) :
    Continuous (normalizedCellIntegral F) := by
  -- Near `p` all `c` are heads for one gauge `Γ`, so the integrand of `besselOrbitalIntegral` is
  -- supported in a fixed compact set, and it is jointly continuous.
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  obtain ⟨L, hL, hp, -⟩ := hF.exists_gauge_isHead 𝔰.ϱ p p 0
  let Γ : Gauge hF.complexData := hF.gauge (le_add_of_le_of_nonneg hL zero_le_one)
  have boost_cont : Continuous fun c : (ℕ → ℂˣ) × 𝔰.G₁ ↦ cellChart 𝔰 𝔰.ϱ (c.1 𝔰.ϱ) := by
    -- At a nonzero entry of the top floor, `cellChart` is given by the formula for the boost.
    have chart_eq (c : ℂˣ) : cellChart 𝔰 𝔰.ϱ c =
        cellBoost 𝔰 (c / (min 1 ‖(c : ℂ)‖ : ℝ)) (one_le_norm_div_min c.ne_zero) :=
      dite_eq_left ⟨rfl, c.ne_zero⟩
    simp only [continuous_U_iff_matrix, chart_eq]
    fun_prop (disch := simp [ne_of_gt])
  -- The inverse partial products of `p` have norm at most L < L + 1, the size of `Γ`.
  have heads : ∀ᶠ c in nhds p, Γ.IsHead 𝔰.ϱ c := by
    refine (Set.finite_Iic 𝔰.ϱ).eventually_all.2 fun i hi ↦ ?_
    have norm_cont : ContinuousAt (fun c : ℕ → ℂˣ ↦ ‖((∏ a ∈ range i, c a)⁻¹ : ℂˣ).val‖) p := by
      fun_prop
    have p_lt : ‖((∏ a ∈ range i, p a)⁻¹ : ℂˣ).val‖ < (L + 1) ^ 1 := (hp i hi).trans_lt (by simp)
    exact norm_cont.eventually_le_const p_lt
  have J_cont :
      ContinuousOn (fun c ↦ besselOrbitalIntegral volume F
        (weylElem 𝔰.ϱ c * cellChart 𝔰 𝔰.ϱ (c 𝔰.ϱ)))
        {c | Γ.IsHead 𝔰.ϱ c} := by
    refine (PiLp.continuous_toLp ..).comp_continuousOn (continuousOn_pi.2 fun i ↦
      continuousOn_integral_of_compact_support (Γ.isCompact_hasMatrixSize (j := 60 * 𝔰.n ^ 2))
        (by fun_prop) fun c y hc y_large ↦ ?_)
    -- Off the compact set one of the two values of `F` in the integrand is zero.
    have h_zero : F y = 0 ∨ F ((weylElem 𝔰.ϱ c * cellChart 𝔰 𝔰.ϱ (c 𝔰.ϱ))⁻¹ * y) = 0 := by
      by_contra! ⟨hy, hy'⟩
      exact y_large
        (Γ.hasMatrixSize_of_ne_zero hF.isCut_complexData hc cellChart_mem_floorGroup hy hy')
    rcases h_zero with h | h <;> rw [h] <;> simp
  -- `normalizedCellIntegral` is `besselOrbitalIntegral` times a continuous real factor.
  exact .smul (M := ℝ) (by fun_prop) (J_cont.continuousAt heads)

/-- The compact group U(κ), embedded in G₁ by `embedH`, acts on the values of a cut Bessel function
by unitary maps, so left translation by it keeps the inner products of these values. -/
lemma IsCutBessel.inner_embedH_mul (hF : IsCutBessel F rep ρ s b W f)
    (k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (x y : 𝔰.G₁) :
    ⟪F (embedH k * x), F (embedH k * y)⟫_ℂ = ⟪F x, F y⟫_ℂ := by
  simp [(hF.isBesselFunction .cut).map_unitary_mul, Unitary.map_mem,
    ContinuousLinearMap.inner_map_map_of_mem_unitary]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `F` be a cut Bessel function and let `p`, `q` have the same entry at index `ϱ`, `q ϱ = p ϱ`.
Let `σ` fix the hyperbolic basis vectors of floor below `ϱ`, with h(z, σ
z) = `realFrameGram σ 𝔰.top 𝔰.top` equal to `p ϱ`. Then the inner product of
`normalizedCellIntegral F p` and `normalizedCellIntegral F q` equals that of
`normalizedOrbitalIntegral σ F p` and `normalizedOrbitalIntegral σ F q`. -/
lemma IsCutBessel.inner_normalizedCellIntegral_eq_of_last_entry [Nonempty I]
    (hF : IsCutBessel F rep ρ s b W f) {σ : (𝔰.middleGram (1 : ℂ)).G} (hσ : σ ∈ floorGroup 𝔰.ϱ)
    {p q : ℕ → ℂˣ} (hp : realFrameGram σ 𝔰.top 𝔰.top = p 𝔰.ϱ) (hq : q 𝔰.ϱ = p 𝔰.ϱ) :
    ⟪normalizedCellIntegral F p, normalizedCellIntegral F q⟫_ℂ =
      ⟪normalizedOrbitalIntegral σ F p, normalizedOrbitalIntegral σ F q⟫_ℂ := by
  by_cases! norm_p : ‖(p 𝔰.ϱ).val‖ ≤ 1
  · -- The normalising factor √(‖p ϱ‖ ^ 2 - 1) vanishes on both sides.
    simp [normalizedCellIntegral, norm_p, hF.k_eq, normalizedOrbitalIntegral, sqrt_eq_zero']
  obtain ⟨L, hL, head_p, head_q, -⟩ := hF.exists_gauge_isHead 𝔰.ϱ p q 0
  obtain ⟨k, k', rfl⟩ : ∃ k k' : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
      σ = embedH k * cellChart 𝔰 𝔰.ϱ (p 𝔰.ϱ) * embedH k' :=
    cartan_decomposition hσ hp norm_p
  -- Both sides have the same normalising factors and are double integrals.
  simp only [normalizedCellIntegral, normalizedOrbitalIntegral, hq, inner_smul_left_eq_smul,
    inner_smul_right_eq_smul, hσ, cellChart_mem_floorGroup,
    inner_besselOrbitalIntegral _ hF.isCut_complexData F.continuous_toFun head_p head_q]
  congr 2
  -- On the right-hand side, multiply both variables on the left by `k`, which commutes with the
  -- Weyl elements.
  have translate (r : ℕ → ℂˣ) (τ y : 𝔰.G₁) :
      (weylElem 𝔰.ϱ r * (embedH k * τ * embedH k'))⁻¹ * (embedH k * y) =
        embedH k'⁻¹ * ((weylElem 𝔰.ϱ r * τ)⁻¹ * y) := by
    simp [mul_assoc, weylElem_mul_left_comm, embedH_mem_floorGroup]
  nth_rw 2 [← integral_mul_left_eq_self _ (embedH k, embedH k)]
  simp only [Prod.fst_mul, Prod.snd_mul, translate, hF.inner_embedH_mul]

/-- The integrand `partialCorrelationProduct` above the top floor ϱ, for a cut Bessel function `F`,
the Weyl elements w_p, w_q = `weylElem ϱ p`, `weylElem ϱ q` and `σ` fixing the hyperbolic basis
vectors, is ⟪F y, F (y x)⟫ ⟪F (σ⁻¹ w_q⁻¹ y x), F (σ⁻¹ w_p⁻¹ y)⟫ at the position `x` and the point
`y`. -/
lemma IsCutBessel.partialCorrelationProduct_top_eq (hF : IsCutBessel F rep ρ s b W f) (p q : ℕ → ℂˣ)
    {σ : (𝔰.middleGram (1 : ℂ)).G} (hσ : σ ∈ floorGroup 𝔰.ϱ) (x y : (𝔰.middleGram (1 : ℂ)).G) :
    hF.complexData.partialCorrelationProduct (𝔰.ϱ + 1) F x ((weylElem 𝔰.ϱ q)⁻¹ * weylElem 𝔰.ϱ p)
        (weylElem 𝔰.ϱ p * σ) y =
      ⟪F y, F (y * x)⟫_ℂ *
        ⟪F (σ⁻¹ * (weylElem 𝔰.ϱ q)⁻¹ * (y * x)), F (σ⁻¹ * (weylElem 𝔰.ϱ p)⁻¹ * y)⟫_ℂ := by
  -- The partial correlations are averages over U(κ) of inner products, which U(κ) keeps.
  have average_eq (d u v : (𝔰.middleGram (1 : ℂ)).G) :
      hF.complexData.partialCorrelation (𝔰.ϱ + 1) (frameCorrelation F d) u v =
        ∫ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), ⟪F (embedH k * u), F (d * (embedH k * v))⟫_ℂ := by
    simp (disch := fun_prop) [descConv, integral_map, partialCorrelation]
  simp only [partialCorrelationProduct, average_eq]
  simp [mul_assoc, hF.inner_embedH_mul, embedH_mem_floorGroup, weylElem_mul_left_comm, hσ]

/-- Descent on the top floor ϱ. Let `F` be a cut Bessel function, φ a measurable function on ℂ with
|φ| ≤ 1, and `p`, `q` lists of units. Let p_c and q_c be these lists with the entry at position ϱ
set to c (to 1 if c = 0), and let Φ(c) = φ(c) ⟪Ξ(p_c), Ξ(q_c)⟫, where Ξ =
`normalizedCellIntegral F`. Then Φ is Lebesgue integrable on ℂ, and its integral is `formConst`
times the form `floorForm` of floor ϱ at `p`, `q` with the weight x ↦ φ(h(z, x z)). -/
lemma IsCutBessel.descent_last_entry_of_norm_le_one [Nonempty I] (hF : IsCutBessel F rep ρ s b W f)
    (p q : ℕ → ℂˣ) {φ : ℂ → ℂ} (hφ : Measurable φ) (hφ_le : ∀ c : ℂ, ‖φ c‖ ≤ 1) :
    let Φ (c : ℂ) : ℂ := φ c *
      ⟪normalizedCellIntegral F (update p 𝔰.ϱ (unitOrOne c)),
        normalizedCellIntegral F (update q 𝔰.ϱ (unitOrOne c))⟫_ℂ
    Integrable Φ ∧
    ∫ c : ℂ, Φ c = hF.formConst *
      hF.complexData.floorForm 𝔰.ϱ p q F fun x : 𝔰.G₁ ↦ φ (realFrameGram x 𝔰.top 𝔰.top) := by
  -- Apply `integrable_and_integral_succ_eq_mul_floorForm` with the chart `cellChart` and the
  -- density `cellDensity`; it remains to identify the integrand at each unit `z`.
  obtain ⟨⟨ratio_ne_zero : hF.haarRatio ≠ 0, ratio_ne_top : hF.haarRatio ≠ ∞⟩,
    measure_eq : hF.complexData.groupMeasure = hF.haarRatio • volume, -⟩ :=
      hF.haarRatio_ne_zero_and_groupMeasure_eq_smul
  obtain ⟨L, hL, head_p, head_q, -⟩ := hF.exists_gauge_isHead 𝔰.ϱ p q 0
  have density_lt_top : ∀ᵐ c : ℂ, cellDensity 𝔰 𝔰.ϱ c < ∞ := by simp [cellDensity]
  have floor_eq : hF.complexData.floorMeasure (𝔰.top : ℕ) =
      (volume.withDensity (cellDensity 𝔰 𝔰.ϱ)).map (fun c : ℂ ↦ (cellChart 𝔰 𝔰.ϱ c)⁻¹) ∗ₘ
        hF.complexData.measureH :=
    (ite_eq_right (by simp)).trans (ite_eq_left rfl)
  have support_H : ∀ᵐ h ∂hF.complexData.measureH,
      h ∈ partialUnitriangularGroup (𝔰.top + 1) ⊓ floorGroup 𝔰.top :=
    hF.complexData.ae_measureH_mem_besselH.mono partialUnitriangularGroup_inf_floorGroup_last.ge
  refine integrable_and_integral_succ_eq_mul_floorForm hF.gauge hF.isCut_complexData 𝔰.top hφ hφ_le
    (hF.lintegral_formMajorant_ne_top le_rfl) support_H density_lt_top floor_eq
    (Place.ae_isUnit.mono ?_)
  rintro _ ⟨z, rfl⟩
  by_cases! norm_z : ‖z.val‖ ≤ 1
  · -- Both the normalising factor and the density vanish.
    simp [normalizedCellIntegral, norm_z, hF.k_eq, normalizedOrbitalIntegral, cellDensity,
      sqrt_eq_zero']
  -- On the right both measures are `groupMeasure`, which is `haarRatio` times `volume`.
  have top_stack :
      (hF.complexData.measureH ∗ₘ hF.complexData.floorMeasure (𝔰.top : ℕ)) ∗ₘ
        hF.complexData.partialGroupMeasure 0 (𝔰.top : ℕ) = hF.complexData.groupMeasure := by
    rw [show (𝔰.top : ℕ) = 𝔰.ϱ from rfl, ← partialGroupMeasure_top]
    simp [descConv_add]
  rw [top_stack, measure_eq]
  -- The Gram form is a double integral for `volume`; substitute (y, y x).
  let σ : (𝔰.middleGram (1 : ℂ)).G := cellChart 𝔰 𝔰.ϱ z
  have integral_eq :
      ∫ y : (𝔰.middleGram (1 : ℂ)).G × (𝔰.middleGram (1 : ℂ)).G, ⟪F y.1, F y.2⟫_ℂ *
          ⟪F (σ⁻¹ * (weylElem 𝔰.ϱ q)⁻¹ * y.2), F (σ⁻¹ * (weylElem 𝔰.ϱ p)⁻¹ * y.1)⟫_ℂ
          ∂volume.prod volume =
        ∫ y : (𝔰.middleGram (1 : ℂ)).G × (𝔰.middleGram (1 : ℂ)).G,
          hF.complexData.partialCorrelationProduct (𝔰.ϱ + 1) F y.1
            ((weylElem 𝔰.ϱ q)⁻¹ * weylElem 𝔰.ϱ p)
            (weylElem 𝔰.ϱ p * σ) y.2 ∂volume.prod volume := by
    rw [← (measurePreserving_prod_mul_swap ..).hasLaw.integral_comp (by fun_prop)]
    simp only [σ, hF.partialCorrelationProduct_top_eq p q cellChart_mem_floorGroup, comp_def]
  -- The constants agree: `haarRatio` cancels against `formConst`, and `Shape.openCellConst` is
  -- the constant of `cellDensity` times the ratio of volumes in `formConst`.
  let N (r : ℕ → ℂˣ) : ℝ := √𝔰.openCellConst * √(‖z.val‖ ^ 2 - 1) ^ (𝔰.k - 1) / card I *
    ∏ a ∈ range 𝔰.ϱ, ‖(update r 𝔰.ϱ z a).val‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))
  have const_eq : N q * N p = hF.formConst * ((hF.complexData.headDensity 𝔰.ϱ p q).toReal *
      (cellDensity 𝔰 𝔰.ϱ z).toReal * (hF.haarRatio.toReal * hF.haarRatio.toReal)) := by
    have density_eq : (cellDensity 𝔰 𝔰.ϱ z).toReal =
        2 * π ^ 𝔰.k / (𝔰.k - 1).factorial * max (‖z.val‖ ^ 2 - 1) 0 ^ (𝔰.k - 1) := by
      rw [cellDensity, ite_eq_right (lt_irrefl _), toReal_ofReal (by positivity), posPart_def]
    rw [density_eq]
    simp [N, headDensity, prod_range, ne_of_lt, ← toReal_rpow, ← one_div, ← sqrt_eq_rpow, mul_pow,
      prod_mul_distrib]
    grind [formConst, toReal_ne_zero, Shape.openCellConst, 𝔰.openCellConst_pos, pow_right_comm]
  -- Both sides are φ z times the constant times the integral.
  simp [normalizedCellIntegral, inner_besselOrbitalIntegral _ hF.isCut_complexData
    F.continuous_toFun head_p
      head_q, prod_smul_left, prod_smul_right,
    realFrameGram_cellChart norm_z, mul_left_comm _ (φ _), ← mul_assoc _ _ (integral ..),
    normalizedOrbitalIntegral, cellChart_mem_floorGroup, weylRatio]
  rw [integral_eq]
  congr 2
  exact_mod_cast const_eq

/-- Descent on the top floor for the character `wave c = exp (c - c̄)`. Give `p` and `q` the common
entry c at position ϱ. The integral over c of `wave (ξ c)` times the Gram form of
`normalizedCellIntegral` converges. It is `formConst` times the form of floor ϱ with the weight
x ↦ `wave` (ξ h(z, x z)). -/
lemma IsCutBessel.integrable_and_integral_wave_mul_inner_normalizedCellIntegral [Nonempty I]
    (hF : IsCutBessel F rep ρ s b W f) (p q : ℕ → ℂˣ) (ξ : ℂ) :
    let Φ (c : ℂ) : ℂ := wave (ξ * c) *
      ⟪normalizedCellIntegral F (update p 𝔰.ϱ (unitOrOne c)),
        normalizedCellIntegral F (update q 𝔰.ϱ (unitOrOne c))⟫_ℂ
    Integrable Φ ∧
    ∫ c : ℂ, Φ c = hF.formConst *
      hF.complexData.floorForm 𝔰.ϱ p q F fun x : 𝔰.G₁ ↦ wave (ξ * realFrameGram x 𝔰.top 𝔰.top) :=
  hF.descent_last_entry_of_norm_le_one p q (φ := fun c ↦ wave (ξ * c)) (by fun_prop [wave])
    fun c ↦ (norm_wave (ξ * c)).le

/-- The matrix coefficient `⟪A, R(x) B⟫` in `L²(𝖴∖G₁)`, where `R(x)` is right translation, 𝖴 is the
unipotent group `besselU` and `besselQuotMeasure` computes integrals over `𝖴∖G₁`. -/
noncomputable def quotientPairing (A B : 𝔰.G₁ → EuclideanSpace ℂ I) (x : 𝔰.G₁) : ℂ :=
  ∫ y, ⟪A y, B (y * x)⟫_ℂ ∂besselQuotMeasure

/-- Cauchy–Schwarz on `𝖴∖G₁`; right translation keeps the norm of a Bessel function. Let `A` be
strongly measurable, `B` a Bessel function of type `rep`, and `x` in `G₁`. For `besselQuotMeasure`,
the square of the integral of ‖⟪A y, B (y x)⟫‖ is at most the product of the integrals of ‖A y‖² and
‖B y‖². -/
lemma sq_lintegral_enorm_inner_le {A B : 𝔰.G₁ → EuclideanSpace ℂ I} (hA : StronglyMeasurable A)
    (hB : IsBesselFunction rep B) (x : 𝔰.G₁) :
    (∫⁻ y, ‖⟪A y, B (y * x)⟫_ℂ‖ₑ ∂besselQuotMeasure) ^ 2 ≤
      (∫⁻ y, ‖A y‖ₑ ^ 2 ∂besselQuotMeasure) * ∫⁻ y, ‖B y‖ₑ ^ 2 ∂besselQuotMeasure := by
  have hB_meas : StronglyMeasurable B := hB.stronglyMeasurable
  have h_inv (u : (𝔰.middleGram (1 : ℂ)).besselU) (y : 𝔰.G₁) :
      ‖B (u • y)‖ₑ ^ 2 = ‖B y‖ₑ ^ 2 := by
    rw [Subgroup.smul_def, smul_eq_mul,
      hB.enorm_besselS_mul (mem_partialUnitriangularGroup_of_mem_besselU u.2)]
  have h_translate : ∫⁻ y, ‖B (y * x)‖ₑ ^ 2 ∂besselQuotMeasure =
      ∫⁻ y, ‖B y‖ₑ ^ 2 ∂besselQuotMeasure :=
    (identDistrib_orbitMeasure_mul_right (F := fun y ↦ ‖B y‖ₑ ^ 2) x h_inv).lintegral_eq
  rw [← h_translate]
  refine sq_lintegral_le (by fun_prop) (by fun_prop) fun y ↦ ?_
  rw [← mul_pow]
  exact pow_le_pow_left' (coe_mono (nnnorm_inner_le_nnnorm ..)) 2

/-!
## The mass on the bottom floor, decay, and the local bounds
-/

/-- The difference of two Bessel functions of the same type `rep` is a Bessel function. -/
lemma isBesselFunction_sub {A B : 𝔰.G₁ → EuclideanSpace ℂ I} (hA : IsBesselFunction rep A)
    (hB : IsBesselFunction rep B) : IsBesselFunction rep fun y : 𝔰.G₁ ↦ A y - B y where
  stronglyMeasurable := hA.stronglyMeasurable.sub hB.stronglyMeasurable
  bounded := by
    obtain ⟨a, A_le⟩ := hA.bounded
    obtain ⟨c, B_le⟩ := hB.bounded
    exact ⟨a + c, fun y ↦ norm_sub_le_of_le (A_le y) (B_le y)⟩
  map_unipotent_mul u hu y := by
    rw [hA.map_unipotent_mul u hu, hB.map_unipotent_mul u hu, smul_sub]
  map_unitary_mul h y := by rw [hA.map_unitary_mul, hB.map_unitary_mul, map_sub]

/-- Let `F` be the cut of the Bessel function `W` with base `b` and degree `f`, so that their L²
distance is at most `b ^ (-r ^ 3 f) √(card I)`. Replacing `F` by `W` changes the matrix coefficient
`quotientPairing` by at most `2 b ^ (-r ^ 3 f) card I` at every position `x`. -/
lemma IsCutBessel.enorm_quotientPairing_sub_le (hF : IsCutBessel F rep ρ s b W f) (x : 𝔰.G₁) :
    ‖quotientPairing F F x - quotientPairing W W x‖ₑ ≤
      2 * (.ofReal (b⁻¹ ^ (𝔰.r ^ 3 * f)) * card I) := by
  -- The difference is `⟪F - W, R(x) F⟫ + ⟪W, R(x) (F - W)⟫`.
  have hF_bes : IsBesselFunction rep F := hF.isBesselFunction .cut
  have hW_bes : IsBesselFunction rep W := hF.isBesselFunction .full
  have h_sub_bes : IsBesselFunction rep fun y ↦ F y - W y := isBesselFunction_sub hF_bes hW_bes
  set ε : ℝ≥0∞ := .ofReal (b⁻¹ ^ (𝔰.r ^ 3 * f))
  have F_norm : ∫⁻ y, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure ≤ card I := hF.lintegral_sq_cut_le
  have W_norm : ∫⁻ y, ‖W y‖ₑ ^ 2 ∂besselQuotMeasure ≤ card I := hF.lintegral_sq_full_eq.le
  have sub_norm : ∫⁻ y, ‖F y - W y‖ₑ ^ 2 ∂besselQuotMeasure ≤ ε ^ 2 * card I :=
    hF.lintegral_sq_sub_le
  have integrable {B : C(𝔰.G₁, EuclideanSpace ℂ I)} (hB : IsBesselFunction rep B)
      (B_norm : ∫⁻ y, ‖B y‖ₑ ^ 2 ∂besselQuotMeasure ≤ card I) :
      Integrable (fun y ↦ ⟪B y, B (y * x)⟫_ℂ) besselQuotMeasure := by
    have L1_le : ∫⁻ y, ‖⟪B y, B (y * x)⟫_ℂ‖ₑ ∂besselQuotMeasure ≤ card I := by
      grw [← ENNReal.pow_le_pow_left_iff two_ne_zero,
        sq_lintegral_enorm_inner_le hB.stronglyMeasurable hB, B_norm, sq]
    exact ⟨by fun_prop, L1_le.trans_lt (natCast_lt_top (card I))⟩
  have first_le : ∫⁻ y, ‖⟪F y - W y, F (y * x)⟫_ℂ‖ₑ ∂besselQuotMeasure ≤ ε * card I := by
    grw [← ENNReal.pow_le_pow_left_iff two_ne_zero,
      sq_lintegral_enorm_inner_le h_sub_bes.stronglyMeasurable hF_bes, sub_norm, F_norm]
    exact le_of_eq (by ring)
  have second_le : ∫⁻ y, ‖⟪W y, F (y * x) - W (y * x)⟫_ℂ‖ₑ ∂besselQuotMeasure ≤ ε * card I := by
    grw [← ENNReal.pow_le_pow_left_iff two_ne_zero,
      sq_lintegral_enorm_inner_le hW_bes.stronglyMeasurable h_sub_bes, sub_norm, W_norm]
    exact le_of_eq (by ring)
  calc
    _ = ‖∫ y, ⟪F y - W y, F (y * x)⟫_ℂ + ⟪W y, F (y * x) - W (y * x)⟫_ℂ ∂besselQuotMeasure‖ₑ := by
      simp_rw [inner_sub_left, inner_sub_right, sub_add_sub_cancel]
      rw [integral_sub (integrable hF_bes F_norm) (integrable hW_bes W_norm), quotientPairing,
        quotientPairing]
    _ ≤ ∫⁻ y, ‖⟪F y - W y, F (y * x)⟫_ℂ‖ₑ + ‖⟪W y, F (y * x) - W (y * x)⟫_ℂ‖ₑ
        ∂besselQuotMeasure :=
      (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y ↦ enorm_add_le _ _)
    _ ≤ 2 * (ε * card I) := by grw [lintegral_add_left (by fun_prop), first_le, second_le, two_mul]

/-- For a cut Bessel function `F` and `x` in G₁, the number `formIntegrandL1Norm` that bounds the
form of floor `0` with weight `1` at the position `x` is λ² |∫_{𝖴∖G₁} ⟪F(y), F(y x)⟫ dy|². The
integral is the matrix coefficient `quotientPairing F F x`, and λ = `haarRatio` is the ratio of the
measure of the place datum to the Haar measure of G₁. The value does not depend on the lists `p`,
`q`. -/
lemma IsCutBessel.formIntegrandL1Norm_zero_eq (hF : IsCutBessel F rep ρ s b W f) (p q : ℕ → ℂˣ)
    (x : 𝔰.G₁) :
    hF.complexData.formIntegrandL1Norm 0 p q F x 1 = hF.haarRatio ^ 2 * ‖quotientPairing F F x‖ₑ ^
      2 := by
  obtain ⟨⟨-, ratio_ne_top : hF.haarRatio ≠ ∞⟩, -, h_unfold, -⟩ :=
    hF.haarRatio_ne_zero_and_groupMeasure_eq_smul
  let c (y : 𝔰.G₁) : ℂ := ⟪F y, F (y * x)⟫_ℂ
  have c_meas : Measurable c := by fun_prop
  have c_inv (u : 𝔰.G₁) (hu : u ∈ besselU) (y : 𝔰.G₁) : c (u * y) = c y := by
    simp only [c, mul_assoc u, (hF.isBesselFunction .cut).map_unipotent_mul u hu, inner_smul_left,
      inner_smul_right]
    simp [← mul_assoc, Complex.mul_conj']
  -- The integrand `c` is left invariant under `𝖴`, so its law for the floors is `hF.haarRatio`
  -- times its law on the quotient.
  have h_law : (hF.complexData.quotientMeasureFrom 0).map c = hF.haarRatio • besselQuotMeasure.map
    c := by
    refine ext_of_lintegral _ fun g hg ↦ ?_
    have g_inv : besselU.FixesLeft fun y : 𝔰.G₁ ↦ g (c y) := fun u hu y ↦ congrArg g (c_inv u hu y)
    rw [lintegral_smul_measure, lintegral_map hg c_meas, lintegral_map hg c_meas]
    exact h_unfold (fun y ↦ g (c y)) (hg.comp c_meas) g_inv
  have h_pairing : hF.complexData.partialCorrelation 0 (frameCorrelation F 1) 1 x =
      hF.haarRatio.toReal • quotientPairing F F x :=
    calc
      _ = ∫ y, c y ∂hF.complexData.quotientMeasureFrom 0 := by simp [c, partialCorrelation]
      _ = ∫ z, z ∂(hF.complexData.quotientMeasureFrom 0).map c :=
        (integral_map c_meas.aemeasurable aestronglyMeasurable_id).symm
      _ = hF.haarRatio.toReal • ∫ z, z ∂besselQuotMeasure.map c := by
        rw [h_law, integral_smul_measure]
      _ = _ := by
        rw [integral_map (f := fun z ↦ z) c_meas.aemeasurable aestronglyMeasurable_id,
          quotientPairing]
  -- At floor `0` the Weyl elements are trivial, so the two factors of the integrand are conjugate.
  have h_square : hF.complexData.formIntegrandL1Norm 0 p q F x 1 =
      ‖hF.complexData.partialCorrelation 0 (frameCorrelation F 1) 1 x‖ₑ ^ 2 := by
    simp [formIntegrandL1Norm, descConv, ← partialCorrelationProduct_eq hF.gauge
      hF.isCut_complexData,
      partialCorrelationProduct, sq, weylRatio]
  rw [h_square, h_pairing, enorm_smul, mul_pow, Real.enorm_of_nonneg toReal_nonneg,
    ofReal_toReal ratio_ne_top]

/-- Minkowski's inequality in `L²`: if `g` and `h` have `L²` norms at most `α` and `β`, then `g + h`
has `L²` norm at most `α + β`. -/
lemma lintegral_add_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {g h : X → ℝ≥0∞}
    {α β : ℝ≥0∞} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
    (hα : ∫⁻ x : X, g x ^ 2 ∂μ ≤ α ^ 2) (hβ : ∫⁻ x : X, h x ^ 2 ∂μ ≤ β ^ 2) :
    ∫⁻ x : X, (g x + h x) ^ 2 ∂μ ≤ (α + β) ^ 2 := by
  have root_le_iff {a c : ℝ≥0∞} : a ^ (1 / 2 : ℝ) ≤ c ↔ a ≤ c ^ 2 := by
    rw [one_div, rpow_inv_le_iff two_pos, ENNReal.rpow_two]
  have minkowski : (∫⁻ x, (g x + h x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤
      (∫⁻ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫⁻ x, h x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    simpa only [ENNReal.rpow_two, Pi.add_apply] using lintegral_Lp_add_le hg hh one_le_two
  exact root_le_iff.1 (minkowski.trans (add_le_add (root_le_iff.2 hα) (root_le_iff.2 hβ)))

/-- The box radius `ρ = b ^ (6 n + 2)` of a cut Bessel function is at most `b ^ (7 n)`. -/
lemma IsCutBessel.rho_le_pow (hF : IsCutBessel F rep ρ s b W f) : ρ ≤ b ^ (7 * 𝔰.n) := by
  have two_le_n : 2 ≤ 𝔰.n := Nat.succ_le_succ (le_trans (by norm_num) hF.ten_pow_le_varrho)
  rw [hF.rho_eq]
  exact pow_le_pow_right₀ (one_le_two.trans hF.two_le_b) (by lia)

/-- For a cut Bessel function `F` (`IsCutBessel F rep ρ s b W f`), the rank `𝔰.r` = 2ϱ + k + 1 of G₁
equals `s + 5 * 𝔰.n + 5`. This follows from `k = s + 3 n + 6`. -/
lemma IsCutBessel.r_eq_add (hF : IsCutBessel F rep ρ s b W f) : 𝔰.r = s + 5 * 𝔰.n + 5 := by
  rw [show 𝔰.r = 𝔰.ϱ + (𝔰.k + 1 + 𝔰.ϱ) by simp, hF.k_eq]
  lia

/-- Let `F` be a cut Bessel function (`IsCutBessel`) with box radius `ρ` and base `b`. Let
n = ϱ + 1, where ϱ is the number of hyperbolic planes of `𝔰`, and let r be the rank of G₁. If `x`
lies in the position ball at the scale `T = b ^ (6 r) * ρ ^ (11 n)`, that is, the entries of `x - 1`
have modulus at most `T ^ (99 n)`, then the matrix of `x` has operator norm at most
`b ^ (700 n r)`. -/
lemma IsCutBessel.norm_le_of_mem_positionBall (hF : IsCutBessel F rep ρ s b W f) {x : 𝔰.G₁}
    (hx : x ∈ positionBall 𝔰 (b ^ (6 * 𝔰.r) * ρ ^ (11 * 𝔰.n))) :
    ‖(x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ b ^ (700 * 𝔰.n * 𝔰.r) := by
  have one_le_b : 1 ≤ b := one_le_two.trans hF.two_le_b
  have one_le_ρ : 1 ≤ ρ := by linarith [hF.four_le]
  have ρ_le : ρ ≤ b ^ (7 * 𝔰.n) := hF.rho_le_pow
  let X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := x
  let R : ℝ := (b ^ (6 * 𝔰.r) * ρ ^ (11 * 𝔰.n)) ^ (99 * 𝔰.n)
  have one_le_R : 1 ≤ R :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_b) (one_le_pow₀ one_le_ρ))
  have h_entries : ‖X - 1‖ ≤ 𝔰.r * 𝔰.r * R := l2_opNorm_le_of_apply hx
  have rank_sq_le : (𝔰.r : ℝ) * 𝔰.r + 1 ≤ ρ ^ 2 := by
    nlinarith [hF.eight_mul_r_le_rho, hF.four_le, Nat.cast_nonneg (α := ℝ) 𝔰.r]
  have cube_le : 10 ^ 9 * 𝔰.n ^ 3 ≤ 𝔰.r := hF.mul_cube_lt_s.le.trans (by grind [hF.r_eq_add])
  calc ‖X‖ ≤ ‖X - 1‖ + 1 := by simpa using norm_add_le (X - 1) 1
    _ ≤ (𝔰.r * 𝔰.r + 1) * R := by linarith
    _ ≤ ρ ^ 2 * R := by gcongr
    _ ≤ (b ^ (7 * 𝔰.n)) ^ 2 * (b ^ (6 * 𝔰.r) * (b ^ (7 * 𝔰.n)) ^ (11 * 𝔰.n)) ^ (99 * 𝔰.n) := by
      unfold R
      gcongr
    _ ≤ b ^ (700 * 𝔰.n * 𝔰.r) := by
      simp only [← pow_mul, ← pow_add]
      refine pow_le_pow_right₀ one_le_b ?_
      -- Exponents: `14 n + 7623 n ^ 3 ≤ 106 n r`, as `10 ^ 9 n ^ 3 ≤ r`.
      have one_le_n : 1 ≤ 𝔰.n := Nat.succ_pos _
      generalize 𝔰.n = n, 𝔰.r = r at *
      nlinarith [Nat.le_self_pow three_ne_zero n]

/-- For `2 ≤ b`, `n, r ≥ 1` and `f ≥ 4000 n`, the square of the error `2 b ^ (-r ^ 3 f)` times the
volume bound `T ^ (9 r²) b ^ (99 r²)` at the radius `T = b ^ (700 n r)` is at most `b ^ (-24)`. -/
lemma sq_error_mul_ballBound_le {n r : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (h_degree : 4000 * n ≤ f) :
    (2 * b⁻¹ ^ (r ^ 3 * f)) ^ 2 * ((b ^ (700 * n * r)) ^ (9 * r ^ 2) * b ^ (99 * r ^ 2)) ≤
      (b⁻¹ ^ 12) ^ 2 := by
  have one_le_b : 1 ≤ b := one_le_two.trans hb
  let E : ℕ := 2 + 6300 * n * r ^ 3 + 99 * r ^ 2
  have exponent_le : E + 24 ≤ 2 * (r ^ 3 * f) := by
    have sq_le_cube : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by lia)
    have one_le_cube : 1 ≤ r ^ 3 := Nat.one_le_pow 3 r hr
    have cube_le : r ^ 3 ≤ r ^ 3 * n := Nat.le_mul_of_pos_right _ hn
    have degree_le : r ^ 3 * (4000 * n) ≤ r ^ 3 * f := Nat.mul_le_mul_left _ h_degree
    lia
  calc
    _ ≤ (b * b⁻¹ ^ (r ^ 3 * f)) ^ 2 * ((b ^ (700 * n * r)) ^ (9 * r ^ 2) * b ^ (99 * r ^ 2)) := by
      gcongr
    _ = b ^ E / b ^ (2 * (r ^ 3 * f)) := by ring
    _ ≤ b ^ E / b ^ (E + 24) := by gcongr
    _ = (b⁻¹ ^ 12) ^ 2 := by field

/-- Let `F` be the cut of `W` in degree `f ≥ 4000 n`, and `deg > 0`. Suppose that the matrix
coefficient `quotientPairing W W` has squared `L²` norm at most `(card I) ^ 2 / deg`, and that the
ball of radius `T ≥ 1` in G₁ has volume at most `T ^ (9 r²) b ^ (99 r²) / deg`. Then on the position
ball at the scale `b ^ (6 r) * ρ ^ (11 n)` the matrix coefficient of `F` has squared `L²` norm at
most `(1 + b⁻¹ ^ 12) ^ 2 (card I) ^ 2 / deg`. -/
lemma IsCutBessel.setLIntegral_quotientPairing_sq_le (hF : IsCutBessel F rep ρ s b W f) {deg : ℝ}
    (deg_pos : 0 < deg)
    (h_coeff : ∫⁻ x : 𝔰.G₁, ‖quotientPairing W W x‖ₑ ^ 2 ≤ .ofReal deg⁻¹ * card I ^ 2)
    (h_ball : ∀ T : ℝ, T ≥ 1 →
      .ofReal deg * volume {g : 𝔰.G₁ | ‖(g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ T} ≤
        ENNReal.ofReal (T ^ (9 * 𝔰.r ^ 2) * b ^ (99 * 𝔰.r ^ 2)))
    (h_degree : 4000 * 𝔰.n ≤ f) :
    ∫⁻ x : 𝔰.G₁ in positionBall 𝔰 (b ^ (6 * 𝔰.r) * ρ ^ (11 * 𝔰.n)),
        ‖quotientPairing F F x‖ₑ ^ 2 ≤
      .ofReal ((1 + b⁻¹ ^ 12) ^ 2 / deg) * card I ^ 2 := by
  -- Compare with the coefficient of `W`, which has norm at most `card I / √deg`; the difference is
  -- small at every position of a set of bounded volume.
  have hb : 2 ≤ b := hF.two_le_b
  have one_le_b : 1 ≤ b := one_le_two.trans hb
  set C : Set 𝔰.G₁ := positionBall 𝔰 (b ^ (6 * 𝔰.r) * ρ ^ (11 * 𝔰.n))
  let ε : ℝ≥0∞ := .ofReal (b⁻¹ ^ (𝔰.r ^ 3 * f))
  let α : ℝ≥0∞ := .ofReal √deg⁻¹ * card I
  have α_sq : α ^ 2 = .ofReal deg⁻¹ * card I ^ 2 := by
    rw [mul_pow, ← ofReal_pow (sqrt_nonneg _), sq_sqrt (by positivity)]
  have h_meas : StronglyMeasurable (quotientPairing W W) := .integral_prod_right (by fun_prop)
  have h_schur : ∫⁻ x in C, ‖quotientPairing W W x‖ₑ ^ 2 ≤ α ^ 2 := by
    grw [setLIntegral_le_lintegral, h_coeff, α_sq]
  let T : ℝ := b ^ (700 * 𝔰.n * 𝔰.r)
  let V : ℝ := T ^ (9 * 𝔰.r ^ 2) * b ^ (99 * 𝔰.r ^ 2)
  have h_volume : volume C ≤ .ofReal deg⁻¹ * .ofReal V := by
    grw [← h_ball T (one_le_pow₀ one_le_b), ← mul_assoc, ← ofReal_mul (by positivity),
      inv_mul_cancel₀ deg_pos.ne', ofReal_one, one_mul]
    exact measure_mono fun x hx ↦ hF.norm_le_of_mem_positionBall hx
  have h_small : (2 * ε) ^ 2 * .ofReal V ≤ .ofReal (b⁻¹ ^ 12) ^ 2 := by
    have one_le_r : 1 ≤ 𝔰.r := Fintype.card_pos
    grw [← ofReal_pow (by positivity), ← sq_error_mul_ballBound_le hb (by lia) one_le_r h_degree,
      ofReal_mul (sq_nonneg _), ofReal_pow (by positivity) 2, ofReal_mul zero_le_two, ofReal_ofNat]
  have h_change : ∫⁻ _ in C, (2 * (ε * card I)) ^ 2 ≤ (.ofReal (b⁻¹ ^ 12) * α) ^ 2 :=
    calc _ ≤ (2 * (ε * card I)) ^ 2 * (.ofReal deg⁻¹ * .ofReal V) := by
          grw [setLIntegral_const, h_volume]
      _ = (2 * ε) ^ 2 * .ofReal V * α ^ 2 := by
          rw [α_sq]
          ring
      _ ≤ (.ofReal (b⁻¹ ^ 12) * α) ^ 2 := by grw [h_small, ← mul_pow]
  calc
    _ ≤ ∫⁻ x in C, (‖quotientPairing W W x‖ₑ + 2 * (ε * card I)) ^ 2 := by
      refine lintegral_mono fun x ↦ pow_le_pow_left' ?_ 2
      grw [← hF.enorm_quotientPairing_sub_le x, ← enorm_add_le, add_sub_cancel]
    _ ≤ (α + .ofReal (b⁻¹ ^ 12) * α) ^ 2 :=
      lintegral_add_sq_le (by fun_prop) aemeasurable_const h_schur h_change
    _ = (1 + .ofReal (b⁻¹ ^ 12)) ^ 2 * (.ofReal deg⁻¹ * card I ^ 2) := by
      rw [← one_add_mul, mul_pow, α_sq]
    _ = .ofReal ((1 + b⁻¹ ^ 12) ^ 2 / deg) * card I ^ 2 := by
      rw [div_eq_mul_inv, ofReal_mul (sq_nonneg _), ofReal_pow (by positivity) 2,
        ofReal_add zero_le_one (by positivity), ofReal_one, mul_assoc]

/-- Let `ρ`, `s`, `b` be the sizes of a cut Bessel function, Θ = `scaledVolumeRatio` the constant of
the local bounds, `deg * Θ ≤ b ^ (4 r²)` and `t = b ^ (6 r)`. Then
`Θ ρ ^ (10⁹ n⁴) ρ ^ (24 k) t ^ (10⁸ n⁴) / t ^ s`, which bounds the contribution of the remote
positions, is at most `b⁻¹ ^ 12 / deg`. -/
lemma IsCutBessel.scaledVolumeRatio_mul_pow_div_pow_le (hF : IsCutBessel F rep ρ s b W f) {deg : ℝ}
    (deg_pos : 0 < deg) (deg_le : deg * 𝔰.scaledVolumeRatio ≤ b ^ (4 * 𝔰.r ^ 2)) :
    𝔰.scaledVolumeRatio * ρ ^ (10 ^ 9 * 𝔰.n ^ 4) * ρ ^ (24 * 𝔰.k) *
      (b ^ (6 * 𝔰.r)) ^ (10 ^ 8 * 𝔰.n ^ 4) / (b ^ (6 * 𝔰.r)) ^ s ≤ b⁻¹ ^ 12 / deg := by
  have one_le_b : 1 ≤ b := one_le_two.trans hF.two_le_b
  have ρ_nonneg : 0 ≤ ρ := by linarith [hF.four_le]
  have ρ_le : ρ ≤ b ^ (7 * 𝔰.n) := hF.rho_le_pow
  have const_le : 𝔰.scaledVolumeRatio ≤ b ^ (4 * 𝔰.r ^ 2) / deg := (le_div_iff₀' deg_pos).2 deg_le
  let E : ℕ := 4 * 𝔰.r ^ 2 + 7 * 𝔰.n * (10 ^ 9 * 𝔰.n ^ 4) + 7 * 𝔰.n * (24 * 𝔰.k) +
    6 * 𝔰.r * (10 ^ 8 * 𝔰.n ^ 4)
  have exponent_le : E + 12 ≤ 6 * 𝔰.r * s := by
    -- Use `r = s + 5 n + 5`, `k = s + 3 n + 6` and `10 ^ 10 n ^ 4 ≤ s`.
    simp only [E, hF.r_eq_add, hF.k_eq]
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, s = 10 ^ 10 * 𝔰.n ^ 4 + d := exists_add_of_le hF.mul_pow_four_le_s
    lia
  calc
    _ ≤ b ^ (4 * 𝔰.r ^ 2) / deg * (b ^ (7 * 𝔰.n)) ^ (10 ^ 9 * 𝔰.n ^ 4) *
        (b ^ (7 * 𝔰.n)) ^ (24 * 𝔰.k) * (b ^ (6 * 𝔰.r)) ^ (10 ^ 8 * 𝔰.n ^ 4) /
          (b ^ (6 * 𝔰.r)) ^ s := by gcongr
    _ = b ^ E / b ^ (6 * 𝔰.r * s) / deg := by
      simp only [E, pow_add, pow_mul b (7 * 𝔰.n), pow_mul b (6 * 𝔰.r), div_eq_mul_inv]
      ac_rfl
    _ ≤ b ^ E / b ^ (E + 12) / deg := by gcongr
    _ = b⁻¹ ^ 12 / deg := by field

variable [Nonempty I]

/-- For `2 ≤ b`, the sum of the bounds `(1 + b⁻¹ ^ 12) ^ 2` for the positions in the position ball
and `b⁻¹ ^ 12` for the remote positions is at most `1 + b⁻¹ ^ 10`. -/
lemma one_add_inv_pow_twelve_sq_add_le (hb : 2 ≤ b) :
    (1 + b⁻¹ ^ 12) ^ 2 + b⁻¹ ^ 12 ≤ 1 + b⁻¹ ^ 10 := by
  have inv_le : b⁻¹ ≤ 2⁻¹ := inv_anti₀ two_pos hb
  have pow_le_one : b⁻¹ ^ 12 ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  calc (1 + b⁻¹ ^ 12) ^ 2 + b⁻¹ ^ 12 = 1 + (3 + b⁻¹ ^ 12) * b⁻¹ ^ 2 * b⁻¹ ^ 10 := by ring
    _ ≤ 1 + (3 + 1) * 2⁻¹ ^ 2 * b⁻¹ ^ 10 := by gcongr
    _ = 1 + b⁻¹ ^ 10 := by ring

/-- The normalising constant `formConst` = vol U(k) / vol U(r) / (λ · card I)², times
(λ · card I)², is vol U(k) / vol U(r). Its product with the ratio λ = `haarRatio` of the Haar
measures is at most `1`. -/
lemma IsCutBessel.enorm_formConst_mul_le_one (hF : IsCutBessel F rep ρ s b W f) :
    ‖(hF.formConst : ℂ)‖ₑ * hF.haarRatio * (hF.haarRatio * card I) ^ 2 ≤ 1 := by
  obtain ⟨⟨ratio_ne_zero : hF.haarRatio ≠ 0, ratio_ne_top : hF.haarRatio ≠ ∞⟩, -, -,
    ratio_le : .ofReal (volU 𝔰.k / volU 𝔰.r) * hF.haarRatio ≤ 1⟩ :=
      hF.haarRatio_ne_zero_and_groupMeasure_eq_smul
  simpa [← toReal_le_toReal, field, formConst, mul_eq_top, le_of_lt, ratio_ne_zero,
    ratio_ne_top, abs_of_pos] using ratio_le

/-- The mass at a real place. Let `F` be the cut of `W` in degree `f ≥ 4000 n`, and `deg > 0`.
Suppose that the matrix coefficient `quotientPairing W W` has squared `L²` norm at most
`(card I) ^ 2 / deg`, that `deg * scaledVolumeRatio ≤ b ^ (4 r²)`, and that the ball of radius
`T ≥ 1` in G₁ has volume at most `T ^ (9 r²) b ^ (99 r²) / deg`. Then the form `floorForm 0` of
floor `0` with weight `1`, times the normalising constant `formConst`, has modulus at most
`(1 + b⁻¹ ^ 10) / deg` for all lists `p`, `q`. -/
lemma IsCutBessel.norm_floorForm_zero_le (hF : IsCutBessel F rep ρ s b W f) {deg : ℝ}
    (deg_pos : 0 < deg)
    (h_coeff : ∫⁻ x : 𝔰.G₁, ‖quotientPairing W W x‖ₑ ^ 2 ≤ .ofReal deg⁻¹ * card I ^ 2)
    (deg_le : deg * 𝔰.scaledVolumeRatio ≤ b ^ (4 * 𝔰.r ^ 2))
    (h_ball : ∀ T : ℝ, T ≥ 1 →
      .ofReal deg * volume {g : 𝔰.G₁ | ‖(g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ T} ≤
        ENNReal.ofReal (T ^ (9 * 𝔰.r ^ 2) * b ^ (99 * 𝔰.r ^ 2)))
    (h_degree : 4000 * 𝔰.n ≤ f) (p q : ℕ → ℂˣ) :
    ‖hF.formConst * hF.complexData.floorForm 0 p q F 1‖ ≤ (1 + b⁻¹ ^ 10) / deg := by
  -- Split the positions at the scale `b ^ (6 r) * ρ ^ (11 n)` into those in the position ball and
  -- remote ones.
  have hb : 2 ≤ b := hF.two_le_b
  let C : Set 𝔰.G₁ := positionBall 𝔰 (b ^ (6 * 𝔰.r) * ρ ^ (11 * 𝔰.n))
  let μ : Measure 𝔰.G₁ := hF.complexData.groupMeasure
  let c : ℝ≥0∞ := ‖(hF.formConst : ℂ)‖ₑ
  let Φ (x : 𝔰.G₁) : ℝ≥0∞ := hF.complexData.formIntegrandL1Norm 0 p q F x 1
  have close_le : c * ∫⁻ x in C, Φ x ∂μ ≤ .ofReal ((1 + b⁻¹ ^ 12) ^ 2 / deg) := by
    obtain ⟨⟨-, ratio_ne_top : hF.haarRatio ≠ ∞⟩, μ_eq : μ = hF.haarRatio • volume, -⟩ :=
      hF.haarRatio_ne_zero_and_groupMeasure_eq_smul
    calc
      _ = c * (hF.haarRatio * (hF.haarRatio ^ 2 * ∫⁻ x in C, ‖quotientPairing F F x‖ₑ ^ 2)) := by
          simp only [Φ, hF.formIntegrandL1Norm_zero_eq]
          rw [μ_eq, setLIntegral_smul_measure, lintegral_const_mul' _ _ (pow_ne_top ratio_ne_top),
            smul_eq_mul]
      _ ≤ c * (hF.haarRatio * (hF.haarRatio ^ 2 *
            (.ofReal ((1 + b⁻¹ ^ 12) ^ 2 / deg) * card I ^ 2))) := by
          grw [hF.setLIntegral_quotientPairing_sq_le deg_pos h_coeff h_ball h_degree]
      _ = c * hF.haarRatio * (hF.haarRatio * card I) ^ 2 *
            .ofReal ((1 + b⁻¹ ^ 12) ^ 2 / deg) := by ring
      _ ≤ .ofReal ((1 + b⁻¹ ^ 12) ^ 2 / deg) := by grw [hF.enorm_formConst_mul_le_one, one_mul]
  -- At floor `0` every list is a head, and `headDensity` is an empty product.
  have density_eq : hF.complexData.headDensity 0 p q = 1 := by rw [headDensity, prod_range_zero]
  have remote_le : c * ∫⁻ x in Cᶜ, Φ x ∂μ ≤ .ofReal (b⁻¹ ^ 12 / deg) := by
    have head (l : ℕ → ℂˣ) : hF.gauge.IsHead 0 l := by simp [Size.IsHead, Size.zero_one_mem_ofSize]
    have Φ_le (x : 𝔰.G₁) : Φ x ≤ hF.complexData.formMajorant 0 p q F x :=
      hF.isCut_complexData.formIntegrandL1Norm_le_formMajorant (by simp)
    have one_le_scale : 1 ≤ b ^ (6 * 𝔰.r) := one_le_pow₀ (one_le_two.trans hb)
    calc
      _ ≤ c * (hF.complexData.headDensity 0 p q *
            ∫⁻ x in Cᶜ, hF.complexData.formMajorant 0 p q F x ∂μ) := by
          grw [density_eq, one_mul, lintegral_mono Φ_le]
      _ ≤ .ofReal (b⁻¹ ^ 12 / deg) :=
          (hF.formConst_mul_setLIntegral_compl_positionBall_le zero_le (head p) (head q)
            one_le_scale).trans
            (ofReal_le_ofReal (hF.scaledVolumeRatio_mul_pow_div_pow_le deg_pos deg_le))
  rw [← ofReal_le_ofReal_iff (by positivity)]
  calc
    _ = c * ‖hF.complexData.floorForm 0 p q F 1‖ₑ := by rw [ofReal_norm, enorm_mul]
    _ ≤ c * ∫⁻ x, Φ x ∂μ := by grw [enorm_floorForm_le, density_eq, one_mul]
    _ = c * ∫⁻ x in C, Φ x ∂μ + c * ∫⁻ x in Cᶜ, Φ x ∂μ := by
      rw [← mul_add, lintegral_add_compl _ (measurableSet_positionBall _)]
    _ ≤ .ofReal ((1 + b⁻¹ ^ 12) ^ 2 / deg) + .ofReal (b⁻¹ ^ 12 / deg) :=
      add_le_add close_le remote_le
    _ ≤ .ofReal ((1 + b⁻¹ ^ 10) / deg) := by
      grw [← ofReal_add (by positivity) (by positivity), ← add_div,
        one_add_inv_pow_twelve_sq_add_le hb]

/-- For a cut Bessel function `F`, lists `p`, `q`, a floor `i ≤ ϱ` and a frequency `ν ≠ 0`, take the
form of floor `i`, normalised by `formConst`, whose weight is the character `wave` of `ν` times the
diagonal frame entry number `i`. Its modulus times the dimension `card I` is at most
`scaledVolumeRatio * b ^ (2000 n ^ 9)` times the decay `dampedPower (k - n ^ 7) ‖ν‖⁻¹` times the
weights `headWeight` of `p` and `q`. -/
theorem IsCutBessel.norm_floorForm_wave_le (hF : IsCutBessel F rep ρ s b W f) {i : ℕ}
    (hi : i ≤ 𝔰.ϱ) (p q : ℕ → ℂˣ) (ν : ℂˣ) :
    card I * ‖hF.formConst * hF.complexData.floorForm i p q F
        fun x : 𝔰.G₁ ↦ wave (ν * (realFrameGram x).diag ⟨i, Nat.lt_succ_of_le hi⟩)‖ ≤
      𝔰.scaledVolumeRatio * b ^ (2000 * 𝔰.n ^ 9) * dampedPower (𝔰.k - 𝔰.n ^ 7) ‖(ν : ℂ)‖⁻¹ *
        (headWeight (b ^ (60 * 𝔰.n ^ 2)) (𝔰.n ^ 6) i p *
          headWeight (b ^ (60 * 𝔰.n ^ 2)) (𝔰.n ^ 6) i q) :=
  hF.norm_floorForm_le hi ν (fun _ ↦ (norm_wave _).le) fun Γ hp ↦
    Γ.formIntegrandL1Norm_sq_le_of_char hF.isCut_complexData hi hp trivial fun _ _ ↦ rfl

/-- Decay for unequal last entries at a real place. If `i + 1 ≤ ϱ` and `ν = (p i)⁻¹ - (q i)⁻¹` is
not zero, the modulus of the form of floor `i + 1` with weight `1`, normalised by `formConst`, times
the dimension `card I` is at most `scaledVolumeRatio * b ^ (2000 n ^ 9)` times the decay
`dampedPower (k - n ^ 7) ‖ν‖⁻¹` times the weights `headWeight` of `p` and `q`. -/
theorem IsCutBessel.norm_floorForm_heads_le (hF : IsCutBessel F rep ρ s b W f) {i : ℕ}
    (hi : i + 1 ≤ 𝔰.ϱ) (p q : ℕ → ℂˣ) (ν : ℂˣ)
    (hν : (ν : ℂ) = ((p i)⁻¹ : ℂˣ) - ((q i)⁻¹ : ℂˣ)) :
    card I * ‖hF.formConst * hF.complexData.floorForm (i + 1) p q F 1‖ ≤
      𝔰.scaledVolumeRatio * b ^ (2000 * 𝔰.n ^ 9) * dampedPower (𝔰.k - 𝔰.n ^ 7) ‖(ν : ℂ)‖⁻¹ *
        (headWeight (b ^ (60 * 𝔰.n ^ 2)) (𝔰.n ^ 6) (i + 1) p *
          headWeight (b ^ (60 * 𝔰.n ^ 2)) (𝔰.n ^ 6) (i + 1) q) :=
  hF.norm_floorForm_le hi ν (by simp) fun Γ hp ↦
    Γ.formIntegrandL1Norm_sq_le_of_heads hF.isCut_complexData hi hp trivial rfl (by simp [hν])

/-- Let `F` be a cut Bessel function (`IsCutBessel`) and `i < ϱ`. Replace the entries of `p` and `q`
at position `i` by the common unit `unitOrOne c`, which is 1 at c = 0. Then the integral over c of
`wave (ξ * c)` times the normalised form of floor `i + 1` converges. It equals the normalised form
of floor `i` with the weight x ↦ `wave (ξ * (realFrameGram x).diag i)`. A normalised form is
`formConst` times `floorForm`, and that of floor `i + 1` has weight 1. Here ϱ is the number of
hyperbolic planes. -/
lemma IsCutBessel.integrable_and_integral_wave_mul_floorForm_succ (hF : IsCutBessel F rep ρ s b W f)
    {i : ℕ} (hi : i < 𝔰.ϱ) (p q : ℕ → ℂˣ) (ξ : ℂ) :
    let Φ (c : ℂ) : ℂ := wave (ξ * c) * (hF.formConst *
      hF.complexData.floorForm (i + 1) (update p i (unitOrOne c)) (update q i (unitOrOne c)) F 1)
    Integrable Φ ∧
    ∫ c : ℂ, Φ c = hF.formConst * hF.complexData.floorForm i p q F
      fun x : 𝔰.G₁ ↦ wave (ξ * (realFrameGram x).diag ⟨i, Nat.lt_succ_of_lt hi⟩) :=
  hF.gauge.integral_psi_mul_floorForm_succ hF.isCut_complexData ⟨i, hi⟩ hF.formConst ξ
    (hF.lintegral_formMajorant_ne_top hi.le)

/-- Let `F` be the cut of `W` in degree `f ≥ 4000 n`, and let `deg > 0` play the part of a formal
degree: the matrix coefficient `quotientPairing W W` has squared `L²` norm at most
`(card I) ^ 2 / deg`. Suppose also that `deg * scaledVolumeRatio ≤ b ^ (4 r²)` and that the ball of
radius `T ≥ 1` in G₁ has volume at most `T ^ (9 r²) b ^ (99 r²) / deg`. Then there are forms `J i`
on pairs of lists with the local bounds `HasLocalBounds`: each form below the top is an integral of
the next, whose `wave` transform in the entry `i` decays in the frequency; `J (i + 1) p q` decays in
`(p i)⁻¹ - (q i)⁻¹` for `i < ϱ`; the bottom form has modulus at most `(1 + b⁻¹ ^ 10) / deg`; and the
top form `J (ϱ + 1)` is continuous, and positive semidefinite on lists with a common last entry. -/
lemma exists_hasLocalBounds_of_isCutBessel (hF : IsCutBessel F rep ρ s b W f) {deg : ℝ}
    (deg_pos : 0 < deg)
    (h_coeff : ∫⁻ x : 𝔰.G₁, ‖quotientPairing W W x‖ₑ ^ 2 ≤ .ofReal deg⁻¹ * card I ^ 2)
    (deg_le : deg * 𝔰.scaledVolumeRatio ≤ b ^ (4 * 𝔰.r ^ 2))
    (h_ball : ∀ T : ℝ, T ≥ 1 →
      .ofReal deg * volume {g : 𝔰.G₁ | ‖(g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ T} ≤
        ENNReal.ofReal (T ^ (9 * 𝔰.r ^ 2) * b ^ (99 * 𝔰.r ^ 2)))
    (h_degree : 4000 * 𝔰.n ≤ f) :
    ∃ J : ℕ → (ℕ → ℂˣ) → (ℕ → ℂˣ) → ℂ, HasLocalBounds b F deg J := by
  -- The forms are the normalised forms of the floors `i ≤ ϱ` and the Gram form of
  -- `normalizedCellIntegral` on top.
  let J (i : ℕ) (p q : ℕ → ℂˣ) : ℂ :=
    if i ≤ 𝔰.ϱ then hF.formConst * hF.complexData.floorForm i p q F 1
    else ⟪normalizedCellIntegral F p, normalizedCellIntegral F q⟫_ℂ
  have J_floor {i : ℕ} (hi : i ≤ 𝔰.ϱ) (p q : ℕ → ℂˣ) :
      J i p q = hF.formConst * hF.complexData.floorForm i p q F 1 := ite_eq_left hi
  have J_top (p q : ℕ → ℂˣ) : J (𝔰.ϱ + 1) p q = ⟪normalizedCellIntegral F p,
    normalizedCellIntegral F q⟫_ℂ :=
    ite_eq_right (Nat.not_succ_le_self 𝔰.ϱ)
  -- The local bounds do not keep the factor `card I` of the bounds for the decay.
  have one_le_card : (1 : ℝ) ≤ card I := mod_cast card_pos
  refine ⟨J,
    { psi_zero := by simp [wave]
      integrable_and_integral_update := fun i p q ξ hi ↦ ?_
      posSemidef := fun a _ _ ↦ ?_
      continuous := ?_
      norm_bot_le := fun p q ↦ ?_
      norm_le_of_isUnit_sub := fun i p q hi ξ_unit ↦ ?_ },
    fun σ hσ p q hp hq ↦ (J_top p q).trans
      (hF.inner_normalizedCellIntegral_eq_of_last_entry hσ hp hq)⟩
  · -- Descent: the transform in the next entry is the form of floor `i` with the weight `ω`.
    let ω (x : 𝔰.G₁) : ℂ := wave (ξ * (realFrameGram x).diag ⟨i, Nat.lt_succ_of_le hi⟩)
    intro Φ
    have ⟨Φ_integrable, integral_Φ⟩ : Integrable Φ ∧
        ∫ c, Φ c = hF.formConst * hF.complexData.floorForm i p q F ω := by
      obtain hlt | rfl := hi.lt_or_eq
      · simpa only [Φ, J_floor hlt] using hF.integrable_and_integral_wave_mul_floorForm_succ hlt p q
          ξ
      · simp only [Φ, J_top]
        exact hF.integrable_and_integral_wave_mul_inner_normalizedCellIntegral p q ξ
    rw [integral_Φ]
    refine ⟨Φ_integrable, fun ξ_zero ↦ ?_, fun ξ_unit ↦ ?_⟩
    · have ω_eq : ω = 1 := funext fun x ↦ by simp [ω, ξ_zero, wave]
      rw [ω_eq, J_floor hi]
    · exact (le_mul_of_one_le_left (norm_nonneg _) one_le_card).trans
        (hF.norm_floorForm_wave_le hi p q ξ_unit.unit)
  · -- The top form is a Gram form, so it is positive semidefinite.
    simp only [J_top]
    exact posSemidef_gram ℂ fun i ↦ normalizedCellIntegral F (a i)
  · simpa only [uncurry_def, J_top] using
      hF.continuous_normalizedCellIntegral.fst'.inner hF.continuous_normalizedCellIntegral.snd'
  · rw [J_floor zero_le]
    exact hF.norm_floorForm_zero_le deg_pos h_coeff deg_le h_ball h_degree p q
  · -- Decay in the difference of the inverse last entries.
    rw [J_floor hi]
    exact (le_mul_of_one_le_left (norm_nonneg _) one_le_card).trans
      (hF.norm_floorForm_heads_le hi p q ξ_unit.unit (by simp))

end BandLimits

end New.Floors

end
