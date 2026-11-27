import New.Spanning.Frames.FiniteDepth
import New.Spanning.Frames.Shells

/-!
# Shells, decay and mass at the finite places

The positions `x` are sorted by the ideal of the denominators of `(x - 1) / g`, and into dyadic
shells by its index. The sum over the shells gives the decay of the forms in the frequency and the
mass. Here `R = P.integers` is the ring of integers of `A`, `g = F.levelUnit` is the level unit of
the place datum `F`, `ϱ = 𝔰.ϱ`, `n = 𝔰.n = ϱ + 1` and `k = 𝔰.k`.

Notions from other files:
* `New.Floors.IntegralPlace.IsLargeLatticeData.gauge`: the gauge of scale `α`, for a unit `α` of `A`
  that is integral and fixed by the involution; size `j` means `α ^ j * x ∈ R`, and the loss is
  `2 / modulus α`.
* `New.Floors.Size.IsHead`: `p` is a head of length `j` if the inverses of the products
  `p 0 ⋯ p (l - 1)`, `l ≤ j`, have size 1.
* `New.Floors.PlaceData.HasDeepVector`: at a given position, every active point has a vector after
  the head of at least the given depth.
* `New.Floors.PlaceData.formIntegrandL1Norm`, `New.Floors.PlaceData.formMajorant`: the modulus of
  the integrand of the form of floor `j` at a position, and a majorant of it that does not depend on
  the weight.
* `New.Floors.PlaceData.IntermediateGroup`: an integral group `Z` that contains the congruence group
  `K(g) = F.congruenceSubgroup`.

## Main definitions and results

* `New.Floors.PlaceData.dyadicShell`,
  `New.Floors.IntegralPlace.IsLargeLatticeData.isShell_dyadicShell`: the shells; each collects few
  ideals.
* `New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_shells_le`: the sum over the shells.
* `New.Floors.IntegralPlace.IsLargeLatticeData.enorm_floorForm_le`: the decay in the frequency.
* `New.Floors.IntegralPlace.IsLargeLatticeData.setLIntegral_compl_congruenceSubgroup_le`,
  `New.Floors.IntegralPlace.IsLargeLatticeData.massIntegral_le_main_add_error`: the positions
  outside `K(g)` contribute little to the mass.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Fintype FloorGroups InnerProductSpace Subgroup
  IntegralPlace Place Set PlaceData Size SemilocalField QuotientGroup Finset

variable {A ι : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A] [P : IntegralPlace A]
  [Fintype ι] [DecidableEq ι] {m : ℕ} {T : 𝔰.Form A} [IsHermitianUnit T.splitGram]

variable {F : PlaceData ι T (m + 1)} {x y : T.G} (Z : F.IntermediateGroup)

namespace IntegralPlace.IsLargeLatticeData

variable [h : IsLargeLatticeData F]

variable {j K : ℕ} (r t : ℕ) {p q : ℕ → Aˣ} {ξ : Aˣ} {Γ : Gauge F} (hj : j ≤ 𝔰.ϱ)
  (hr : r + 10 ^ 8 * 𝔰.n ^ 4 ≤ 𝔰.k) (ht : t + 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.k)

omit h in
/-- The shell of an ideal `J` of `R = P.integers`: the positions `x` for which `J` is the set of the
common denominators in `R` of the entries of `(x - 1) / g`, where `g = F.levelUnit`. -/
def _root_.New.Floors.PlaceData.idealShell (F : PlaceData ι T (m + 1)) (J : Ideal P.integers) :
    Set T.G :=
  {x ∈ F.positions |
    {ε : A | ε ∈ integers ∧
      ∀ i k : 𝔰.BesselIndex, ε * (F.levelUnit⁻¹.val • (x.val.val - 1)) i k ∈ integers} =
    integers.subtype '' J}

omit h in
/-- For `x` in the group `T.G` and `g = F.levelUnit`, the common denominators in `R = P.integers` of
the entries of `(x - 1) / g` form a principal ideal `J = c R`, where `c ∈ R` is a unit of `A`, and
`J` has finite index `(modulus c)⁻¹`. -/
theorem exists_denominator_ideal (x : T.G) :
    ∃ (c : Aˣ) (J : Ideal P.integers),
      c.val ∈ integers ∧
      J.cardQuot ≠ 0 ∧
      J.cardQuot = (P.modulus c)⁻¹ ∧
      integers.subtype '' J = {ε : A | c⁻¹.val * ε ∈ integers} ∧
      {ε : A | ε ∈ integers ∧
        ∀ i k : 𝔰.BesselIndex, ε * (F.levelUnit⁻¹.val • (x.val.val - 1)) i k ∈ integers} =
          integers.subtype '' J := by
  -- Take `c = t⁻¹` for the content `t` of the vector `D` that lists `1` and these entries.
  classical
  let D (i : Option (𝔰.BesselIndex × 𝔰.BesselIndex)) : A :=
    i.elim 1 (F.levelUnit⁻¹.val • (x.val.val - 1)).uncurry
  obtain ⟨t, -, -, -, ht⟩ :
      ∃ t : Aˣ, ∃ r ∈ intVectors integers _, r ⬝ᵥ D = t ∧
        ∀ ε : A, (∀ i, ε * D i ∈ integers) ↔ t * ε ∈ integers :=
    exists_content (i := none) isUnit_one
  have hc : t⁻¹.val ∈ integers := by simpa [D] using (ht t⁻¹.val).2 (by simp) none
  obtain ⟨J, hJ_ne, hJ, hJ_card⟩ :
      ∃ J : Ideal P.integers, J.cardQuot ≠ 0 ∧
        integers.subtype '' J = {ε : A | t⁻¹⁻¹.val * ε ∈ integers} ∧
        J.cardQuot = (P.modulus t⁻¹.val)⁻¹ :=
    exists_ideal_cardQuot_eq t⁻¹ hc
  -- A common denominator of `1` and the entries is an `ε` with `t ε` integral.
  have h_den (ε : A) :
      (ε ∈ integers ∧
        ∀ i k : 𝔰.BesselIndex, ε * (F.levelUnit⁻¹.val • (x.val.val - 1)) i k ∈ integers) ↔
      t * ε ∈ integers := by
    rw [← ht ε, Option.forall, Prod.forall]
    simp only [D, Option.elim, Function.uncurry, mul_one]
  refine ⟨t⁻¹, J, hc, hJ_ne, hJ_card, hJ, ?_⟩
  rw [hJ, inv_inv]
  exact Set.ext h_den

omit h in
/-- If the shell `F.idealShell J` has a point `x`, then `J = c R` for a unit `c` of `A` that lies in
`R = P.integers`, and the index of `J` is `(modulus c)⁻¹`. -/
theorem exists_generator_of_mem_idealShell {J : Ideal P.integers} {x : T.G}
    (hx : x ∈ F.idealShell J) :
    ∃ c : Aˣ,
      c.val ∈ integers ∧
      J.cardQuot = (P.modulus c)⁻¹ ∧
      integers.subtype '' J = {ε : A | c⁻¹.val * ε ∈ integers} := by
  obtain ⟨c, J', hc, -, h_card, hJ', h_den'⟩ := exists_denominator_ideal (F := F) x
  obtain ⟨-, h_den⟩ := hx
  have h_image : integers.subtype '' (J' : Set P.integers) =
      integers.subtype '' (J : Set P.integers) := h_den'.symm.trans h_den
  obtain rfl : J' = J :=
    SetLike.coe_injective (integers.subtype_injective.image_injective h_image)
  exact ⟨c, hc, h_card, hJ'⟩

/-- An ideal of denominators of large index forces a deep vector. Let `F` be a large lattice datum
with level unit `g = F.levelUnit`, and let `Γ = h.gauge α` be the gauge of scale `α`. Let `p`, `q`
be heads of length `j ≤ 𝔰.ϱ` for `Γ`, and let `g⁻¹` have size 1 if `j ≠ 0`. Let `x` lie in the shell
`F.idealShell J` of the ideal `J` of `R = P.integers`. Suppose `σ < 1` and
`Γ.loss ^ (990 𝔰.n²) ≤ σ ^ (400 𝔰.n²) · J.cardQuot`. Then
`F.HasDeepVector j p q Z.besselVector x (σ²)⁻¹` holds: at every point `y` that is active at `x` for
the Bessel vector of `Z`, the depth `F.depth a y x` is at least `σ⁻²` for some index `a ≥ j`. -/
theorem hasDeepVector_of_mem_idealShell {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    [h : IsLargeLatticeData F] {j : ℕ} {p q : ℕ → Aˣ} {Γ : Gauge F} (hj : j ≤ 𝔰.ϱ)
    {α : Aˣ} {hα : α.val ∈ integers} {hα_star : star α.val = α} (hΓ : Γ = h.gauge α hα hα_star)
    (hp_head : Γ.IsHead j p) (hq_head : Γ.IsHead j q)
    (hg_size : j ≠ 0 → F.levelUnit⁻¹.val ∈ Γ.ofSize 1)
    {J : Ideal P.integers} {x : T.G} (hx : x ∈ F.idealShell J) {σ : ℝ≥0∞} (hσ_lt : σ < 1)
    (hσ : Γ.loss ^ (10 * 𝔰.n * (99 * 𝔰.n)) ≤ σ ^ (400 * 𝔰.n ^ 2) * J.cardQuot) :
    F.HasDeepVector j p q Z.besselVector x (σ ^ 2)⁻¹ := by
  obtain ⟨c, -, h_card, hJ_eq⟩ :
      ∃ c : Aˣ, c.val ∈ integers ∧ J.cardQuot = (P.modulus c)⁻¹ ∧
        integers.subtype '' J = {ε : A | c⁻¹.val * ε ∈ integers} :=
    exists_generator_of_mem_idealShell hx
  obtain ⟨-, hx_den⟩ := hx
  have h_root : P.modulus c * Γ.loss ^ (10 * 𝔰.n * (99 * 𝔰.n)) ≤ σ ^ (400 * 𝔰.n ^ 2) := by
    obtain ⟨hc_ne_zero, hc_ne_top⟩ := modulus_ne_zero_and_ne_top c
    grw [hσ, h_card, mul_left_comm, ENNReal.mul_inv_cancel hc_ne_zero hc_ne_top, mul_one]
  have h_dvd (ε : A) (hε : ε ∈ integers)
      (h_den : ∀ i k : 𝔰.BesselIndex, ε * (F.levelUnit⁻¹.val • (x.val.val - 1)) i k ∈ integers) :
      c⁻¹.val * ε ∈ integers :=
    (hx_den.trans hJ_eq).subset ⟨hε, h_den⟩
  exact hasDeepVector_inv_iff.2 fun y ⟨hy, h_near_p, h_near_q⟩ ↦
    exists_volume_stableProducts_le Z hj hΓ hp_head hq_head hg_size hσ_lt h_root h_dvd hy h_near_p
      h_near_q

/-- Let `F` be a large lattice datum, `Γ` a gauge and `J` an ideal of finite index of
`R = P.integers`. Then some gauge `Γ'` contains the shell `F.idealShell J` in `Γ'.positionsOfSize`:
for every position `x` in it, the matrix `(x - 1) / F.levelUnit` has size 1 for `Γ'`. Moreover
`Γ'.loss ≤ Γ.loss · J.cardQuot²`, where `J.cardQuot = [R : J]`. -/
theorem exists_gauge_idealShell_subset {F : PlaceData ι T (m + 1)} [h : IsLargeLatticeData F]
    (Γ : Gauge F) {J : Ideal P.integers} (hJ : J.cardQuot ≠ 0) :
    ∃ Γ' : Gauge F, F.idealShell J ⊆ Γ'.positionsOfSize ∧ Γ'.loss ≤ Γ.loss * J.cardQuot ^ 2 := by
  obtain h_empty | ⟨x₀, hx₀⟩ := (F.idealShell J).eq_empty_or_nonempty
  · have one_le : (1 : ℝ≥0∞) ≤ J.cardQuot := by exact_mod_cast hJ.pos
    exact ⟨Γ, h_empty.le.trans (Set.empty_subset _), le_mul_of_one_le_right' (one_le_pow₀ one_le)⟩
  -- In the gauge of scale `star c * c` the matrices `(x - 1) / F.levelUnit` have size 1, and its
  -- `loss` is `2 / modulus c ^ 2 = 2 [R : J] ^ 2`.
  obtain ⟨c, hc, h_card, hJ_eq⟩ :
      ∃ c : Aˣ, c.val ∈ integers ∧ J.cardQuot = (P.modulus c)⁻¹ ∧
        integers.subtype '' J = {ε : A | c⁻¹.val * ε ∈ integers} :=
    exists_generator_of_mem_idealShell hx₀
  have hc_star : star c.val ∈ integers := isAdelic.toIsStarStable.star_mem hc
  refine ⟨h.gauge (star c * c) (mul_mem hc_star hc),
    fun x ⟨hx_pos, hx_den⟩ ↦ ⟨hx_pos, fun i k ↦ ?_⟩, ?_⟩
  · have hc_gen : c.val ∈ {ε : A | c⁻¹.val * ε ∈ integers} := by simp
    obtain ⟨-, h_den⟩ : c.val ∈ integers ∧
        ∀ i k : 𝔰.BesselIndex, c.val * (F.levelUnit⁻¹.val • (x.val.val - 1)) i k ∈ integers :=
      (hx_den.trans hJ_eq).superset hc_gen
    simpa [mul_assoc] using mul_mem hc_star (h_den i k)
  · grw [h_card, ← Γ.two_le_loss]
    simp [div_eq_mul_inv, sq, ENNReal.mul_inv]

omit h in
/-- The dyadic shell of height `2 ^ t`: the positions for which `2 ^ t` is the least of `1, 2, 4, …`
that bounds the index of the ideal of the common denominators of the entries of `(x - 1) / g`. -/
def _root_.New.Floors.PlaceData.dyadicShell (F : PlaceData ι T (m + 1)) (t : ℕ) : Set T.G :=
  ⋃ J ∈ {J : Ideal P.integers | J.cardQuot ≠ 0 ∧ Nat.clog 2 J.cardQuot = t}, F.idealShell J

/-- For `N ≠ 0`, the least power of two that is at least `N` is at most `2 N`. -/
theorem two_pow_clog_le_two_mul {N : ℕ} (hN : N ≠ 0) : 2 ^ Nat.clog 2 N ≤ 2 * N := by
  obtain rfl | h_one := (Nat.one_le_iff_ne_zero.2 hN).eq_or_lt
  · simp
  · have h_pred : 2 ^ (Nat.clog 2 N).pred < N := Nat.pow_pred_clog_lt_self one_lt_two h_one
    rw [← Nat.succ_pred_eq_of_pos (Nat.clog_pos one_lt_two h_one), pow_succ']
    omega

/-- Let `F` be a large lattice datum with level unit `g = F.levelUnit`, let `Γ = h.gauge α` be the
gauge of scale `α`, let `p`, `q` be heads of length `j ≤ ϱ` for `Γ`, and let `g⁻¹` have size 1
unless `j = 0`. Then `F.dyadicShell t` is a shell of height `2 ^ t` for the Bessel vector of `Z`: it
is covered by the position balls of few gauges `Γ'` with `Γ'.loss ≤ Γ.loss (2 ^ t)²`, and a large
height forces a deep vector. -/
theorem isShell_dyadicShell {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    [h : IsLargeLatticeData F] {j : ℕ} {p q : ℕ → Aˣ} {Γ : Gauge F} (hj : j ≤ 𝔰.ϱ) {α : Aˣ}
    {hα : α.val ∈ integers} {hα_star : star α.val = α} (hΓ : Γ = h.gauge α hα hα_star)
    (hp_head : Γ.IsHead j p) (hq_head : Γ.IsHead j q)
    (hg_size : j ≠ 0 → F.levelUnit⁻¹.val ∈ Γ.ofSize 1) (t : ℕ) :
    Γ.IsShell j p q Z.besselVector (F.dyadicShell t) (2 ^ t) := by
  classical
  have h_one_le : (1 : ℝ≥0∞) ≤ 2 ^ t := one_le_pow₀ one_le_two
  refine ⟨h_one_le, by finiteness, ?few_gauges, fun x hx σ hσ_lt hσ ↦ ?deep_vector⟩
  case few_gauges =>
    -- Take one gauge `G J` for each of the finitely many ideals of index at most `2 ^ t`.
    obtain ⟨h_zeta, hm : m < 9 * 𝔰.n, -⟩ := h.zeta_le_and_le_card
    -- As `idealZeta P.integers m ≤ 2`, at most `2 (2 ^ t) ^ m` ideals have index at most `2 ^ t`.
    have h_zeta_two : idealZeta P.integers m ≤ 2 := le_two_of_pow_le_ofReal h_zeta
    have h_ne_zero : ((2 : ℝ≥0∞) ^ t)⁻¹ ^ m ≠ 0 := by simp
    obtain ⟨h_finite, h_card⟩ :
        ∃ h_finite : {J : {J : Ideal P.integers // J.cardQuot ≠ 0} |
            ((2 : ℝ≥0∞) ^ t)⁻¹ ^ m ≤ (J.val.cardQuot : ℝ≥0∞)⁻¹ ^ m}.Finite,
          (#h_finite.toFinset : ℝ≥0∞) ≤ 2 / ((2 : ℝ≥0∞) ^ t)⁻¹ ^ m :=
      ENNReal.finset_card_const_le_le_of_tsum_le ofNat_ne_top h_zeta_two h_ne_zero
    have h_gauge (J : {J : Ideal P.integers // J.cardQuot ≠ 0}) :
        ∃ Γ' : Gauge F, F.idealShell J.val ⊆ Γ'.positionsOfSize ∧
          Γ'.loss ≤ Γ.loss * J.val.cardQuot ^ 2 :=
      exists_gauge_idealShell_subset Γ J.prop
    choose G hG_subset hG_scale using h_gauge
    let S : Finset {J : Ideal P.integers // J.cardQuot ≠ 0} :=
      {J ∈ h_finite.toFinset | J.val.cardQuot ≤ 2 ^ t}
    have hS_card : (#S : ℝ≥0∞) ≤ 2 * (2 ^ t) ^ m :=
      calc (#S : ℝ≥0∞) ≤ #h_finite.toFinset := Nat.cast_le.2 (card_filter_le _ _)
        _ ≤ 2 / ((2 : ℝ≥0∞) ^ t)⁻¹ ^ m := h_card
        _ = 2 * (2 ^ t) ^ m := by rw [div_eq_mul_inv, ← ENNReal.inv_pow, inv_inv]
    have hS_cover : F.dyadicShell t ⊆ ⋃ Γ' ∈ S.image G, Γ'.positionsOfSize := by
      intro x hx
      obtain ⟨J, ⟨hJ, rfl⟩, hxJ⟩ := Set.mem_iUnion₂.1 hx
      have h_le : J.cardQuot ≤ 2 ^ Nat.clog 2 J.cardQuot := Nat.le_pow_clog one_lt_two _
      have h_mem : (⟨J, hJ⟩ : {J : Ideal P.integers // J.cardQuot ≠ 0}) ∈ h_finite.toFinset := by
        rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        gcongr
        exact_mod_cast h_le
      exact Set.mem_biUnion (mem_image_of_mem G (mem_filter.2 ⟨h_mem, h_le⟩))
        (hG_subset ⟨J, hJ⟩ hxJ)
    have hS_scale (Γ' : Gauge F) (hΓ' : Γ' ∈ S.image G) : Γ'.loss ≤ Γ.loss * (2 ^ t) ^ 2 := by
      obtain ⟨J, hJ, rfl⟩ := mem_image.1 hΓ'
      have h_le : (J.val.cardQuot : ℝ≥0∞) ≤ 2 ^ t := by exact_mod_cast (mem_filter.1 hJ).2
      grw [hG_scale J, h_le]
    have h_few : (#(S.image G) : ℝ≥0∞) ≤ 2 * (2 ^ t) ^ (9 * 𝔰.n) := by
      grw [card_image_le, hS_card, pow_le_pow_right₀ h_one_le hm.le]
    exact ⟨S.image G, h_few, hS_cover, hS_scale⟩
  case deep_vector =>
    -- The index of the ideal is at least half the height; one factor `Γ.loss ≥ 2` pays for this.
    obtain ⟨J, ⟨hJ, rfl⟩, hxJ⟩ := Set.mem_iUnion₂.1 hx
    have h_half : (2 : ℝ≥0∞) ^ Nat.clog 2 J.cardQuot ≤ 2 * J.cardQuot := by
      exact_mod_cast two_pow_clog_le_two_mul hJ
    have h_double : 2 * Γ.loss ^ (10 * 𝔰.n * (99 * 𝔰.n)) ≤ 2 * (σ ^ (400 * 𝔰.n ^ 2) * J.cardQuot) :=
      calc _ ≤ Γ.loss ^ (10 * 𝔰.n * (99 * 𝔰.n) + 1) := by grw [Γ.two_le_loss, pow_succ']
        _ ≤ Γ.loss ^ (1200 * 𝔰.n ^ 2) := pow_le_pow_right₀ Γ.one_le_loss (by lia)
        _ ≤ 2 * (σ ^ (400 * 𝔰.n ^ 2) * J.cardQuot) := by grw [hσ, h_half, mul_left_comm]
    have h_large : Γ.loss ^ (10 * 𝔰.n * (99 * 𝔰.n)) ≤ σ ^ (400 * 𝔰.n ^ 2) * J.cardQuot := by
      rwa [ENNReal.mul_le_mul_iff_right two_ne_zero ofNat_ne_top] at h_double
    exact hasDeepVector_of_mem_idealShell Z hj hΓ hp_head hq_head hg_size hxJ hσ_lt h_large

/-- The sum over the shells at the finite places. Let `F` be a large lattice datum with level unit
`g = F.levelUnit`, let `Γ = h.gauge α` be the gauge of scale `α`, let `p`, `q` be heads of length
`j ≤ 𝔰.ϱ` for `Γ`, let `g⁻¹` have size 1 if `j ≠ 0`, and let `r + 10⁸ 𝔰.n⁴ ≤ 𝔰.k`. Let `f` lie below
the majorant `F.formMajorant` of `p`, `q` and the Bessel vector of `Z` and, if `e < 1`, have a
square at most `(e ^ s)²` times `Γ.weightedSquareProduct` at every position, where
`s = F.volumeExponent`. Then `F.headDensity j p q` times the integral of `f` is at most
`min 1 e ^ r · Z.massRatio · Γ.loss ^ (10⁹ 𝔰.n⁴)`. -/
theorem lintegral_shells_le {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    [h : IsLargeLatticeData F] {j : ℕ} (r : ℕ) {p q : ℕ → Aˣ} {Γ : Gauge F} (hj : j ≤ 𝔰.ϱ)
    (hr : r + 10 ^ 8 * 𝔰.n ^ 4 ≤ 𝔰.k) {α : Aˣ} {hα : (α : A) ∈ integers}
    {hα_star : star (α : A) = (α : A)} (hΓ : Γ = h.gauge α hα hα_star)
    (hp_head : Γ.IsHead j p) (hq_head : Γ.IsHead j q)
    (hg_size : j ≠ 0 → F.levelUnit⁻¹.val ∈ Γ.ofSize 1) {f : T.G → ℝ≥0∞} {e : ℝ≥0∞}
    (hf : ∀ {x : T.G}, f x ≤ F.formMajorant j p q Z.besselVector x)
    (he : e < 1 → ∀ x ∈ F.positions,
      f x ^ 2 ≤ (e ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct j p q Z.besselVector x) :
    F.headDensity j p q * ∫⁻ x : T.G, f x ∂F.groupMeasure ≤
      min 1 e ^ r * Z.massRatio * Γ.loss ^ (10 ^ 9 * 𝔰.n ^ 4) := by
  obtain ⟨-, hm, h_rank⟩ := h.zeta_le_and_le_card
  have h_exp : 9 * 10 ^ 7 * 𝔰.n ^ 4 + r ≤ F.volumeExponent := by
    have h_card : 𝔰.k + 1 = Fintype.card ι + 2 * (m + 1) + 2 := F.card_eq
    simp only [volumeExponent, blockRank, Fintype.card_fin]
    lia
  -- Each position lies in the dyadic shell of the denominator ideal of `(x - 1) / g`.
  have h_cover : f.support ⊆ ⋃ t : ℕ, F.dyadicShell t := by
    intro x hx
    obtain ⟨c, J, -, hJ_finite, -, -, h_den⟩ := exists_denominator_ideal (F := F) x
    have h_pos : x ∈ F.positions :=
      mem_positions_of_formMajorant_ne_zero Z (ne_bot_of_le_ne_bot hx hf)
    have hxJ : x ∈ F.idealShell J := ⟨h_pos, h_den⟩
    exact Set.mem_iUnion.2 ⟨Nat.clog 2 J.cardQuot, Set.mem_iUnion₂.2 ⟨J, ⟨hJ_finite, rfl⟩, hxJ⟩⟩
  -- The mass of floor `j`, bounded in the gauge of scale `1`, where the loss is `2`.
  have h_mass : F.FloorMassLe j (2 ^ (99 * (𝔰.n * 13))) 1 := by
    simpa [SemilocalField.volume_O, mul_assoc] using
      h.gauge.floorMassLe_one ⟨j, by lia⟩
  have one_le_mass : (1 : ℝ≥0∞) ≤ 2 ^ (99 * (𝔰.n * 13)) := one_le_pow₀ one_le_two
  have h_gain (he_lt : e < 1) (x : T.G) (hx : x ∈ F.positions) : f x ^ 2 ≤
      (2 ^ (99 * (𝔰.n * 13)) * e ^ F.volumeExponent) ^ 2 *
        Γ.weightedSquareProduct j p q Z.besselVector x := by
    grw [he he_lt x hx, ← one_le_mass, one_mul]
  have h_unit : F.shellNormalization Z.besselVector ≤ Z.massRatio := by
    simpa [shellNormalization, data_normalised, mul_comm] using pairingNormSq_mul_le_massRatio Z
  calc F.headDensity j p q * ∫⁻ x : T.G, f x ∂F.groupMeasure
      ≤ 2 ^ (99 * (𝔰.n * 13)) * min 1 e ^ r * Γ.loss ^ (4 * 10 ^ 8 * 𝔰.n ^ 4) *
          F.shellNormalization Z.besselVector :=
        Γ.lintegral_le_of_shells (isShell_dyadicShell Z hj hΓ hp_head hq_head hg_size) h_cover
          (isCut_besselVector Z) hj hp_head hq_head h_mass one_le_mass (fun _ ↦ hf) h_gain h_exp
    _ ≤ min 1 e ^ r * Z.massRatio * Γ.loss ^ (99 * (𝔰.n * 13) + 4 * 10 ^ 8 * 𝔰.n ^ 4) := by
        grw [h_unit, Γ.two_le_loss]
        exact le_of_eq (by ring)
    _ ≤ min 1 e ^ r * Z.massRatio * Γ.loss ^ (10 ^ 9 * 𝔰.n ^ 4) := by
        gcongr
        · exact Γ.one_le_loss
        · lia

/-- Let `F` be a large lattice datum, let `Z` be a group with `F.congruenceSubgroup` ≤ `Z` ≤ K,
where K is the integral unitary group, let `p`, `q` be any sequences of units of `A`, and let
`j ≤ 𝔰.ϱ`. Suppose `r + 10⁸ 𝔰.n⁴ ≤ 𝔰.k` for some `r`, so the rank `𝔰.k` is large. Then the majorant
`F.formMajorant j p q Z.besselVector` of the form of floor `j` has a finite integral over the group
`T.G` for `F.groupMeasure`. -/
theorem lintegral_formMajorant_ne_top {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    [h : IsLargeLatticeData F] {j : ℕ} (r : ℕ) {p q : ℕ → Aˣ} (hj : j ≤ 𝔰.ϱ)
    (hr : r + 10 ^ 8 * 𝔰.n ^ 4 ≤ 𝔰.k) :
    ∫⁻ x : T.G, F.formMajorant j p q Z.besselVector x ∂F.groupMeasure ≠ ∞ := by
  -- If the majorant is not identically zero, `exists_gauge_of_formMajorant_ne_zero` gives a gauge
  -- to which `lintegral_shells_le` applies with `e = 1`. Its bound is finite and
  -- `F.headDensity j p q ≠ 0`.
  by_cases! h_ne : ∀ x : T.G, F.formMajorant j p q Z.besselVector x = 0
  · simp [h_ne]
  obtain ⟨α, hα, hα_star, hp_head, hq_head, hg_size, -⟩ :=
    exists_gauge_of_formMajorant_ne_zero Z hj 0 p q h_ne
  set Γ : Gauge F := h.gauge α hα hα_star
  have h_bound : F.headDensity j p q *
      ∫⁻ x : T.G, F.formMajorant j p q Z.besselVector x ∂F.groupMeasure ≤
        min 1 (1 : ℝ≥0∞) ^ r * Z.massRatio * Γ.loss ^ (10 ^ 9 * 𝔰.n ^ 4) :=
    lintegral_shells_le Z r hj hr rfl hp_head hq_head hg_size le_rfl (by simp)
  have h_density : F.headDensity j p q ≠ 0 := by simp [headDensity, prod_eq_zero_iff]
  have h_finite : min 1 (1 : ℝ≥0∞) ^ r * Z.massRatio * Γ.loss ^ (10 ^ 9 * 𝔰.n ^ 4) ≠ ∞ := by
    simp [massRatio_ne_zero_and_ne_top, mul_eq_top, Γ.loss_ne_top]
  exact (lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top h_finite h_bound) h_density).ne

/-- Two units `ξ`, `β` of `A` have a common divisor `η` over the ring `R = P.integers` of integers.
That is, `ξ η⁻¹ ∈ R` and `η⁻¹ β ∈ R`. This `η` is a unit of `A` and is congruent to `ξ` modulo
`β R`: `η = ξ + c β` for some `c ∈ R`. -/
theorem exists_unit_common_divisor (ξ β : Aˣ) :
    ∃ η : Aˣ,
      ξ * η⁻¹.val ∈ P.integers ∧
      η⁻¹ * β.val ∈ P.integers ∧
      ∃ c ∈ P.integers, η = ξ + c * β := by
  -- For some integral idempotent `e`, `d = ξ - e (ξ - β)` divides `ξ = d x` and `β = d y`.
  obtain ⟨e, he_idem, ⟨x, hx, hξ⟩, he, y, hy, hβ⟩ :
      ∃ e : A, e * e = e ∧ (∃ x ∈ P.integers, ξ = (ξ - e * (ξ - β)) * x) ∧
        e ∈ P.integers ∧ ∃ y ∈ P.integers, β = (ξ - e * (ξ - β)) * y := by
    simpa using isValuationPair ξ.val β
  -- Since `e d = e β`, one has `d = ξ + (e - x e) β`, with inverse `ξ⁻¹ x`.
  have h_ed : e * (ξ - e * (ξ - β) : A) = e * β := by
    linear_combination (β - ξ : A) * he_idem
  have hd_eq : (ξ + (e - x * e) * β : A) = ξ - e * (ξ - β) := by
    linear_combination e * hξ + x * h_ed
  have hd_inv : (ξ - e * (ξ - β) : A) * (ξ⁻¹.val * x) = 1 := by
    linear_combination ξ.mul_inv - ξ⁻¹.val * hξ
  let η : Aˣ := .mkOfMulEqOne (ξ + (e - x * e) * β) (ξ⁻¹.val * x) (by rw [hd_eq, hd_inv])
  have hη_inv : η⁻¹.val = ξ⁻¹.val * x := rfl
  refine ⟨η, ?_, ?_, e - x * e, sub_mem he (mul_mem hx he), rfl⟩
  · rwa [hη_inv, Units.mul_inv_cancel_left]
  · have hy_eq : ξ⁻¹.val * x * β = y := by
      linear_combination (ξ⁻¹.val * x) * hβ + y * hd_inv
    rwa [hη_inv, hy_eq]

/-- The unit that gives the gain for the weights of `enorm_floorForm_le`. Let `F` be a large lattice
datum with level unit `g = F.levelUnit`, let `α` be a unit of `A` that is integral and fixed by the
involution, and measure sizes in the gauge `Γ = h.gauge α` of scale `α`. Let `p` be a head of length
`j ≤ ϱ`, let `g⁻¹` have size 1 if `j ≠ 0`, and let `1 / p i - 1 / q i` have size 1 for `i < j`. Let
the weight `ω` and the unit `ξ` be of one of two kinds: (a) `ω x = ψ (ξ h(f_j, x f_j))` for the
frame vector `f_j`, or (b) `ω = 1`, `j = i + 1` and `ξ = (1 / p i - 1 / q i) / g`. Then there are
units `η` and `w` such that `w`, `ξ w` and `ξ / η` are integral, at every position the square of
`F.formIntegrandL1Norm` for the Bessel vector of `Z` is at most
`(kernelBound / modulus η) ^ card F.FreeIndex` times `Γ.weightedSquareProduct`, and
`min 1 √(genIndex η) ^ 2` is at most `modulus w / modulus (α ^ (200 n²))`. Here `genIndex η` is the
inverse of the modulus of `η` and `kernelBound` is the constant in Plancherel's formula. -/
theorem exists_unit_formIntegrandL1Norm_sq_le {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    [h : IsLargeLatticeData F] {j : ℕ} {p q : ℕ → Aˣ} {ξ : Aˣ} (hj : j ≤ 𝔰.ϱ) {α : Aˣ}
    (hα : (α : A) ∈ integers) (hα_star : star (α : A) = (α : A)) {ω : T.G → ℂ}
    (hp_head : (h.gauge α hα hα_star).IsHead j p)
    (hg_size : j ≠ 0 → F.levelUnit⁻¹.val ∈ (h.gauge α hα hα_star).ofSize 1)
    (h_close : ∀ i < j, (p i)⁻¹.val - (q i)⁻¹.val ∈ (h.gauge α hα hα_star).ofSize 1)
    (hω :
      (ω = fun x : T.G ↦ P.ψ (ξ * (T.frameGram x.val.val).diag ⟨j, Nat.lt_succ_of_le hj⟩)) ∨
      ∃ i : ℕ, j = i + 1 ∧ ω = 1 ∧ ξ.val = F.levelUnit⁻¹.val * ((p i)⁻¹.val - (q i)⁻¹.val)) :
    ∃ η w : Aˣ,
      w.val ∈ integers ∧
      ξ * w.val ∈ integers ∧
      ξ * η⁻¹.val ∈ integers ∧
      (∀ x ∈ F.positions,
        F.formIntegrandL1Norm j p q Z.besselVector x ω ^ 2 ≤
          (P.kernelBound / P.modulus η) ^ card F.FreeIndex *
            (h.gauge α hα hα_star).weightedSquareProduct j p q Z.besselVector x) ∧
      min 1 (ENNReal.ofReal √(genIndex η.val)) ^ 2 ≤
        P.modulus w * P.modulus (α ^ (200 * 𝔰.n ^ 2))⁻¹.val := by
  have h_cut : F.IsCut Z.besselVector := isCut_besselVector Z
  set Γ : Gauge F := h.gauge α hα hα_star
  set β : Aˣ := α ^ (200 * 𝔰.n ^ 2)
  have hβ : β.val ∈ integers := pow_mem hα _
  obtain rfl | ⟨i, hi, rfl, hξ⟩ := hω
  · -- Free head: `η ≡ ξ` modulo `β R`, so `ψ(ξ z) = ψ(η z)` whenever `β z ∈ R`; `w = β / η`.
    obtain ⟨η, hξη, hηβ, c, hc, hη⟩ :
        ∃ η : Aˣ, ξ * η⁻¹.val ∈ P.integers ∧ η⁻¹ * β.val ∈ P.integers ∧
          ∃ c ∈ P.integers, η = ξ + c * β :=
      exists_unit_common_divisor ξ β
    have hψ (z : A) (hz : z ∈ Γ.ofSize (200 * 𝔰.n ^ 2)) : P.ψ (ξ * z) = P.ψ (η * z) := by
      have hβz : P.ψ (c * (β * z)) = 1 := by
        simpa [mul_comm] using (self_dual (β * z)).2 hz c hc
      rw [hη, add_mul, P.ψ.map_add_eq_mul, mul_assoc, hβz, mul_one]
    have hwξ : ξ * (η⁻¹ * β).val ∈ integers := by simpa [mul_assoc] using mul_mem hξη hβ
    refine ⟨η, η⁻¹ * β, hηβ, hwξ, hξη,
      fun x hx ↦ Γ.formIntegrandL1Norm_sq_le_of_char h_cut hj hp_head hx hψ, ?_⟩
    grw [min_le_right, ← inv_modulus_eq_sqrt_genIndex_sq, ← map_mul]
    simp
  · -- Summed head: `η = ξ` and `w = β`, as `ξ` has size `2 ≤ 200 * 𝔰.n ^ 2`.
    have hξ_size : ξ.val ∈ Γ.ofSize (200 * 𝔰.n ^ 2) := by
      rw [hξ]
      exact mem_ofSize_mono (Γ.mul_mem_ofSize (hg_size (by lia)) (h_close i hi.ge))
    refine ⟨ξ, β, hβ, ?_, by simp,
      fun x hx ↦ Γ.formIntegrandL1Norm_sq_le_of_heads h_cut hj hp_head hx hi hξ, ?_⟩
    · have hβξ : β.val * ξ ∈ integers := hξ_size
      rwa [mul_comm]
    · simp [ENNReal.mul_inv_cancel, pow_le_one']

/-- If `ξ`, `w` are units of `A` with `w` and `ξ w` in `R = P.integers`, then `P.modulus w` is at
most the inverse of `denomIndex R ξ = [R : R ∩ ξ⁻¹ R]`. -/
theorem modulus_le_inv_denomIndex {ξ w : Aˣ} (hw : w.val ∈ P.integers)
    (hξw : ξ * w.val ∈ P.integers) :
    P.modulus w ≤ (denomIndex P.integers ξ.val : ℝ≥0∞)⁻¹ := by
  -- `w R` lies in `R ∩ ξ⁻¹ R`, whose volume is the inverse of its index in `R`.
  let L : AddSubgroup A := P.integers.toAddSubgroup.comap (AddMonoidHom.mulLeft ξ.val)
  have h_volume : volume ((L : Set A) ∩ P.integers.toAddSubgroup) =
      (denomIndex P.integers ξ.val : ℝ≥0∞)⁻¹ :=
    measure_inter_eq_inv_relIndex_add isCompact_O (isOpen_O.preimage (continuous_const_mul ξ.val))
      volume SemilocalField.volume_O
  rw [← h_volume]
  refine modulus_le_volume fun a ha ↦ ⟨?_, P.integers.mul_mem hw ha⟩
  change ξ.val * (w.val * a) ∈ integers
  rw [← mul_assoc]
  exact mul_mem hξw ha

/-- Let `ξ`, `η`, `w` be units of `A` with `w`, `ξ w` and `ξ / η` in `R`, and put
`e = √(genIndex η)`. If `min 1 e ^ 2 ≤ modulus w · L`, then `min 1 e ^ (t + 12)` is at most
`√(genIndex ξ) ^ t` times the sixth power of `L / denomIndex R ξ`, where
`denomIndex R ξ = [R : R ∩ ξ⁻¹ R]`. -/
theorem min_sqrt_genIndex_pow_le {ξ η w : Aˣ} {L : ℝ≥0∞} (t : ℕ) (hw : w.val ∈ P.integers)
    (hξw : ξ * w.val ∈ P.integers) (hξη : ξ * η⁻¹.val ∈ P.integers)
    (h_sq : min 1 (ENNReal.ofReal √(genIndex η.val)) ^ 2 ≤ P.modulus w * L) :
    min 1 (ENNReal.ofReal √(genIndex η.val)) ^ (t + 12) ≤
      ENNReal.ofReal √(genIndex ξ.val) ^ t * ((denomIndex P.integers ξ.val : ℝ≥0∞)⁻¹ * L) ^ 6 := by
  -- `ξ / η` is integral, so its index is at least 1.
  have h_index : genIndex η.val ≤ genIndex ξ.val :=
    calc genIndex η.val ≤ genIndex (ξ * η⁻¹.val) * genIndex η.val :=
        le_mul_of_one_le_left (genIndex_pos η).le (one_le_genIndex hξη (by simp))
      _ = genIndex ξ.val := by rw [← map_mul, η.inv_mul_cancel_right]
  calc _ = min 1 (ENNReal.ofReal √(genIndex η.val)) ^ t *
        (min 1 (ENNReal.ofReal √(genIndex η.val)) ^ 2) ^ 6 := by ring
    _ ≤ _ := by grw [h_sq, modulus_le_inv_denomIndex hw hξw, min_le_right, h_index]

/-- The bound for the form of floor `j ≤ 𝔰.ϱ`. Let `F` be a large lattice datum with level unit
`g = F.levelUnit`, let `Z` be an integral group that contains the congruence subgroup
K(g) = `F.congruenceSubgroup`, let `R` = `integers` be the ring of integers of `A`, let `p`, `q` be
sequences of units of `A`, and let `t + 10¹⁰ 𝔰.n⁴ ≤ 𝔰.k` and `10¹⁰ 𝔰.n⁴ ≤ K`. The weight `ω` and the
unit `ξ` are of one of two kinds: (a) `ω x = P.ψ (ξ ⟨f_j, x f_j⟩)` for the hermitian form of `T` and
the frame vector `f_j`, or (b) `ω = 1`, `j = i + 1` and `ξ = (1 / p i - 1 / q i) / g`. Then the form
`F.floorForm` of `p`, `q` and the Bessel vector of `Z` has norm at most the product of
`Z.massRatio = vol(Z) vol(K(g)) / F.unipotentMass ^ 2`, of `√(genIndex ξ) ^ t`, of the sixth power
of the inverse of `denomIndex R ξ = [R : R ∩ ξ⁻¹ R]`, of `(2 / P.modulus g) ^ K` and of the weights
`New.finHeadWeight K j` of `p` and `q`. -/
theorem enorm_floorForm_le {F : PlaceData ι T (m + 1)} [h : IsLargeLatticeData F]
  (Z : F.IntermediateGroup)
    {j K : ℕ} (t : ℕ) {p q : ℕ → Aˣ} {ξ : Aˣ} (hj : j ≤ 𝔰.ϱ)
    (ht : t + 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.k) {ω : T.G → ℂ} (hK : 10 ^ 10 * 𝔰.n ^ 4 ≤ K)
    (hω :
      -- free head: the weight is the character `ψ(ξ ·)` of the diagonal Gram entry of index `j`
      (ω = fun x : T.G ↦ P.ψ (ξ * (T.frameGram x.val.val).diag ⟨j, Nat.lt_succ_of_le hj⟩)) ∨
      -- summed head: no weight, and `ξ` is read off the last entries of the heads
      ∃ i : ℕ, j = i + 1 ∧ ω = 1 ∧ ξ.val = F.levelUnit⁻¹.val * ((p i)⁻¹.val - (q i)⁻¹.val)) :
    ‖F.floorForm j p q Z.besselVector ω‖ₑ ≤
      Z.massRatio *
        (ENNReal.ofReal √(genIndex ξ.val) ^ t * (denomIndex integers ξ.val : ℝ≥0∞)⁻¹ ^ 6 *
          (2 / P.modulus F.levelUnit) ^ K *
          ENNReal.ofReal (finHeadWeight K j p * finHeadWeight K j q)) := by
  -- Apply `lintegral_shells_le` in the gauge of `exists_gauge_of_formMajorant_ne_zero`, with the
  -- gain `e = √(genIndex η)` that the local theorems give for a suitable unit `η` dividing `ξ`;
  -- then trade `min 1 e ^ 12` for `(denomIndex R ξ)⁻¹ ^ 6`.
  have h_major {x : T.G} :
      F.formIntegrandL1Norm j p q Z.besselVector x ω ≤ F.formMajorant j p q Z.besselVector x :=
    (isCut_besselVector Z).formIntegrandL1Norm_le_formMajorant (by bound)
  by_cases! h_ne : ∀ x : T.G, F.formMajorant j p q Z.besselVector x = 0
  · grw [PlaceData.enorm_floorForm_le, h_major]
    simp [h_ne]
  obtain ⟨α, hα_mem, hα_star, hp_head, hq_head, hg_size, h_close, h_Lambda_pow⟩ :
      ∃ (α : Aˣ) (hα_mem : α.val ∈ integers) (hα_star : star α.val = α.val),
        let Γ : Gauge F := h.gauge α hα_mem hα_star
        Γ.IsHead j p ∧ Γ.IsHead j q ∧ (j ≠ 0 → F.levelUnit⁻¹.val ∈ Γ.ofSize 1) ∧
        (∀ i : ℕ, i < j → (p i)⁻¹.val - (q i)⁻¹.val ∈ Γ.ofSize 1) ∧
        ∀ E : ℕ, 4 * E ≤ K → Γ.loss ^ E ≤
          (2 / P.modulus F.levelUnit) ^ K * ENNReal.ofReal
            (finHeadWeight K j p * finHeadWeight K j q) :=
    exists_gauge_of_formMajorant_ne_zero Z hj K p q h_ne
  set Γ : Gauge F := h.gauge α hα_mem hα_star
  let β : Aˣ := α ^ (200 * 𝔰.n ^ 2)
  obtain ⟨η, w, hw, hξw, hξη, h_local, h_md⟩ :
      ∃ η w : Aˣ, w.val ∈ integers ∧ ξ * w.val ∈ integers ∧ ξ * η⁻¹.val ∈ integers ∧
        (∀ x ∈ F.positions, F.formIntegrandL1Norm j p q Z.besselVector x ω ^ 2 ≤
          (P.kernelBound / P.modulus η) ^ card F.FreeIndex *
            Γ.weightedSquareProduct j p q Z.besselVector x) ∧
        min 1 (ENNReal.ofReal √(genIndex η.val)) ^ 2 ≤ P.modulus w * P.modulus β⁻¹.val :=
    exists_unit_formIntegrandL1Norm_sq_le Z hj hα_mem hα_star hp_head hg_size h_close hω
  set e : ℝ≥0∞ := ENNReal.ofReal √(genIndex η.val) with he
  set s : ℝ≥0∞ := ENNReal.ofReal √(genIndex ξ.val)
  set d : ℝ≥0∞ := (denomIndex integers ξ.val : ℝ≥0∞)⁻¹
  -- `P.kernelBound = 1`, so `P.kernelBound / modulus η = e ^ 2`.
  have h_gain (he_lt : e < 1) (x : T.G) (hx : x ∈ F.positions) :
      F.formIntegrandL1Norm j p q Z.besselVector x ω ^ 2 ≤
        (e ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct j p q Z.besselVector x := by
    have h_kernel : P.kernelBound = 1 := by simp [data_normalised]
    have h_exp : F.volumeExponent ≤ card F.FreeIndex := tsub_le_self
    grw [h_local x hx, h_kernel, one_div, inv_modulus_eq_sqrt_genIndex_sq, pow_right_comm, ← he,
      pow_le_pow_right_of_le_one' he_lt.le h_exp]
  have hβ_md : P.modulus β⁻¹.val ≤ Γ.loss ^ (200 * 𝔰.n ^ 2) := by
    have h_one : β.val * β⁻¹.val ∈ integers := by simp
    exact Γ.modulus_le (200 * 𝔰.n ^ 2) β⁻¹ h_one
  have h_pow : min 1 e ^ (t + 12) ≤ s ^ t * (d * Γ.loss ^ (200 * 𝔰.n ^ 2)) ^ 6 :=
    min_sqrt_genIndex_pow_le t hw hξw hξη (h_md.trans (by grw [hβ_md]))
  -- The exponents of `Γ.loss` add up to at most `K / 4`.
  let E : ℕ := 200 * 𝔰.n ^ 2 * 6 + 10 ^ 9 * 𝔰.n ^ 4
  have hE : 4 * E ≤ K := by
    have h_sq : 𝔰.n ^ 2 ≤ 𝔰.n ^ 4 := Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num)
    omega
  calc ‖F.floorForm j p q Z.besselVector ω‖ₑ
      ≤ F.headDensity j p q * ∫⁻ x : T.G,
        F.formIntegrandL1Norm j p q Z.besselVector x ω ∂F.groupMeasure :=
        PlaceData.enorm_floorForm_le ω
    _ ≤ min 1 e ^ (t + 12) * Z.massRatio * Γ.loss ^ (10 ^ 9 * 𝔰.n ^ 4) :=
        lintegral_shells_le Z (t + 12) hj (by lia) rfl hp_head hq_head hg_size h_major h_gain
    _ ≤ s ^ t * (d * Γ.loss ^ (200 * 𝔰.n ^ 2)) ^ 6 * Z.massRatio * Γ.loss ^ (10 ^ 9 * 𝔰.n ^ 4) := by
        grw [h_pow]
    _ = Z.massRatio * (s ^ t * d ^ 6 * Γ.loss ^ E) := by ring
    _ ≤ Z.massRatio * (s ^ t * d ^ 6 * (2 / P.modulus F.levelUnit) ^ K *
          ENNReal.ofReal (finHeadWeight K j p * finHeadWeight K j q)) := by
        grw [h_Lambda_pow E hE, ← mul_assoc (s ^ t * d ^ 6)]

/-- Let `Q` be at most the index of every proper ideal of finite index of the ring of integers `R`.
A unit `c` of `A` with `c ∈ R` and `c⁻¹ ∉ R` has modulus at most `Q⁻¹`: it generates a proper ideal
of index `(modulus c)⁻¹`. -/
theorem modulus_le_inv_of_le_cardQuot {A : Type} [SemilocalField A] [StarRing A]
    [P : IntegralPlace A]
    {Q : ℕ} (hQ_le : ∀ I : Ideal P.integers, I ≠ ⊤ → I.cardQuot ≠ 0 → Q ≤ I.cardQuot) (c : Aˣ)
    (hc : c.val ∈ P.integers) (hc_inv : c⁻¹.val ∉ P.integers) : P.modulus c ≤ (Q : ℝ≥0∞)⁻¹ := by
  obtain ⟨I, hI_ne, hI_eq, hI_card⟩ : ∃ I : Ideal P.integers, I.cardQuot ≠ 0 ∧
      integers.subtype '' I = {x : A | c⁻¹.val * x ∈ integers} ∧ I.cardQuot = (P.modulus c)⁻¹ :=
    exists_ideal_cardQuot_eq c hc
  have h_proper : I ≠ ⊤ := by
    rintro rfl
    -- `1` lies in the image of the whole ring, which is the set of `x` with `c⁻¹ * x` integral.
    have h_one : (1 : A) ∈ {x : A | c⁻¹.val * x ∈ integers} := hI_eq.le ⟨1, Submodule.mem_top, rfl⟩
    exact hc_inv (by simpa using h_one)
  rw [ENNReal.le_inv_iff_le_inv, ← hI_card]
  exact_mod_cast hQ_le I h_proper hI_ne

/-- Let `R = P.integers` be the ring of integers of `A`. A unit `c` of `A` with `c ∈ R` and
`c⁻¹ ∉ R` has modulus at most `1 / 2`. -/
theorem modulus_le_half {A : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] (c : Aˣ)
    (hc : c.val ∈ P.integers) (hc_inv : c⁻¹.val ∉ P.integers) : P.modulus c ≤ 2⁻¹ := by
  have h_two (I : Ideal P.integers) (h_proper : I ≠ ⊤) (h_finite : I.cardQuot ≠ 0) :
      2 ≤ I.cardQuot :=
    (Nat.two_le_iff _).2 ⟨h_finite, mt Submodule.cardQuot_eq_one_iff.1 h_proper⟩
  exact_mod_cast modulus_le_inv_of_le_cardQuot h_two c hc hc_inv

/-- Let `R = P.integers` be the ring of integers of `A`. For a unit `c` of `A` with `c ∈ R` and
`c⁻¹ ∉ R`, the ideal `c R` consists of non-units of `R`, so the modulus of `c` is at most the volume
of the set of non-units. -/
theorem modulus_le_volume_nonunits {A : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A]
    (c : Aˣ) (hc : c.val ∈ P.integers) (hc_inv : c⁻¹.val ∉ P.integers) :
    P.modulus c ≤ volume (P.integers \ P.intUnits) := by
  refine modulus_le_volume fun a ha ↦ ⟨mul_mem hc ha, ?_⟩
  rintro ⟨-, v, hv : v⁻¹.val ∈ integers, hcv : (v : A) = c * a⟩
  have h_inv : c⁻¹.val = a * v⁻¹.val := by grind [Units.mul_inv]
  have h_mem : a * v⁻¹.val ∈ integers := mul_mem ha hv
  exact hc_inv (by rwa [h_inv])

/-- Let `F` be a large lattice datum with level unit `g` and congruence subgroup
K(g) = `F.congruenceSubgroup`, let `Z` be an integral group that contains K(g), and let `e` bound
the modulus of every integral unit of `A` whose inverse is not integral. If the point `x` of the
group `T.G` is not in K(g), every point `y` that is active at `x` has an index `a` with
`e⁻¹ ≤ F.depth a y x`. -/
theorem hasDeepVector_of_notMem_congruenceSubgroup {F : PlaceData ι T (m + 1)} {x : T.G}
    (Z : F.IntermediateGroup) [h : IsLargeLatticeData F] {e : ℝ≥0∞}
    (he : ∀ c : Aˣ, c.val ∈ integers → c⁻¹.val ∉ integers → P.modulus c ≤ e)
    (hx : x ∉ F.congruenceSubgroup) :
    F.HasDeepVector 0 1 1 Z.besselVector x e⁻¹ := by
  -- Otherwise each set `F.stableProducts a y x` contains a unit of `R`, and `(x - 1) / g` is
  -- integral.
  refine hasDeepVector_inv_iff.2 fun y ⟨hy, h_near_p, h_near_q⟩ ↦ ?_
  by_contra! h_big : ∀ a : Fin 𝔰.ϱ, 0 ≤ a.val → e < volume (F.stableProducts a y x)
  let Γ : Gauge F := h.gauge 1 (one_mem integers) (star_one A)
  have h_head : Γ.IsHead 0 1 := by simp [IsHead, Γ]
  have h_unit (a : Fin 𝔰.ϱ) (ha : 0 ≤ a.val) :
      ∃ c : Aˣ, ↑c ∈ F.stableProducts a y x ∧ ↑c⁻¹ ∈ Γ.ofSize 1 := by
    obtain ⟨c, hc, hc_mem, hc_vol⟩ : ∃ c : Aˣ, c.val ∈ integers ∧ c.val ∈ F.stableProducts a y x ∧
        volume (F.stableProducts a y x) ≤ P.modulus c :=
      exists_unit_mem_stableProducts Z a x hy
    have hc_inv : c⁻¹.val ∈ integers := by
      by_contra h_not
      exact (h_big a ha).not_ge (hc_vol.trans (he c hc h_not))
    exact ⟨c, hc_mem, by simpa [Γ] using hc_inv⟩
  have h_size : Γ.HasMatrixSize (99 * 𝔰.n) (F.levelUnit⁻¹.val • (x.val.val - 1)) :=
    Γ.hasMatrixSize_sub_one_of_stableProducts Γ bot_le h_head h_head (hM := by simp) (hS := by simp)
      (exists_mem_boxSet_hasMatrixSize_of_inner_ne_zero Z hy) h_near_p h_near_q h_unit
  -- In the gauge of scale `1` every size means integral.
  have h_int : IsIntMatrix integers (F.levelUnit⁻¹.val • (x.val.val - 1)) := fun i k ↦ by
    have h_entry : (F.levelUnit⁻¹.val • (x.val.val - 1)) i k ∈ Γ.ofSize (99 * 𝔰.n) := h_size i k
    simpa [Γ] using h_entry
  obtain ⟨h_gram : IsUnimodular integers T.splitGram, -, hg : F.levelUnit.val ∈ integers, -⟩ :=
    h.integral_data
  exact hx (h_gram.mem_unitaryLevel hg h_int)

/-- Let `F` be a large lattice datum with congruence group K(g) = `F.congruenceSubgroup`, and let
`Z` be a group with K(g) ≤ `Z` ≤ K. Let `e` bound `P.modulus c` for every unit `c` of `A` in
`integers` whose inverse is not in `integers`, and let `r + 10⁸ 𝔰.n⁴ ≤ 𝔰.k`. Then the majorant
`F.formMajorant 0 1 1 Z.besselVector` has integral at most
`min 1 e ^ r · Z.massRatio · 2 ^ (10⁹ 𝔰.n⁴)` outside K(g). -/
theorem setLIntegral_compl_congruenceSubgroup_le_pow {F : PlaceData ι T (m + 1)}
    (Z : F.IntermediateGroup) [h : IsLargeLatticeData F] {e : ℝ≥0∞}
    (he : ∀ c : Aˣ, c.val ∈ integers → c⁻¹.val ∉ integers → P.modulus c ≤ e) {r : ℕ}
    (hr : r + 10 ^ 8 * 𝔰.n ^ 4 ≤ 𝔰.k) :
    ∫⁻ x : T.G in (F.congruenceSubgroup : Set T.G)ᶜ,
        F.formMajorant 0 1 1 Z.besselVector x ∂F.groupMeasure ≤
      min 1 e ^ r * Z.massRatio * 2 ^ (10 ^ 9 * 𝔰.n ^ 4) := by
  -- Sum over the shells in the gauge of scale `1`, where `Γ.loss = 2`. Outside K(g) there is a
  -- vector of depth at least `e⁻¹`, which gives the gain `e ^ F.volumeExponent`.
  let Γ : Gauge F := h.gauge 1 (one_mem integers) (star_one A)
  let f : T.G → ℝ≥0∞ :=
    (F.congruenceSubgroup : Set T.G)ᶜ.indicator (F.formMajorant 0 1 1 Z.besselVector)
  have h_head : Γ.IsHead 0 1 := by simp [IsHead, Γ]
  have h_gain (_ : e < 1) (x : T.G) (hx : x ∈ F.positions) :
      f x ^ 2 ≤ (e ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct 0 1 1 Z.besselVector x := by
    by_cases hx_level : x ∈ F.congruenceSubgroup
    · simp [f, hx_level]
    · simpa [f, hx_level] using Γ.formMajorant_zero_sq_le_of_hasDeepVector (isCut_besselVector Z)
        hx (hasDeepVector_of_notMem_congruenceSubgroup Z he hx_level)
  have h_major {x : T.G} : f x ≤ F.formMajorant 0 1 1 Z.besselVector x :=
    Set.indicator_le_self _ _ x
  have h_shell : ∫⁻ x : T.G, f x ∂F.groupMeasure ≤
      min 1 e ^ r * Z.massRatio * 2 ^ (10 ^ 9 * 𝔰.n ^ 4) := by
    simpa [headDensity, Γ] using lintegral_shells_le Z r bot_le hr (Γ := Γ) rfl
      h_head h_head (fun h_ne ↦ absurd rfl h_ne) h_major h_gain
  have h_meas : MeasurableSet (F.congruenceSubgroup : Set T.G) := measurableSet_unitaryLevel
  rwa [lintegral_indicator h_meas.compl] at h_shell

/-- **Outside the congruence subgroup.** Let `F` be a large lattice datum with congruence group
K(g) = `F.congruenceSubgroup`, and let `Z` be a group with K(g) ≤ Z ≤ K, where K is the integral
unitary group. Let `Q ≥ 2` be such that every unit `c` of `A` with `c ∈ R` and `c⁻¹ ∉ R` has modulus
at most `Q⁻¹`. If `t + 2 · 10⁹ n⁴ ≤ k`, where n = `𝔰.n` and k = `𝔰.k`, then the integral of
`F.formMajorant 0 1 1 Z.besselVector` over the complement of K(g), against `F.groupMeasure`, is at
most `Q⁻¹ ^ t * Z.massRatio`. -/
theorem setLIntegral_compl_congruenceSubgroup_le {F : PlaceData ι T (m + 1)}
    (Z : F.IntermediateGroup) [h : IsLargeLatticeData F] {Q : ℝ≥0∞} {t : ℕ} (hQ_two : 2 ≤ Q)
    (hQ : ∀ c : Aˣ, c.val ∈ integers → c⁻¹.val ∉ integers → P.modulus c ≤ Q⁻¹)
    (ht : t + 2 * 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.k) :
    ∫⁻ x : T.G in (F.congruenceSubgroup : Set T.G)ᶜ,
        F.formMajorant 0 1 1 Z.besselVector x ∂F.groupMeasure ≤
      Q⁻¹ ^ t * Z.massRatio := by
  let N : ℕ := 10 ^ 9 * 𝔰.n ^ 4
  have h_shell : ∫⁻ x : T.G in (F.congruenceSubgroup : Set T.G)ᶜ,
      F.formMajorant 0 1 1 Z.besselVector x ∂F.groupMeasure ≤
        min 1 Q⁻¹ ^ (t + N) * Z.massRatio * 2 ^ N :=
    setLIntegral_compl_congruenceSubgroup_le_pow Z hQ (by lia)
  -- The spare powers of `Q⁻¹ ≤ 2⁻¹` absorb `2 ^ N`.
  have h_two : Q⁻¹ * 2 ≤ 1 := by grw [hQ_two, ENNReal.inv_mul_le_one]
  calc _ ≤ Q⁻¹ ^ (t + N) * Z.massRatio * 2 ^ N := by grw [h_shell, min_le_right]
    _ = Q⁻¹ ^ t * Z.massRatio * (Q⁻¹ * 2) ^ N := by
      rw [pow_add, mul_pow, mul_right_comm (Q⁻¹ ^ t), mul_assoc]
    _ ≤ Q⁻¹ ^ t * Z.massRatio := by grw [h_two, one_pow, mul_one]

/-- Let `F` be a large lattice datum with congruence group K(g) = `F.congruenceSubgroup`, where
`g = F.levelUnit`, and let `Z` be a group with K(g) ≤ `Z` ≤ K. Let `vol` be the Haar measure
`F.groupMeasure`. Let `Q ≥ 2` be such that `Q⁻¹` bounds `P.modulus c` for every unit `c` of `A` in
`integers` whose inverse is not in `integers`, and let `t + 2 · 10⁹ 𝔰.n⁴ ≤ 𝔰.k`. Then
`F.massIntegral Z = ∫_G |∫_Z extendedBesselChar g (y x y⁻¹) dy|² dx` is at most `vol(Z) vol(K(g))`
times the sum of `vol(Z)`, which comes from K(g), and the error `Q⁻¹ ^ t`, which comes from its
complement. The function `extendedBesselChar g` is `New.Floors.IntegralPlace.extendedBesselChar
F.levelUnit`. -/
theorem massIntegral_le_main_add_error {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    [h : IsLargeLatticeData F] {Q : ℝ≥0∞} {t : ℕ} (hQ_two : 2 ≤ Q)
    (hQ : ∀ c : Aˣ, c.val ∈ integers → c⁻¹.val ∉ integers → P.modulus c ≤ Q⁻¹)
    (ht : t + 2 * 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.k) :
    F.massIntegral Z ≤
      F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup * (F.groupMeasure Z + Q⁻¹ ^ t) := by
  have h_ker : F.IsPairingKernel 0 (frameCorrelation Z.besselVector 1) 1 :=
    h.gauge.isPairingKernel_frameCorrelation_one (isCut_besselVector Z) 0
  have h_meas : MeasurableSet (F.congruenceSubgroup : Set T.G) := measurableSet_unitaryLevel
  have h_integrand (x : T.G) :
      ‖∫ y : T.G in Z, extendedBesselChar F.levelUnit (y * x * y⁻¹) ∂F.groupMeasure‖ₑ ^ 2 ≤
        F.formMajorant 0 1 1 Z.besselVector x * F.unipotentMass ^ 2 := by
    rw [formMajorant_zero_eq]
    grw [(enorm_integral_extendedBesselChar_eq_enorm_mul Z).le, h_ker.enorm_partialCorrelation_le,
      mul_pow]
  have h_cancel : Z.massRatio * F.unipotentMass ^ 2 =
      F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup := by
    rw [IntermediateGroup.massRatio, ENNReal.div_mul_cancel (by simp) (by simp)]
  calc F.massIntegral Z
      ≤ F.groupMeasure Z ^ 2 * F.groupMeasure F.congruenceSubgroup +
          (∫⁻ x : T.G in (F.congruenceSubgroup : Set T.G)ᶜ,
            F.formMajorant 0 1 1 Z.besselVector x ∂F.groupMeasure) * F.unipotentMass ^ 2 := by
        grw [massIntegral, ← lintegral_add_compl _ h_meas,
          setLIntegral_congruenceSubgroup_integral_sq,
          setLIntegral_mono' h_meas.compl fun x _ ↦ h_integrand x]
        rw [lintegral_mul_const' _ _ (by simp)]
    _ ≤ F.groupMeasure Z ^ 2 * F.groupMeasure F.congruenceSubgroup +
          Q⁻¹ ^ t * (Z.massRatio * F.unipotentMass ^ 2) := by
        grw [setLIntegral_compl_congruenceSubgroup_le Z hQ_two hQ ht, mul_assoc]
    _ = F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup * (F.groupMeasure Z + Q⁻¹ ^ t) := by
        rw [h_cancel]
        ring

end IntegralPlace.IsLargeLatticeData

end New.Floors

end
