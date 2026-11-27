import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure

/-!
# The place ℂ: polar coordinates, Cartan decomposition and the measure of the hyperboloid

The archimedean instance of the local theory: the place `ℂ` and the top floor `ϱ` of the group
`New.Shape.G₁`, the unitary group of `ϱ` hyperbolic planes plus `V_ϱ = X₀ ⊕ ℂ z`, where `X₀ = ℂ^κ`
is standard and `h(z, z) = -1`. `New.RealPlace.embedH` embeds `U(X₀)` (written `U 1`) in it.
`floorGroup l` is the subgroup that fixes the basis vectors of the floors below `l`.

* `New.Floors.complexPlace`, `New.Floors.complexBasis`: `ℂ` is a place (`New.Floors.Place`); a
  hyperbolic basis of `V_ϱ`.
* `New.Floors.lintegral_eq_polar`: polar coordinates on `ℂ^κ` by the unitary group.
* `New.Floors.cellChart`, `New.Floors.cellDensity`, `New.Floors.cellLaw`: for each floor a chart
  `ℂ → G₁` (a boost at the top for `c ≠ 0`, a Weyl element otherwise), its density, and the law of
  its inverse.
* `New.Floors.cartan_decomposition`: the Cartan decomposition `U(X₀) · boost · U(X₀)` of an element
  of the top floor group whose corner entry `h(z, σ z)` has absolute value above 1.
* `New.Floors.map_orbitPoint_cellLaw_top`: polar coordinates for the measure of the hyperboloid
  `h(v, v) = -1`.

Notions from other files:
* `New.Shape.middleGram`: for a scalar N, the diagonal matrix on κ plus one point, with entries 1 on
  κ and −N at the extra point.
* `New.Floors.FloorGroups.orbitPoint`: for b ≤ ϱ and an isometry g, the vector g⁻¹f_b, where
  f = (e_0, …, e_{ϱ-1}, z) is the frame; `𝔰.top` is the position ϱ of z.
* `New.Floors.HyperbolicBasis.floorQuadricMeasure`: the measure on a quadric in V_b, a level set of
  v ↦ h(v, v) (by default h(f_b, f_b)): the image of `New.Floors.Place.quadricMeasure` under the
  basis `F.floorBasis b`.
* `New.realFrameGram`: for y in G₁, the (ϱ+1)×(ϱ+1) complex matrix Z(y) of products h(f_j, y f_l) of
  the frame with its translate.

## Relation to the literature

Known results: polar coordinates on ℂ^κ, the Cartan decomposition of a unitary group of rank one,
and the invariant measure of the hyperboloid h(v, v) = −1, here written in the coordinates of the
top floor. Source: Knapp, Lie Groups Beyond an Introduction; Helgason, Groups and Geometric
Analysis, Ch. I §5.
-/

noncomputable section

namespace New.Floors

open MeasureTheory Measure Matrix Real Fintype Set Complex ComplexConjugate RealPlace Sum
  FloorGroups GaussianFourier ComplexOrder Function

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The place `ℂ`: `τ = 1/2`, `δ = i/2`, `ν` the image of Lebesgue measure under `r ↦ r i`,
modulus `‖x‖ ^ 2`, character `x ↦ exp (x - x̄)` and constant `c = π ^ 2`. -/
@[simps]
instance complexPlace : Place ℂ := by
  -- The kernel is the Gaussian `exp (-‖x‖²)`, and `gauss` says that its integral is `π`.
  have gauss := HasGaussianIntegral.integral_exp_eq (V := ℂ) one_pos
  have integrable := Integrable.of_integral_ne_zero (gauss.trans_ne (by simp))
  -- its Fourier transform, and the mass of `π exp (-‖x‖²)` as a Lebesgue integral
  have fourier (z : ℂ) := integral_cexp_neg_mul_sq_norm_add (b := 1) one_pos (2 * I) (z / I)
  have mass := ofReal_integral_norm_eq_lintegral_enorm (integrable.const_mul π)
  refine .mk (toTraceOne := ⟨2⁻¹, by norm_num⟩) (skewUnit := .mk0 (I / 2) (by norm_num))
    (skewMeasure := volume.map fun r : ℝ ↦ ⟨r * I, by simp [skewAdjoint.mem_iff]⟩)
    (modulus := ⟨⟨(‖·‖ₑ ^ 2), by norm_num⟩, by norm_num [mul_pow]⟩)
    (ψ := ⟨wave, by norm_num [wave], by simp [← Complex.exp_add, sub_add_sub_comm, wave]⟩)
    (kernelBound := .ofReal (π ^ 2))
    (haar := ?haar) (continuous_psi := show Continuous wave by fun_prop [wave])
    (measurable_modulus := show Measurable fun x : ℂ ↦ ‖x‖ₑ ^ 2 by fun_prop)
    (star_skewUnit := by norm_num [neg_div]) (measurePreserving_split := ⟨by fun_prop, ?split⟩)
    (modulus_star_and_neg := by norm_num)
    (map_mulVec_volume := by norm_num +contextual
                               [Fock.map_mulVec_addHaar_eq_smul, ENNReal.inv_pow])
    (ae_isUnit := by simpa using ae_ne volume 0)
    (exists_locallyIntegrable_bound := ⟨(‖·‖⁻¹), ?int, by norm_num [ENNReal.inv_pow]⟩)
    (norm_psi := by norm_num)
    (exists_plancherel_kernel :=
      ⟨_, by fun_prop, integrable, fun _ ↦ (exp_pos _).le, by norm_num, ?ker⟩)
  case haar =>
    -- `r ↦ r * I` is a bicontinuous additive isomorphism onto the skew elements
    refine AddEquiv.isAddHaarMeasure_map _ ⟨⟨_, (·.1.im), by
      norm_num [LeftInverse], ?_⟩, by norm_num [add_mul]⟩
      ?_ ?_
    · simp_all [RightInverse, Complex.ext_iff, self_eq_neg, LeftInverse, skewAdjoint.mem_iff]
    all_goals
      norm_num
      fun_prop
  case split =>
    -- with `τ = 1 / 2` and `δ = I / 2` the splitting sends `(r I, s I)` to `r + s I`
    rw [map_prod_map, Measure.map_map, ← volume_preserving_equiv_real_prod.symm.2] <;> try fun_prop
    congr 1
    simp [Complex.ext_iff, funext_iff]
  -- the bound `‖x‖⁻¹` is locally integrable, ℂ having real dimension 2
  case int =>
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ (by fun_prop) <;>
      norm_num [rpow_neg_one]
  case ker =>
    -- by `fourier` the inner integral is `π exp (-‖z‖²)`, whose integral is `π ^ 2`
    simp_all [← Complex.exp_add, ↓sub_conj, mul_right_comm _ _ I, ← sub_eq_add_neg, sq,
      ← ofReal_norm, abs_of_pos pi_pos, neg_add_eq_sub, integral_const_mul, wave, norm_exp]
    grind

/-- For the fixed index k₀ of κ (`𝔰.k₀`), the basis of V_ϱ = X₀ ⊕ ℂz made of the hyperbolic pair
(1+i)/2·(x_{k₀} ± z) and the orthonormal vectors x_i, i ≠ k₀. -/
def complexBasis (𝔰 : Shape) : HyperbolicBasis {i // i ≠ 𝔰.k₀} (𝔰.middleGram (1 : ℂ)) 0 :=
  { basisMatrix :=
      of fun i ↦
        (fun a ↦
          (1 + I) / 2 *
            (Pi.single 𝔰.k₀ 1 ⊕ᵥ ![1, -1] a) i) ⊕ᵥ (0 ⊕ᵥ (inclMatrix ℂ (inl ·.1) i ⊕ᵥ 0))
    gram_eq := by
      -- entry by entry, the products of the columns are those of a plane and an orthonormal family
      simp [← ext_iff, middleGram, map_ofNat, inclMatrix, Matrix.mul_apply, Pi.single_apply,
        Matrix.one_apply]
      grind [I_sq]
    card_eq := by
      simp
      grind [card_pos_iff.2 ⟨𝔰.k₀⟩]
    modulus_det := by simp [middleGram] }

/-- Polar coordinates on `ℂ^κ`, with `m = |κ|`: for an index `k` in `κ` and measurable
`g : ℂ^κ → [0, ∞]`, `∫ g(ω) dω = ∫₀^∞ π^m r^(m-1) / (m-1)! ∫_{U(m)} g(h (√r x)) dh dr`, where `x` is
the basis vector of index `k`, `r` is the squared norm and `dh` is the Haar probability measure. -/
lemma lintegral_eq_polar (k : κ) {g : (κ → ℂ) → ENNReal} (hg : Measurable g) :
    ∫⁻ ω : κ → ℂ, g ω =
      ∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (sphereDensity (card κ) r / 2) *
          ∫⁻ h : U 1, g (h.val.val *ᵥ √r • Pi.single k 1) := by
  -- Average `g` over the unitary group, which preserves the volume; the average depends only on
  -- `r = |ω|²`, whose law is given by `measurePreserving_normSq_sphereDensity`.
  have : Nonempty κ := ⟨k⟩
  have rot (h : U 1) : ∫⁻ ω : κ → ℂ, g (h.val.val *ᵥ ω) = ∫⁻ ω : κ → ℂ, g ω :=
    (complexPlace.measurePreserving_mulVec _ (U.det (by simp) h).2.1).lintegral_comp hg
  calc ∫⁻ ω, g ω = ∫⁻ h : U 1, ∫⁻ ω, g (h.val.val *ᵥ ω) := by simp [rot]
    _ = ∫⁻ ω, ∫⁻ h : U 1, g (h.1.1 *ᵥ ω) := lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ ω : κ → ℂ, ∫⁻ h : U 1, g (h.1.1 *ᵥ √‖star ω ⬝ᵥ ω‖ • Pi.single k 1) := by
      -- a unitary `u` takes `ω` to the multiple of the basis vector with the same norm
      refine lintegral_congr fun ω ↦ ?_
      obtain ⟨u, hu⟩ := exists_unitary_mulVec_eq ω (v := √‖star ω ⬝ᵥ ω‖ • Pi.single k 1)
        (by simp (disch :=
          positivity) [← ofReal_mul, norm_of_nonneg', dotProduct, conj_mul', Pi.single_apply])
      rw [← lintegral_mul_right_eq_self _ u]
      simp [← mulVec_mulVec, hu]
    _ = _ := by
      -- pass from `ω` to `r = |ω|²` (`erw`: the integrand is a product and a composite up to defeq)
      erw [← lintegral_withDensity_eq_lintegral_mul,
          ← measurePreserving_normSq_sphereDensity.lintegral_comp] <;>
        fun_prop

/-- The boost in the plane of k₀ and z with parameter a, for 1 ≤ |a|. With s = √(|a|² - 1) it acts
on that plane by the matrix with rows (conj a, s) and (-s, -a), and it fixes the other basis
vectors. -/
def cellBoost (𝔰 : Shape) (a : ℂ) (ha : 1 ≤ ‖a‖) : 𝔰.G₁ :=
  let s : 𝔰.κ → ℂ := √(‖a‖ ^ 2 - 1) • Pi.single 𝔰.k₀ 1
  let boost : Matrix (𝔰.κ ⊕ Unit) (𝔰.κ ⊕ Unit) ℂ :=
    fromBlocks (diagonal (update 1 𝔰.k₀ (conj a))) (replicateCol Unit s) (-replicateRow Unit s)
      (of fun _ _ ↦ -a)
  U.of IsHermitianUnit.isUnit (fromBlocks 1 0 0 (fromBlocks boost 0 0 1)) <| by
    simp [boost, s, splitGram, middleGram, ← ext_iff, diagonal_apply, update_apply, apply_ite conj,
      ← ofReal_mul, RCLike.star_def, ha, fromBlocks_conjTranspose, fromBlocks_multiply,
      Matrix.one_apply, Matrix.mul_apply, Pi.single_apply, conj_mul']
    grind [conj_mul']

/-- The boost depends continuously on its parameter. -/
@[fun_prop]
lemma continuous_cellBoost (𝔰 : Shape) {X : Type*} [TopologicalSpace X] {a : X → ℂ}
    (ha : Continuous a) (ha_norm : ∀ x : X, 1 ≤ ‖a x‖) :
    Continuous fun x : X ↦ cellBoost 𝔰 (a x) (ha_norm x) := by
  refine continuous_U_iff_matrix.2 ?_
  simp only [cellBoost, U.of]
  fun_prop

/-- For a ≠ 0 the point a / min(1, |a|) lies outside the open unit disc. -/
lemma one_le_norm_div_min {a : ℂ} (ha : a ≠ 0) : 1 ≤ ‖a / (min 1 ‖a‖ : ℝ)‖ := by
  have h_pos : 0 < min 1 ‖a‖ := lt_min one_pos (norm_pos_iff.2 ha)
  simp [abs_of_pos h_pos, one_le_div h_pos]

/-- The chart of the big cell of floor l. On the top floor and for c ≠ 0 it is the boost at
c / min(1, |c|), which is c if 1 ≤ |c| and c / |c| otherwise. In all other cases it is
`floorWeyl l c`. -/
def cellChart (𝔰 : Shape) (l : ℕ) (c : ℂ) : 𝔰.G₁ :=
  if h : l = 𝔰.ϱ ∧ c ≠ 0 then cellBoost 𝔰 (c / (min 1 ‖c‖ : ℝ)) (one_le_norm_div_min h.2)
  else floorWeyl l c

/-- The density of floor l at c: |c|^{2(k−1)+4(ϱ−l)} for l < ϱ; otherwise
2π^k((|c|²−1)⁺)^{k−1}/(k−1)!; k = |κ|. For l ≥ ϱ and |c| ≤ 1 this is 0 if and only if k > 1. -/
def cellDensity (𝔰 : Shape) (l : ℕ) (c : ℂ) : ENNReal :=
  if l < 𝔰.ϱ then
    ‖c‖ₑ ^ (2 * (𝔰.k - 1) + 4 * (𝔰.ϱ - l))
  else
    ENNReal.ofReal (sphereDensity 𝔰.k (‖c‖ ^ 2 - 1)⁺)

variable {𝔰 : Shape}

/-- The measure on G₁ that is the image of the density `New.Floors.cellDensity` of floor l times dc
on ℂ under c ↦ w_l(c)⁻¹ (`New.Floors.cellChart`). -/
abbrev cellLaw (l : ℕ) : Measure 𝔰.G₁ :=
  (volume.withDensity (cellDensity 𝔰 l)).map fun c ↦ (cellChart 𝔰 l c)⁻¹

/-- On the top floor and for 1 ≤ |c|, the chart is the boost at c. -/
lemma cellChart_top_of_one_le {c : ℂ} (hc : 1 ≤ ‖c‖) :
    cellChart 𝔰 𝔰.ϱ c = cellBoost 𝔰 c hc := by
  simp [cellChart, norm_pos_iff.1 (one_pos.trans_le hc), min_eq_left hc]

/-- For 1 ≤ |c| the boost at c fixes the basis vectors of the floors below the top, that is, it
lies in `floorGroup ϱ`. -/
lemma cellBoost_mem_floorGroup {c : ℂ} (hc : 1 ≤ ‖c‖) : cellBoost 𝔰 c hc ∈ floorGroup 𝔰.ϱ := by
  simp +contextual [cellBoost, mem_floorGroup, Matrix.one_apply]

/-- The chart of floor l takes its values in the group of floor l, which fixes the basis vectors
of the floors below l. -/
lemma cellChart_mem_floorGroup {l : ℕ} {c : ℂ} : cellChart 𝔰 l c ∈ floorGroup l := by
  unfold cellChart
  split_ifs with h
  · obtain ⟨rfl, hc⟩ := h
    exact cellBoost_mem_floorGroup (one_le_norm_div_min hc)
  · exact floorWeyl_mem_floorGroup

/-- The embedding of U(X₀) in G₁ takes its values in the group of the top floor, which fixes the
basis vectors of all floors below ϱ. -/
lemma embedH_mem_floorGroup (k : U 1) : embedH (𝔰 := 𝔰) k ∈ floorGroup 𝔰.ϱ := by
  simp [mem_floorGroup, val_toBesselH_apply_coe, Matrix.one_apply]

/-- The chart of floor l is a measurable function of its parameter. -/
@[fun_prop]
lemma measurable_cellChart {l : ℕ} : Measurable (cellChart 𝔰 l) := by
  refine measurable_unitary_of_coe ?_
  simp -iota [cellChart, cellBoost, apply_dite]
  apply Measurable.ite <;> measurability

/-- The density of floor l is a measurable function on ℂ. -/
@[fun_prop]
lemma measurable_cellDensity {l : ℕ} : Measurable (cellDensity 𝔰 l) := by
  delta cellDensity
  measurability

/-- For `1 < ‖c‖` the boost `w = cellChart 𝔰 ϱ c` has `h(z, w z) = c`: this is the entry at
(`top`, `top`) of the matrix `realFrameGram` of products of the frame with its translate by `w`,
`top` being the position of `z`. -/
lemma realFrameGram_cellChart {c : ℂ} (hc : 1 < ‖c‖) :
    realFrameGram (cellChart 𝔰 𝔰.ϱ c) 𝔰.top 𝔰.top = c := by
  simp [cellChart_top_of_one_le hc.le, cellBoost, U.of, middleGram, splitGram, frameGram,
    Matrix.mul_apply]

/-! ### The top floor: Cartan decomposition and the hyperboloid -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Cartan decomposition of `U(V_ϱ)`, the isometry group of the form `middleGram 1` (diagonal: 1 on
X₀, indexed by κ, and −1 at z). Let `σ` fix the basis vectors of the floors below the top
(`σ ∈ floorGroup ϱ`) and let `c = h(z, σ z)`, the last diagonal entry of `realFrameGram σ`, have
`|c| > 1`. Then `σ = k w_ϱ(c) k'` for some `k`, `k'` in `U(X₀)`, embedded by `embedH` (identity off
X₀), where `w_ϱ(c)` is the boost `cellChart 𝔰 ϱ c`. -/
lemma cartan_decomposition {c : ℂ} {σ : (𝔰.middleGram (1 : ℂ)).G} (hσ : σ ∈ floorGroup 𝔰.ϱ)
    (hZ : realFrameGram σ 𝔰.top 𝔰.top = c) (hc : 1 < ‖c‖) :
    ∃ k k' : U 1, σ = embedH k * cellChart 𝔰 𝔰.ϱ c * embedH k' := by
  -- The column of `σ` at `z` has `h(·,·) = -1` and entry `-c` at `z`, so its part `v` in `X₀` has
  -- `‖v‖² = ‖c‖² - 1`.
  let v (i : 𝔰.κ) : ℂ := σ.1.1 (inr (inl (inl i))) 𝔰.z
  have h_entry : σ.1.1 𝔰.z 𝔰.z = -c := by
    simp [apply_eq_one_apply_of_mem_floorGroup hσ, ← hZ, middleGram, frameGram, splitGram,
      Matrix.mul_apply]
  have h_gram : (σ.1.1ᴴ * (𝔰.middleGram (1 : ℂ)).splitGram * σ.1.1) 𝔰.z 𝔰.z =
      (𝔰.middleGram (1 : ℂ)).splitGram 𝔰.z 𝔰.z := congr_fun₂ σ.2 𝔰.z 𝔰.z
  have h_col : ∑ i : 𝔰.κ, (‖v i‖ : ℂ) ^ 2 = ‖c‖ ^ 2 - 1 := by
    simpa [apply_eq_one_apply_of_mem_floorGroup hσ, h_entry, add_neg_eq_iff_eq_add, middleGram,
      splitGram,
      Matrix.mul_apply, Matrix.one_apply, conj_mul', neg_add_eq_sub] using h_gram
  obtain ⟨u, hu⟩ : ∃ u : U 1, u.val.val *ᵥ (√(‖c‖ ^ 2 - 1) • Pi.single 𝔰.k₀ 1) = v :=
    exists_unitary_mulVec_eq _
      (by simp [← ofReal_mul, hc, h_col, dotProduct, Pi.single_apply, le_of_lt, conj_mul'])
  -- `embedH u * cellChart 𝔰 ϱ c` and `σ` take `z` to the same vector
  have h_eq : orbitPoint 𝔰.top (embedH u * cellChart 𝔰 𝔰.ϱ c)⁻¹ = orbitPoint 𝔰.top σ⁻¹ := by
    simpa [cellChart_top_of_one_le hc.le, cellBoost, h_entry,
      apply_eq_one_apply_of_mem_floorGroup hσ, orbitPoint, val_toBesselH_apply_coe,
        fromBlocks_multiply, funext_iff,
      Matrix.mul_apply, Pi.single_apply, mulVec_smul] using hu
  -- both lie in `floorGroup ϱ` and their quotient fixes `z`, so it comes from `U(X₀)`
  have h_mem := inv_mul_mem_of_orbitPoint_eq
    (mul_mem (embedH_mem_floorGroup u) cellChart_mem_floorGroup) hσ h_eq
  obtain ⟨k', hk' : (embedH u * cellChart 𝔰 𝔰.ϱ c)⁻¹ * σ = embedH k'⟩ :=
    exists_eq_toBesselH (partialUnitriangularGroup_inf_floorGroup_last.le h_mem) isUnit_one
  exact ⟨u, k', eq_mul_of_inv_mul_eq hk'⟩

/-- The point √(Γ + |c|²) h x + c z of X₀ ⊕ ℂz, in the coordinates `BesselIndex` of the whole space
(`definiteCols` puts X₀ into them), for a real level Γ and a pair (c, h), x being the basis vector
at k₀. For Γ + |c|² ≥ 0 it lies on the hyperboloid h(v, v) = Γ. -/
abbrev hyperboloidPoint (Γ : ℝ) (p : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) : 𝔰.BesselIndex → ℂ :=
  update (𝔰.definiteCols *ᵥ (√(Γ + ‖p.1‖ ^ 2) * p.2.val.val · 𝔰.k₀)) 𝔰.z p.1

/-- The image of S((Γ + |c|²)⁺) dc dh under `hyperboloidPoint Γ`, where S is `sphereDensity k`,
S(r) = 2π^k r^(k−1)/(k−1)! with k = |κ|, and dh is the Haar probability measure of U(X₀). For k > 1
it is a measure on the hyperboloid h(v, v) = Γ of V_ϱ, written in polar coordinates. -/
abbrev hyperboloidMeasure (Γ : ℝ) : Measure (𝔰.BesselIndex → ℂ) :=
  map (hyperboloidPoint Γ)
    (volume.withDensity fun p : ℂ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦
      .ofReal (sphereDensity 𝔰.k (Γ + ‖p.1‖ ^ 2)⁺))

/-- An integral against `hyperboloidMeasure Γ` is the iterated integral over c and h of the
integrand at `hyperboloidPoint Γ (c, h)`, with the density S((Γ + |c|²)⁺). -/
lemma lintegral_hyperboloidMeasure (Γ : ℝ) {g : (𝔰.BesselIndex → ℂ) → ENNReal} (hg : Measurable g) :
    ∫⁻ v : 𝔰.BesselIndex → ℂ, g v ∂hyperboloidMeasure Γ =
      ∫⁻ c : ℂ, .ofReal (sphereDensity 𝔰.k (Γ + ‖c‖ ^ 2)⁺) *
        ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), g (hyperboloidPoint Γ (c, h)) := by
  simp (disch := with_unfolding_all fun_prop) only [lintegral_map, volume_eq_prod, lintegral_prod,
    lintegral_const_mul, lintegral_withDensity_eq_lintegral_mul, Pi.mul_apply]

/-- For Γ + |c|² ≥ 0 the point `hyperboloidPoint Γ (c, u)` has h(v, v) = Γ. -/
lemma star_dotProduct_hyperboloidPoint {Γ : ℝ} {c : ℂ} (hΓ : 0 ≤ Γ + ‖c‖ ^ 2)
    (u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
    star (hyperboloidPoint Γ (c, u)) ⬝ᵥ
      (𝔰.middleGram (1 : ℂ)).splitGram *ᵥ hyperboloidPoint Γ (c, u) = Γ := by
  -- the column of `u` at `k₀` has norm one
  have h_col : ∑ i, (‖u.val.val i 𝔰.k₀‖ : ℂ) ^ 2 = 1 := by
    simpa [Matrix.mul_apply, conj_mul'] using congr_fun₂ u.2 𝔰.k₀ 𝔰.k₀
  -- the part in X₀ has squared norm `Γ + ‖c‖²` and the entry at z contributes `-‖c‖²`
  suffices ((√(Γ + ‖c‖ ^ 2) ^ 2 : ℝ) : ℂ) + -(‖c‖ : ℂ) ^ 2 = Γ by
    simpa [apply_ite conj, -map_mul, ← Finset.sum_mul, ← Finset.mul_sum, h_col,
      abs_of_nonneg (sqrt_nonneg _), dotProduct, mulVec, splitGram, middleGram,
      Matrix.one_apply, Pi.single_apply, conj_mul', mul_pow, inclMatrix] using this
  simp [sq_sqrt hΓ]

/-- Polar coordinates on the slice of X₀ ⊕ ℂz with coordinate c at z, for |κ| > 1: with r the
squared norm of the part in X₀ and r = 2t + |c|², the integral over x ∈ X₀ of f(h(v, v), v) is,
where v is (x, c) in the indices `MiddleIndex` of X₀ ⊕ ℂz, put by `inclMatrix` into the coordinates
`BesselIndex` of the whole space, ∫ S((2t + |c|²)⁺) ∫ f(2t, `hyperboloidPoint (2t) (c, u)`) du dt, S
being `sphereDensity k`. -/
lemma lintegral_slice_eq_hyperboloid (hk : 1 < 𝔰.k) (c : ℂ)
    {f : ℂ × (𝔰.BesselIndex → ℂ) → ENNReal} (hf : Measurable f) :
    (∫⁻ x : 𝔰.κ → ℂ,
        let v : 𝔰.BesselIndex → ℂ :=
          inclMatrix ℂ (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ (x ⊕ᵥ fun _ : Unit ↦ c)
        f (star v ⬝ᵥ (𝔰.middleGram (1 : ℂ)).splitGram *ᵥ v, v)) =
      ∫⁻ t : ℝ, .ofReal (sphereDensity 𝔰.k (2 * t + ‖c‖ ^ 2)⁺) *
        ∫⁻ u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
          f ((2 * t : ℝ), hyperboloidPoint (2 * t) (c, u)) := by
  let F (r : ℝ) : ENNReal :=
    ∫⁻ u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
      f ((r - ‖c‖ ^ 2 : ℝ), hyperboloidPoint (r - ‖c‖ ^ 2) (c, u))
  have h_point {r : ℝ} (u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
      inclMatrix ℂ (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ
          ((u.val.val *ᵥ √r • Pi.single 𝔰.k₀ 1) ⊕ᵥ fun _ ↦ c) =
        hyperboloidPoint (r - ‖c‖ ^ 2) (c, u) := by
    simp [mul_comm, inclMatrix, funext_iff, mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]
  calc _ = ∫⁻ r in Ioi 0, .ofReal (sphereDensity 𝔰.k r / 2) * F r := by
        rw [lintegral_eq_polar 𝔰.k₀ (by fun_prop)]
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        simp [F, h_point, star_dotProduct_hyperboloidPoint, hr.le]
    _ = ∫⁻ r, .ofReal (sphereDensity 𝔰.k r⁺ / 2) * F r := by
        -- for `k > 1` the density vanishes at `r⁺ = 0`
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun r ↦ ?_
        by_cases hr : 0 < r <;> simp [hr, le_of_not_gt, le_of_lt, show 𝔰.k - 1 ≠ 0 by omega]
    _ = ∫⁻ t, 2 * (.ofReal (sphereDensity 𝔰.k (2 * t + ‖c‖ ^ 2)⁺ / 2) *
          F (2 * t + ‖c‖ ^ 2)) := by
        conv_lhs =>
          rw [← lintegral_add_right_eq_self _ (‖c‖ ^ 2), ← smul_map_volume_mul_left two_ne_zero]
        rw [lintegral_smul_measure, lintegral_map (by fun_prop) (by fun_prop), smul_eq_mul,
          ← lintegral_const_mul' _ _ (by simp)]
        norm_num
    _ = _ := lintegral_congr fun t ↦ by
        simp [F, ← mul_assoc, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul, mul_div_cancel₀]

/-- For k = |κ| > 1, let h be standard on X₀ = ℂ^κ with h(z, z) = −1. The measures
`hyperboloidMeasure (2 Im β)` on the level sets h(v, v) = 2 Im β, β skew, disintegrate the volume of
V_ϱ = X₀ ⊕ ℂz along h(v, v). The volume is extended by zero to the whole space, and integrating
f(δ⁻¹β, v) against them and then over β = ri (Lebesgue in r) gives the integral of f(h(v, v), v);
here δ = i/2, so δ⁻¹β = 2 Im β. -/
lemma isDisintegration_hyperboloidMeasure (hk : 1 < 𝔰.k) :
    complexPlace.IsDisintegration
      (volume.map (inclMatrix ℂ (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ ·))
      (𝔰.middleGram (1 : ℂ)).splitGram
      fun β : skewAdjoint ℂ ↦ hyperboloidMeasure (2 * im (β : ℂ)) := by
  refine ⟨fun {g} (hg_cont : Continuous g) (hg_supp : HasCompactSupport g) ↦ ?_, fun f hf ↦ ?_⟩
  · -- the integrands vanish off one compact set of `(c, h)`, as `c` is the coordinate at `z`
    simp (disch := with_unfolding_all fun_prop) only [lintegral_map,
      lintegral_withDensity_eq_lintegral_mul, Pi.mul_apply]
    have h_compact : IsCompact
        (((· 𝔰.z) '' tsupport g) ×ˢ (univ : Set (U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)))) :=
      (hg_supp.image_of_continuous (· 𝔰.z)).prod isCompact_univ
    -- the first coordinate of a point where the integrand is nonzero is the value at `z`
    exact continuous_lintegral_and_lt_top h_compact (by fun_prop) fun _ _ h_ne ↦
      ⟨⟨_, subset_closure (right_ne_zero_of_mul h_ne), by simp⟩, trivial⟩
  -- split off the coordinate `c` at `z`
  have h_split (g : (𝔰.MiddleIndex → ℂ) → ENNReal) (hg : Measurable g) :
      ∫⁻ a, g a = ∫⁻ c : ℂ, ∫⁻ x : 𝔰.κ → ℂ, g (x ⊕ᵥ fun _ ↦ c) := by
    rw [← (measurePreserving_sumElim (A := ℂ) (ι := 𝔰.κ) (κ := Unit)).lintegral_comp hg,
      volume_eq_prod, lintegral_prod_symm _ (by fun_prop),
      ← (volume_preserving_funUnique Unit ℂ).symm.lintegral_comp (by fun_prop)]
    rfl
  simp (disch := with_unfolding_all fun_prop) only [lintegral_hyperboloidMeasure]
  rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_lintegral_swap (by fun_prop),
    h_split _ (by fun_prop)]
  refine lintegral_congr fun c ↦ ?_
  -- the skew elements are `t * I`, and `δ⁻¹ (t * I) = 2 t`
  rw [lintegral_slice_eq_hyperboloid hk c hf, complexPlace_skewMeasure,
    lintegral_map (by fun_prop) (by fun_prop)]
  simp [mul_comm, mul_left_comm, ← mul_assoc I, I_mul_I]

/-- Polar coordinates on the hyperboloid h(v, v) = −1 of V_ϱ = X₀ ⊕ ℂz, where X₀ has an orthonormal
basis indexed by κ and h(z, z) = −1, assuming `1 < 𝔰.k` (i.e. |κ| > 1). Let c have the law
`cellDensity`(c) dc, let w_ϱ(c) be the boost `cellChart 𝔰 ϱ c`, and let h ∈ U(X₀), embedded in G₁ by
`embedH`, have the Haar probability law. Then the map σ ↦ σ⁻¹z (`orbitPoint` at the top position)
carries the law of w_ϱ(c)⁻¹h to `floorQuadricMeasure`, the image of `quadricMeasure` of that
hyperboloid under the basis `complexBasis 𝔰`. -/
lemma map_orbitPoint_cellLaw_top (hk : 1 < 𝔰.k) :
    (cellLaw 𝔰.ϱ ∗ₘ volume.map embedH).map (orbitPoint 𝔰.top) =
    (complexBasis 𝔰).floorQuadricMeasure 𝔰.top := by
  -- By uniqueness of disintegrations the right side is `hyperboloidMeasure (-1)`; the left side
  -- becomes this measure on substituting `-c` for `c` and `h⁻¹` for `h`.
  have h_quadric : (complexBasis 𝔰).floorQuadricMeasure 𝔰.top = hyperboloidMeasure (-1) := by
    rw [((complexBasis 𝔰).isDisintegration_floorVolume 𝔰.top
      map_inclMatrix_middle_eq_floorVolume).unique (isDisintegration_hyperboloidMeasure hk)]
    simp [splitGram, middleGram]
  refine ext_of_lintegral _ fun f hf ↦ ?_
  rw [h_quadric, lintegral_hyperboloidMeasure _ hf]
  simp (disch := with_unfolding_all fun_prop) only [lintegral_map, lintegral_mconv,
    lintegral_withDensity_eq_lintegral_mul, Pi.mul_apply]
  show ∫⁻ c : ℂ, cellDensity 𝔰 𝔰.ϱ c *
      ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), f (orbitPoint 𝔰.top ((cellChart 𝔰 𝔰.ϱ c)⁻¹ * embedH h)) =
    ∫⁻ c : ℂ, .ofReal (sphereDensity 𝔰.k (-1 + ‖c‖ ^ 2)⁺) *
      ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), f (hyperboloidPoint (-1) (c, h))
  rw [← lintegral_neg_eq_self]
  refine lintegral_congr fun c ↦ ?_
  rw [← lintegral_inv_eq_self]
  by_cases hc : 1 < ‖c‖
  · have hc_neg : 1 ≤ ‖-c‖ := by simpa using hc.le
    -- `h` times the boost at `-c` takes `z` to `√(‖c‖² - 1) h x + c z`
    have h_point (h : U 1) : orbitPoint 𝔰.top ((cellBoost 𝔰 (-c) hc_neg)⁻¹ * embedH h⁻¹) =
        hyperboloidPoint (-1) (c, h) := by
      simp [cellBoost, hyperboloidPoint, mul_comm, orbitPoint,
        val_toBesselH_apply_coe, inclMatrix, neg_add_eq_sub, funext_iff, mulVec, dotProduct,
        Matrix.mul_apply, Pi.single_apply, Matrix.one_apply]
    simp only [cellChart_top_of_one_le hc_neg, h_point]
    simp [cellDensity, neg_add_eq_sub]
  · -- for `‖c‖ ≤ 1` both densities vanish, as `k > 1`
    have h_pos : (‖c‖ ^ 2 - 1)⁺ = 0 :=
      posPart_eq_zero.2 (sub_nonpos.2 (pow_le_one₀ (norm_nonneg c) (not_lt.1 hc)))
    simp [cellDensity, neg_add_eq_sub, h_pos, show 𝔰.k - 1 ≠ 0 by omega]

instance : IsProbabilityMeasure (volume.map (embedH (𝔰 := 𝔰))) :=
  (isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

end New.Floors

end
