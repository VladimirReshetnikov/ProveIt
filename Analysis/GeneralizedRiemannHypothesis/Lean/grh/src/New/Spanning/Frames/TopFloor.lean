import New.Spanning.Frames.FiberMeasures
import New.Spanning.Frames.TopCorrelation

/-!
# The density at the last entry

A finite set of finite places is read as one ring (`IntegralPlace`); the docstrings call it a finite
place. This file defines the pairing over a fibre and the density at the last entry. The pairing of
the scaled orbital integrals over the fixer of `z` in G^(ϱ), `PlaceData.fiberPairing`, is a function
of `e = l⁻¹ z` on the last vector quadric. At a large lattice datum it agrees there with a step
function. Its integral over the vectors `e` with a given pairing `⟨z, e⟩` is the density
`PlaceData.lastEntryDensity`. The file proves four things. This density is continuous. Its sums
against positive semidefinite matrices, over heads with one common last entry, are nonnegative. Its
Fourier transform in the last entry is the form of floor `𝔰.ϱ`. Finally, the file bounds, by the
fiber pairing at a point, the sums of the pairings of scaled orbital integrals over the congruence
cosets of the links that lie over that point.

## Main definitions and results

* `New.Floors.IntegralPlace.IsLargeLatticeData.sum_fiberPairing_nonneg`: At a large lattice datum
  `F` and at every vector `e`, the sum of the fiber pairings of the heads `ω a` against a positive
  semidefinite matrix `R` is a nonnegative real.
* `New.Floors.IntegralPlace.IsLargeLatticeData.floorForm_top_eq_integral_floorQuadric`: At a large
  lattice datum `F`, the form `F.floorForm 𝔰.ϱ` with the weight `ψ (ξ θ)` on the last diagonal entry
  `θ` of the frame Gram matrix is the integral, over the points `e` of the last vector quadric, of
  `ψ (ξ ⟨z, e⟩)` (`z` the last frame vector) times any continuous function `Φ` that extends the
  fiber pairing.

Notions from other files:
* `T.floorGroup l`, written G^(l), fixes the basis vectors of the floors below `l` in the unitary
  group `T.G`; `besselH` is `T.floorGroup 𝔰.n` with `𝔰.n = 𝔰.ϱ + 1`, which also fixes the last frame
  vector `z`, in position `𝔰.top`; `orbitPoint 𝔰.top l` is `l⁻¹ z`.
* Place data `F` give measures on these groups (`F.measureH` on `besselH`) and a congruence subgroup
  `F.congruenceSubgroup`; `P.IsLargeLatticeData F` says that they are large lattice data at a finite
  place `P`.
* `Z` is a group between `F.congruenceSubgroup` and the integral unitary group, and `Z.besselVector`
  is the vector of the finite Bessel functions of the cosets of `F.congruenceSubgroup` in `Z`.
* `weylElem 𝔰.ϱ p` is the Weyl element of a sequence `p` of units. An element `w_p l⁻¹` with `l` in
  the floor group has head `p` and link `l⁻¹`. The sequence is a head for a gauge `Γ` (a family of
  compact bounds on entries) if its inverse partial products are bounded by the gauge.
* `PlaceData.scaledOrbitalIntegral` (in `New.Spanning.Frames.TopCorrelation`) is the normalized
  orbital integral of the finite Bessel vector of `Z` at `w_p l⁻¹`, indexed by pairs of cosets.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure Set ENNReal SemilocalField FloorGroups InnerProductSpace
  ComplexOrder Function PlaceData Filter Finset

section FiberPairing

variable {A ι : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A] {m : ℕ} {T : 𝔰.Form A}
  [P : IntegralPlace A] [IsHermitianUnit T.splitGram] [Fintype ι] [DecidableEq ι]
  {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup) (p q : ℕ → Aˣ) {j : Type} [Fintype j]

open scoped Classical in
/-- The pairing of the scaled orbital integrals of `Z` with heads `p` and `q` at `k * l`, integrated
over `k` in `besselH`, the fixer of the last frame vector `z` in the floor group G^(ϱ), as a
function of the vector `e = l⁻¹ z` for `l` in G^(ϱ); it is zero off the orbit of `z`. -/
def PlaceData.fiberPairing (e : 𝔰.BesselIndex → A) : ℂ :=
  if h : ∃ l ∈ T.floorGroup 𝔰.ϱ, orbitPoint 𝔰.top l = e then
    ∫ k : T.G, ⟪scaledOrbitalIntegral Z p (k * h.choose),
      scaledOrbitalIntegral Z q (k * h.choose)⟫_ℂ ∂F.measureH
  else 0

/-- Two elements `l`, `l'` of the floor group G^(ϱ) with `l'⁻¹ z = l⁻¹ z` differ on the left by an
element of `besselH`, the fixer in G^(ϱ) of the last frame vector `z`. -/
lemma mul_inv_mem_besselH_of_orbitPoint_eq {A : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A]
    {T : 𝔰.Form A} [IsHermitianUnit T.splitGram] {l l' : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ)
    (hl' : l' ∈ T.floorGroup 𝔰.ϱ) (h_point : orbitPoint 𝔰.top l' = orbitPoint 𝔰.top l) :
    l' * l⁻¹ ∈ T.besselH := by
  simpa only [inv_inv] using partialUnitriangularGroup_inf_floorGroup_last.le
    (inv_mul_mem_of_orbitPoint_eq (inv_mem hl') (inv_mem hl) (by simpa using h_point))

/-- For `l` in the floor group G^(ϱ) = `T.floorGroup 𝔰.ϱ`, the fixer of the hyperbolic pairs,
`fiberPairing Z p q` at `orbitPoint 𝔰.top l = l⁻¹ z` is the integral over `k` of the pairing of
`scaledOrbitalIntegral Z p (k * l)` and `scaledOrbitalIntegral Z q (k * l)`. Here `k` is integrated
against `F.measureH`, the measure of the place datum on `besselH`, the fixer of `z` in G^(ϱ). -/
lemma PlaceData.fiberPairing_orbitPoint {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ) {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    fiberPairing Z p q (orbitPoint 𝔰.top l) =
      ∫ k : T.G, ⟪scaledOrbitalIntegral Z p (k * l),
        scaledOrbitalIntegral Z q (k * l)⟫_ℂ ∂F.measureH := by
  -- The chosen element is `l` up to `besselH` on the left, and `F.measureH` is right invariant.
  have h_ex : ∃ l' ∈ T.floorGroup 𝔰.ϱ, orbitPoint 𝔰.top l' = orbitPoint 𝔰.top l := ⟨l, hl, rfl⟩
  let l' : T.G := h_ex.choose
  obtain ⟨hl', h_point⟩ : l' ∈ T.floorGroup 𝔰.ϱ ∧ orbitPoint 𝔰.top l' = orbitPoint 𝔰.top l :=
    h_ex.choose_spec
  have h_fix : l' * l⁻¹ ∈ T.besselH := mul_inv_mem_besselH_of_orbitPoint_eq hl hl' h_point
  have h_pres : MeasurePreserving (fun k : T.G ↦ k * (l' * l⁻¹)) F.measureH F.measureH :=
    ⟨measurable_mul_const _, by rw [← mconv_dirac, F.measureH_mconv_dirac h_fix]⟩
  let f (g : T.G) : ℂ := ⟪scaledOrbitalIntegral Z p g, scaledOrbitalIntegral Z q g⟫_ℂ
  calc fiberPairing Z p q (orbitPoint 𝔰.top l)
    _ = ∫ k, f (k * l') ∂F.measureH := dite_eq_left h_ex
    _ = ∫ k, f (k * (l' * l⁻¹) * l) ∂F.measureH := by simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = ∫ k, f (k * l) ∂F.measureH :=
      h_pres.integral_comp (measurableEmbedding_mulRight _) fun k ↦ f (k * l)

/-- Every `l` in `T.floorGroup 𝔰.ϱ` maps `lastVectorQuadric T` into itself. Here
`lastVectorQuadric T` is the set of vectors with no component along the hyperbolic pairs and with
the norm of the last frame vector `z`. -/
lemma mulVec_mem_lastVectorQuadric {A : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A]
    {T : 𝔰.Form A}
    [IsHermitianUnit T.splitGram] {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) {e : 𝔰.BesselIndex → A}
    (he : e ∈ lastVectorQuadric T) : (l : GL 𝔰.BesselIndex A).val *ᵥ e ∈ lastVectorQuadric T := by
  obtain ⟨h_floor, h_norm⟩ : (∀ i : 𝔰.BesselIndex, floorOf i < 𝔰.ϱ → e i = 0) ∧
      star e ⬝ᵥ T.splitGram *ᵥ e = T.splitGram 𝔰.z 𝔰.z := he
  refine ⟨fun i hi ↦ ?_, (U.form_mulVec_mulVec l e e).trans h_norm⟩
  -- The row `i` of `l` is that of the identity matrix.
  have h_row (a : 𝔰.BesselIndex) :
      (l : GL 𝔰.BesselIndex A) i a = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i a :=
    apply_eq_one_apply_of_mem_floorGroup hl i a (.inl ⟨hi, hi⟩)
  simp [mulVec, dotProduct, h_row, Matrix.one_apply, h_floor i hi]

/-- The pairings of the scaled orbital integrals of `Z` at `l`, for the heads `ω a`, summed against
a matrix `R`. If `R` is the Gram matrix of vectors `x a`, this is the squared norm of the sum over
`a` of the scaled orbital integrals tensored with the `x a`. -/
def PlaceData.headSumNormSq (R : Matrix j j ℂ) (ω : j → ℕ → Aˣ) (l : T.G) : ℂ :=
  ∑ a : j, ∑ b : j, R a b * ⟪scaledOrbitalIntegral Z (ω a) l, scaledOrbitalIntegral Z (ω b) l⟫_ℂ

/-- Let `F` be a place datum and `Z` a group between the congruence subgroup `F.congruenceSubgroup`
and the integral unitary group. The sum `headSumNormSq Z R ω l` against `R` of the pairings of the
scaled orbital integrals with heads `ω a` splits over the coordinates `x` of these integrals, which
are pairs of cosets of `F.congruenceSubgroup` in `Z`: the term of `x` is `v^* R v` for the vector
`v a = scaledOrbitalIntegral Z (ω a) l x`. -/
lemma PlaceData.headSumNormSq_eq_sum {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    {j : Type} [Fintype j] (R : Matrix j j ℂ) (ω : j → ℕ → Aˣ) (l : T.G) :
    headSumNormSq Z R ω l = ∑ x : Z.Cosets × Z.Cosets,
      star (fun a : j ↦ scaledOrbitalIntegral Z (ω a) l x) ⬝ᵥ R *ᵥ fun a : j ↦
        scaledOrbitalIntegral Z (ω a) l x := by
  let c (a : j) : EuclideanSpace ℂ (Z.Cosets × Z.Cosets) := scaledOrbitalIntegral Z (ω a) l
  calc headSumNormSq Z R ω l
    _ = ∑ a : j, ∑ b : j, ∑ x : Z.Cosets × Z.Cosets, star (c a x) * (R a b * c b x) := by
      simp [c, headSumNormSq, inner, mul_sum, mul_comm, mul_assoc]
    _ = ∑ x : Z.Cosets × Z.Cosets, ∑ a : j, ∑ b : j, star (c a x) * (R a b * c b x) := by
      simp only [sum_comm (γ := Z.Cosets × Z.Cosets)]
    _ = _ := by simp [c, mulVec, dotProduct, mul_sum]

/-- The pairings of the scaled orbital integrals of `Z` at `l` for the heads `ω a`, summed against a
positive semidefinite matrix `R`, give a nonnegative real. -/
lemma PlaceData.headSumNormSq_nonneg {R : Matrix j j ℂ} (hR : R.PosSemidef) (ω : j → ℕ → Aˣ)
    (l : T.G) : 0 ≤ headSumNormSq Z R ω l := by
  rw [headSumNormSq_eq_sum]
  exact sum_nonneg fun x _ ↦ hR.dotProduct_mulVec_nonneg _

/-- For `l` in the floor group `T.floorGroup 𝔰.ϱ`, the vector `orbitPoint 𝔰.top l = l⁻¹ z` lies in
`lastVectorQuadric T`: it has no component along the hyperbolic pairs and has the norm of the last
frame vector `z`. -/
lemma orbitPoint_mem_lastVectorQuadric {A : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A]
    {T : 𝔰.Form A} [IsHermitianUnit T.splitGram] {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    orbitPoint 𝔰.top l ∈ lastVectorQuadric T := by
  have hz : Pi.single (𝔰.besselFrame 𝔰.top) 1 ∈ lastVectorQuadric T := by
    refine ⟨fun i hi ↦ Pi.single_eq_of_ne ?_ 1, by simp⟩
    rintro rfl
    simp at hi
  exact mulVec_mem_lastVectorQuadric (inv_mem hl) hz

namespace IntegralPlace.IsLargeLatticeData

/-- If the form `T` of shape `𝔰` has a large lattice datum `F`, the index set `𝔰.κ` of the basis
vectors outside the hyperbolic pairs and the last frame vector has at least two elements. -/
lemma two_le_card {F : PlaceData ι T (m + 1)} [_h : P.IsLargeLatticeData F] :
    2 ≤ Fintype.card 𝔰.κ := by
  have h_rank : Fintype.card 𝔰.κ + 1 = Fintype.card ι + 2 * (m + 1) + 2 := F.card_eq
  omega

/-- Let `F` be a large lattice datum, `R` a positive semidefinite matrix, and `l` in the floor group
G^(ϱ). Let `headSumNormSq Z R ω (g * l)`, the nonnegative sum against `R` of the pairings of scaled
orbital integrals, be integrated over `g` in `besselH`, the fixer in G^(ϱ) of the last frame vector
`z`. The integral is the sum against `R` of the fiber pairings of the heads `ω a` at `l⁻¹ z`. -/
lemma lintegral_headSumNormSq_eq {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup) {j : Type}
    [Fintype j] [h : P.IsLargeLatticeData F] {R : Matrix j j ℂ} (hR : R.PosSemidef) (ω : j → ℕ → Aˣ)
    {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    ∫⁻ g : T.G, ENNReal.ofReal (headSumNormSq Z R ω (g * l)).re ∂F.measureH =
      ENNReal.ofReal
        (∑ a : j, ∑ b : j, R a b * fiberPairing Z (ω a) (ω b) (orbitPoint 𝔰.top l)).re := by
  have h_int (a b : j) : Integrable
      (fun g : T.G ↦ ⟪scaledOrbitalIntegral Z (ω a) (g * l),
        scaledOrbitalIntegral Z (ω b) (g * l)⟫_ℂ) F.measureH :=
    integrable_inner_scaledOrbitalIntegral Z (ω a) (ω b) hl
  simpa only [fiberPairing_orbitPoint Z _ _ hl, headSumNormSq] using
    lintegral_ofReal_re_sum_sum_mul (R := R) h_int fun g ↦ headSumNormSq_nonneg Z hR ω (g * l)

/-- If `F` is a large lattice datum (`P.IsLargeLatticeData F`) and `R` is positive semidefinite,
then for every vector `e` the sum `∑ a b, R a b * fiberPairing Z (ω a) (ω b) e` is a nonnegative
real. -/
lemma sum_fiberPairing_nonneg {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup) {j : Type}
    [Fintype j] [h : P.IsLargeLatticeData F] {R : Matrix j j ℂ} (hR : R.PosSemidef) (ω : j → ℕ → Aˣ)
    (e : 𝔰.BesselIndex → A) : 0 ≤ ∑ a : j, ∑ b : j, R a b * fiberPairing Z (ω a) (ω b) e := by
  by_cases h_orbit : ∃ l ∈ T.floorGroup 𝔰.ϱ, orbitPoint 𝔰.top l = e
  · -- At `l⁻¹ z` the sum is the integral over `besselH` of `headSumNormSq Z R ω (g * l) ≥ 0`.
    obtain ⟨l, hl, rfl⟩ : ∃ l ∈ T.floorGroup 𝔰.ϱ, orbitPoint 𝔰.top l = e := h_orbit
    have h_int (a b : j) : Integrable
        (fun g : T.G ↦ ⟪scaledOrbitalIntegral Z (ω a) (g * l),
          scaledOrbitalIntegral Z (ω b) (g * l)⟫_ℂ) F.measureH :=
      integrable_inner_scaledOrbitalIntegral Z (ω a) (ω b) hl
    simpa only [fiberPairing_orbitPoint Z _ _ hl] using
      sum_sum_mul_integral_nonneg (R := R) h_int fun g ↦ headSumNormSq_nonneg Z hR ω (g * l)
  · simp [fiberPairing, h_orbit]

/-- The scaled orbital integral of the finite Bessel vector of `Z` with head `r` does not change
when the inverse link `l` is multiplied on the left by an element of
`besselH ⊓ F.congruenceSubgroup`, the fixer of the hyperbolic pairs and the last frame vector in the
congruence subgroup. -/
lemma _root_.New.Floors.PlaceData.scaledOrbitalIntegral_mul_left {F : PlaceData ι T (m + 1)}
    (Z : F.IntermediateGroup) (r : ℕ → Aˣ) {k : T.G} (hk : k ∈ besselH ⊓ F.congruenceSubgroup)
      (l : T.G) :
    scaledOrbitalIntegral Z r (k * l) = scaledOrbitalIntegral Z r l := by
  have hW (y : T.G) : Z.besselVector ((weylElem 𝔰.ϱ r * (k * l)⁻¹)⁻¹ * y) =
      Z.besselVector ((weylElem 𝔰.ϱ r * l⁻¹)⁻¹ * y) := by
    simp [mul_assoc, besselVector_mul_left Z hk]
  rw [scaledOrbitalIntegral, scaledOrbitalIntegral,
    besselOrbitalIntegral_congr F.groupMeasure fun y _ ↦ hW y]

/-- Let the elements `β θ` of a group lie in distinct left cosets of a subgroup `K`, so that at most
one `g * β θ` lies in `K`. If `c θ ≤ b` whenever `g * β θ ∈ K`, then the sum of the `c θ` over the
`θ` with `g * β θ ∈ K` is at most `b`. -/
lemma _root_.New.Floors.sum_indicator_mul_le_of_inv_mul_mem {G i : Type*} [Group G] [Fintype i]
    {K : Subgroup G} {β : i → G} (h_sep : ∀ θ θ' : i, (β θ)⁻¹ * β θ' ∈ K → θ = θ') {g : G}
    {c : i → ℝ≥0∞} {b : ℝ≥0∞} (h_le : ∀ θ : i, g * β θ ∈ K → c θ ≤ b) :
    ∑ θ : i, (K : Set G).indicator (fun _ : G ↦ c θ) (g * β θ) ≤ b := by
  by_cases h_mem : ∃ θ : i, g * β θ ∈ K
  · obtain ⟨θ, hθ⟩ := h_mem
    have h_other (θ' : i) (hθ' : θ' ≠ θ) : g * β θ' ∉ K := fun h_mem' ↦
      hθ' (h_sep θ' θ (by simpa [mul_assoc] using mul_mem (inv_mem h_mem') hθ))
    rw [Fintype.sum_eq_single θ fun θ' hθ' ↦ indicator_of_notMem (h_other θ' hθ') _,
      indicator_of_mem hθ]
    exact h_le θ hθ
  · simp [indicator_of_notMem (not_exists.1 h_mem _)]

/-- Let `F` be a large lattice datum and `R` a positive semidefinite matrix. Let the elements `l θ`
of the floor group G^(ϱ) lie over one vector `e = (l θ)⁻¹ z` and in distinct right cosets of the
congruence subgroup `F.congruenceSubgroup`. Then the sums `headSumNormSq Z R ω (l θ)` against `R` of
the pairings of scaled orbital integrals, times the volume of the congruence subgroup in `besselH`,
the fixer of `z` in G^(ϱ), add up to at most the sum of the fiber pairings at `e` against `R`. -/
lemma sum_headSumNormSq_le_fiberPairing {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    {j : Type} [Fintype j] [h : P.IsLargeLatticeData F] {R : Matrix j j ℂ} (hR : R.PosSemidef)
    (ω : j → ℕ → Aˣ) {e : 𝔰.BesselIndex → A} {i : Type} [Fintype i] {l : i → T.G}
    (hl : ∀ θ : i, l θ ∈ T.floorGroup 𝔰.ϱ ∧ orbitPoint 𝔰.top (l θ) = e)
    (h_sep : ∀ θ θ' : i, l θ * (l θ')⁻¹ ∈ F.congruenceSubgroup → θ = θ') :
    F.measureH F.congruenceSubgroup * ∑ θ : i, ENNReal.ofReal (headSumNormSq Z R ω (l θ)).re ≤
      ENNReal.ofReal (∑ a : j, ∑ b : j, R a b * fiberPairing Z (ω a) (ω b) e).re := by
  -- The right side is an integral over `besselH`. Each `θ` gives a coset of the congruence group
  -- on which the integrand is the term of `θ`, and these cosets are disjoint.
  obtain _ | ⟨⟨θ₀⟩⟩ := isEmpty_or_nonempty i
  · rw [univ_eq_empty, sum_empty, mul_zero]
    exact zero_le
  obtain ⟨l₀, hl₀, rfl⟩ : ∃ l₀ ∈ T.floorGroup 𝔰.ϱ, orbitPoint 𝔰.top l₀ = e := ⟨l θ₀, hl θ₀⟩
  -- `l₀ = β θ * l θ` with `β θ` in `besselH`. For `g` in `besselH` with `g * β θ` in
  -- `F.congruenceSubgroup`, the scaled orbital integrals at `g * l₀` are those at `l θ`.
  let β (θ : i) : T.G := l₀ * (l θ)⁻¹
  have hβ (θ : i) : β θ ∈ besselH := by
    obtain ⟨h_floor, h_point⟩ : l θ ∈ T.floorGroup 𝔰.ϱ ∧
        orbitPoint 𝔰.top (l θ) = orbitPoint 𝔰.top l₀ := hl θ
    exact mul_inv_mem_besselH_of_orbitPoint_eq h_floor hl₀ h_point.symm
  have h_coset (θ : i) (g : T.G) (hg : g ∈ besselH) (hgβ : g * β θ ∈ F.congruenceSubgroup)
      (r : ℕ → Aˣ) : scaledOrbitalIntegral Z r (l θ) = scaledOrbitalIntegral Z r (g * l₀) := by
    have h_arg : g * l₀ = g * β θ * l θ := by simp [β, mul_assoc]
    rw [h_arg, scaledOrbitalIntegral_mul_left Z r ⟨mul_mem hg (hβ θ), hgβ⟩]
  have β_sep (θ θ' : i) (h_quot : (β θ)⁻¹ * β θ' ∈ F.congruenceSubgroup) : θ = θ' :=
    h_sep θ θ' (by simpa [β, mul_assoc] using h_quot)
  have h_mem : ∀ᵐ g : T.G ∂F.measureH, g ∈ besselH := F.ae_measureH_mem_besselH
  let I (g : T.G) : ℝ≥0∞ := ENNReal.ofReal (headSumNormSq Z R ω g).re
  calc F.measureH F.congruenceSubgroup * ∑ θ : i, I (l θ)
    _ = ∑ θ : i, ∫⁻ g, (F.congruenceSubgroup : Set T.G).indicator (fun _ ↦ I (l θ)) (g * β θ)
          ∂F.measureH := by
      simp_rw [← lintegral_mconv_dirac, F.measureH_mconv_dirac (hβ _),
        lintegral_indicator_const measurableSet_unitaryLevel, mul_sum, mul_comm]
    _ = ∫⁻ g, ∑ θ : i, (F.congruenceSubgroup : Set T.G).indicator (fun _ ↦ I (l θ)) (g * β θ)
          ∂F.measureH :=
      (lintegral_finsetSum _ (by fun_prop (disch := exact measurableSet_unitaryLevel))).symm
    _ ≤ ∫⁻ g, I (g * l₀) ∂F.measureH := by
      refine lintegral_le_of_ae_imp h_mem fun g hg ↦
        sum_indicator_mul_le_of_inv_mul_mem β_sep fun θ hθ ↦ le_of_eq ?_
      simp only [I, headSumNormSq, h_coset θ g hg hθ]
    _ = ENNReal.ofReal
          (∑ a : j, ∑ b : j, R a b * fiberPairing Z (ω a) (ω b) (orbitPoint 𝔰.top l₀)).re :=
      lintegral_headSumNormSq_eq Z hR ω hl₀

/-- At a large lattice datum `F`, the fiber pairing, as a function on the orbit of the last frame
vector `z` under the floor group G^(ϱ), is invariant under the matrices of
`besselH ⊓ F.congruenceSubgroup`, the fixer of the hyperbolic pairs and `z` in the congruence
subgroup. -/
lemma fiberPairing_mulVec {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup) (p q : ℕ → Aˣ)
    [h : P.IsLargeLatticeData F] {k : T.G} (hk : k ∈ besselH ⊓ F.congruenceSubgroup) {l : T.G}
    (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    fiberPairing Z p q ((k : GL 𝔰.BesselIndex A).val *ᵥ orbitPoint 𝔰.top l) =
      fiberPairing Z p q (orbitPoint 𝔰.top l) := by
  obtain ⟨hk_fix, -⟩ : k ∈ besselH ∧ k ∈ F.congruenceSubgroup := Subgroup.mem_inf.1 hk
  have hk' : k ∈ T.floorGroup 𝔰.ϱ := floorGroup_anti 𝔰.ϱ.le_succ hk_fix
  have h_point : (k : GL 𝔰.BesselIndex A).val *ᵥ orbitPoint 𝔰.top l =
      orbitPoint 𝔰.top (l * k⁻¹) := by
    rw [orbitPoint, orbitPoint, mulVec_mulVec, _root_.mul_inv_rev, inv_inv]
    rfl
  -- Substitute `k * y` for `y` in the scaled orbital integral; `k` commutes with the Weyl element.
  have h_corr (r : ℕ → Aˣ) (g : T.G) :
      scaledOrbitalIntegral Z r (g * (l * k⁻¹)) = scaledOrbitalIntegral Z r (g * l) := by
    let w : T.G := weylElem 𝔰.ϱ r
    unfold scaledOrbitalIntegral
    refine congrArg ((F.headDensity 𝔰.ϱ r 1).toReal • ·) (PiLp.ext fun i ↦ ?_)
    change ∫ y : T.G, Z.besselVector y i.1 * starRingEnd ℂ
          (Z.besselVector ((w * (g * (l * k⁻¹))⁻¹)⁻¹ * y) i.2) ∂F.groupMeasure =
      ∫ y : T.G, Z.besselVector y i.1 * starRingEnd ℂ
          (Z.besselVector ((w * (g * l)⁻¹)⁻¹ * y) i.2) ∂F.groupMeasure
    rw [← integral_mul_left_eq_self _ k]
    simp [w, mul_assoc, (weylElem_mul_left_comm hk').2, besselVector_mul_left Z hk]
  rw [h_point, fiberPairing_orbitPoint Z p q hl,
    fiberPairing_orbitPoint Z p q (mul_mem hl (inv_mem hk'))]
  simp only [h_corr]

/-- At a large lattice datum `F` there is a compact subset `C` of the floor group `T.floorGroup 𝔰.ϱ`
such that `fiberPairing Z p q e` vanishes unless `e` is in the image of `C` under
`orbitPoint 𝔰.top`. -/
lemma exists_isCompact_fiberPairing_support {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] :
    ∃ C : Set T.G, IsCompact C ∧
      C ⊆ T.floorGroup 𝔰.ϱ ∧
      ∀ e : 𝔰.BesselIndex → A, fiberPairing Z p q e ≠ 0 → e ∈ orbitPoint 𝔰.top '' C := by
  obtain ⟨C, hC, h_supp⟩ : ∃ C : Set T.G, IsCompact C ∧
      ∀ l ∈ T.floorGroup 𝔰.ϱ, scaledOrbitalIntegral Z p l ≠ 0 → l ∈ C :=
    exists_isCompact_scaledOrbitalIntegral_support Z p
  refine ⟨C ∩ T.floorGroup 𝔰.ϱ, hC.inter_right (isClosed_of_entries_eq_one mem_floorGroup),
    inter_subset_right, fun e he ↦ ?_⟩
  obtain ⟨l, hl, rfl⟩ : ∃ l ∈ T.floorGroup 𝔰.ϱ, orbitPoint 𝔰.top l = e :=
    by_contra fun h_off ↦ he (dite_eq_right h_off)
  -- Some `k * l` with `k` in `besselH` has a nonzero scaled orbital integral; its point is the
  -- same.
  obtain ⟨k, hk, h_ne⟩ : ∃ k ∈ T.besselH, scaledOrbitalIntegral Z p (k * l) ≠ 0 := by
    by_contra! h_zero
    refine he ((fiberPairing_orbitPoint Z p q hl).trans (integral_eq_zero_of_ae ?_))
    filter_upwards [F.ae_measureH_mem_besselH] with k hk
    simp [h_zero k hk]
  obtain ⟨hk_tri, hk_floor⟩ : k ∈ partialUnitriangularGroup 𝔰.n ∧ k ∈ T.floorGroup 𝔰.ϱ :=
    partialUnitriangularGroup_inf_floorGroup_last.ge hk
  have hkl : k * l ∈ T.floorGroup 𝔰.ϱ := mul_mem hk_floor hl
  have k_fix : orbitPoint 𝔰.top k = Pi.single (𝔰.besselFrame 𝔰.top) 1 :=
    (mem_partialUnitriangularGroup_succ_iff hk_floor).1 hk_tri
  refine ⟨k * l, ⟨h_supp _ hkl h_ne, hkl⟩, ?_⟩
  calc orbitPoint 𝔰.top (k * l)
    _ = ((l⁻¹ : T.G) : GL 𝔰.BesselIndex A).val *ᵥ orbitPoint 𝔰.top k := by
      rw [orbitPoint, orbitPoint, mulVec_mulVec, _root_.mul_inv_rev]
      rfl
    _ = orbitPoint 𝔰.top l := by rw [k_fix, orbitPoint]

/-- Let the form `T` have a large lattice datum `F`, let the units of `A` be open, and let `z` be
the last frame vector. The map `l ↦ orbitPoint 𝔰.top l = l⁻¹ z` has local sections on
`lastVectorQuadric T`, the vectors without components in the hyperbolic planes that have the norm of
`z`. For `l` in `T.floorGroup 𝔰.ϱ`, there is a map `σ` tending to `1` at `l⁻¹ z`. Every point `x` of
the quadric near `l⁻¹ z` then has `σ x` in `T.floorGroup 𝔰.ϱ` and
`orbitPoint 𝔰.top (l * σ x) = x`. -/
lemma exists_section_orbitPoint {F : PlaceData ι T (m + 1)} [h : P.IsLargeLatticeData F]
    [IsOpenUnits A] {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    ∃ σ : (𝔰.BesselIndex → A) → T.G, Tendsto σ (nhds (orbitPoint 𝔰.top l)) (nhds 1) ∧
      ∀ᶠ x : 𝔰.BesselIndex → A in nhds (orbitPoint 𝔰.top l), x ∈ lastVectorQuadric T →
        σ x ∈ T.floorGroup 𝔰.ϱ ∧ orbitPoint 𝔰.top (l * σ x) = x := by
  -- Conjugate by `l` the Eichler map that takes `l x` to `z`.
  obtain ⟨u, hu_dual, hu_last⟩ : ∃ u : 𝔰.BesselIndex → A,
      star u ᵥ* T.splitGram = Pi.single (𝔰.besselFrame 𝔰.top) 1 ∧ u (𝔰.besselFrame 𝔰.top) = 0 :=
    h.exists_isotropic
  have h_open : Topology.IsOpenEmbedding (Units.val : Aˣ → A) :=
    IsOpenUnits.isOpenEmbedding_unitsVal
  let z : 𝔰.BesselIndex → A := Pi.single (𝔰.besselFrame 𝔰.top) 1
  have h_move : Tendsto (fun x : 𝔰.BesselIndex → A ↦ (l : GL 𝔰.BesselIndex A).val *ᵥ x)
      (nhds (orbitPoint 𝔰.top l)) (nhds z) :=
    Continuous.tendsto' (by fun_prop) _ _ (orbitPoint_eq_iff.1 rfl)
  have h_inv : ContinuousAt Ring.inverse (z (𝔰.besselFrame 𝔰.top)) := by
    have hz_one : z (𝔰.besselFrame 𝔰.top) = (1 : Aˣ) := Pi.single_eq_same _ _
    have h_units : Continuous fun a : Aˣ ↦ Ring.inverse (a : A) :=
      Units.continuous_coe_inv.congr (by simp)
    rw [hz_one]
    exact h_open.continuousAt_iff.1 h_units.continuousAt
  have h_eichler : Tendsto (topEichler hu_dual hu_last) (nhds z) (nhds 1) := by
    rw [← topEichler_single hu_dual hu_last]
    exact continuousAt_topEichler hu_dual hu_last h_inv
  have h_unit : ∀ᶠ e in nhds z, IsUnit (e (𝔰.besselFrame 𝔰.top)) :=
    (h_open.isOpen_range.preimage (by fun_prop)).mem_nhds ⟨1, by simp [z]⟩
  refine ⟨fun x : 𝔰.BesselIndex → A ↦
    l⁻¹ * topEichler hu_dual hu_last ((l : GL 𝔰.BesselIndex A).val *ᵥ x) * l, ?_, ?_⟩
  · simpa using ((h_eichler.comp h_move).const_mul l⁻¹).mul_const l
  · filter_upwards [h_move.eventually h_unit] with x hx_unit hx
    let e : 𝔰.BesselIndex → A := (l : GL 𝔰.BesselIndex A).val *ᵥ x
    obtain ⟨h_floor, h_norm⟩ : (∀ i : 𝔰.BesselIndex, floorOf i < 𝔰.ϱ → e i = 0) ∧
        star e ⬝ᵥ T.splitGram *ᵥ e = T.splitGram 𝔰.z 𝔰.z := mulVec_mem_lastVectorQuadric hl hx
    refine ⟨mul_mem (mul_mem (inv_mem hl) (topEichler_mem_floorGroup _ _ h_floor)) hl, ?_⟩
    -- The Eichler map of `e = l x` sends `e` to `z`.
    have h_sends : (topEichler hu_dual hu_last e : GL 𝔰.BesselIndex A).val *ᵥ e = z :=
      orbitPoint_eq_iff.1 (orbitPoint_topEichler hu_dual hu_last h_norm hx_unit)
    rw [orbitPoint_eq_iff]
    simpa [e, z, mul_assoc, ← mulVec_mulVec] using h_sends

/-- At a large lattice datum `F`, the fiber pairing `fiberPairing Z p q` is locally constant along
the last vector quadric `lastVectorQuadric T` at the points `orbitPoint 𝔰.top l = l⁻¹ z`, for `l` in
the floor group `T.floorGroup 𝔰.ϱ` and `z` the last frame vector. Near such a point it takes the
same value at every point of the quadric. -/
lemma eventually_fiberPairing_eq {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ)
    [h : P.IsLargeLatticeData F] [IsOpenUnits A] {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    ∀ᶠ x : 𝔰.BesselIndex → A in nhds (orbitPoint 𝔰.top l), x ∈ lastVectorQuadric T →
      fiberPairing Z p q x = fiberPairing Z p q (orbitPoint 𝔰.top l) := by
  obtain ⟨σ, σ_tendsto, σ_spec⟩ : ∃ σ : (𝔰.BesselIndex → A) → T.G,
      Tendsto σ (nhds (orbitPoint 𝔰.top l)) (nhds 1) ∧
      ∀ᶠ x : 𝔰.BesselIndex → A in nhds (orbitPoint 𝔰.top l), x ∈ lastVectorQuadric T →
        σ x ∈ T.floorGroup 𝔰.ϱ ∧ orbitPoint 𝔰.top (l * σ x) = x :=
    h.exists_section_orbitPoint hl
  -- The scaled orbital integrals do not see `σ x` when it is near `1`.
  have h_near (r : ℕ → Aˣ) : ∀ᶠ x in nhds (orbitPoint 𝔰.top l), σ x ∈ T.floorGroup 𝔰.ϱ →
      ∀ g ∈ T.floorGroup 𝔰.ϱ, scaledOrbitalIntegral Z r (g * σ x) = scaledOrbitalIntegral Z r g :=
    σ_tendsto (eventually_scaledOrbitalIntegral_mul_eq_self Z r).curry_nhds.self_of_nhds
  filter_upwards [σ_spec, h_near p, h_near q] with x hσ hp hq hx
  obtain ⟨σ_mem, h_point⟩ : σ x ∈ T.floorGroup 𝔰.ϱ ∧ orbitPoint 𝔰.top (l * σ x) = x := hσ hx
  rw [← h_point, fiberPairing_orbitPoint Z p q hl, fiberPairing_orbitPoint Z p q (mul_mem hl σ_mem)]
  refine integral_congr_ae (F.ae_measureH_mem_besselH.mono fun k hk ↦ ?_)
  have hkl : k * l ∈ T.floorGroup 𝔰.ϱ := mul_mem (floorGroup_anti 𝔰.ϱ.le_succ hk) hl
  have hp_eq : scaledOrbitalIntegral Z p (k * (l * σ x)) = scaledOrbitalIntegral Z p (k * l) := by
    rw [← mul_assoc, hp σ_mem _ hkl]
  have hq_eq : scaledOrbitalIntegral Z q (k * (l * σ x)) = scaledOrbitalIntegral Z q (k * l) := by
    rw [← mul_assoc, hq σ_mem _ hkl]
  simp only [hp_eq, hq_eq]

/-- At a large lattice datum `F`, the fiber pairing agrees on the last vector quadric with a
function `Φ` of compact support that is invariant under small translations and under
`besselH ⊓ F.congruenceSubgroup`, the fixer of the hyperbolic pairs and the last frame vector in the
congruence subgroup. -/
lemma exists_step_function_eqOn_fiberPairing {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] [IsOpenUnits A] :
    ∃ Φ : (𝔰.BesselIndex → A) → ℂ,
      HasCompactSupport Φ ∧
      (∀ᶠ v : 𝔰.BesselIndex → A in nhds 0, ∀ x : 𝔰.BesselIndex → A, Φ (x + v) = Φ x) ∧
      (∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → A,
        Φ ((k : GL 𝔰.BesselIndex A).val *ᵥ x) = Φ x) ∧
      ∀ e ∈ lastVectorQuadric T, Φ e = fiberPairing Z p q e := by
  obtain ⟨C, hC, hC_floor, h_supp⟩ : ∃ C : Set T.G, IsCompact C ∧ C ⊆ T.floorGroup 𝔰.ϱ ∧
      ∀ e : 𝔰.BesselIndex → A, fiberPairing Z p q e ≠ 0 → e ∈ orbitPoint 𝔰.top '' C :=
    exists_isCompact_fiberPairing_support Z p q
  have h_integral : besselH ⊓ F.congruenceSubgroup ≤ (intGL 𝔰.BesselIndex P.integers).subgroupOf
    T.G := by
    intro k hk
    obtain ⟨-, h_int, -⟩ : k ∈ besselH ∧ (k : GL 𝔰.BesselIndex A) ∈ intGL 𝔰.BesselIndex P.integers ∧
        IsIntMatrix P.integers (F.levelUnit⁻¹ • ((k : GL 𝔰.BesselIndex A).val - 1)) :=
      Subgroup.mem_inf.1 hk
    exact h_int
  refine exists_step_function_extension h_integral (hC.image (continuous_orbitPoint (b := 𝔰.top)))
    ?_ ?_ ?_
  · -- the support lies in the image of `C`, which is on the quadric
    intro x hx
    obtain ⟨l, hl, rfl⟩ : ∃ l ∈ C, orbitPoint 𝔰.top l = x := h_supp x hx
    exact ⟨mem_image_of_mem _ hl, orbitPoint_mem_lastVectorQuadric (hC_floor hl)⟩
  · intro k hk x hx
    obtain ⟨l, hl, rfl⟩ : ∃ l ∈ C, orbitPoint 𝔰.top l = x := h_supp x hx
    exact fiberPairing_mulVec Z p q hk (hC_floor hl)
  · rintro _ ⟨l, hl, rfl⟩
    exact eventually_fiberPairing_eq Z p q (hC_floor hl)

/-- At a large lattice datum `F`, the form `F.floorForm 𝔰.ϱ` with the weight `ψ (ξ θ)` on the last
diagonal entry `θ` of the frame Gram matrix is the integral, over the points `e` of the last vector
quadric, of `ψ (ξ ⟨z, e⟩)` (`z` the last frame vector) times any continuous function `Φ` that
extends the fiber pairing. -/
lemma floorForm_top_eq_integral_floorQuadric {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] (ξ : A) {Φ : (𝔰.BesselIndex → A) → ℂ}
    (hΦ : Continuous Φ) (Φ_eq : ∀ e ∈ lastVectorQuadric T, Φ e = fiberPairing Z p q e) :
    F.floorForm 𝔰.ϱ p q Z.besselVector
        (fun x : T.G ↦ P.ψ (ξ * T.frameGram x.val 𝔰.top 𝔰.top)) =
      ∫ e : 𝔰.BesselIndex → A, P.ψ (ξ * (T.splitGram *ᵥ e) 𝔰.z) * Φ e
        ∂F.floorQuadricMeasure 𝔰.top := by
  -- The measure on the floor group is `F.measureH ∗ₘ F.floorMeasure 𝔰.ϱ`, and `orbitPoint` maps
  -- `F.floorMeasure 𝔰.ϱ` to the measure of the top quadric.
  let f (l : T.G) : ℂ :=
    P.ψ (ξ * T.frameGram l⁻¹.val 𝔰.top 𝔰.top) * ⟪scaledOrbitalIntegral Z p l,
      scaledOrbitalIntegral Z q l⟫_ℂ
  obtain ⟨f_int, h_form⟩ : Integrable f (F.measureH ∗ₘ F.floorMeasure 𝔰.ϱ) ∧
      F.floorForm 𝔰.ϱ p q Z.besselVector
          (fun x : T.G ↦ P.ψ (ξ * T.frameGram x.val 𝔰.top 𝔰.top)) =
        ∫ l, f l ∂(F.measureH ∗ₘ F.floorMeasure 𝔰.ϱ) := by
    rw [← partialGroupMeasure_top]
    exact floorForm_top_eq_integral Z p q ξ
  have h_entry (l k : T.G) (hk : k ∈ T.besselH) :
      T.frameGram (k * l)⁻¹.val 𝔰.top 𝔰.top = (T.splitGram *ᵥ orbitPoint 𝔰.top l) 𝔰.z := by
    -- The factor `k⁻¹` fixes `z`, and the entry at `l⁻¹` is `⟨z, l⁻¹ z⟩`.
    have hk_inv : k⁻¹ ∈ T.partialUnitriangularGroup (𝔰.top + 1) ⊓ T.floorGroup 𝔰.top :=
      partialUnitriangularGroup_inf_floorGroup_last.ge (inv_mem hk)
    have h_one : orbitPoint 𝔰.top (1 : T.G) = Pi.single (𝔰.besselFrame 𝔰.top) 1 :=
      orbitPoint_eq_iff.2 (one_mulVec _)
    calc T.frameGram (k * l)⁻¹.val 𝔰.top 𝔰.top
      _ = T.frameGram (1 * l⁻¹ : T.G) 𝔰.top 𝔰.top := by
        rw [_root_.mul_inv_rev, (frameGram_diag_mul hk_inv l⁻¹).2, one_mul]
      _ = star (orbitPoint 𝔰.top (1 : T.G)) ⬝ᵥ T.splitGram *ᵥ orbitPoint 𝔰.top l := by
        rw [frameGram_eq_form_orbitPoint]
      _ = (T.splitGram *ᵥ orbitPoint 𝔰.top l) 𝔰.z := by simp [h_one]
  have h_pres : MeasurePreserving (orbitPoint 𝔰.top) (F.floorMeasure 𝔰.ϱ)
      (F.floorQuadricMeasure 𝔰.top) :=
    measurePreserving_orbitPoint 𝔰.top
  calc
    _ = ∫ l, ∫ k, f (k * l) ∂F.measureH ∂F.floorMeasure 𝔰.ϱ := by
      rw [h_form, mconv, integral_map measurable_mul.aemeasurable f_int.aestronglyMeasurable]
      exact integral_prod_symm _ (f_int.comp_measurable measurable_mul)
    _ = ∫ l, P.ψ (ξ * (T.splitGram *ᵥ orbitPoint 𝔰.top l) 𝔰.z) * Φ (orbitPoint 𝔰.top l)
        ∂F.floorMeasure 𝔰.ϱ := by
      refine integral_congr_ae (F.ae_floorMeasure_mem.mono fun l hl ↦ ?_)
      have h_fiber : Φ (orbitPoint 𝔰.top l) =
          ∫ k, ⟪scaledOrbitalIntegral Z p (k * l),
            scaledOrbitalIntegral Z q (k * l)⟫_ℂ ∂F.measureH :=
        (Φ_eq _ (orbitPoint_mem_lastVectorQuadric hl)).trans (fiberPairing_orbitPoint Z p q hl)
      simp only [h_fiber, ← integral_const_mul]
      refine integral_congr_ae (F.ae_measureH_mem_besselH.mono fun k hk ↦ ?_)
      simp only [f, h_entry l k hk]
    _ = _ := by
      rw [← h_pres.map_eq, integral_map h_pres.aemeasurable (by fun_prop)]

end IntegralPlace.IsLargeLatticeData

end FiberPairing

section TopDensity

variable {A ι : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A] {m : ℕ} [P : IntegralPlace A]
  [Fintype ι] [DecidableEq ι] {j : Type} [Fintype j] {N : A}

/-- The density at the last entry `t = p 𝔰.ϱ` of the head `p`: the integral of the fiber pairing of
the heads `p`, `q` over the vectors `e` of the last vector quadric with `⟨z, e⟩ = t` (`z` the last
frame vector), with `(modulus π)⁻¹` times the measure `dx / d⟨x, x⟩` on the sphere over `t`. It is
used with `π * star π = N`, so that this factor is `|N| ^ (-1/2)`, and for heads with `q 𝔰.ϱ = t`,
although the definition does not read `q 𝔰.ϱ`. -/
def PlaceData.lastEntryDensity (π : Aˣ) [IsHermitianUnit (latticeMiddleGram 𝔰 N).splitGram]
    {F : PlaceData ι (latticeMiddleGram 𝔰 N) (m + 1)} (Z : F.IntermediateGroup) (p q : ℕ → Aˣ) :
      ℂ :=
  (P.modulus π)⁻¹.toReal * ∫ x : 𝔰.κ → A, fiberPairing Z p q (vectorOfLastEntry π (p 𝔰.ϱ) x)
    ∂P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π (p 𝔰.ϱ))

variable {π : Aˣ} [IsHermitianUnit (latticeMiddleGram 𝔰 N).splitGram]

namespace IntegralPlace.IsLargeLatticeData

/-- Descent from the last entry. Let `π` be a unit with `π * star π = N`, and `F` a large lattice
datum of `latticeMiddleGram 𝔰 N`. This is the Gram matrix in the lattice basis of the sum of the
standard form on `𝔰.κ → A` and a line spanned by `z` of norm `-N`. The density
`lastEntryDensity π Z p q` is `(modulus π)⁻¹` times the integral of `fiberPairing Z p q` over the
vectors `e` of the last vector quadric with `⟨z, e⟩ = p 𝔰.ϱ`. Replace the entries `p 𝔰.ϱ`, `q 𝔰.ϱ`
by `unitOrOne t` (`t` if it is a unit, else `1`). Then the density times `P.ψ (ξ t)` is integrable
in `t`. Its integral is `F.floorForm 𝔰.ϱ p q Z.besselVector` with the weight `P.ψ (ξ θ)`, where `θ`
is the last diagonal entry of the frame Gram matrix. -/
lemma integral_lastEntryDensity {F : PlaceData ι (latticeMiddleGram 𝔰 N) (m + 1)}
    (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] [IsOpenUnits A] (hN : π * star ↑π = N) (ξ : A) :
    let f (t : A) : ℂ := P.ψ (ξ * t) *
      lastEntryDensity π Z (update p 𝔰.ϱ (unitOrOne t)) (update q 𝔰.ϱ (unitOrOne t))
    Integrable f ∧ ∫ t : A, f t = F.floorForm 𝔰.ϱ p q Z.besselVector
      fun x : (latticeMiddleGram 𝔰 N).G ↦
        P.ψ (ξ * (latticeMiddleGram 𝔰 N).frameGram x.val 𝔰.top 𝔰.top) := by
  -- Both sides are the integral over the top quadric of `g e = ψ (ξ ⟨z, e⟩) Φ e`, where `Φ` is the
  -- step function that extends the fiber pairing.
  intro f
  obtain ⟨Φ, Φ_supp, Φ_unif, -, Φ_eq⟩ : ∃ Φ : (𝔰.BesselIndex → A) → ℂ, HasCompactSupport Φ ∧
      (∀ᶠ v : 𝔰.BesselIndex → A in nhds 0, ∀ x : 𝔰.BesselIndex → A, Φ (x + v) = Φ x) ∧
      (∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → A,
        Φ ((k : GL 𝔰.BesselIndex A).val *ᵥ x) = Φ x) ∧
      ∀ e ∈ lastVectorQuadric (latticeMiddleGram 𝔰 N), Φ e = fiberPairing Z p q e :=
    exists_step_function_eqOn_fiberPairing Z p q
  have Φ_cont : Continuous Φ := (isLocallyConstant_of_eventually_add Φ_unif).continuous
  let g (e : 𝔰.BesselIndex → A) : ℂ := P.ψ (ξ * ((latticeMiddleGram 𝔰 N).splitGram *ᵥ e) 𝔰.z) * Φ e
  have g_cont : Continuous g := .mul (by fun_prop) Φ_cont
  let slice (t : A) : ℂ :=
    (P.modulus π)⁻¹.toReal * ∫ x, g (vectorOfLastEntry π t x) ∂P.normFiberMeasure 𝔰.κ
      (lastEntrySphereIndex π t)
  obtain ⟨slice_int, slice_eq⟩ :
      Integrable slice ∧ ∫ t, slice t = ∫ e, g e ∂F.floorQuadricMeasure 𝔰.top :=
    F.integral_floorQuadricMeasure_top hN h.two_le_card g_cont Φ_supp.mul_left
  -- Almost every `t` is a unit, and the fiber pairing does not see the entry `𝔰.ϱ` of the heads.
  have f_eq : slice =ᵐ[volume] f := by
    filter_upwards [P.ae_isUnit] with _ ⟨t, ht⟩
    subst ht
    have h_heads (e : 𝔰.BesselIndex → A) :
        fiberPairing Z (update p 𝔰.ϱ t) (update q 𝔰.ϱ t) e = fiberPairing Z p q e := by
      simp [fiberPairing, scaledOrbitalIntegral, headDensity, prod_range, LT.lt.ne]
    have h_sphere : ∫ x, Φ (vectorOfLastEntry π t x) ∂P.normFiberMeasure 𝔰.κ
      (lastEntrySphereIndex π t) =
        ∫ x, fiberPairing Z p q (vectorOfLastEntry π t x) ∂P.normFiberMeasure 𝔰.κ
          (lastEntrySphereIndex π t) :=
      integral_congr_ae ((ae_vectorOfLastEntry_mem_lastVectorQuadric hN h.two_le_card _).mono
        fun _ ↦ Φ_eq _)
    have h_last (x : 𝔰.κ → A) :
        ((latticeMiddleGram 𝔰 N).splitGram *ᵥ vectorOfLastEntry π (t : A) x) 𝔰.z = t :=
      (form_vectorOfLastEntry hN).2
    simp only [slice, f, g, lastEntryDensity, update_self, unitOrOne_val, h_last,
      integral_const_mul, h_heads, h_sphere]
    ring
  refine ⟨slice_int.congr f_eq, ?_⟩
  rw [← integral_congr_ae f_eq, slice_eq,
    floorForm_top_eq_integral_floorQuadric Z p q ξ Φ_cont Φ_eq]

/-- Let `π` be a unit with `π * star π = N`, and let `F` be a large lattice datum of the lattice
form `latticeMiddleGram 𝔰 N`, whose last frame vector `z` has norm `-N`. Then the density
`lastEntryDensity π Z p q` is continuous as a function of the pair `(p, q)`. -/
lemma continuous_lastEntryDensity {F : PlaceData ι (latticeMiddleGram 𝔰 N) (m + 1)}
    (Z : F.IntermediateGroup) [h : P.IsLargeLatticeData F] [IsOpenUnits A] (hN : π * star ↑π = N) :
    Continuous (lastEntryDensity π Z).uncurry := by
  classical
  -- Near `(p, q)` the fiber pairing does not change, and its step function `Φ` does not see the
  -- change of the last entry. What moves is the sphere; the fiber measures are weakly continuous.
  refine continuous_iff_continuousAt.2 fun (p, q) ↦ ?_
  obtain ⟨Φ, Φ_supp, Φ_unif, -, Φ_eq⟩ : ∃ Φ : (𝔰.BesselIndex → A) → ℂ, HasCompactSupport Φ ∧
      (∀ᶠ v : 𝔰.BesselIndex → A in nhds 0, ∀ x : 𝔰.BesselIndex → A, Φ (x + v) = Φ x) ∧
      (∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → A,
        Φ ((k : GL 𝔰.BesselIndex A).val *ᵥ x) = Φ x) ∧
      ∀ e ∈ lastVectorQuadric (latticeMiddleGram 𝔰 N), Φ e = fiberPairing Z p q e :=
    exists_step_function_eqOn_fiberPairing Z p q
  have Φ_cont : Continuous Φ := (isLocallyConstant_of_eventually_add Φ_unif).continuous
  have h_emb : Topology.IsClosedEmbedding
      (vectorOfLastEntry π (p 𝔰.ϱ) : (𝔰.κ → A) → 𝔰.BesselIndex → A) :=
    isClosedEmbedding_vectorOfLastEntry
  have h_weak : Continuous fun b ↦ ∫ x, Φ (vectorOfLastEntry π (p 𝔰.ϱ) x) ∂P.normFiberMeasure 𝔰.κ
    b :=
    (isDisintegration_normFiberMeasure h.two_le_card).continuous_integral
      (Φ_cont.comp h_emb.continuous)
      (Φ_supp.comp_isClosedEmbedding h_emb)
  have h_level : Continuous fun z : (ℕ → Aˣ) × (ℕ → Aˣ) ↦ lastEntrySphereIndex π (z.1 𝔰.ϱ : A) := by
    fun_prop
  refine ((h_weak.comp h_level).const_mul ((P.modulus π)⁻¹.toReal : ℂ)).continuousAt.congr ?_
  have h_corr (r : ℕ → Aˣ) : ∀ᶠ r' in nhds r, ∀ l ∈ (latticeMiddleGram 𝔰 N).floorGroup 𝔰.ϱ,
      scaledOrbitalIntegral Z r' l = scaledOrbitalIntegral Z r l := by
    filter_upwards [(Continuous.prodMk_left 1).continuousAt
      (eventually_scaledOrbitalIntegral_mul_eq_self Z r)]
      with r' h_eq l hl
    simpa only [mul_one] using h_eq (one_mem _) l hl
  have h_shift : Tendsto (fun z : (ℕ → Aˣ) × (ℕ → Aˣ) ↦
      vectorOfLastEntry π ((z.1 𝔰.ϱ : A) - p 𝔰.ϱ) (0 : 𝔰.κ → A)) (nhds (p, q)) (nhds 0) :=
    Continuous.tendsto' (by fun_prop) (p, q) 0 (by simp [vectorOfLastEntry, ← Pi.zero_def])
  filter_upwards [prod_mem_nhds (h_corr p) (h_corr q), h_shift.eventually Φ_unif]
    with z ⟨hp, hq⟩ hΦ
  -- `z` is a pair of heads near `(p, q)`; the density at `z` is the integral of `Φ` on its sphere
  have h_pairing (e : 𝔰.BesselIndex → A) : fiberPairing Z z.1 z.2 e = fiberPairing Z p q e := by
    by_cases h_orbit : ∃ l ∈ (latticeMiddleGram 𝔰 N).floorGroup 𝔰.ϱ, orbitPoint 𝔰.top l = e
    · obtain ⟨l, hl, rfl⟩ : ∃ l ∈ (latticeMiddleGram 𝔰 N).floorGroup 𝔰.ϱ, orbitPoint 𝔰.top l = e :=
        h_orbit
      rw [fiberPairing_orbitPoint Z z.1 z.2 hl, fiberPairing_orbitPoint Z p q hl]
      refine integral_congr_ae (F.ae_measureH_mem_besselH.mono fun k hk ↦ ?_)
      have hkl : k * l ∈ floorGroup 𝔰.ϱ := mul_mem (floorGroup_anti 𝔰.ϱ.le_succ hk) hl
      simp only [hp _ hkl, hq _ hkl]
    · simp [fiberPairing, h_orbit]
  have h_add (x : 𝔰.κ → A) :
      vectorOfLastEntry π (p 𝔰.ϱ) x + vectorOfLastEntry π ((z.1 𝔰.ϱ : A) - p 𝔰.ϱ) (0 : 𝔰.κ → A) =
        vectorOfLastEntry π (z.1 𝔰.ϱ) x := by
    rw [vectorOfLastEntry, vectorOfLastEntry, vectorOfLastEntry, ← mulVec_add]
    congr 1
    simp [funext_iff, mul_sub]
  change (P.modulus π)⁻¹.toReal * ∫ x, Φ (vectorOfLastEntry π (p 𝔰.ϱ) x)
      ∂P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π (z.1 𝔰.ϱ : A)) = lastEntryDensity π Z z.1 z.2
  refine congrArg _ (integral_congr_ae ?_)
  filter_upwards [ae_vectorOfLastEntry_mem_lastVectorQuadric hN h.two_le_card _] with x hx
  rw [h_pairing, ← Φ_eq _ hx, ← h_add, hΦ]

/-- Let `π * star π = N`, and let `F` be a large lattice datum of `latticeMiddleGram 𝔰 N`. The fiber
pairing at `vectorOfLastEntry π t x = x - N⁻¹ t z` is integrable in `x` for
`P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t)`, the fiber measure `dx / d⟨x, x⟩` of the sphere
`x* x = t t̄ / N - N`. -/
lemma integrable_fiberPairing_vectorOfLastEntry {F : PlaceData ι (latticeMiddleGram 𝔰 N) (m + 1)}
    (Z : F.IntermediateGroup) (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] [IsOpenUnits A]
    (hN : π * star ↑π = N) (t : A) :
    Integrable (fun x : 𝔰.κ → A ↦ fiberPairing Z p q (vectorOfLastEntry π t x))
      (P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t)) := by
  -- On the sphere the pairing agrees with a continuous function of compact support.
  let μ : Measure (𝔰.κ → A) := P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t)
  have : IsFiniteMeasureOnCompacts μ :=
    (isDisintegration_normFiberMeasure h.two_le_card).isFiniteMeasureOnCompacts _
  have h_emb : Topology.IsClosedEmbedding (vectorOfLastEntry π t : (𝔰.κ → A) → 𝔰.BesselIndex → A) :=
    isClosedEmbedding_vectorOfLastEntry
  obtain ⟨Φ, Φ_supp, Φ_unif, -, Φ_eq⟩ : ∃ Φ : (𝔰.BesselIndex → A) → ℂ, HasCompactSupport Φ ∧
      (∀ᶠ v : 𝔰.BesselIndex → A in nhds 0, ∀ x : 𝔰.BesselIndex → A, Φ (x + v) = Φ x) ∧
      (∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → A,
        Φ ((k : GL 𝔰.BesselIndex A).val *ᵥ x) = Φ x) ∧
      ∀ e ∈ lastVectorQuadric (latticeMiddleGram 𝔰 N), Φ e = fiberPairing Z p q e :=
    exists_step_function_eqOn_fiberPairing Z p q
  have Φ_cont : Continuous Φ := (isLocallyConstant_of_eventually_add Φ_unif).continuous
  have Φ_int : Integrable (Φ ∘ vectorOfLastEntry π t) μ :=
    (Φ_cont.comp h_emb.continuous).integrable_of_hasCompactSupport
      (Φ_supp.comp_isClosedEmbedding h_emb)
  exact Φ_int.congr ((ae_vectorOfLastEntry_mem_lastVectorQuadric hN h.two_le_card _).mono fun _ ↦
    Φ_eq _)

/-- For heads `ω a` with a common last entry `t`, the sum of the densities against a matrix `R` is
`(modulus π)⁻¹` times the sum against `R` of the integrals of the fiber pairings over the sphere of
`t`. -/
lemma _root_.New.Floors.PlaceData.sum_lastEntryDensity_eq
    {F : PlaceData ι (latticeMiddleGram 𝔰 N) (m + 1)}
    (Z : F.IntermediateGroup) (R : Matrix j j ℂ) (ω : j → ℕ → Aˣ)
    {t : Aˣ} (ht : ∀ a : j, ω a 𝔰.ϱ = t) :
    ∑ a : j, ∑ b : j, R a b * lastEntryDensity π Z (ω a) (ω b) =
      (P.modulus π)⁻¹.toReal * ∑ a : j, ∑ b : j, R a b * ∫ x : 𝔰.κ → A,
        fiberPairing Z (ω a) (ω b) (vectorOfLastEntry π t x) ∂P.normFiberMeasure 𝔰.κ
          (lastEntrySphereIndex π t) := by
  simp only [lastEntryDensity, ht, mul_sum, mul_left_comm (R _ _)]

/-- Let `π * star π = N`, and let `F` be a large lattice datum of `latticeMiddleGram 𝔰 N`. Suppose
the heads `ω a` have a common last entry `ω a 𝔰.ϱ = t`, and `R` is a positive semidefinite matrix.
Then the sum `∑ a, ∑ b, R a b * lastEntryDensity π Z (ω a) (ω b)` is a nonnegative real. -/
lemma sum_lastEntryDensity_nonneg {F : PlaceData ι (latticeMiddleGram 𝔰 N) (m + 1)}
    (Z : F.IntermediateGroup) [h : P.IsLargeLatticeData F] [IsOpenUnits A] (hN : π * star ↑π = N)
    {R : Matrix j j ℂ} (hR : R.PosSemidef) (ω : j → ℕ → Aˣ)
    {t : Aˣ} (ht : ∀ a : j, ω a 𝔰.ϱ = t) :
    0 ≤ ∑ a : j, ∑ b : j, R a b * lastEntryDensity π Z (ω a) (ω b) := by
  have h_sphere : 0 ≤ ∑ a : j, ∑ b : j, R a b * ∫ x : 𝔰.κ → A,
      fiberPairing Z (ω a) (ω b) (vectorOfLastEntry π t x) ∂P.normFiberMeasure 𝔰.κ
        (lastEntrySphereIndex π t) :=
    sum_sum_mul_integral_nonneg (fun a b ↦
      integrable_fiberPairing_vectorOfLastEntry Z (ω a) (ω b) hN t)
      fun x ↦ sum_fiberPairing_nonneg Z hR ω (vectorOfLastEntry π t x)
  rw [sum_lastEntryDensity_eq Z R ω ht]
  exact mul_nonneg (Complex.zero_le_real.2 toReal_nonneg) h_sphere

/-- Let `π * star π = N`, and let `F` be a large lattice datum of `latticeMiddleGram 𝔰 N`. Take
heads `ω a` (sequences of units) with a common last entry `ω a 𝔰.ϱ = t` and a positive semidefinite
matrix `R`. Then the sum of `lastEntryDensity π Z (ω a) (ω b)` against `R` is nonnegative. It is
`(P.modulus π)⁻¹` times the integral of the sums of `fiberPairing Z (ω a) (ω b)` against `R` at
`vectorOfLastEntry π t x = x - N⁻¹ t z`. Here `x` is integrated against
`P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t)`, the fiber measure `dx / d⟨x, x⟩` of the sphere
`x* x = t t̄ / N - N`. -/
lemma sum_lastEntryDensity_nonneg_and_eq_inv_mul_lintegral
    {F : PlaceData ι (latticeMiddleGram 𝔰 N) (m + 1)}
    (Z : F.IntermediateGroup) [h : P.IsLargeLatticeData F] [IsOpenUnits A] (hN : π * star ↑π = N)
    {R : Matrix j j ℂ} (hR : R.PosSemidef) (ω : j → ℕ → Aˣ)
    {t : Aˣ} (ht : ∀ a : j, ω a 𝔰.ϱ = t) :
    0 ≤ ∑ a : j, ∑ b : j, R a b * lastEntryDensity π Z (ω a) (ω b) ∧
      ENNReal.ofReal (∑ a : j, ∑ b : j, R a b * lastEntryDensity π Z (ω a) (ω b)).re =
        (P.modulus π)⁻¹ * ∫⁻ x : 𝔰.κ → A, ENNReal.ofReal
            (∑ a : j, ∑ b : j, R a b * fiberPairing Z (ω a) (ω b) (vectorOfLastEntry π t x)).re
          ∂P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t) := by
  refine ⟨sum_lastEntryDensity_nonneg Z hN hR ω ht, ?_⟩
  let μ : Measure (𝔰.κ → A) := P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t)
  have h_sphere : ∫⁻ x : 𝔰.κ → A, ENNReal.ofReal
      (∑ a : j, ∑ b : j, R a b * fiberPairing Z (ω a) (ω b) (vectorOfLastEntry π t x)).re ∂μ =
        ENNReal.ofReal (∑ a : j, ∑ b : j, R a b * ∫ x : 𝔰.κ → A,
          fiberPairing Z (ω a) (ω b) (vectorOfLastEntry π t x) ∂μ).re :=
    lintegral_ofReal_re_sum_sum_mul
      (fun a b ↦ integrable_fiberPairing_vectorOfLastEntry Z (ω a) (ω b) hN t)
      fun x ↦ sum_fiberPairing_nonneg Z hR ω (vectorOfLastEntry π t x)
  rw [sum_lastEntryDensity_eq Z R ω ht, h_sphere, Complex.re_ofReal_mul, ofReal_mul toReal_nonneg,
    ofReal_toReal (by simp)]

end IntegralPlace.IsLargeLatticeData

end TopDensity

end New.Floors

end
