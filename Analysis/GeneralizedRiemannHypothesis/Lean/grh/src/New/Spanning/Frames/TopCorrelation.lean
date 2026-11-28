import New.Spanning.Frames.BesselVector

/-!
# Scaled orbital integrals of the finite Bessel vector on the floor group

A finite set of finite places is read as one ring (`IntegralPlace`); the docstrings call it a finite
place. This file defines the scaled orbital integrals `PlaceData.scaledOrbitalIntegral`. These are
normalized orbital integrals of the finite Bessel vector at the elements `w_p l⁻¹` with head `p` and
link `l⁻¹`. It also defines the integrand `PlaceData.unfoldedPairing` of their pairing. At a large
lattice datum it shows three things. The scaled orbital integrals are locally constant in the head
and on the floor group G^(ϱ). They vanish off a compact set. Their pairings are integrable over
`besselH`. It also writes the form `F.floorForm 𝔰.ϱ`, with a weight on the last diagonal entry of
`T.frameGram`, as an integral of these pairings. General lemmas give compactly supported step
extensions of locally constant functions and the nonnegativity of sums of integrals against a
matrix.

## Main definitions and results

* `New.Floors.IntegralPlace.IsLargeLatticeData.exists_isCompact_scaledOrbitalIntegral_support`: Let
  `F` be a large lattice datum. The scaled orbital integral `scaledOrbitalIntegral Z p l`, a density
  times `∫ W y ⊗ (W (l w_p⁻¹ y))^*` over the unitary group, with `W` the finite Bessel vector of `Z`
  and `w_p` the Weyl element of the head `p`, vanishes for the `l` in the floor group G^(ϱ) outside
  some compact set.
* `New.Floors.IntegralPlace.IsLargeLatticeData.inner_scaledOrbitalIntegral`: At a large lattice
  datum `F` and for `l` in the floor group G^(ϱ), the pairing of the scaled orbital integrals with
  heads `p`, `q` at `l` is the density `F.headDensity 𝔰.ϱ p q` of the two heads times the integral
  of the integrand `unfoldedPairing Z p q l` over two copies of the group.

Notions from other files:
* `T.floorGroup l`, written G^(l), fixes the basis vectors of the floors below `l` in the unitary
  group `T.G`; `besselH` is `T.floorGroup 𝔰.n` with `𝔰.n = 𝔰.ϱ + 1`, which also fixes the last frame
  vector `z`, in position `𝔰.top`; `orbitPoint 𝔰.top l` is `l⁻¹ z`.
* Place data `F` gives measures on these groups (`F.measureH` on `besselH`) and a congruence
  subgroup `F.congruenceSubgroup`; `P.IsLargeLatticeData F` says that it is large lattice data at a
  finite place `P`.
* `Z` is a group between `F.congruenceSubgroup` and the integral unitary group, and `Z.besselVector`
  is the vector of the finite Bessel functions of the cosets of `F.congruenceSubgroup` in `Z`.
* `weylElem 𝔰.ϱ p` is the Weyl element of a sequence `p` of units. An element `w_p l⁻¹` with `l` in
  the floor group has head `p` and link `l⁻¹`. The sequence is a head for a gauge `Γ` (a family of
  compact bounds on entries) if its inverse partial products are bounded by the gauge.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure Set ENNReal SemilocalField FloorGroups InnerProductSpace
  ComplexOrder Function PlaceData Filter Finset

lemma sum_sum_mul_integral {X j : Type} [MeasurableSpace X] [Fintype j] {μ : Measure X}
    (R : Matrix j j ℂ) {f : j → j → X → ℂ} (hf : ∀ a b : j, Integrable (f a b) μ) :
    ∑ a : j, ∑ b : j, R a b * ∫ x : X, f a b x ∂μ =
      ∫ x : X, ∑ a : j, ∑ b : j, R a b * f a b x ∂μ := by
  simp (disch := fun_prop) only [← integral_const_mul, ← integral_finsetSum]

/-- Let `R` be a complex matrix and `f a b` integrable functions. If `∑ a b, R a b * f a b x` is a
nonnegative real for every `x`, then `∑ a b, R a b * ∫ f a b` is a nonnegative real. -/
lemma sum_sum_mul_integral_nonneg {X j : Type} [MeasurableSpace X] [Fintype j] {μ : Measure X}
    {R : Matrix j j ℂ} {f : j → j → X → ℂ} (hf : ∀ a b : j, Integrable (f a b) μ)
    (h_nonneg : ∀ x : X, 0 ≤ ∑ a : j, ∑ b : j, R a b * f a b x) :
    0 ≤ ∑ a : j, ∑ b : j, R a b * ∫ x : X, f a b x ∂μ := by
  rw [sum_sum_mul_integral R hf]
  exact integral_nonneg h_nonneg

/-- Let `R` be a complex matrix and `f a b` integrable functions. If `∑ a b, R a b * f a b x` is a
nonnegative real for every `x`, then the lower Lebesgue integral of these values is the real part
of `∑ a b, R a b * ∫ f a b`. -/
lemma lintegral_ofReal_re_sum_sum_mul {X j : Type} [MeasurableSpace X] [Fintype j] {μ : Measure X}
    {R : Matrix j j ℂ} {f : j → j → X → ℂ} (hf : ∀ a b : j, Integrable (f a b) μ)
    (h_nonneg : ∀ x : X, 0 ≤ ∑ a : j, ∑ b : j, R a b * f a b x) :
    ∫⁻ x : X, ENNReal.ofReal (∑ a : j, ∑ b : j, R a b * f a b x).re ∂μ =
      ENNReal.ofReal (∑ a : j, ∑ b : j, R a b * ∫ x : X, f a b x ∂μ).re := by
  have h_int : Integrable (fun x : X ↦ ∑ a : j, ∑ b : j, R a b * f a b x) μ := by fun_prop
  have h_re : (∑ a : j, ∑ b : j, R a b * ∫ x : X, f a b x ∂μ).re =
      ∫ x : X, (∑ a : j, ∑ b : j, R a b * f a b x).re ∂μ := by
    rw [sum_sum_mul_integral R hf]
    exact (integral_re h_int).symm
  have h_re_nonneg (x : X) : 0 ≤ (∑ a : j, ∑ b : j, R a b * f a b x).re :=
    (Complex.nonneg_iff.1 (h_nonneg x)).1
  rw [h_re]
  exact (ofReal_integral_eq_lintegral_ofReal h_int.re (.of_forall h_re_nonneg)).symm

/-- Let `C` and `L` be compact sets of vectors over `A`, and let `φ` be locally constant along `Q`
at the points of `C`. Then for all scalars `b` near `0` one has `φ (x + b • v) = φ x` whenever
`x ∈ C`, `v ∈ L`, and both `x` and `x + b • v` lie in `Q`. -/
lemma eventually_forall_apply_add_smul_eq {A n : Type} [SemilocalField A] [Fintype n]
    {Q C L : Set (n → A)} (hC : IsCompact C) (hL : IsCompact L) {φ : (n → A) → ℂ}
    (h_loc : ∀ e ∈ C, ∀ᶠ x : n → A in nhds e, x ∈ Q → φ x = φ e) :
    ∀ᶠ b : A in nhds 0, ∀ z ∈ C ×ˢ L,
      z.1 ∈ Q → z.1 + b • z.2 ∈ Q → φ (z.1 + b • z.2) = φ z.1 := by
  refine (hC.prod hL).eventually_forall_of_forall_eventually fun (x, v) ⟨hx, _⟩ ↦ ?_
  -- For `(b, x', v')` near `(0, x, v)`, both `x'` and `x' + b • v'` are close to `x`.
  have h_fst : Tendsto (fun ((_, x', _) : A × (n → A) × (n → A)) ↦ x') (nhds (0, x, v)) (nhds x) :=
    continuousAt_snd.fst
  have h_shift : Tendsto (fun ((b, x', v') : A × (n → A) × (n → A)) ↦ x' + b • v')
      (nhds (0, x, v)) (nhds x) :=
    Continuous.tendsto' (by fun_prop) (0, x, v) x (by simp)
  filter_upwards [h_fst (h_loc x hx), h_shift (h_loc x hx)]
    with ⟨b, x', v'⟩ h_at_fst h_at_shift hQ_fst hQ_shift
  exact (h_at_shift hQ_shift).trans (h_at_fst hQ_fst).symm

/-- Let `C` and `L` be compact sets of vectors over a finite place `A`, and let `φ` be locally
constant along `Q` at the points of `C`. Then for some unit `u` one has `φ x = φ y` whenever
`x ∈ Q`, `y ∈ C ∩ Q` and `x - y` lies in `u • L`. -/
lemma exists_unit_forall_apply_eq_of_inv_smul_sub_mem {A n : Type} [SemilocalField A] [StarRing A]
    [P : IntegralPlace A] [Fintype n] {Q C L : Set (n → A)} (hC : IsCompact C) (hL : IsCompact L)
    {φ : (n → A) → ℂ} (h_loc : ∀ e ∈ C, ∀ᶠ x : n → A in nhds e, x ∈ Q → φ x = φ e) :
    ∃ u : Aˣ, ∀ x ∈ Q, ∀ y ∈ C ∩ Q, u⁻¹ • (x - y) ∈ L → φ x = φ y := by
  -- Units are dense, since almost every element is a unit.
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ : ∃ b : A, IsUnit b ∧ ∀ z ∈ C ×ˢ L,
      z.1 ∈ Q → z.1 + b • z.2 ∈ Q → φ (z.1 + b • z.2) = φ z.1 :=
    (dense_of_ae P.ae_isUnit).inter_nhds_nonempty
      (eventually_forall_apply_add_smul_eq hC hL h_loc)
  refine ⟨u, fun x hx y ⟨hyC, hyQ⟩ hxy ↦ ?_⟩
  have h_point : y + (u : A) • (u⁻¹ • (x - y)) = x := by simp [← Units.smul_def]
  have h_step : y + (u : A) • (u⁻¹ • (x - y)) ∈ Q → φ (y + (u : A) • (u⁻¹ • (x - y))) = φ y :=
    hu (y, u⁻¹ • (x - y)) ⟨hyC, hxy⟩ hyQ
  rw [h_point] at h_step
  exact h_step hx

/-- Let `φ` be a function on vectors over a finite place `A`, supported in `C ∩ Q` with `C` compact,
locally constant along `Q` at the points of `C`, and invariant on its support under a group `H` of
matrices in `GL n R`, where `R = P.integers` is the ring of integers. Then `φ` agrees on `Q` with a
compactly supported function `Φ` that is invariant under small translations and under `H`. -/
theorem exists_step_function_extension {A n : Type} [SemilocalField A] [StarRing A]
    [P : IntegralPlace A] [Fintype n] [DecidableEq n] {G : Subgroup (GL n A)} {H : Subgroup G}
    (hH : H ≤ (intGL n P.integers).subgroupOf G) {Q C : Set (n → A)} (hC : IsCompact C)
    {φ : (n → A) → ℂ} (h_supp : ∀ x : n → A, φ x ≠ 0 → x ∈ C ∩ Q)
    (h_inv : ∀ k ∈ H, ∀ x : n → A, φ x ≠ 0 → φ ((k : GL n A).val *ᵥ x) = φ x)
    (h_loc : ∀ e ∈ C, ∀ᶠ x : n → A in nhds e, x ∈ Q → φ x = φ e) :
    ∃ Φ : (n → A) → ℂ,
      HasCompactSupport Φ ∧
      (∀ᶠ v : n → A in nhds 0, ∀ x : n → A, Φ (x + v) = Φ x) ∧
      (∀ k ∈ H, ∀ x : n → A, Φ ((k : GL n A).val *ᵥ x) = Φ x) ∧
      ∀ x ∈ Q, Φ x = φ x := by
  classical
  -- Let `L = R ^ n`. For a small unit `u`, `φ` is constant on `(y + u • L) ∩ Q` for `y` in `C ∩ Q`.
  -- Give `Φ` this value on the class `y + u • L` if `φ y ≠ 0`, and `0` on the other classes.
  obtain ⟨hL_open, hL_compact, -⟩ : IsOpen (intVectors P.integers n : Set (n → A)) ∧
      IsCompact (intVectors P.integers n : Set (n → A)) ∧ volume
        (intVectors P.integers n : Set (n → A)) = 1 :=
    P.isOpen_isCompact_volume_intVectors
  obtain ⟨u, hu⟩ : ∃ u : Aˣ, ∀ x ∈ Q, ∀ y ∈ C ∩ Q,
    u⁻¹ • (x - y) ∈ intVectors P.integers n → φ x = φ y :=
    exists_unit_forall_apply_eq_of_inv_smul_sub_mem hC hL_compact h_loc
  let Near (x y : n → A) : Prop := φ y ≠ 0 ∧ u⁻¹ • (x - y) ∈ intVectors P.integers n
  have const (x y : n → A) (hx : x ∈ Q) (hy : Near x y) : φ x = φ y :=
    hu x hx y (h_supp y hy.1) hy.2
  let Φ (x : n → A) : ℂ := if hx : ∃ y : n → A, Near x y then φ hx.choose else 0
  have Φ_eq (x y : n → A) (hy : Near x y) : Φ x = φ y := by
    have hx : ∃ y : n → A, Near x y := ⟨y, hy⟩
    obtain ⟨h_ne, h_int⟩ : Near x hx.choose := hx.choose_spec
    obtain ⟨hy_ne, hy_int⟩ := hy
    have h_diff : u⁻¹ • (hx.choose - y) ∈ intVectors P.integers n := by
      simpa [smul_sub] using sub_mem hy_int h_int
    exact (dite_eq_left hx).trans (const hx.choose y (h_supp hx.choose h_ne).2 ⟨hy_ne, h_diff⟩)
  have Φ_zero (x : n → A) (hx : ¬∃ y : n → A, Near x y) : Φ x = 0 := dite_eq_right hx
  -- `Φ x'` equals `Φ x` as soon as the near points of `x` and `x'` correspond with equal values.
  have Φ_congr (x x' : n → A) (h : ∀ y : n → A, Near x y → ∃ y' : n → A, Near x' y' ∧ φ y' = φ y)
      (h' : ∀ y' : n → A, Near x' y' → ∃ y : n → A, Near x y) : Φ x' = Φ x := by
    by_cases hx : ∃ y : n → A, Near x y
    · obtain ⟨y, hy⟩ : ∃ y : n → A, Near x y := hx
      obtain ⟨y', hy', h_eq⟩ : ∃ y' : n → A, Near x' y' ∧ φ y' = φ y := h y hy
      rw [Φ_eq x y hy, Φ_eq x' y' hy', h_eq]
    · rw [Φ_zero x hx, Φ_zero x' fun ⟨y', hy'⟩ ↦ hx (h' y' hy')]
  have move (k : G) (hk : k ∈ H) (x y : n → A) (hy : Near x y) :
      Near ((k : GL n A).val *ᵥ x) ((k : GL n A).val *ᵥ y) ∧
        φ ((k : GL n A).val *ᵥ y) = φ y := by
    obtain ⟨hy_ne, hy_int⟩ := hy
    have h_value : φ ((k : GL n A).val *ᵥ y) = φ y := h_inv k hk y hy_ne
    refine ⟨⟨h_value.trans_ne hy_ne, ?_⟩, h_value⟩
    rw [← mulVec_sub, ← mulVec_smul]
    exact (mulVec_mem_intVectors_iff (hH hk)).2 hy_int
  refine ⟨Φ, ?_, ?_, fun k hk x ↦ ?_, fun x hx ↦ ?_⟩
  · -- The support lies in `C + u • L`.
    refine HasCompactSupport.intro (hC.add (hL_compact.smul u)) fun x hx ↦
      Φ_zero x fun ⟨y, hy_ne, hy_int⟩ ↦ hx ?_
    have h_diff : u • (u⁻¹ • (x - y)) = x - y := smul_inv_smul u _
    exact ⟨y, (h_supp y hy_ne).1, x - y, ⟨u⁻¹ • (x - y), hy_int, h_diff⟩, add_sub_cancel y x⟩
  · -- Translation by `u • L` keeps the classes.
    have h_small : ∀ᶠ v : n → A in nhds 0, u⁻¹ • v ∈ intVectors P.integers n :=
      (hL_open.preimage (continuous_const_smul u⁻¹)).mem_nhds (by simp)
    filter_upwards [h_small] with v hv x
    have h_iff (y : n → A) : Near (x + v) y ↔ Near x y := by
      simp [Near, add_sub_right_comm, add_mem_cancel_right hv]
    exact Φ_congr x (x + v) (fun y hy ↦ ⟨y, (h_iff y).2 hy, rfl⟩) fun y hy ↦ ⟨y, (h_iff y).1 hy⟩
  · -- The matrices `k` and `k⁻¹` exchange the near points of `x` and of `k *ᵥ x`.
    refine Φ_congr x ((k : GL n A).val *ᵥ x)
      (fun y hy ↦ ⟨(k : GL n A).val *ᵥ y, move k hk x y hy⟩) fun y hy ↦ ?_
    have h_back : Near (((k⁻¹ : G) : GL n A).val *ᵥ (k : GL n A).val *ᵥ x)
        (((k⁻¹ : G) : GL n A).val *ᵥ y) :=
      (move k⁻¹ (inv_mem hk) ((k : GL n A).val *ᵥ x) y hy).1
    exact ⟨((k⁻¹ : G) : GL n A).val *ᵥ y, by simpa using h_back⟩
  · by_cases h_near : ∃ y : n → A, Near x y
    · obtain ⟨y, hy⟩ : ∃ y : n → A, Near x y := h_near
      rw [Φ_eq x y hy, const x y hx hy]
    · have h_zero : φ x = 0 := by_contra fun h_ne ↦ h_near ⟨x, h_ne, by simp⟩
      rw [Φ_zero x h_near, h_zero]

/-- The coordinate `(i, j)` of the orbital integral tensor `∫ W y ⊗ (W (γ⁻¹ * y))^* ∂μ`. -/
lemma besselOrbitalIntegral_apply {G I : Type*} [Group G] [MeasurableSpace G] (μ : Measure G)
    (W : G → EuclideanSpace ℂ I) (γ : G) (i j : I) :
    besselOrbitalIntegral μ W γ (i, j) = ∫ y : G, W y i * starRingEnd ℂ (W (γ⁻¹ * y) j) ∂μ :=
  rfl

/-- The orbital integral tensor `∫ W y ⊗ (W (γ⁻¹ * y))^* ∂μ` depends only on the values
`W (γ⁻¹ * y)` at the points `y` with `W y ≠ 0`. -/
lemma besselOrbitalIntegral_congr {G I : Type*} [Group G] [MeasurableSpace G] (μ : Measure G)
    {W : G → EuclideanSpace ℂ I} {γ γ' : G}
    (h_eq : ∀ y : G, W y ≠ 0 → W (γ⁻¹ * y) = W (γ'⁻¹ * y)) :
    besselOrbitalIntegral μ W γ = besselOrbitalIntegral μ W γ' := by
  ext ⟨i, j⟩
  rw [besselOrbitalIntegral_apply, besselOrbitalIntegral_apply]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  by_cases hy : W y = 0
  · simp [hy]
  · simp only [h_eq y hy]

/-- If the orbital integral tensor `∫ W y ⊗ (W (γ⁻¹ * y))^* ∂μ` is not zero, then `W y` and
`W (γ⁻¹ * y)` are both nonzero for some `y`. -/
lemma exists_ne_zero_of_besselOrbitalIntegral_ne_zero {G I : Type*} [Group G] [MeasurableSpace G]
    {μ : Measure G} {W : G → EuclideanSpace ℂ I} {γ : G} (h_ne : besselOrbitalIntegral μ W γ ≠ 0) :
    ∃ y : G, W y ≠ 0 ∧ W (γ⁻¹ * y) ≠ 0 := by
  by_contra! h_zero
  refine h_ne (PiLp.ext fun (i, j) ↦ ?_)
  rw [besselOrbitalIntegral_apply]
  refine integral_eq_zero_of_ae (.of_forall fun y ↦ ?_)
  by_cases hy : W y = 0
  · simp [hy]
  · simp [h_zero y hy]

/-- Two units of a finite place whose quotient is a unit of the ring of integers `O` (also written
`P.integers`) have the same modulus. -/
lemma IntegralPlace.modulus_eq_of_inv_mul_mem_units {A : Type} [SemilocalField A] [StarRing A]
    [P : IntegralPlace A] {a b : Aˣ} (hab : a⁻¹ * b ∈ (O : Subring A).units) :
    P.modulus b = P.modulus a := by
  obtain ⟨h_int, h_inv_int⟩ : (a⁻¹ * b).val ∈ O ∧ (a⁻¹ * b)⁻¹.val ∈ O :=
    (Submonoid.mem_units_iff _ _).1 hab
  have h_inv_le : (P.modulus (a⁻¹ * b : Aˣ))⁻¹ ≤ 1 :=
    (P.modulus_inv (a⁻¹ * b)).symm.trans_le (modulus_le_one _ h_inv_int)
  have h_one : P.modulus (a⁻¹ * b : Aˣ) = 1 :=
    (modulus_le_one _ h_int).antisymm (ENNReal.inv_le_one.1 h_inv_le)
  calc P.modulus b
    _ = P.modulus a * P.modulus (a⁻¹ * b : Aˣ) := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel_left]
    _ = P.modulus a := by rw [h_one, mul_one]

section Correlation


variable {A ι : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A] {m : ℕ} {T : 𝔰.Form A}
  [P : IntegralPlace A] [IsHermitianUnit T.splitGram] [Fintype ι] [DecidableEq ι]
  {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup) (p q : ℕ → Aˣ)

/-- The normalized orbital integral at the element `w_p l⁻¹` with head `p` and link `l⁻¹`, where
`w_p` is the Weyl element `weylElem 𝔰.ϱ p`: the density `F.headDensity 𝔰.ϱ p 1` times the
correlations of the finite Bessel vector of `Z` with its translate by `w_p l⁻¹`, indexed by pairs of
cosets. Functions of the link are written below as functions of its inverse `l`. -/
def PlaceData.scaledOrbitalIntegral (l : T.G) : EuclideanSpace ℂ (Z.Cosets × Z.Cosets) :=
  (F.headDensity 𝔰.ϱ p 1).toReal •
    besselOrbitalIntegral F.groupMeasure Z.besselVector (weylElem 𝔰.ϱ p * l⁻¹)

/-- The coordinate of the finite Bessel vector of `Z` at a coset `c` of `F.congruenceSubgroup` in
`Z`, in terms of the chosen representative `c.out`. -/
lemma PlaceData.besselVector_apply (x : T.G) (c : Z.Cosets) :
    Z.besselVector x c = P.extendedBesselChar F.levelUnit (x * (c.out : T.G)⁻¹) :=
  rfl

/-- Let `F` be a place datum of the form `T`, whose Gram matrix `T.splitGram` is hermitian and
invertible, and let `Z` be a group between `F.congruenceSubgroup` and the integral unitary group.
The finite Bessel vector of `Z`, whose coordinates are right translates of the Bessel function
`P.extendedBesselChar F.levelUnit`, is left invariant under the elements of `F.congruenceSubgroup`
in `besselH`, the fixer of the hyperbolic pairs and the last frame vector. -/
lemma PlaceData.besselVector_mul_left {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    {k : T.G} (hk : k ∈ besselH ⊓ F.congruenceSubgroup) (x : T.G) :
    Z.besselVector (k * x) = Z.besselVector x := by
  obtain ⟨hk_fix, hk_cong⟩ : k ∈ besselH ∧ k ∈ F.congruenceSubgroup := Subgroup.mem_inf.1 hk
  have h_phase (y : T.G) : P.extendedBesselChar F.levelUnit (k * y) = P.extendedBesselChar
    F.levelUnit y := by
    -- `k` lies in the coset `1 * F.congruenceSubgroup`, and the character of `1` is trivial.
    have h_mul : P.extendedBesselChar F.levelUnit (k * y) =
        P.ψ (F.levelUnit⁻¹.val * simpleRootSum (1 : T.G)) * P.extendedBesselChar F.levelUnit y :=
      P.extendedBesselChar_besselS_mul (mem_partialUnitriangularGroup_of_mem_floorGroup hk_fix)
        (one_mem besselU)
        (by simpa using hk_cong)
    simpa [simpleRootSum_eq_zero_of_mem_besselH (one_mem T.besselH)] using h_mul
  ext c
  rw [besselVector_apply, besselVector_apply, mul_assoc, h_phase]

/-- The finite Bessel vector of `Z`, whose coordinates are translates of the Bessel function
`P.extendedBesselChar F.levelUnit`, is right invariant under the congruence group
`F.congruenceSubgroup`, which `Z` normalises. -/
lemma PlaceData.besselVector_mul_right (x : T.G) {k : T.G} (hk : k ∈ F.congruenceSubgroup) :
    Z.besselVector (x * k) = Z.besselVector x := by
  ext c
  rw [besselVector_apply, besselVector_apply]
  set z : T.G := (c.out : T.G)
  have hZ : (Z : Subgroup T.G) ≤ unitaryLevel P.integers 1 T.splitGram :=
    (Set.mem_Icc.1 Z.property).2
  have h_conj : z * k * z⁻¹ ∈ F.congruenceSubgroup := conj_mem_unitaryLevel (hZ c.out.property) hk
  calc P.extendedBesselChar F.levelUnit (x * k * z⁻¹)
    _ = P.extendedBesselChar F.levelUnit (x * z⁻¹ * (z * k * z⁻¹)) := by simp [mul_assoc]
    _ = P.extendedBesselChar F.levelUnit (x * z⁻¹) :=
      P.extendedBesselChar_mul_of_mem_unitaryLevel h_conj

/-- The finite Bessel vector of `Z` is a continuous function on the unitary group `T.G`. -/
@[fun_prop] lemma PlaceData.continuous_besselVector : Continuous Z.besselVector := by
  fun_prop [IntermediateGroup.besselVector]

/-- The integrand of the pairing of the scaled orbital integrals with heads `p`, `q` at the inverse
link `l`, on two copies of the group: with `W` the finite Bessel vector of `Z`, its value at
`(y₁, y₂)` is `⟪W y₁, W y₂⟫ * ⟪W ((w_q l⁻¹)⁻¹ y₂), W ((w_p l⁻¹)⁻¹ y₁)⟫`. -/
def PlaceData.unfoldedPairing (l : T.G) (y : T.G × T.G) : ℂ :=
  ⟪Z.besselVector y.1, Z.besselVector y.2⟫_ℂ *
    ⟪Z.besselVector ((weylElem 𝔰.ϱ q * l⁻¹)⁻¹ * y.2),
      Z.besselVector ((weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * y.1)⟫_ℂ

/-- The integrand `unfoldedPairing Z p q l y` is continuous in the inverse link `l` and the pair
`y` of group variables together. -/
@[fun_prop] lemma PlaceData.continuous_unfoldedPairing :
    Continuous fun z : T.G × T.G × T.G ↦ unfoldedPairing Z p q z.1 z.2 := by
  fun_prop [unfoldedPairing]

omit [IntegralPlace A] [IsHermitianUnit T.splitGram] in
/-- Factors in `besselH`, the fixer of the hyperbolic pairs and the last frame vector, do not change
the last diagonal entry of `T.frameGram x`, the matrix of products of the frame with its image under
`x`: for `g`, `k` in `besselH` the entries at `g x k` and at `x` agree. -/
lemma frameGram_top_eq_of_mem_besselH {g k : T.G} (hg : g ∈ T.besselH) (hk : k ∈ T.besselH)
    (x : T.G) :
    T.frameGram (g * x * k : T.G) 𝔰.top 𝔰.top = T.frameGram x 𝔰.top 𝔰.top := by
  have h_le : T.besselH ≤ T.partialUnitriangularGroup (𝔰.top + 1) ⊓ T.floorGroup 𝔰.top :=
    partialUnitriangularGroup_inf_floorGroup_last.ge
  have h_left (y : T.G) : T.frameGram (g * y : T.G) 𝔰.top 𝔰.top = T.frameGram y 𝔰.top 𝔰.top :=
    (frameGram_diag_mul (h_le hg) y).1
  have h_right (y : T.G) : T.frameGram (y * k : T.G) 𝔰.top 𝔰.top = T.frameGram y 𝔰.top 𝔰.top :=
    (frameGram_diag_mul (h_le hk) y).2
  rw [h_right, h_left]

/-- For `s` in the floor group `T.floorGroup 𝔰.ϱ`, which commutes with the Weyl element
`weylElem 𝔰.ϱ r` (written `w_r`), one has `(w_r * (a * s⁻¹)⁻¹)⁻¹ * (s * x) = a * w_r⁻¹ * x` for all
`a`, `x`. -/
lemma inv_weylElem_mul_inv_mul {A : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A]
    {T : 𝔰.Form A} [IsHermitianUnit T.splitGram] {s : T.G} (hs : s ∈ T.floorGroup 𝔰.ϱ) (a x : T.G)
    (r : ℕ → Aˣ) :
    (weylElem 𝔰.ϱ r * (a * s⁻¹)⁻¹)⁻¹ * (s * x) = a * (weylElem 𝔰.ϱ r)⁻¹ * x :=
  calc (weylElem 𝔰.ϱ r * (a * s⁻¹)⁻¹)⁻¹ * (s * x)
    _ = a * s⁻¹ * ((weylElem 𝔰.ϱ r)⁻¹ * (s * x)) := by group
    _ = a * s⁻¹ * (s * ((weylElem 𝔰.ϱ r)⁻¹ * x)) := by rw [(weylElem_mul_left_comm hs).2]
    _ = a * (weylElem 𝔰.ϱ r)⁻¹ * x := by group

namespace IntegralPlace.IsLargeLatticeData

/-- At a large lattice datum `F`, some `Γ : Gauge F` (a scale: a notion of size with a loss
Λ = `Γ.loss`) makes every sequence of units `r` near `p`, and every one near `q`, a head of length
`𝔰.ϱ` (`Γ.IsHead 𝔰.ϱ r`). This means that the inverses of the products `r 0 * ⋯ * r (l-1)`,
`l ≤ 𝔰.ϱ`, have size 1. -/
lemma exists_gauge_isHead {F : PlaceData ι T (m + 1)} (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] :
    ∃ Γ : Gauge F,
      (∀ᶠ r : ℕ → Aˣ in nhds p, Γ.IsHead 𝔰.ϱ r) ∧
      ∀ᶠ r : ℕ → Aˣ in nhds q, Γ.IsHead 𝔰.ϱ r := by
  -- Take the gauge of scale `star α * α` for a unit `α` close to `0`: as `O` is open, this scale
  -- absorbs the finitely many inverse products, locally uniformly in the head.
  -- `Bounded a r` says that these products have size `1` for the scale `star a * a`.
  let Bounded (a : A) (r : ℕ → Aˣ) : Prop :=
    ∀ i ≤ 𝔰.ϱ, (star a * a) ^ 1 * (∏ l ∈ range i, r l)⁻¹.val ∈ O
  have near (r₀ : ℕ → Aˣ) : ∀ᶠ a : A in nhds 0, ∀ᶠ r : ℕ → Aˣ in nhds r₀, Bounded a r := by
    refine Eventually.curry_nhds (p := fun z : A × (ℕ → Aˣ) ↦ Bounded z.1 z.2) ?_
    refine (finite_le_nat 𝔰.ϱ).eventually_all.2 fun i _ ↦ ?_
    have h_cont : Continuous fun z : A × (ℕ → Aˣ) ↦
        (star z.1 * z.1) ^ 1 * (∏ l ∈ range i, z.2 l)⁻¹.val := by fun_prop
    -- At `a = 0` the value is `0`, which lies in the open set `O`.
    exact h_cont.continuousAt.eventually_mem (isOpen_O.mem_nhds (by simp))
  -- Units are dense, since almost every element is a unit.
  obtain ⟨_, ⟨α, rfl⟩, hp, hq⟩ : ∃ a : A, IsUnit a ∧
      (∀ᶠ r : ℕ → Aˣ in nhds p, Bounded a r) ∧ ∀ᶠ r : ℕ → Aˣ in nhds q, Bounded a r :=
    (dense_of_ae P.ae_isUnit).inter_nhds_nonempty ((near p).and (near q))
  have hp_zero : (star α.val * α.val) ^ 1 * (∏ l ∈ range 0, p l)⁻¹.val ∈ O :=
    hp.self_of_nhds 0 (Nat.zero_le _)
  have α_int : (star α * α).val ∈ P.integers := by simpa using hp_zero
  have α_star : star (star α * α).val = (star α * α).val := by simp [mul_comm]
  let Γ : Gauge F := gauge (star α * α) α_int α_star
  have isHead_iff (r : ℕ → Aˣ) : Γ.IsHead 𝔰.ϱ r ↔ Bounded α r := Iff.rfl
  exact ⟨Γ, by simpa only [isHead_iff] using hp, by simpa only [isHead_iff] using hq⟩

/-- Let `F` be a large lattice datum. The scaled orbital integral `scaledOrbitalIntegral Z p l` is a
density depending on `p` times `∫ W y ⊗ (W (l w_p⁻¹ y))^*` over the unitary group, with `W` the
finite Bessel vector of `Z` and `w_p` the Weyl element of the head `p`. For `z = (r, s)` near
`(p, 1)` with `s` in the floor group G^(ϱ), it does not change when `p` is replaced by `r` and `l`
by `l * s`, for all `l` in G^(ϱ) at once. -/
lemma eventually_scaledOrbitalIntegral_mul_eq_self {F : PlaceData ι T (m + 1)}
    (Z : F.IntermediateGroup) (p : ℕ → Aˣ) [h : P.IsLargeLatticeData F] :
    ∀ᶠ z : (ℕ → Aˣ) × T.G in nhds (p, 1), z.2 ∈ T.floorGroup 𝔰.ϱ →
      ∀ l ∈ T.floorGroup 𝔰.ϱ, scaledOrbitalIntegral Z z.1 (l * z.2) = scaledOrbitalIntegral Z p
        l := by
  -- For heads of a gauge, the integrand defining `scaledOrbitalIntegral` vanishes off the compact
  -- set `C` (`Gauge.hasMatrixSize_of_ne_zero`). For `z` near `(p, 1)` the argument changes, for all
  -- `y` in `C`, by a right translation from `F.congruenceSubgroup`.
  obtain ⟨Γ, head_p, -⟩ : ∃ Γ : Gauge F, (∀ᶠ r : ℕ → Aˣ in nhds p, Γ.IsHead 𝔰.ϱ r) ∧
      ∀ᶠ r : ℕ → Aˣ in nhds p, Γ.IsHead 𝔰.ϱ r := h.exists_gauge_isHead p p
  let C : Set T.G := {y : T.G | Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (y : GL 𝔰.BesselIndex A).val}
  have cong_open : IsOpen (F.congruenceSubgroup : Set T.G) := unitaryLevel_open_compact.1
  have near_cong : ∀ᶠ z : (ℕ → Aˣ) × T.G in nhds (p, 1), ∀ y ∈ C,
      y⁻¹ * weylElem 𝔰.ϱ p * z.2 * (weylElem 𝔰.ϱ z.1)⁻¹ * y ∈ F.congruenceSubgroup :=
    Γ.isCompact_hasMatrixSize.eventually_forall_of_forall_eventually fun y _ ↦
      -- At `(p, 1)` the product is `1`, which lies in the open group `F.congruenceSubgroup`.
      (cong_open.preimage (by fun_prop)).mem_nhds (by simp)
  have near_unit : ∀ᶠ r : ℕ → Aˣ in nhds p, ∀ j ∈ range 𝔰.ϱ, (p j)⁻¹ * r j ∈ O.units := by
    refine (range 𝔰.ϱ).eventually_all.2 fun j _ ↦ ?_
    have h_cont : Continuous fun r : ℕ → Aˣ ↦ (p j)⁻¹ * r j := by fun_prop
    exact h_cont.continuousAt.eventually_mem ((O.isOpen_units isOpen_O).mem_nhds (by simp))
  filter_upwards [near_cong, continuousAt_fst (head_p.and near_unit)]
    with ⟨r, s⟩ h_cong ⟨head_r, h_unit⟩ hs l hl
  have modulus_eq (j : ℕ) (hj : j ∈ range 𝔰.ϱ) : P.modulus (r j) = P.modulus (p j) :=
    modulus_eq_of_inv_mul_mem_units (h_unit j hj)
  have density_eq : F.headDensity 𝔰.ϱ r 1 = F.headDensity 𝔰.ϱ p 1 := by
    unfold headDensity
    exact prod_congr rfl fun j hj ↦ by simp [modulus_eq j hj]
  have W_eq (y : T.G) (hy : Z.besselVector y ≠ 0) :
      Z.besselVector ((weylElem 𝔰.ϱ r * (l * s)⁻¹)⁻¹ * y) =
        Z.besselVector ((weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * y) := by
    by_contra h_ne
    -- One of the two values is nonzero; with `Z.besselVector y ≠ 0` this puts `y` in `C`.
    have hC : y ∈ C := by
      obtain h_r | h_p : Z.besselVector ((weylElem 𝔰.ϱ r * (l * s)⁻¹)⁻¹ * y) ≠ 0 ∨
          Z.besselVector ((weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * y) ≠ 0 := Ne.ne_or_ne 0 h_ne
      · exact Γ.hasMatrixSize_of_ne_zero (isCut_besselVector Z) head_r (inv_mem (mul_mem hl hs)) hy
          h_r
      · exact Γ.hasMatrixSize_of_ne_zero (isCut_besselVector Z) head_p.self_of_nhds (inv_mem hl) hy
          h_p
    have h_arg : (weylElem 𝔰.ϱ r * (l * s)⁻¹)⁻¹ * y =
        (weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * y *
          (y⁻¹ * weylElem 𝔰.ϱ p * s * (weylElem 𝔰.ϱ r)⁻¹ * y) := by
      group
    exact h_ne (by rw [h_arg, besselVector_mul_right Z _ (h_cong y hC)])
  rw [scaledOrbitalIntegral, scaledOrbitalIntegral, density_eq,
    besselOrbitalIntegral_congr F.groupMeasure W_eq]

/-- Let `F` be a large lattice datum. The scaled orbital integral `scaledOrbitalIntegral Z p l`
vanishes for `l` in the floor group `T.floorGroup 𝔰.ϱ` outside some compact set. -/
lemma exists_isCompact_scaledOrbitalIntegral_support {F : PlaceData ι T (m + 1)}
    (Z : F.IntermediateGroup) (p : ℕ → Aˣ) [h : P.IsLargeLatticeData F] :
    ∃ C : Set T.G, IsCompact C ∧ ∀ l ∈ T.floorGroup 𝔰.ϱ,
      scaledOrbitalIntegral Z p l ≠ 0 → l ∈ C := by
  -- If the integral at `l` is not zero, some `y` and `y' = l w⁻¹ y` lie in the compact set `S`,
  -- where `w` is the Weyl element of `p`, and `l = y' y⁻¹ w`.
  obtain ⟨Γ, hp⟩ : ∃ Γ : Gauge F, Γ.IsHead 𝔰.ϱ p :=
    (h.exists_gauge_isHead p p).imp fun Γ ⟨h_near, _⟩ ↦ h_near.self_of_nhds
  have h_cut : F.IsCut Z.besselVector := isCut_besselVector Z
  let S : Set T.G := {y : T.G | Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (y : GL 𝔰.BesselIndex A).val}
  have hS : IsCompact S := Γ.isCompact_hasMatrixSize
  refine ⟨(fun (y, y') ↦ y' * y⁻¹ * weylElem 𝔰.ϱ p) '' S ×ˢ S,
    (hS.prod hS).image (by fun_prop), fun l hl h_ne ↦ ?_⟩
  obtain ⟨y, hy, hy'⟩ : ∃ y : T.G, Z.besselVector y ≠ 0 ∧
      Z.besselVector ((weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * y) ≠ 0 :=
    exists_ne_zero_of_besselOrbitalIntegral_ne_zero (right_ne_zero_of_smul h_ne)
  have y_mem : y ∈ S := Γ.hasMatrixSize_of_ne_zero h_cut hp (inv_mem hl) hy hy'
  set y' : T.G := (weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * y
  -- The two points change roles for the head `star p` and the link `l`.
  have h_back : (weylElem 𝔰.ϱ (star p) * l)⁻¹ * y' = y := by
    simp [y', mul_assoc, (weylElem_mul_left_comm hl).1]
  have y'_mem : y' ∈ S := Γ.hasMatrixSize_of_ne_zero h_cut hp.star_head hl hy' (by rwa [h_back])
  exact ⟨(y, y'), ⟨y_mem, y'_mem⟩, by simp [y', mul_assoc]⟩

/-- At a large lattice datum `F` and for `l` in the floor group G^(ϱ), the pairing of the scaled
orbital integrals with heads `p`, `q` at `l` is the density `F.headDensity 𝔰.ϱ p q` of the two heads
times the integral of the integrand `unfoldedPairing Z p q l` over two copies of the group. -/
lemma inner_scaledOrbitalIntegral {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    ⟪scaledOrbitalIntegral Z p l, scaledOrbitalIntegral Z q l⟫_ℂ = (F.headDensity 𝔰.ϱ p q).toReal *
      ∫ y : T.G × T.G, unfoldedPairing Z p q l y ∂F.groupMeasure.prod F.groupMeasure := by
  obtain ⟨Γ, hp, hq⟩ : ∃ Γ : Gauge F, (∀ᶠ r : ℕ → Aˣ in nhds p, Γ.IsHead 𝔰.ϱ r) ∧
      ∀ᶠ r : ℕ → Aˣ in nhds q, Γ.IsHead 𝔰.ϱ r := h.exists_gauge_isHead p q
  have h_density : ((F.headDensity 𝔰.ϱ p q).toReal : ℂ) =
      (F.headDensity 𝔰.ϱ p 1).toReal * (F.headDensity 𝔰.ϱ q 1).toReal := by
    simp [headDensity, mul_rpow_of_nonneg, mul_pow, prod_mul_distrib]
  have h_inner : ⟪besselOrbitalIntegral F.groupMeasure Z.besselVector (weylElem 𝔰.ϱ p * l⁻¹),
      besselOrbitalIntegral F.groupMeasure Z.besselVector (weylElem 𝔰.ϱ q * l⁻¹)⟫_ℂ =
        ∫ y : T.G × T.G, unfoldedPairing Z p q l y ∂F.groupMeasure.prod F.groupMeasure := by
    simpa only [unfoldedPairing, inner_conj_symm] using
      Γ.inner_besselOrbitalIntegral (μ := F.groupMeasure) (isCut_besselVector Z)
        (continuous_besselVector Z) hp.self_of_nhds hq.self_of_nhds (inv_mem hl)
  rw [scaledOrbitalIntegral, scaledOrbitalIntegral, inner_smul_left_eq_smul,
    inner_smul_right_eq_smul, h_inner,
    h_density]
  simp [mul_assoc]

/-- Let `p` and `q` be heads for a gauge `Γ` of a large lattice datum, and let `l` lie in the floor
group G^(ϱ). If the integrand `unfoldedPairing Z p q l` of the pairing of the scaled orbital
integrals is nonzero at `(y₁, y₂)`, then the entries of `y₁` and `y₂` have size `60 * 𝔰.n ^ 2` for
`Γ`. -/
lemma hasMatrixSize_of_unfoldedPairing_ne_zero {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    {p q : ℕ → Aˣ} [h : P.IsLargeLatticeData F] {Γ : Gauge F} (hp : Γ.IsHead 𝔰.ϱ p)
      (hq : Γ.IsHead 𝔰.ϱ q)
    {l y₁ y₂ : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) (h_ne : unfoldedPairing Z p q l (y₁, y₂) ≠ 0) :
    Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (y₁ : GL 𝔰.BesselIndex A).val ∧
      Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (y₂ : GL 𝔰.BesselIndex A).val := by
  -- Both inner products in the integrand are nonzero, hence so are all four vectors.
  have h_cut : F.IsCut Z.besselVector := isCut_besselVector Z
  have h₁ : Z.besselVector y₁ ≠ 0 := fun h_zero ↦ h_ne (by simp [unfoldedPairing, h_zero])
  have h₂ : Z.besselVector y₂ ≠ 0 := fun h_zero ↦ h_ne (by simp [unfoldedPairing, h_zero])
  have h₁' : Z.besselVector ((weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * y₁) ≠ 0 := fun h_zero ↦
    h_ne (by simp only [unfoldedPairing, h_zero, inner_zero_right, mul_zero])
  have h₂' : Z.besselVector ((weylElem 𝔰.ϱ q * l⁻¹)⁻¹ * y₂) ≠ 0 := fun h_zero ↦
    h_ne (by simp only [unfoldedPairing, h_zero, inner_zero_left, mul_zero])
  exact ⟨Γ.hasMatrixSize_of_ne_zero h_cut hp (inv_mem hl) h₁ h₁',
    Γ.hasMatrixSize_of_ne_zero h_cut hq (inv_mem hl) h₂ h₂'⟩

/-- At a large lattice datum `F` there is a finite constant `C` such that the integral over `k` of
the norm of the integrand `unfoldedPairing Z p q (k * l) (y₁, y₂)` is at most `C` times the norm of
`⟪W y₁, W y₂⟫`, with `W` the finite Bessel vector of `Z`. Here `k` is integrated against
`F.quotientMeasureFrom i`, the convolution of the measures of the floors from `i` on. -/
lemma exists_lintegral_enorm_unfoldedPairing_le {F : PlaceData ι T (m + 1)}
    (Z : F.IntermediateGroup) (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] (i : ℕ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ l y₁ y₂ : T.G,
      ∫⁻ k : T.G, ‖unfoldedPairing Z p q (k * l) (y₁, y₂)‖ₑ ∂F.quotientMeasureFrom i ≤
        ‖⟪Z.besselVector y₁, Z.besselVector y₂⟫_ℂ‖ₑ * C := by
  obtain ⟨Γ, -⟩ := h.exists_gauge_isHead p q
  let W : T.G → EuclideanSpace ℂ Z.Cosets := Z.besselVector
  -- The integrals `∫ ‖⟪W (k * a), W (k * b)⟫_ℂ‖` over these floors are at most `C < ∞`.
  obtain ⟨C, hC, h_bd⟩ : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a b : T.G,
      ∫⁻ k, ‖frameCorrelation W 1 (k * a) (k * b)‖ₑ ∂F.quotientMeasureFrom i ≤ C :=
    (Γ.isPairingKernel_frameCorrelation_one (isCut_besselVector Z) 0).exists_lintegral_le i
  refine ⟨C, hC, fun l y₁ y₂ ↦ ?_⟩
  let a : T.G := l * ((weylElem 𝔰.ϱ q)⁻¹ * y₂)
  let b : T.G := l * ((weylElem 𝔰.ϱ p)⁻¹ * y₁)
  have h_pair : ∫⁻ k, ‖⟪W (k * a), W (k * b)⟫_ℂ‖ₑ ∂F.quotientMeasureFrom i ≤ C := by
    simpa [W, frameCorrelation] using h_bd a b
  calc ∫⁻ k, ‖unfoldedPairing Z p q (k * l) (y₁, y₂)‖ₑ ∂F.quotientMeasureFrom i
    _ = ‖⟪W y₁, W y₂⟫_ℂ‖ₑ * ∫⁻ k, ‖⟪W (k * a), W (k * b)⟫_ℂ‖ₑ ∂F.quotientMeasureFrom i := by
      simp [W, a, b, unfoldedPairing, mul_assoc, ← ofReal_norm, lintegral_const_mul']
    _ ≤ ‖⟪W y₁, W y₂⟫_ℂ‖ₑ * C := by gcongr

/-- Let `F` be a large lattice datum, `i ≥ 𝔰.ϱ`, and `l` in the floor group `T.floorGroup 𝔰.ϱ`. The
integrand `unfoldedPairing Z p q (k * l) (y₁, y₂)` of the pairing of the scaled orbital integrals at
`k * l` is integrable in `(k, y₁, y₂)`. Here `k` is integrated against `F.quotientMeasureFrom i`,
the convolution of the measures of the floors from `i` on. -/
lemma integrable_unfoldedPairing {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ)
    [h : P.IsLargeLatticeData F] {i : ℕ} (hi : 𝔰.ϱ ≤ i) {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    Integrable (fun z : T.G × T.G × T.G ↦ unfoldedPairing Z p q (z.1 * l) z.2)
      ((F.quotientMeasureFrom i).prod (F.groupMeasure.prod F.groupMeasure)) := by
  -- The integral of the norm over `k` is bounded by a continuous function of the two group
  -- variables, and it vanishes off a compact set.
  obtain ⟨Γ, hp, hq⟩ : ∃ Γ : Gauge F, (∀ᶠ r : ℕ → Aˣ in nhds p, Γ.IsHead 𝔰.ϱ r) ∧
      ∀ᶠ r : ℕ → Aˣ in nhds q, Γ.IsHead 𝔰.ϱ r := h.exists_gauge_isHead p q
  let Φ (k : T.G) (y : T.G × T.G) : ℂ := unfoldedPairing Z p q (k * l) y
  let B (y : T.G × T.G) : ℂ := ⟪Z.besselVector y.1, Z.besselVector y.2⟫_ℂ
  have : BorelSpace (T.G × T.G) := Prod.borelSpace
  have hΦ : Measurable (uncurry Φ) := Continuous.measurable (by fun_prop)
  have hB : Continuous B := by fun_prop
  let M₂ : Measure (T.G × T.G) := F.groupMeasure.prod F.groupMeasure
  obtain ⟨C, hC, h_le⟩ : ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ y : T.G × T.G, ∫⁻ k, ‖Φ k y‖ₑ ∂F.quotientMeasureFrom i ≤ ‖B y‖ₑ * C :=
    (exists_lintegral_enorm_unfoldedPairing_le Z p q i).imp
      fun C ⟨hC, h_bd⟩ ↦ ⟨hC, fun (y₁, y₂) ↦ h_bd l y₁ y₂⟩
  let S : Set T.G := {y : T.G | Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (y : GL 𝔰.BesselIndex A).val}
  have hS : IsCompact S := Γ.isCompact_hasMatrixSize
  have h_supp : support (fun y : T.G × T.G ↦ ∫⁻ k, ‖Φ k y‖ₑ ∂F.quotientMeasureFrom i) ⊆ S ×ˢ S := by
    rintro ⟨y₁, y₂⟩ hy
    obtain ⟨k, hk, h_ne⟩ : ∃ k ∈ T.floorGroup i, ‖Φ k (y₁, y₂)‖ₑ ≠ 0 :=
      exists_ne_zero_of_ae (ae_descConv_mem ae_floorMeasure_mem) hy
    exact hasMatrixSize_of_unfoldedPairing_ne_zero Z hp.self_of_nhds hq.self_of_nhds
      (mul_mem (floorGroup_anti hi hk) hl) (enorm_ne_zero.1 h_ne)
  have hB_int : IntegrableOn B (S ×ˢ S) M₂ := hB.continuousOn.integrableOn_compact (hS.prod hS)
  refine ⟨hΦ.aestronglyMeasurable, ?_⟩
  calc ∫⁻ z, ‖uncurry Φ z‖ₑ ∂(F.quotientMeasureFrom i).prod M₂
    _ = ∫⁻ y, ∫⁻ k, ‖Φ k y‖ₑ ∂F.quotientMeasureFrom i ∂M₂ :=
      lintegral_prod_symm _ hΦ.enorm.aemeasurable
    _ = ∫⁻ y in S ×ˢ S, ∫⁻ k, ‖Φ k y‖ₑ ∂F.quotientMeasureFrom i ∂M₂ :=
      (setLIntegral_eq_of_support_subset h_supp).symm
    _ ≤ ∫⁻ y in S ×ˢ S, ‖B y‖ₑ * C ∂M₂ := lintegral_mono h_le
    _ = (∫⁻ y in S ×ˢ S, ‖B y‖ₑ ∂M₂) * C := lintegral_mul_const' C _ hC.ne
    _ < ∞ := ENNReal.mul_lt_top hB_int.hasFiniteIntegral hC

/-- If `F` is a large lattice datum and `l` lies in `T.floorGroup 𝔰.ϱ`, the group fixing every basis
vector of floor below `𝔰.ϱ`, then the inner product of `scaledOrbitalIntegral Z p (k * l)` and
`scaledOrbitalIntegral Z q (k * l)` is integrable in `k` for `F.measureH`. -/
lemma integrable_inner_scaledOrbitalIntegral {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] {l : T.G} (hl : l ∈ T.floorGroup 𝔰.ϱ) :
    Integrable (fun k : T.G ↦ ⟪scaledOrbitalIntegral Z p (k * l),
      scaledOrbitalIntegral Z q (k * l)⟫_ℂ) F.measureH := by
  have h_mem : ∀ᵐ k : T.G ∂F.measureH, k ∈ besselH := F.ae_measureH_mem_besselH
  have h_top : F.quotientMeasureFrom 𝔰.ϱ.succ = F.measureH := by simp [descConv]
  have h_int : Integrable (fun k : T.G ↦ ∫ y : T.G × T.G, unfoldedPairing Z p q (k * l) y
      ∂F.groupMeasure.prod F.groupMeasure) F.measureH := by
    rw [← h_top]
    exact (integrable_unfoldedPairing Z p q 𝔰.ϱ.le_succ hl).integral_prod_left
  refine (h_int.const_mul (F.headDensity 𝔰.ϱ p q).toReal).congr ?_
  filter_upwards [h_mem] with k hk
  exact (inner_scaledOrbitalIntegral Z p q (mul_mem (floorGroup_anti 𝔰.ϱ.le_succ hk) hl)).symm

/-- For `a` and `s` in the floor group `T.floorGroup 𝔰.ϱ`, the integrand `unfoldedPairing Z p q` at
the inverse link `a * s⁻¹` and the pair `(s * y, s * y * x)` is ⟪W (s y), W (s y x)⟫ times ⟪W (r (a
w_p⁻¹ y) x), W (a w_p⁻¹ y)⟫. Here `W = Z.besselVector`, `w_p = weylElem 𝔰.ϱ p` and
`r = weylRatio 𝔰.ϱ p q = w_q⁻¹ w_p`. -/
lemma _root_.New.Floors.PlaceData.unfoldedPairing_mul_inv {F : PlaceData ι T (m + 1)}
    (Z : F.IntermediateGroup) (p q : ℕ → Aˣ) {a s : T.G} (ha : a ∈ T.floorGroup 𝔰.ϱ)
    (hs : s ∈ T.floorGroup 𝔰.ϱ) (x y : T.G) :
    unfoldedPairing Z p q (a * s⁻¹) (s * y, s * y * x) =
      ⟪Z.besselVector (s * y), Z.besselVector (s * y * x)⟫_ℂ *
        ⟪Z.besselVector (weylRatio 𝔰.ϱ p q * (a * (weylElem 𝔰.ϱ p)⁻¹ * y) * x),
          Z.besselVector (a * (weylElem 𝔰.ϱ p)⁻¹ * y)⟫_ℂ := by
  -- The Weyl elements commute with the floor group.
  have h_ratio : weylRatio 𝔰.ϱ p q * (a * (weylElem 𝔰.ϱ p)⁻¹ * y) * x =
      a * (weylElem 𝔰.ϱ q)⁻¹ * (y * x) := by
    rw [weylRatio, mul_assoc a, mul_assoc _ (weylElem 𝔰.ϱ p), (weylElem_mul_left_comm ha).1,
      (weylElem_mul_left_comm ha).2]
    group
  simp only [unfoldedPairing, mul_assoc s y x, inv_weylElem_mul_inv_mul hs, h_ratio]

/-- Let `F` be a large lattice datum and `φ` a measurable weight on the group, left and right
invariant under `besselH`, the fixer of the hyperbolic pairs and the last frame vector. Then `Φ`,
the integrand `unfoldedPairing Z p q` at `(l, y₁, y₂)` weighted by `φ l⁻¹`, and `Ψ`, the integrand
of the form `F.floorForm 𝔰.ϱ` with all its integrals written out, have the same law under the
product measures shown. -/
lemma identDistrib_unfoldedPairing {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup)
    (p q : ℕ → Aˣ) [h : P.IsLargeLatticeData F] {φ : T.G → ℂ} (hφ : Measurable φ)
    (hφ_inv : ∀ g ∈ T.besselH, ∀ k ∈ T.besselH, ∀ x : T.G, φ (g * x * k) = φ x) :
    let W : T.G → EuclideanSpace ℂ Z.Cosets := Z.besselVector
    let Φ : T.G × T.G × T.G → ℂ :=
      fun z : T.G × T.G × T.G ↦ φ z.1⁻¹ * unfoldedPairing Z p q z.1 z.2
    let Ψ : T.G × T.G × T.G × T.G × T.G × T.G → ℂ := fun (k, τ, g, σ, x, y) ↦
      let z : T.G := k * τ * (weylElem 𝔰.ϱ p)⁻¹ * y
      φ (σ * τ⁻¹) * ⟪W (g * σ * y), W (g * σ * y * x)⟫_ℂ * ⟪W (weylRatio 𝔰.ϱ p q * z * x), W z⟫_ℂ
    ProbabilityTheory.IdentDistrib Φ Ψ
      ((F.partialGroupMeasure 𝔰.ϱ 2).prod (F.groupMeasure.prod F.groupMeasure))
      (F.measureH.prod ((F.floorMeasure 𝔰.ϱ).prod (F.measureH.prod ((F.floorMeasure 𝔰.ϱ).prod
        (F.groupMeasure.prod (F.partialGroupMeasure 0 𝔰.ϱ)))))) := by
  -- Substitute `l = k τ (g σ)⁻¹`, `y₁ = g σ y` and `y₂ = y₁ x`, with `g`, `k` in `besselH` and `σ`,
  -- `τ` in G^(ϱ). The laws are compared by integrating a measurable `χ : ℂ → ℝ≥0∞`.
  intro W Φ Ψ
  have hW : Measurable W := (continuous_besselVector Z).measurable
  have hΨ : Measurable Ψ := by fun_prop
  have hΦ : Measurable Φ := by fun_prop
  refine ⟨hΦ.aemeasurable, hΨ.aemeasurable, ext_of_lintegral _ fun χ hχ ↦ ?_⟩
  let θ : Measure T.G := F.floorMeasure 𝔰.ϱ
  let η : Measure T.G := F.floorMeasure 𝔰.n
  have h_fiber (x y : T.G) {σ g : T.G} (hσ : σ ∈ floorGroup 𝔰.ϱ) (hg : g ∈ floorGroup 𝔰.n) :
      ∫⁻ l, χ (Φ (l, g * σ * y, g * σ * y * x)) ∂F.partialGroupMeasure 𝔰.ϱ 2 =
        ∫⁻ τ, ∫⁻ k, χ (Ψ (k, τ, g, σ, x, y)) ∂η ∂θ := by
    -- Translate `l` on the right by `(g * σ)⁻¹`, and split it as `k * τ`.
    have hgσ : g * σ ∈ floorGroup 𝔰.ϱ := mul_mem (floorGroup_anti 𝔰.ϱ.le_succ hg) hσ
    rw [← partialGroupMeasure_mconv_dirac rfl (inv_mem hgσ), lintegral_mconv_dirac,
      partialGroupMeasure_top,
      lintegral_mconv_symm (by fun_prop), ← floorMeasure_top]
    -- `τ` and `k` may be taken in the floor groups that carry `θ` and `η`.
    congr! 2 with τ hτ k hk
    have hkτ : k * τ ∈ floorGroup 𝔰.ϱ := mul_mem (floorGroup_anti 𝔰.ϱ.le_succ hk) hτ
    have h_weight : φ (k * τ * (g * σ)⁻¹)⁻¹ = φ (σ * τ⁻¹) := by
      have h_arg : (k * τ * (g * σ)⁻¹)⁻¹ = g * (σ * τ⁻¹) * k⁻¹ := by group
      rw [h_arg, hφ_inv g hg k⁻¹ (inv_mem hk)]
    simp only [Φ, Ψ]
    rw [h_weight, unfoldedPairing_mul_inv Z p q hkτ hgσ, mul_assoc (φ _)]
  have hM : F.groupMeasure = (η ∗ₘ θ) ∗ₘ F.partialGroupMeasure 0 𝔰.ϱ :=
    (descConv_add 𝔰.ϱ 2 0).trans (by simp [η, θ, partialGroupMeasure_top])
  calc ∫⁻ c, χ c ∂((F.partialGroupMeasure 𝔰.ϱ 2).prod (F.groupMeasure.prod F.groupMeasure)).map Φ
    _ = ∫⁻ x, ∫⁻ y₁, ∫⁻ l, χ (Φ (l, y₁, y₁ * x)) ∂F.partialGroupMeasure 𝔰.ϱ 2 ∂F.groupMeasure
        ∂F.groupMeasure := by
      rw [← (measurePreserving_prod_mul_swap F.groupMeasure F.groupMeasure).map_eq,
        lintegral_map hχ hΦ, lintegral_prod_symm' _ (by fun_prop),
        lintegral_map (by fun_prop) (by fun_prop), lintegral_prod _ (by fun_prop)]
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ σ, ∫⁻ g, ∫⁻ l, χ (Φ (l, g * σ * y, g * σ * y * x))
        ∂F.partialGroupMeasure 𝔰.ϱ 2 ∂η ∂θ ∂F.partialGroupMeasure 0 𝔰.ϱ ∂F.groupMeasure := by
      refine lintegral_congr fun x ↦ ?_
      rw [hM, lintegral_mconv_symm (by fun_prop)]
      refine lintegral_congr fun y ↦ ?_
      rw [lintegral_mconv_symm (by fun_prop)]
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ σ, ∫⁻ g, ∫⁻ τ, ∫⁻ k, χ (Ψ (k, τ, g, σ, x, y))
        ∂η ∂θ ∂η ∂θ ∂F.partialGroupMeasure 0 𝔰.ϱ ∂F.groupMeasure := by
      unfold η θ
      congr! 6 with x y σ hσ g hg
      exact h_fiber x y hσ hg
    _ = ∫⁻ c, χ c ∂(F.measureH.prod (θ.prod (F.measureH.prod (θ.prod
        (F.groupMeasure.prod (F.partialGroupMeasure 0 𝔰.ϱ)))))).map Ψ := by
      rw [lintegral_map hχ hΨ, ← floorMeasure_top]
      iterate 4 rw [lintegral_prod_symm' _ (by fun_prop)]
      rw [lintegral_prod _ (by fun_prop)]

/-- Fubini's theorem for the first four variables of an integrable function on a product of five
spaces with s-finite measures. -/
lemma _root_.New.Floors.integral_prod_prod_prod_prod_symm {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ₁ μ₂ μ₃ μ₄ : Measure X} {ν : Measure Y} [SFinite μ₁] [SFinite μ₂]
    [SFinite μ₃] [SFinite μ₄] [SFinite ν] {f : X × X × X × X × Y → ℂ}
    (hf : Integrable f (μ₁.prod (μ₂.prod (μ₃.prod (μ₄.prod ν))))) :
    ∫ z : X × X × X × X × Y, f z ∂μ₁.prod (μ₂.prod (μ₃.prod (μ₄.prod ν))) =
      ∫ y : Y, ∫ x₄ : X, ∫ x₃ : X, ∫ x₂ : X, ∫ x₁ : X, f (x₁, x₂, x₃, x₄, y)
        ∂μ₁ ∂μ₂ ∂μ₃ ∂μ₄ ∂ν := by
  rw [integral_prod_symm _ hf, integral_prod_symm _ hf.integral_prod_right,
    integral_prod_symm _ hf.integral_prod_right.integral_prod_right,
    integral_prod_symm _ hf.integral_prod_right.integral_prod_right.integral_prod_right]

/-- Let `F` be a large lattice datum, and let the weight `φ x` be `P.ψ (ξ * θ)`, with `P.ψ` the
additive character of the place and `θ = ⟨z, x z⟩` the last diagonal entry of `T.frameGram x`, `z`
being the last frame vector. Let `f l` be `φ l⁻¹` times the pairing of the scaled orbital integrals
with heads `p`, `q` at the inverse link `l`. Then `f` is integrable for the measure
`F.partialGroupMeasure 𝔰.ϱ 2` of the top floors, and its integral is the form `F.floorForm 𝔰.ϱ`: the
density of the heads times an integral, weighted by `φ`, of a product of two correlations of the
finite Bessel vector of `Z`. -/
lemma floorForm_top_eq_integral {F : PlaceData ι T (m + 1)} (Z : F.IntermediateGroup) (p q : ℕ → Aˣ)
    [h : P.IsLargeLatticeData F] (ξ : A) :
    let φ (x : T.G) : ℂ := P.ψ (ξ * T.frameGram x.val 𝔰.top 𝔰.top)
    let f (l : T.G) : ℂ := φ l⁻¹ * ⟪scaledOrbitalIntegral Z p l, scaledOrbitalIntegral Z q l⟫_ℂ
    Integrable f (F.partialGroupMeasure 𝔰.ϱ 2) ∧
      F.floorForm 𝔰.ϱ p q Z.besselVector φ = ∫ l : T.G, f l ∂F.partialGroupMeasure 𝔰.ϱ 2 := by
  -- By `inner_scaledOrbitalIntegral`, `f l` is a constant times the integral of `Φ (l, ·)` over two
  -- copies of the group. Changes of variables carry `Φ` to the integrand `Ψ` of
  -- `PlaceData.floorForm`, with the same law; `Φ` is integrable, and Fubini concludes.
  intro φ f
  set W : T.G → EuclideanSpace ℂ Z.Cosets := Z.besselVector
  have hφ : Measurable φ := by fun_prop [frameGram]
  let Φ : T.G × T.G × T.G → ℂ := fun z ↦ φ z.1⁻¹ * unfoldedPairing Z p q z.1 z.2
  let Ψ : T.G × T.G × T.G × T.G × T.G × T.G → ℂ := fun (k, τ, g, σ, x, y) ↦
    let z : T.G := k * τ * (weylElem 𝔰.ϱ p)⁻¹ * y
    φ (σ * τ⁻¹) * ⟪W (g * σ * y), W (g * σ * y * x)⟫_ℂ * ⟪W (weylRatio 𝔰.ϱ p q * z * x), W z⟫_ℂ
  let M₂ : Measure (T.G × T.G) := F.groupMeasure.prod F.groupMeasure
  have h_inv (g : T.G) (hg : g ∈ T.besselH) (k : T.G) (hk : k ∈ T.besselH) (x : T.G) :
      φ (g * x * k) = φ x :=
    congrArg (fun θ : A ↦ P.ψ (ξ * θ)) (frameGram_top_eq_of_mem_besselH hg hk x)
  let M₆ : Measure (T.G × T.G × T.G × T.G × T.G × T.G) :=
    F.measureH.prod ((F.floorMeasure 𝔰.ϱ).prod (F.measureH.prod ((F.floorMeasure 𝔰.ϱ).prod
      (F.groupMeasure.prod (F.partialGroupMeasure 0 𝔰.ϱ)))))
  have h_law : ProbabilityTheory.IdentDistrib Φ Ψ ((F.partialGroupMeasure 𝔰.ϱ 2).prod M₂) M₆ :=
    identDistrib_unfoldedPairing Z p q hφ h_inv
  have h_int : Integrable Φ ((F.partialGroupMeasure 𝔰.ϱ 2).prod M₂) := by
    have h_top : F.quotientMeasureFrom 𝔰.ϱ = F.partialGroupMeasure 𝔰.ϱ 2 := by simp [descConv]
    have h_pairing : Integrable (fun z : T.G × T.G × T.G ↦ unfoldedPairing Z p q z.1 z.2)
        ((F.partialGroupMeasure 𝔰.ϱ 2).prod M₂) := by
      simpa only [h_top, mul_one] using integrable_unfoldedPairing Z p q le_rfl (one_mem _)
    have h_norm (x : T.G × T.G × T.G) : ‖φ x.1⁻¹‖ ≤ 1 := by simp [φ]
    exact h_pairing.bdd_mul (c := 1) (Measurable.aestronglyMeasurable (by fun_prop))
      (.of_forall h_norm)
  have hf : (fun l : T.G ↦ (F.headDensity 𝔰.ϱ p q).toReal * ∫ y, Φ (l, y) ∂M₂)
      =ᵐ[F.partialGroupMeasure 𝔰.ϱ 2] f := by
    filter_upwards [ae_partialGroupMeasure_mem] with l hl
    simp only [f, Φ, inner_scaledOrbitalIntegral Z p q hl, integral_const_mul]
    ring
  -- The first four variables of `Ψ` give the inner integrals of `PlaceData.formIntegrand` and
  -- `PlaceData.partialCorrelation`.
  have h_inner (z : T.G × T.G) : F.formIntegrand 𝔰.ϱ p q W z.1 φ z.2 =
      ∫ σ, ∫ g, ∫ τ, ∫ k, Ψ (k, τ, g, σ, z)
        ∂F.measureH ∂F.floorMeasure 𝔰.ϱ ∂F.measureH ∂F.floorMeasure 𝔰.ϱ := by
    simp [Ψ, ← integral_conj, formIntegrand, partialCorrelationProduct, partialCorrelation,
      descConv,
      mul_assoc, mul_left_comm (φ _), integral_const_mul, integral_mul_const]
  refine ⟨(h_int.integral_prod_left.const_mul _).congr hf, ?_⟩
  calc F.floorForm 𝔰.ϱ p q W φ
    _ = (F.headDensity 𝔰.ϱ p q).toReal * ∫ z, Ψ z ∂M₆ := by
      rw [integral_prod_prod_prod_prod_symm (h_law.integrable_iff.1 h_int)]
      simp only [floorForm, h_inner]
    _ = (F.headDensity 𝔰.ϱ p q).toReal * ∫ l, ∫ y, Φ (l, y) ∂M₂ ∂F.partialGroupMeasure 𝔰.ϱ 2 := by
      rw [← h_law.integral_eq, integral_prod _ h_int]
    _ = ∫ l, f l ∂F.partialGroupMeasure 𝔰.ϱ 2 := by rw [← integral_const_mul, integral_congr_ae hf]

end IntegralPlace.IsLargeLatticeData

end Correlation

end New.Floors

end
