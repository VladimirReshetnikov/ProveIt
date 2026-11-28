import New.Spanning.Frames.QuadricVolumes

/-!
# Plancherel's formula on quadrics

Cauchy–Schwarz in the fibres and Plancherel's formula in the orthonormal coordinates bound a Fourier
kernel between two quadrics. Along a Heisenberg group a partial correlation is a Fourier transform
in the next frame vector. The letters G^(l), R^(l), U_(<l), Y^(l) are those of the head of
`New.Spanning.Frames.Lengths`, and K, M those of `New.Spanning.Frames.Levels`.

## Main definitions and results

* `New.Floors.Gauge.fourierSqNormLe_floorQuadricMeasure`: the kernel from the quadric of a floor to
  the same quadric or to the whole floor, by solving in two disjoint blocks.
* `New.Floors.Gauge.partialCorrelation_heisenbergElem_eq_integral`: the correlation along a
  Heisenberg group.
* `New.Floors.Gauge.parseval_heisenbergMeasure_le`: Parseval's inequality along a Heisenberg group.

Notions from other files:
* `F.partialCorrelation l k g y`: the correlation from floor l on, an integral of k(σ g, σ y).
* `F.IsPairingKernel l k d`: the rules obeyed by an orbital integral twisted by d.
* `orbitPoint b σ`: the vector σ⁻¹ f_b, for the b-th frame vector f_b; its law on floor b is
  `F.floorQuadricMeasure b`.
* `Γ.vecsOfSize i`, `Γ.HasMatrixSize i`: vectors and matrices all of whose entries have size i.
* `FourierSqNormLe`: a bound for the kernel ψ(ξ ⟨v, y⟩) on square norms.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

namespace New.Floors.Gauge

open Matrix MeasureTheory BesselIndex ENNReal Fintype FloorGroups ProbabilityTheory Size Set
  PlaceData U
  Place Finset

variable {A ι : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {𝔰 : Shape} [Fintype ι] [DecidableEq ι] {m j : ℕ}
  {T : 𝔰.Form A} [IsHermitianUnit T.splitGram]
  {F : PlaceData ι T m} (Γ : Gauge F) {x t q : T.G} {b : Fin 𝔰.n} (a : Fin 𝔰.ϱ) {k : T.G → T.G → ℂ}
  {d : T.G} {p : ℕ → Aˣ}

/-! ### Masses on the floors and Fourier kernels -/

/-- Let f be measurable and left invariant under R^(b+1) = `partialUnitriangularGroup (b + 1)`. For
each g ∈ K let f(σ g) be at most Ψ(σ⁻¹ f_b) for σ in `floorGroup b`, with f_b the b-th frame vector,
where σ⁻¹ f_b = `orbitPoint b σ` and the measurable function Ψ has integral at most C over the
vectors of size 7 of the quadric of floor b. Then for every g the integral of f(σ g) over the σ on
floor b with σ g near at b + 1 (that is, R^(b+1) σ g meets K) is at most C. -/
lemma floorMassLe_of_chart {f : T.G → ℝ≥0∞} {C : ℝ≥0∞}
    (hf_inv : (partialUnitriangularGroup (b + 1)).FixesLeft f)
    (h_chart : ∀ g ∈ F.boxSet, ∃ Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞,
      ∫⁻ v : 𝔰.BesselIndex → A in Γ.vecsOfSize 7, Ψ v ∂F.floorQuadricMeasure b ≤ C ∧
      Measurable Ψ ∧
      ∀ σ ∈ floorGroup b, f (σ * g) ≤ Ψ (orbitPoint b σ))
    (hf : Measurable f := by fun_prop) :
    F.FloorMassLe b C f := by
  classical
  -- If some `σ * g` is near at `b + 1`, then `ξ * g` lies in K for some `ξ` in
  -- `partialUnitriangularGroup b`, and the integral does not change when `g` is replaced by
  -- `ξ * g`. The vectors `σ⁻¹ f_b` that count then have size `1 + 6`.
  intro g
  let Φ : T.G → ℝ≥0∞ := {z | F.IsNear (b + 1) z}.indicator f
  have hΦ : Measurable Φ := hf.indicator measurableSet_isNear
  refine (lintegral_indicator (measurable_mul_const g measurableSet_isNear) _).ge.trans ?_
  change ∫⁻ σ, Φ (σ * g) ∂F.floorMeasure b ≤ C
  obtain h_far | ⟨ξ, hξ, h_box⟩ := em' (F.IsNear b g)
  · have h_zero (σ : T.G) (hσ : σ ∈ floorGroup b) : Φ (σ * g) = 0 :=
      ite_eq_right fun h_near ↦ h_far (IsNear.of_floorGroup_mul h_near hσ le_self_add)
    grw [lintegral_le_of_ae_imp ae_floorMeasure_mem (g := 0) fun σ hσ ↦ (h_zero σ hσ).le]
    simp
  obtain ⟨Ψ, hΨ_int, hΨ_meas, hΨ_le⟩ : ∃ Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞,
      ∫⁻ v in Γ.vecsOfSize 7, Ψ v ∂F.floorQuadricMeasure b ≤ C ∧ Measurable Ψ ∧
      ∀ σ ∈ floorGroup b, f (σ * (ξ * g)) ≤ Ψ (orbitPoint b σ) :=
    h_chart (ξ * g) h_box
  have hΦ_inv : (partialUnitriangularGroup (b + 1) ⊓ ⊤).FixesLeft fun σ : T.G ↦ Φ (σ * g) := by
    simp +contextual [Φ, indicator, hf_inv, mul_assoc]
  have hΦ_le (σ : T.G) (hσ : σ ∈ floorGroup b) :
      Φ (σ * ξ * g) ≤ (Γ.vecsOfSize 7).indicator Ψ (orbitPoint b σ) := by
    rw [mul_assoc]
    refine indicator_apply_le' (fun h_near ↦ ?_) fun _ ↦ zero_le
    have h_size : orbitPoint b σ ∈ Γ.vecsOfSize 7 :=
      orbitPoint_mem_vecsOfSize hσ (Γ.hasMatrixSize_boxSet h_box) h_near
    rw [indicator_of_mem h_size]
    exact hΨ_le σ hσ
  calc ∫⁻ σ, Φ (σ * g) ∂F.floorMeasure b
    _ = ∫⁻ σ, Φ (σ * ξ * g) ∂F.floorMeasure b :=
      (lintegral_floorMeasure_mul_right le_top hΦ_inv ⟨hξ, Subgroup.mem_top ξ⟩).symm
    _ ≤ ∫⁻ σ, (Γ.vecsOfSize 7).indicator Ψ (orbitPoint b σ) ∂F.floorMeasure b :=
      lintegral_le_of_ae_imp ae_floorMeasure_mem hΦ_le
    _ = ∫⁻ v, (Γ.vecsOfSize 7).indicator Ψ v ∂F.floorQuadricMeasure b :=
      (measurePreserving_orbitPoint b).lintegral_comp (hΨ_meas.indicator measurableSet_vecsOfSize)
    _ ≤ C := (lintegral_indicator_le Ψ (Γ.vecsOfSize 7)).trans hΨ_int

/-- Bounded mass. The measure of the quadric of floor b is the image, under the basis
`F.floorBasis b`, of `quadricMeasure` for the hyperbolic pairs `FloorPairs b m` and the orthonormal
vectors ι, at some value β of the form. If the coordinate vectors of size 11 have mass at most M
for every β, then for every g the σ on floor b with σ g near at b + 1 (`F.IsNear`) have mass at
most M. -/
lemma floorMassLe_one_of_le (b : Fin 𝔰.n) {M : ℝ≥0∞}
    (h_mass : ∀ β : skewAdjoint A,
      quadricMeasure (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) β (Γ.vecsOfSize 11) ≤ M) :
    F.FloorMassLe b M 1 := by
  refine Γ.floorMassLe_of_chart (by simp) fun _ _ ↦ ⟨1, ?_, measurable_one, by simp⟩
  -- vectors of size `7` have coordinates of size `7 + 4`
  refine (setLIntegral_map_floorBasis_le (j := 7) 1).trans ?_
  simpa using h_mass _

/-- For every g, the σ on floor b with σ g near at b + 1 (`F.IsNear`) have mass at most
Λ^(99 · 13 n) times the volume of the vectors of size 11 in X'. Here Λ = `Γ.loss` is the constant of
the gauge, n = `𝔰.n`, and X' is spanned by the orthonormal vectors indexed by `F.FreeIndex`. -/
lemma floorMassLe_one (b : Fin 𝔰.n) :
    F.FloorMassLe b
      (Γ.loss ^ (99 * 𝔰.n * (7 + 6)) * volume (Γ.ofSize 11) ^ Fintype.card F.FreeIndex) 1 := by
  refine Γ.floorMassLe_of_chart (by simp) fun _ _ ↦ ⟨1, ?_, measurable_one, by simp⟩
  have h_vol : ∫⁻ _ : F.FreeIndex → A in Γ.vecsOfSize (7 + 4), 1 ≤
      volume (Γ.ofSize 11) ^ Fintype.card F.FreeIndex :=
    (setLIntegral_one _).le.trans (volume_coordinateBox F.FreeIndex (Γ.ofSize 11)).le
  exact setLIntegral_orthonormalPart_le (φ := 1) (.inr rfl) h_vol measurable_one

/-- Let ρ be the volume `floorVolume b` of Y^(b) or the measure of the quadric of floor b. The
kernel ψ(ξ ⟨v, y⟩), from the vectors y of size j on the quadric to the vectors v of size i with the
measure ρ, multiplies square norms by at most Λ^(99 n (i+6)) Λ^(99 n (j+6)) (c / |ξ|)^(rank X').
Here Λ = `Γ.loss` is the constant of the gauge, n = `𝔰.n`, c = `P.kernelBound`, |ξ| = `P.modulus ξ`
and rank X' = `card F.FreeIndex`. -/
lemma fourierSqNormLe_floorQuadricMeasure (ξ : Aˣ) {ρ : Measure (𝔰.BesselIndex → A)} {i : ℕ}
    (hρ : ρ = FloorGroups.floorVolume b ∨ ρ = F.floorQuadricMeasure b) :
    FourierSqNormLe T.splitGram ξ ρ (F.floorQuadricMeasure b) (Γ.vecsOfSize i) (Γ.vecsOfSize j)
      (Γ.loss ^ (99 * 𝔰.n * (i + 6)) * Γ.loss ^ (99 * 𝔰.n * (j + 6)) *
        (P.kernelBound / P.modulus ξ) ^ Fintype.card F.FreeIndex) := by
  -- In the coordinates of the basis `F.floorBasis b`, solve for `v` and `y` in different blocks.
  have h_solve {μ : Measure (𝔰.BesselIndex → A)}
      (hμ : μ = FloorGroups.floorVolume b ∨ μ = F.floorQuadricMeasure b) :
      ∃ μ₀ : Measure (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A),
        μ = μ₀.map (F.floorBasis b *ᵥ ·) ∧
        ∀ blk : Fin F.blockRank → ι, Function.Injective blk → ∀ l : ℕ,
          IsSolvedIn (.inr ∘ .inr ∘ .inl ∘ blk) μ₀ (Γ.ofSize l)
            (Γ.loss ^ (F.blockRank * (l + 1))) :=
    Γ.exists_isSolvedIn hμ
  obtain ⟨ρ', rfl, h_solved'⟩ := h_solve hρ
  obtain ⟨ρ₀, h_eq, h_solved⟩ := h_solve (.inr rfl)
  obtain ⟨blk', blk, h_inj⟩ : ∃ blk' blk : Fin F.blockRank → ι,
      Function.Injective (F.freeIndex ⊕ᵥ (blk' ⊕ᵥ blk)) := Γ.exists_blocks
  have h_inj' : Function.Injective blk' := h_inj.comp (Sum.inr_injective.comp Sum.inl_injective)
  have h_inj₀ : Function.Injective blk := h_inj.comp (Sum.inr_injective.comp Sum.inr_injective)
  have h_phase (v y : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A) :
      ξ * star (F.floorBasis b *ᵥ v) ⬝ᵥ T.splitGram *ᵥ F.floorBasis b *ᵥ y =
        ξ * star v ⬝ᵥ planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) *ᵥ y := by
    rw [← F.gram_floorBasis b, star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec]
  rw [h_eq]
  refine FourierSqNormLe.map ?_ (by fun_prop) (by fun_prop) h_phase measurableSet_vecsOfSize
    (fun _ ↦ mem_vecsOfSize_of_floorBasis_mulVec) fun _ ↦ mem_vecsOfSize_of_floorBasis_mulVec
  refine (IsSolvedIn.fourierSqNormLe (inner := .inr ∘ .inr ∘ .inl ∘ F.freeIndex)
    (h_solved' blk' h_inj' (i + 4)) (h_solved blk h_inj₀ (j + 4))
    (Γ.isCompact_ofSize (i + 4)).measurableSet ?_ ?_ ξ).mono ?_
  · have h_incl : Function.Injective
        (.inr ∘ .inr ∘ .inl : ι → Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) :=
      Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective)
    simpa only [Sum.comp_elim, Function.comp_assoc] using h_incl.comp h_inj
  · -- the rows of the Gram matrix at the orthonormal vectors are those of the identity
    rintro (i | i) (k | k | k | k) <;> simp [Matrix.one_apply]
  · -- the outer coordinates and one block cost `Λ ^ (99 n (l + 6))` at size `l + 4`
    grw [volume_pow_mul_le (j := i + 4), volume_pow_mul_le (j := j + 4)]

/-- The support of a correlation. Let k be a pairing kernel for the element d (`IsPairingKernel`),
let t lie in `floorGroup b`, let t⁻¹ q lie in `unipotentBelow b`, and let the matrix q x have
entries of size j. For almost every σ on floor b at which the correlation from floor b + 1 on at (σ
x, σ y) is not zero, the vector t σ⁻¹ f_b has size j + 6. -/
lemma correlation_support (ht : t ∈ floorGroup b)
    (h_size : Γ.HasMatrixSize j ((q * x : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hk : F.IsPairingKernel b k d) (y : T.G) (hq : t⁻¹ * q ∈ unipotentBelow b := by simp) :
    ∀ᵐ σ : T.G ∂F.floorMeasure b, F.partialCorrelation (b + 1) k (σ * x) (σ * y) ≠ 0 →
      (t : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ orbitPoint b σ ∈ Γ.vecsOfSize (j + 6) := by
  filter_upwards [ae_floorMeasure_mem] with σ hσ h_ne
  have h_conj : σ * (t⁻¹ * q) * σ⁻¹ ∈ partialUnitriangularGroup (b + 1) :=
    unipotentBelow_le_partialUnitriangularGroup (conj_mem_unipotentBelow hσ hq)
  have h_near : F.IsNear (b + 1) (σ * t⁻¹ * (q * x)) := by
    simpa [mul_assoc] using (isNear_mul_iff h_conj).2 (hk.isNear_of_partialCorrelation_ne_zero h_ne)
  have h_orbit : (t : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ orbitPoint b σ =
      orbitPoint b (σ * t⁻¹) := by
    rw [orbitPoint, orbitPoint, mulVec_mulVec]
    simp
  rw [h_orbit]
  exact orbitPoint_mem_vecsOfSize (mul_mem hσ (inv_mem ht)) h_size h_near

/-- Plancherel's inequality for the amplitude of floor b, that is, the Fourier transform of a
correlation along the quadric of that floor. Let k be a pairing kernel for the element d at floor b,
let t lie in `floorGroup b`, let t⁻¹ q lie in `unipotentBelow b`, and let the matrix q x have
entries of size j (`Γ.HasMatrixSize j`). Let ρ be the Haar measure `floorVolume b` on the vectors of
floor at least b, or the measure `F.floorQuadricMeasure b` of the quadric of floor b. Integrate the
correlation from floor b + 1 on at (σ x, σ y) against ψ(ξ ⟨v + v₀, t σ⁻¹ f_b⟩) over σ on floor b.
Here ψ is the additive character of the place, ⟨·,·⟩ is the form with Gram matrix `T.splitGram`, and
σ⁻¹ f_b = `orbitPoint b σ`, with f = (e_0, …, e_{ϱ-1}, z) the frame. The integral for ρ of the
squared modulus of this transform over the v of size i (`Γ.vecsOfSize i`) is at most Λ^(99 n (i+6))
Λ^(99 n (j+12)) (c / |ξ|)^(card `F.FreeIndex`) times the squared L² norm of the correlation on floor
b. -/
lemma correlation_plancherel (ht : t ∈ floorGroup b)
    (h_size : Γ.HasMatrixSize j ((q * x : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hk : F.IsPairingKernel b k d) (y : T.G) (hq : t⁻¹ * q ∈ unipotentBelow b) (ξ : Aˣ)
    (v₀ : 𝔰.BesselIndex → A) {ρ : Measure (𝔰.BesselIndex → A)} {i : ℕ}
    (hρ : ρ = FloorGroups.floorVolume b ∨ ρ = F.floorQuadricMeasure b) :
    ∫⁻ v : 𝔰.BesselIndex → A in Γ.vecsOfSize i,
        ‖∫ σ : T.G, ψ (ξ * star (v + v₀) ⬝ᵥ T.splitGram *ᵥ t *ᵥ orbitPoint b σ) *
          F.partialCorrelation (b + 1) k (σ * x) (σ * y) ∂F.floorMeasure b‖ₑ ^ 2 ∂ρ ≤
      Γ.loss ^ (99 * 𝔰.n * (i + 6)) * Γ.loss ^ (99 * 𝔰.n * (j + 12)) *
        (P.kernelBound / P.modulus ξ) ^ Fintype.card F.FreeIndex *
        ∫⁻ σ : T.G, ‖F.partialCorrelation (b + 1) k (σ * x) (σ * y)‖ₑ ^ 2 ∂F.floorMeasure b := by
  -- On `G^(b)` the correlation is a measurable function `f₀` of `σ⁻¹ f_b`, so a function `f` of
  -- `t σ⁻¹ f_b` that vanishes off size `j + 6`. The shift by `v₀` multiplies `f` by a phase.
  let κ (σ : T.G) : ℂ := F.partialCorrelation (b + 1) k (σ * x) (σ * y)
  have hκ_inv : (partialUnitriangularGroup (b + 1) ⊓ floorGroup b).FixesLeft κ := by
    simp +contextual [κ, hk.partialCorrelation_mul_left, mul_assoc]
  obtain ⟨f₀, hf₀_meas, hf₀⟩ : ∃ f₀ : (𝔰.BesselIndex → A) → ℂ, Measurable f₀ ∧
      ∀ σ ∈ floorGroup b, F.partialCorrelation (b + 1) k (σ * x) (σ * y) = f₀ (orbitPoint b σ) :=
    exists_factor_orbitPoint b (Φ := κ) (by fun_prop) hκ_inv
  let f : (𝔰.BesselIndex → A) → ℂ := (Γ.vecsOfSize (j + 6)).indicator fun w ↦ f₀ (t⁻¹ *ᵥ w)
  let φ (w : 𝔰.BesselIndex → A) : ℂ := ψ (ξ * star v₀ ⬝ᵥ T.splitGram *ᵥ w) * f w
  have hf_meas : Measurable f := .indicator (by fun_prop) measurableSet_vecsOfSize
  have hφ_meas : Measurable φ := by
    unfold φ
    fun_prop
  have h_law : MeasurePreserving (fun σ ↦ t *ᵥ orbitPoint b σ) (F.floorMeasure b)
      (F.floorQuadricMeasure b) :=
    measurePreserving_mulVec_orbitPoint b ht
  have h_eq : ∀ᵐ σ ∂F.floorMeasure b,
      F.partialCorrelation (b + 1) k (σ * x) (σ * y) = f (t *ᵥ orbitPoint b σ) := by
    filter_upwards [Γ.correlation_support ht h_size hk y hq, ae_floorMeasure_mem] with σ h_supp hσ
    revert h_supp
    simp +contextual [f, indicator, not_imp_comm, hf₀ σ hσ]
  have hκ_int : Integrable κ (F.floorMeasure b) := hk.integrable_partialCorrelation_succ
  have hf_int : Integrable f (F.floorQuadricMeasure b) :=
    (h_law.integrable_comp hf_meas.aestronglyMeasurable).1 (hκ_int.congr h_eq)
  have hφ_int : Integrable φ (F.floorQuadricMeasure b) :=
    hf_int.bdd_mul (c := 1) (by fun_prop) (by simp)
  have hφ_supp (w : 𝔰.BesselIndex → A) (hw : φ w ≠ 0) : w ∈ Γ.vecsOfSize (j + 6) :=
    mem_of_indicator_ne_zero (right_ne_zero_of_mul hw)
  have h_fourier (v : 𝔰.BesselIndex → A) :
      ∫ σ, ψ (ξ * star (v + v₀) ⬝ᵥ T.splitGram *ᵥ t *ᵥ orbitPoint b σ) *
          F.partialCorrelation (b + 1) k (σ * x) (σ * y) ∂F.floorMeasure b =
        ∫ w, ψ (ξ * star v ⬝ᵥ T.splitGram *ᵥ w) * φ w ∂F.floorQuadricMeasure b := by
    rw [← h_law.map_eq, integral_map h_law.aemeasurable (by fun_prop)]
    exact integral_congr_ae (h_eq.mono fun σ hσ ↦ by
      simp [φ, hσ, mul_add, mul_assoc, AddChar.map_add_eq_mul])
  have h_norm : ∫⁻ σ, ‖F.partialCorrelation (b + 1) k (σ * x) (σ * y)‖ₑ ^ 2 ∂F.floorMeasure b =
      ∫⁻ w, ‖φ w‖ₑ ^ 2 ∂F.floorQuadricMeasure b := by
    rw [← h_law.lintegral_comp (by fun_prop)]
    exact lintegral_congr_ae (h_eq.mono fun σ hσ ↦ by simp [φ, hσ, ← ofReal_norm])
  simp only [h_fourier, h_norm]
  exact Γ.fourierSqNormLe_floorQuadricMeasure ξ hρ φ hφ_meas hφ_int hφ_supp

/-! ### Correlations along a Heisenberg group -/

/-- Let k be a pairing kernel (`IsPairingKernel`) from floor a + 1 on for the element d, and let
n = `P.heisenbergElem a t` with t = (ω, β). Suppose that (σ₀(d s d⁻¹) - σ₀(s^ε)) / M = ξ σ₀(s) for s
in the Heisenberg group `floorUnipotent a`, where σ₀ = `simpleRootSum` and M = `F.levelUnit` is the
level. Then the correlation `F.partialCorrelation` from floor a + 1 on at (n^ε x, n y) is the
integral over σ on floor a + 1 of ψ(-ξ ⟨ω, σ⁻¹ f_(a+1)⟩), with f the frame, times the correlation
from floor a + 2 on at (σ x, σ y). -/
lemma partialCorrelation_heisenbergElem_eq_integral {ξ : A} {ε : ℕ}
    (hk : F.IsPairingKernel (a + 1) k d)
    (h_twist : ∀ s ∈ floorUnipotent a,
      F.levelUnit⁻¹.val * (simpleRootSum (d * s * d⁻¹) - simpleRootSum (s ^ ε)) = ξ * simpleRootSum
        s)
    (t : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) (x y : T.G) :
    F.partialCorrelation (a + 1) k (P.heisenbergElem a t ^ ε * x) (P.heisenbergElem a t * y) =
      ∫ σ : T.G,
        ψ (-ξ * star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ T.splitGram *ᵥ orbitPoint a.succ σ) *
          F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y) ∂F.floorMeasure (a + 1) := by
  rw [hk.partialCorrelation_eq_integral_floorMeasure]
  refine integral_congr_ae (ae_floorMeasure_mem.mono fun σ hσ ↦ ?_)
  -- move `n` to the left of `σ` and apply the equivariance of the correlation to `s = σ n σ⁻¹`
  set s : T.G := σ * P.heisenbergElem a t * σ⁻¹ with hs_eq
  have hs : s ∈ floorUnipotent a :=
    conj_mem_floorUnipotent (heisenbergElem_mem_floorUnipotent a t) σ hσ
  have hs_unip : s ∈ unipotentBelow (a + 1) := (Subgroup.mem_inf.1 hs).right
  have h_law : F.partialCorrelation (a + 1 + 1) k (s ^ ε * (σ * x)) (s * (σ * y)) =
      ψ (F.levelUnit⁻¹.val * (simpleRootSum (d * s * d⁻¹) - simpleRootSum (s ^ ε))) *
        F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y) :=
    hk.equivariance (pow_mem hs_unip ε) hs_unip (σ * x) (σ * y)
  rw [h_twist s hs, hs_eq, simpleRootSum_conj_heisenbergElem hσ, mul_neg, ← neg_mul,
    conj_pow] at h_law
  simpa only [mul_assoc, inv_mul_cancel_left] using h_law

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- Let p, q be sequences of units and j ≤ a + 1. Conjugation by the diagonal element
`weylRatio j p q`, with entry p_b / q_b at e_b for b < j, multiplies the character
`simpleRootSum` (the sum of the entries just above the diagonal of the
frame block) on the Heisenberg group `floorUnipotent a` by p_a / q_a if a < j, and by 1
otherwise. -/
lemma simpleRootSum_weylRatio_conj {q : ℕ → Aˣ} {s : T.G} (hs : s ∈ floorUnipotent a)
    (hj : j ≤ a + 1) :
    simpleRootSum (weylRatio j p q * s * (weylRatio j p q)⁻¹) =
      (if a < j then (p a / q a).val else 1) * simpleRootSum s := by
  simp_rw [simpleRootSum, mul_sum]
  congr with b
  -- conjugation by a diagonal matrix scales each entry
  simp only [Subgroup.coe_mul, Units.val_mul, weylRatio_inv, coe_weylRatio,
    diagonal_mul, mul_diagonal]
  obtain rfl | hab := eq_or_ne a b
  · -- the factor is `p a / q a` in row `a` if `a < j`, and `1` in column `a + 1` as `j ≤ a + 1`
    grind
  · -- just above the diagonal only the entry of floor `a` survives
    simp only [floorUnipotent_superdiag_eq_zero b hs (Fin.val_ne_of_ne hab), mul_zero, zero_mul]

/-- Let j ≤ a + 1 and ε ≤ 1, let k satisfy `F.IsPairingKernel (a + 1) k (weylRatio j p q)`, and let
n = `P.heisenbergElem a t` with t = (ω, β). Then `F.partialCorrelation (a + 1) k` at (n^ε x, n y) is
the integral over σ, for `F.floorMeasure (a + 1)`, of ψ(-ξ h(ω, σ⁻¹ f_(a+1))) times
`F.partialCorrelation (a + 2) k` at (σ x, σ y). Here ψ is the additive character of the place `P`, h
is the form with Gram matrix `T.splitGram`, and f = (e_0, …, e_{ϱ-1}, z) is the frame. The frequency
ξ is (p_a / q_a - ε) / M if a < j (that is, j = a + 1), and (1 - ε) / M otherwise. -/
lemma partialCorrelation_weylRatio_heisenbergElem {q : ℕ → Aˣ} {ε : ℕ} (hε : ε ≤ 1) (hj : j ≤ a + 1)
    (hk : F.IsPairingKernel (a + 1) k (weylRatio j p q))
    (t : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) (x y : T.G) :
    F.partialCorrelation (a + 1) k (P.heisenbergElem a t ^ ε * x) (P.heisenbergElem a t * y) =
      ∫ σ : T.G,
        ψ (-(F.levelUnit⁻¹.val * ((if a < j then (p a / q a).val else 1) - ε)) *
            star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ T.splitGram *ᵥ orbitPoint a.succ σ) *
          F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y) ∂F.floorMeasure (a + 1) := by
  refine partialCorrelation_heisenbergElem_eq_integral a hk (fun s hs ↦ ?_) t x y
  have h_pow : simpleRootSum (s ^ ε) = ε * simpleRootSum s := by
    obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hε
    · simp [simpleRootSum_eq_zero_of_mem_besselH]
    · simp
  rw [simpleRootSum_weylRatio_conj a hs hj, h_pow]
  ring

/-- Parseval's inequality along the Heisenberg group N = `floorUnipotent a` of floor a. Let k be a
pairing kernel from floor a + 1 on for the element d, and let the characters of the two points
differ by the invertible frequency ξ on N. For n ∈ N with Φ(n) ≠ 0, let n lie in S and let Φ(n) be
at most C times the squared correlation `F.partialCorrelation` from floor a + 1 on at (n^ε x, n y).
For each n₀ ∈ S let there be t in `partialUnitriangularGroup (a + 1) ⊓ floorGroup a` and q in
`unipotentBelow (a + 1)` such that t q x has entries of size i and, for each n ∈ S, v / u has size
j for some v congruent to (t n₀ (t n)⁻¹ - 1) e*_a modulo the e_b with b < a (`CongrBelow`). Then
the integral of Φ over N is at most C (c / |ξ u|)^(rank X') |u|^(ρ+1/2) Λ^(100 n (i+j+31)) times
the integral over σ on floor a + 1 of the squared correlation from floor a + 2 on at (σ x, σ y).
Here c = `P.kernelBound`, rank X' = `card F.FreeIndex`, |u|^(ρ+1/2) = `F.floorModulus a u` with ρ
the rank of the vector part of N, Λ = `Γ.loss` is the constant of the gauge, and the n in its
exponent is `𝔰.n`. -/
lemma parseval_heisenbergMeasure_le {S : Set T.G} {i : ℕ} {Φ : T.G → ℝ≥0∞} (ξ u : Aˣ) (ε : ℕ)
    (C : ℝ≥0∞) (hk : F.IsPairingKernel (a + 1) k d) (x y : T.G)
    (h_twist : ∀ s ∈ floorUnipotent a,
      F.levelUnit⁻¹.val * (simpleRootSum (d * s * d⁻¹) - simpleRootSum (s ^ ε)) = ξ * simpleRootSum
        s)
    (hΦ : ∀ n ∈ floorUnipotent a, Φ n ≠ 0 →
      n ∈ S ∧ Φ n ≤ C * ‖F.partialCorrelation (a + 1) k (n ^ ε * x) (n * y)‖ₑ ^ 2)
    (h_centre : ∀ n₀ ∈ S, ∃ t ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a,
      ∃ q ∈ unipotentBelow (a + 1),
      Γ.HasMatrixSize i (t * q * x).val.val ∧
      ∀ n ∈ S, ∃ v : 𝔰.BesselIndex → A,
        CongrBelow a (((t * n₀ * (t * n)⁻¹).val.val - 1) *ᵥ Pi.single (eStar a) 1) v ∧
        u⁻¹.val • v ∈ Γ.vecsOfSize j) :
    ∫⁻ n : T.G, Φ n ∂heisenbergMeasure a ≤
      C * ((P.kernelBound / P.modulus (ξ * u)) ^ Fintype.card F.FreeIndex * F.floorModulus a u *
        Γ.loss ^ (100 * 𝔰.n * (i + j + 31)) *
        ∫⁻ σ : T.G, ‖F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y)‖ₑ ^ 2
          ∂F.floorMeasure (a + 1)) := by
  -- Fix `n₀` in the support of `Φ`, write the element that `h_centre` gives as `t * r`, and
  -- substitute `n = r⁻¹ t⁻¹ n(v) t r n₀`. The correlation at `n` is a Fourier transform read at a
  -- translate of `v.1 / u`, and `h_close` bounds the size of a lift of `(n(v)⁻¹ - 1) e*_a / u`.
  obtain h_zero | h_int := eq_or_ne (∫⁻ n, Φ n ∂heisenbergMeasure a) 0
  · exact h_zero.trans_le zero_le
  obtain ⟨n₀, hn₀, hn₀_ne⟩ : ∃ n₀ ∈ floorUnipotent a, Φ n₀ ≠ 0 :=
    exists_ne_zero_of_ae ae_mem_floorUnipotent h_int
  obtain ⟨hn₀_mem, -⟩ := hΦ n₀ hn₀ hn₀_ne
  obtain ⟨t₀, ht₀, q, hq, h_size, h_close⟩ := h_centre n₀ hn₀_mem
  obtain ⟨t, ht, r, hr, rfl⟩ : ∃ t ∈ floorGroup (a + 1), ∃ r ∈ floorUnipotent a, t₀ = t * r :=
    exists_floorGroup_mul_floorUnipotent ht₀
  obtain ⟨w, rfl⟩ := exists_eq_heisenbergElem_of_mem hr
  obtain ⟨z, rfl⟩ := exists_eq_heisenbergElem_of_mem hn₀
  let N (v : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) : T.G :=
    (P.heisenbergElem a w)⁻¹ * (t⁻¹ * P.heisenbergElem a v * t) *
      (P.heisenbergElem a w * P.heisenbergElem a z)
  have hN (v : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) :
      N v ∈ floorUnipotent a := by
    simp only [N, mul_heisenbergElem (inv_mem ht), inv_mul_cancel_right]
    exact mul_mem (mul_mem (inv_mem hr) (heisenbergElem_mem_floorUnipotent a _)) (mul_mem hr hn₀)
  -- the vector part of `N v` is `t⁻¹ v.1 + z.1`
  have h_fourier (v : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) :
      F.partialCorrelation (a + 1) k (N v ^ ε * x) (N v * y) =
        ∫ σ, ψ ((-ξ * star u).val * star (u⁻¹.val • inclMatrix A Subtype.val *ᵥ v.1 +
            u⁻¹.val • t.val.val *ᵥ inclMatrix A Subtype.val *ᵥ z.1) ⬝ᵥ
              T.splitGram *ᵥ t *ᵥ orbitPoint a.succ σ) *
          F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y) ∂F.floorMeasure (a + 1) := by
    simp only [N, mul_heisenbergElem (inv_mem ht), inv_mul_cancel_right, heisenbergElem_inv,
      heisenbergElem_mul, partialCorrelation_heisenbergElem_eq_integral a hk h_twist]
    congr 3 with σ
    simp only [← add_assoc, ← form_mulVec_mulVec t _ (orbitPoint _ _), mulVec_add,
      inclMatrix_mulVec_floor_block a.2, inv_mem, ht]
    simp [← inverse_star_unit, star_mulVec_dotProduct, mul_add, mul_assoc]
  -- the measure is invariant under the group on both sides and under conjugation by `t`
  have h_subst : ∫⁻ n, Φ n ∂heisenbergMeasure a =
      ∫⁻ n, Φ ((P.heisenbergElem a w)⁻¹ * (t⁻¹ * n * t) *
        (P.heisenbergElem a w * P.heisenbergElem a z)) ∂heisenbergMeasure a := by
    obtain ⟨-, h_left⟩ := heisenbergMeasure_mconv_dirac hr
    obtain ⟨h_right, -⟩ := heisenbergMeasure_mconv_dirac (mul_mem hr hn₀)
    rw [lintegral_eq_of_dirac_mconv_eq (h_left.trans h_right.symm),
      lintegral_eq_of_dirac_mconv_eq (dirac_mconv_heisenbergMeasure_comm ht)]
  have h_unip : t⁻¹ * (t * P.heisenbergElem a w * q) ∈ unipotentBelow (a + 1) := by
    simpa [mul_assoc] using mul_mem (Subgroup.mem_inf.1 hr).right hq
  rw [h_subst]
  -- Plancherel's bound on floor `a + 1`, at the frequency `-ξ * star u`
  refine lintegral_heisenbergMeasure_le (j := j) u
    (Γ.correlation_plancherel (b := a.succ) ht h_size hk y h_unip (-ξ * star u)
      (u⁻¹.val • t.val.val *ᵥ inclMatrix A Subtype.val *ᵥ z.1) (.inl rfl))
    fun v h_ne ↦ ?_
  obtain ⟨h_mem, h_le⟩ :
      N v ∈ S ∧ Φ (N v) ≤ C * ‖F.partialCorrelation (a + 1) k (N v ^ ε * x) (N v * y)‖ₑ ^ 2 :=
    hΦ (N v) (hN v) h_ne
  have h_inv : t * P.heisenbergElem a w * P.heisenbergElem a z *
      (t * P.heisenbergElem a w * N v)⁻¹ = (P.heisenbergElem a v)⁻¹ := by
    simp only [N]
    group
  rw [h_fourier v] at h_le
  refine ⟨?_, h_le⟩
  rw [← h_inv]
  exact h_close (N v) h_mem

end New.Floors.Gauge
