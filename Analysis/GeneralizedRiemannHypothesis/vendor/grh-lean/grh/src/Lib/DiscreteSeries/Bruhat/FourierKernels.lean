import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Lib.DiscreteSeries.Bruhat.FloorMeasures
import Lib.DiscreteSeries.Bruhat.QuadricBlocks

/-!
# Fourier kernels between solved measures

The measure theory, valid at any place, that bounds the kernel ψ(ξ ⟨v, y⟩), tested on measurable
integrable functions that vanish off a given set. The square norm of a function is the square of its
L² norm. A measure that is solved in a block has three kinds of coordinates: those of the block,
whose measures give bounded mass to a box; inner coordinates, in which Plancherel's inequality is
applied; and the remaining outer coordinates, which are estimated by the volume of a box.

* `New.Floors.Place.FourierSqNormLe`: the kernel ψ(ξ ⟨v, y⟩) multiplies square norms by at most a
  given constant. The bound passes to images of the measures.
* `New.Floors.Place.IsSolvedIn.setLIntegral_le`: a bound for the integral, over a box, of a function
  of the inner coordinates by its integral in those coordinates alone.
* `New.Floors.Place.IsSolvedIn.fourierSqNormLe`: the bound for the kernel between two measures that
  are solved in two disjoint blocks.

Notions from other files:
* `New.Floors.Place`: a place A, with its character ψ, its modulus |·| = `modulus` and the constant
  c = `kernelBound` of Plancherel's inequality.
* `New.Floors.Place.IsSolvedIn`: a measure on A^κ is the volume in the coordinates off a block times
  a family of measures in the coordinates of the block, each of mass at most M on a box.
* `New.Floors.coordinateBox`: the box of a set R, that is, the vectors with all coordinates in R.

## Relation to the literature
Standard consequences of Fubini's theorem and the inequalities of Cauchy–Schwarz and Plancherel.
-/

namespace New.Floors

open Matrix MeasureTheory Measure ProbabilityTheory ENNReal Fintype Set Sum

/-- Cauchy–Schwarz on the support: if g vanishes off S, then the square of its integral is at most
μ(S) times the integral of its square over S. -/
lemma enorm_integral_sq_le {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {g : Y → ℂ} {S : Set Y}
    (hg_meas : AEStronglyMeasurable g μ) (hg_supp : ∀ y : Y, g y ≠ 0 → y ∈ S) :
    ‖∫ y : Y, g y ∂μ‖ₑ ^ 2 ≤ μ S * ∫⁻ y : Y in S, ‖g y‖ₑ ^ 2 ∂μ := by
  have h_supp : Function.support (fun y : Y ↦ ‖g y‖ₑ) ⊆ S :=
    fun y hy ↦ hg_supp y (enorm_ne_zero.1 hy)
  have h_cs : (∫⁻ y : Y in S, ‖g y‖ₑ ∂μ) ^ 2 ≤
      (∫⁻ _ : Y in S, 1 ∂μ) * ∫⁻ y : Y in S, ‖g y‖ₑ ^ 2 ∂μ :=
    sq_lintegral_le aemeasurable_const (hg_meas.enorm.pow_const 2).restrict
      fun y : Y ↦ (one_mul (‖g y‖ₑ ^ 2)).ge
  grw [enorm_integral_le_lintegral_enorm, ← setLIntegral_eq_of_support_subset h_supp, h_cs,
    setLIntegral_one]

section Fibres

variable {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z] {ν : Measure W} {ζ : Kernel W Z}
  [SFinite ν] [IsSFiniteKernel ζ] {V : Set Z} {M : ℝ≥0∞}

/-- Let each measure ζ(w) give mass at most M to V. The integral over B × V of a function of the
first variable is at most M times its integral over B. -/
lemma setLIntegral_comp_fst_le {B : Set W} {F : W → ℝ≥0∞} (hB : MeasurableSet B)
    (hV : MeasurableSet V) (h_fibre : ∀ w : W, ζ w V ≤ M) (hF : Measurable F) :
    ∫⁻ p : W × Z in B ×ˢ V, F p.1 ∂ν ⊗ₘ ζ ≤ M * ∫⁻ w : W in B, F w ∂ν := by
  rw [Measure.setLIntegral_compProd (by fun_prop) hB hV, ← lintegral_const_mul M hF]
  refine lintegral_mono fun w ↦ ?_
  grw [← h_fibre w, mul_comm]
  exact (setLIntegral_const V (F w)).le

/-- Cauchy–Schwarz in the fibres. Let each measure ζ(w) give mass at most M to V, and let f vanish
unless its second variable lies in V. Integration over the fibres multiplies the square norm of f by
at most M. -/
lemma lintegral_enorm_integral_kernel_sq_le {f : W × Z → ℂ} (hf : Measurable f)
    (h_supp : ∀ p : W × Z, f p ≠ 0 → p.2 ∈ V) (h_fibre : ∀ w : W, ζ w V ≤ M) :
    ∫⁻ w : W, ‖∫ z : Z, f (w, z) ∂ζ w‖ₑ ^ 2 ∂ν ≤ M * ∫⁻ p : W × Z, ‖f p‖ₑ ^ 2 ∂ν ⊗ₘ ζ := by
  rw [Measure.lintegral_compProd (by fun_prop),
    ← lintegral_const_mul M (Measurable.lintegral_kernel_prod_right (by fun_prop))]
  refine lintegral_mono fun w ↦ ?_
  have h_cs : ‖∫ z : Z, f (w, z) ∂ζ w‖ₑ ^ 2 ≤
      ζ w V * ∫⁻ z : Z in V, ‖f (w, z)‖ₑ ^ 2 ∂ζ w :=
    enorm_integral_sq_le (hf.comp measurable_prodMk_left).aestronglyMeasurable
      fun z ↦ h_supp (w, z)
  grw [h_cs, h_fibre w, setLIntegral_le_lintegral]

/-- The integral over the fibres of an integrable function is integrable. -/
lemma integrable_integral_kernel {f : W × Z → ℂ} (hf_meas : Measurable f)
    (hf_int : Integrable f (ν ⊗ₘ ζ)) : Integrable (fun w : W ↦ ∫ z : Z, f (w, z) ∂ζ w) ν := by
  obtain ⟨-, h_norm⟩ :=
    (Measure.integrable_compProd_iff hf_int.aestronglyMeasurable).1 hf_int
  exact h_norm.mono' hf_meas.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
    (.of_forall fun _ ↦ norm_integral_le_integral_norm _)

/-- Cauchy–Schwarz in the first of three variables (y, w, z). If f vanishes unless y lies in S, then
the square of its integral is at most μ(S) times the integral over y of the square of its integral
over w and z. -/
lemma enorm_integral_prod_compProd_sq_le {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]
    {η : Kernel (Y × W) Z} [IsSFiniteKernel η] {f : (Y × W) × Z → ℂ} {S : Set Y}
    (hf_meas : Measurable f) (hf_int : Integrable f ((μ.prod ν) ⊗ₘ η))
    (h_supp : ∀ p : (Y × W) × Z, f p ≠ 0 → p.1.1 ∈ S) :
    ‖∫ p : (Y × W) × Z, f p ∂(μ.prod ν) ⊗ₘ η‖ₑ ^ 2 ≤
      μ S * ∫⁻ y : Y, ‖∫ w : W, ∫ z : Z, f ((y, w), z) ∂η (y, w) ∂ν‖ₑ ^ 2 ∂μ := by
  have h_fibre : Integrable (fun q : Y × W ↦ ∫ z : Z, f (q, z) ∂η q) (μ.prod ν) :=
    integrable_integral_kernel hf_meas hf_int
  have h_supp' (y : Y) (hy : ∫ w : W, ∫ z : Z, f ((y, w), z) ∂η (y, w) ∂ν ≠ 0) : y ∈ S := by
    obtain ⟨w, hw⟩ := exists_ne_zero_of_integral_ne_zero hy
    obtain ⟨z, hz⟩ := exists_ne_zero_of_integral_ne_zero hw
    exact h_supp ((y, w), z) hz
  rw [Measure.integral_compProd hf_int, integral_prod _ h_fibre]
  grw [enorm_integral_sq_le h_fibre.integral_prod_left.aestronglyMeasurable h_supp',
    setLIntegral_le_lintegral]

end Fibres

namespace Place

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {κ n : Type} [Fintype κ] [Fintype n] {J : Matrix κ κ A} {ξ : A} {ρ' ρ : Measure (κ → A)}
  {S' S : Set (κ → A)} {C : ℝ≥0∞}

/-- The kernel ψ(ξ ⟨v, y⟩), with ψ the character of the place and ⟨v, y⟩ = v* J y, multiplies
square norms by at most C from the functions on (S, ρ) to the functions on (S', ρ'). It is tested on
the measurable integrable functions φ that vanish off S. -/
def FourierSqNormLe (J : Matrix κ κ A) (ξ : A) (ρ' ρ : Measure (κ → A)) (S' S : Set (κ → A))
    (C : ℝ≥0∞) : Prop :=
  ∀ φ : (κ → A) → ℂ, Measurable φ → Integrable φ ρ → (∀ y : κ → A, φ y ≠ 0 → y ∈ S) →
    ∫⁻ v : κ → A in S', ‖∫ y : κ → A, ψ (ξ * star v ⬝ᵥ J *ᵥ y) * φ y ∂ρ‖ₑ ^ 2 ∂ρ' ≤
      C * ∫⁻ y : κ → A, ‖φ y‖ₑ ^ 2 ∂ρ

/-- The constant may be enlarged. -/
lemma FourierSqNormLe.mono {C' : ℝ≥0∞} (h : FourierSqNormLe J ξ ρ' ρ S' S C) (hC : C ≤ C') :
    FourierSqNormLe J ξ ρ' ρ S' S C' := by
  intro φ hφ_meas hφ_int hφ_supp
  grw [h φ hφ_meas hφ_int hφ_supp, hC]

/-- A bound for the kernel (`FourierSqNormLe`) passes to the images of the two measures under maps
f', f with ξ₁ ⟨f' v, f y⟩ = ξ ⟨v, y⟩ for all v, y; the two products are formed with J₁ and J. It
holds on all sets U', U, with U' measurable, whose preimages lie in S', S. -/
lemma FourierSqNormLe.map {J₁ : Matrix n n A} {ξ₁ : A} {f' f : (κ → A) → n → A}
    {U' U : Set (n → A)} (h : FourierSqNormLe J ξ ρ' ρ S' S C) (hf' : Measurable f')
    (hf : Measurable f)
    (h_phase : ∀ v y : κ → A, ξ₁ * star (f' v) ⬝ᵥ J₁ *ᵥ f y = ξ * star v ⬝ᵥ J *ᵥ y)
    (hU' : MeasurableSet U') (h_sub' : ∀ v : κ → A, f' v ∈ U' → v ∈ S')
    (h_sub : ∀ y : κ → A, f y ∈ U → y ∈ S) :
    FourierSqNormLe J₁ ξ₁ (ρ'.map f') (ρ.map f) U' U C := by
  intro φ hφ_meas hφ_int hφ_supp
  have h_transform (v : κ → A) :
      ∫ y : n → A, ψ (ξ₁ * star (f' v) ⬝ᵥ J₁ *ᵥ y) * φ y ∂ρ.map f =
        ∫ y : κ → A, ψ (ξ * star v ⬝ᵥ J *ᵥ y) * φ (f y) ∂ρ := by
    rw [integral_map hf.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))]
    simp only [h_phase]
  calc ∫⁻ v : n → A in U', ‖∫ y : n → A, ψ (ξ₁ * star v ⬝ᵥ J₁ *ᵥ y) * φ y ∂ρ.map f‖ₑ ^ 2
        ∂ρ'.map f'
      ≤ ∫⁻ v : κ → A in S', ‖∫ y : κ → A, ψ (ξ * star v ⬝ᵥ J *ᵥ y) * φ (f y) ∂ρ‖ₑ ^ 2 ∂ρ' := by
        grw [restrict_map hf' hU', lintegral_map_le _ hf'.aemeasurable]
        simp only [h_transform]
        exact lintegral_mono_set h_sub'
    _ ≤ C * ∫⁻ y : κ → A, ‖φ (f y)‖ₑ ^ 2 ∂ρ :=
        h (φ ∘ f) (hφ_meas.comp hf) (hφ_int.comp_measurable hf)
          fun y hy ↦ h_sub y (hφ_supp (f y) hy)
    _ = C * ∫⁻ y : n → A, ‖φ y‖ₑ ^ 2 ∂ρ.map f := by rw [lintegral_map (by fun_prop) hf]

variable {ι B B' : Type} [Fintype ι] [Fintype B'] {blk : B → κ} {blk' : B' → κ}
  {inner : ι → κ} {R R' : Set A} {M M' : ℝ≥0∞}

omit [Fintype κ] [Fintype n] in
/-- Multiplication by a value of ψ preserves the absolute value. -/
lemma enorm_psi_mul (x : A) (z : ℂ) : ‖P.ψ x * z‖ₑ = ‖z‖ₑ := by
  simp [← ofReal_norm (P.ψ x), norm_psi]

/-- Plancherel's inequality in the second of two variables: the partial Fourier transform multiplies
square norms by at most (c / |ξ|)^(card ι), where c = `kernelBound` and |·| = `modulus`. -/
lemma lintegral_lintegral_fourier_le [DecidableEq ι] {Y : Type} [MeasurableSpace Y] {μ : Measure Y}
    [SFinite μ] (ξ : Aˣ) {g : Y × (ι → A) → ℂ} (hg_meas : Measurable g)
    (hg_int : Integrable g (μ.prod volume)) :
    ∫⁻ w' : ι → A, ∫⁻ y : Y, ‖∫ w : ι → A, P.ψ (ξ * star w' ⬝ᵥ w) * g (y, w)‖ₑ ^ 2 ∂μ ≤
      (P.kernelBound / P.modulus ξ) ^ card ι * ∫⁻ q : Y × (ι → A), ‖g q‖ₑ ^ 2 ∂μ.prod volume := by
  have h_meas : Measurable fun q : (ι → A) × Y ↦
      ‖∫ w : ι → A, P.ψ (ξ * star q.1 ⬝ᵥ w) * g (q.2, w)‖ₑ ^ 2 :=
    (StronglyMeasurable.integral_prod_right
      (Measurable.stronglyMeasurable (by fun_prop))).measurable.enorm.pow_const 2
  rw [lintegral_lintegral_swap h_meas.aemeasurable, lintegral_prod _ (by fun_prop),
    ← lintegral_const_mul _ (by fun_prop)]
  refine lintegral_mono_ae (hg_int.prod_right_ae.mono fun y hy ↦ ?_)
  exact plancherel_inequality ξ hy (by fun_prop)

/-- Plancherel's inequality in w, after Cauchy–Schwarz in z. Let each measure ζ(y, w) give mass at
most M to V, and let f(y, w, z) vanish unless z lies in V. The partial Fourier transform in w of the
integral of f over z has square norm at most (c / |ξ|)^(card ι) M times that of f. Here ψ is the
character of the place, c = `kernelBound` and |·| = `modulus`. -/
lemma lintegral_lintegral_fourier_integral_kernel_le [DecidableEq ι] {Y Z : Type}
    [MeasurableSpace Y] [MeasurableSpace Z] {μ : Measure Y} [SFinite μ]
    {ζ : Kernel (Y × (ι → A)) Z} [IsSFiniteKernel ζ] {V : Set Z} {M : ℝ≥0∞} (ξ : Aˣ)
    {f : (Y × (ι → A)) × Z → ℂ} (hf_meas : Measurable f)
    (hf_int : Integrable f ((μ.prod volume) ⊗ₘ ζ))
    (h_supp : ∀ p : (Y × (ι → A)) × Z, f p ≠ 0 → p.2 ∈ V)
    (h_fibre : ∀ q : Y × (ι → A), ζ q V ≤ M) :
    ∫⁻ w' : ι → A, ∫⁻ y : Y,
        ‖∫ w : ι → A, P.ψ (ξ * star w' ⬝ᵥ w) * ∫ z : Z, f ((y, w), z) ∂ζ (y, w)‖ₑ ^ 2 ∂μ ≤
      (P.kernelBound / P.modulus ξ) ^ card ι *
        (M * ∫⁻ p : (Y × (ι → A)) × Z, ‖f p‖ₑ ^ 2 ∂(μ.prod volume) ⊗ₘ ζ) := by
  grw [lintegral_lintegral_fourier_le ξ
      hf_meas.stronglyMeasurable.integral_kernel_prod_right'.measurable
      (integrable_integral_kernel hf_meas hf_int),
    lintegral_enorm_integral_kernel_sq_le hf_meas h_supp h_fibre]

/-- The vector with outer coordinates p.1.1, inner coordinates p.1.2 and coordinates p.2 in the
block, along a bijection e of indices. -/
def blockChart {η : Type} (e : (η ⊕ ι) ⊕ B ≃ κ) (p : ((η → A) × (ι → A)) × (B → A)) : κ → A :=
  ((p.1.1 ⊕ᵥ p.1.2) ⊕ᵥ p.2) ∘ e.symm

omit [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] P [Fintype κ] [Fintype ι]
  in
/-- A vector lies in the box of R exactly when its three parts do. -/
lemma preimage_blockChart_coordinateBox {η : Type} (e : (η ⊕ ι) ⊕ B ≃ κ) (R : Set A) :
    blockChart e ⁻¹' coordinateBox κ R =
      (coordinateBox η R ×ˢ coordinateBox ι R) ×ˢ coordinateBox B R := by
  ext p
  simp [blockChart, e.surjective.forall]

omit [CommRing A] [StarRing A] [TopologicalSpace A] P in
/-- The box of a measurable set is measurable. -/
lemma measurableSet_coordinateBox (κ : Type) [Fintype κ] (hR : MeasurableSet R) :
    MeasurableSet (coordinateBox κ R) :=
  (MeasurableSet.univ_pi fun _ : κ ↦ hR).congr (Set.ext fun x ↦ by simp)

omit [CommRing A] [StarRing A] [TopologicalSpace A] P [Fintype κ] in
/-- If T(y, w, z) ≤ K H(y, w), the integral of H(y, w) over all w is at most D, and each measure
ζ(y, w) gives mass at most M to V, then the integral of T over (S × U) × V is at most K M D μ(S). -/
lemma setLIntegral_le_of_le_comp_fst {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    [SFinite (volume : Measure (ι → A))] {μ : Measure Y} [SFinite μ]
    {ζ : Kernel (Y × (ι → A)) Z} [IsSFiniteKernel ζ] {S : Set Y} {U : Set (ι → A)} {V : Set Z}
    {M K D : ℝ≥0∞} {T : (Y × (ι → A)) × Z → ℝ≥0∞} {H : Y × (ι → A) → ℝ≥0∞}
    (hS : MeasurableSet S) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (h_fibre : ∀ q : Y × (ι → A), ζ q V ≤ M) (hH : Measurable H)
    (hT : ∀ p : (Y × (ι → A)) × Z, T p ≤ K * H p.1)
    (hD : ∀ y : Y, ∫⁻ w : ι → A, H (y, w) ≤ D) :
    ∫⁻ p : (Y × (ι → A)) × Z in (S ×ˢ U) ×ˢ V, T p ∂(μ.prod volume) ⊗ₘ ζ ≤
      K * (M * (D * μ S)) := by
  calc _ ≤ K * (M * ∫⁻ q : Y × (ι → A) in S ×ˢ univ, H q ∂μ.prod volume) := by
        grw [lintegral_mono hT, lintegral_const_mul _ (by fun_prop),
          setLIntegral_comp_fst_le (hS.prod hU) hV h_fibre hH,
          lintegral_mono_set (prod_mono_right (subset_univ U))]
    _ ≤ K * (M * (D * μ S)) := by
        grw [← prod_restrict, restrict_univ, lintegral_prod _ (by fun_prop), lintegral_mono hD,
          setLIntegral_const]

omit [Fintype n] in
/-- The square of the transform of φ is a measurable function of its variable v. -/
lemma measurable_enorm_integral_fourier_sq [SFinite ρ] {φ : (κ → A) → ℂ} (hφ : Measurable φ)
    (J : Matrix κ κ A) (ξ : A) :
    Measurable fun v : κ → A ↦ ‖∫ y : κ → A, P.ψ (ξ * star v ⬝ᵥ J *ᵥ y) * φ y ∂ρ‖ₑ ^ 2 :=
  (StronglyMeasurable.integral_prod_right
    (Measurable.stronglyMeasurable (by fun_prop))).measurable.enorm.pow_const 2

omit [Fintype κ] in
/-- The square norm in y of the partial Fourier transform in w of the integral over z of a
measurable f(y', y, w, z) is a measurable function of y' and w'. -/
lemma measurable_lintegral_fourier_integral_kernel {Y Y' Z : Type} [MeasurableSpace Y]
    [MeasurableSpace Y'] [MeasurableSpace Z] {μ : Measure Y} [SFinite μ]
    {ζ : Kernel (Y × (ι → A)) Z} [IsSFiniteKernel ζ] (ξ : A) {f : Y' → (Y × (ι → A)) × Z → ℂ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun q' : Y' × (ι → A) ↦ ∫⁻ y : Y, ‖∫ w : ι → A, P.ψ (ξ * star q'.2 ⬝ᵥ w) *
      ∫ z : Z, f q'.1 ((y, w), z) ∂ζ (y, w)‖ₑ ^ 2 ∂μ := by
  let g (y' : Y') (q : Y × (ι → A)) : ℂ := ∫ z : Z, f y' (q, z) ∂ζ q
  have hg : Measurable (Function.uncurry g) :=
    (StronglyMeasurable.integral_kernel_prod_right (κ := ζ.prodMkLeft Y')
      (f := fun r z ↦ f r.1 (r.2, z)) (Measurable.stronglyMeasurable (by fun_prop))).measurable
  change Measurable fun q' : Y' × (ι → A) ↦
    ∫⁻ y : Y, ‖∫ w : ι → A, P.ψ (ξ * star q'.2 ⬝ᵥ w) * g q'.1 (y, w)‖ₑ ^ 2 ∂μ
  refine Measurable.lintegral_prod_right (Measurable.pow_const (Measurable.enorm ?_) 2)
  exact (StronglyMeasurable.integral_prod_right
    (Measurable.stronglyMeasurable (by fun_prop))).measurable

/-- Cauchy–Schwarz in the outer coordinates. Let a chart x(y, w, z) carry (μ × volume) ⊗ ζ to ρ, let
φ(x(y, w, z)) vanish unless y lies in S, and let the product v* J x(y, w, z) be b(y) + w'*w +
a(y, w, z). The square of the transform of φ at v is at most μ(S) times the square norm in y of the
partial Fourier transform at w' of the integral of ψ(ξ a) φ(x) over z. -/
lemma enorm_integral_fourier_sq_le {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    {μ : Measure Y} [SFinite μ] {ζ : Kernel (Y × (ι → A)) Z} [IsSFiniteKernel ζ]
    {x : (Y × (ι → A)) × Z → κ → A}
    (h_chart : MeasurePreserving x ((μ.prod volume) ⊗ₘ ζ) ρ) {φ : (κ → A) → ℂ}
    (hφ_meas : Measurable φ) (hφ_int : Integrable φ ρ) {S : Set Y}
    (h_supp : ∀ p : (Y × (ι → A)) × Z, φ (x p) ≠ 0 → p.1.1 ∈ S) (ξ : A) (v : κ → A)
    (w' : ι → A) {b : Y → A} {a : (Y × (ι → A)) × Z → A}
    (h_phase : ∀ p : (Y × (ι → A)) × Z,
      star v ⬝ᵥ J *ᵥ x p = b p.1.1 + (star w' ⬝ᵥ p.1.2 + a p)) :
    ‖∫ y : κ → A, P.ψ (ξ * star v ⬝ᵥ J *ᵥ y) * φ y ∂ρ‖ₑ ^ 2 ≤
      μ S * ∫⁻ y : Y, ‖∫ w : ι → A, P.ψ (ξ * star w' ⬝ᵥ w) *
        ∫ z : Z, P.ψ (ξ * a ((y, w), z)) * φ (x ((y, w), z)) ∂ζ (y, w)‖ₑ ^ 2 ∂μ := by
  have h_meas : Measurable x := h_chart.measurable
  let term (p : (Y × (ι → A)) × Z) : ℂ := P.ψ (ξ * star v ⬝ᵥ J *ᵥ x p) * φ (x p)
  have h_int : Integrable term ((μ.prod volume) ⊗ₘ ζ) :=
    (h_chart.integrable_comp_of_integrable hφ_int).bdd_mul (c := 1)
      (Measurable.aestronglyMeasurable (by fun_prop)) (by simp [norm_psi])
  rw [← h_chart.map_eq, integral_map h_meas.aemeasurable (by fun_prop)]
  grw [enorm_integral_prod_compProd_sq_le (by fun_prop) h_int
    fun p hp ↦ h_supp p (right_ne_zero_of_mul hp)]
  simp only [term, h_phase, mul_add, AddChar.map_add_eq_mul, mul_assoc, integral_const_mul,
    enorm_psi_mul, le_refl]

omit [TopologicalSpace A] [MeasureSpace A] [StarRing A] P [Fintype κ] [Fintype ι] [Fintype B'] in
/-- Indices given by an injective map that avoids the inner coordinates and the block of the chart
are outer coordinates. -/
lemma exists_inl_inl_eq_of_injective {η : Type} (e : (η ⊕ ι) ⊕ B ≃ κ)
    (h_inj : Function.Injective ((e ∘ inl ∘ inr) ⊕ᵥ (blk' ⊕ᵥ (e ∘ inr)))) (i : B') :
    ∃ k : η, e (inl (inl k)) = blk' i := by
  obtain ⟨(k | k) | k, hk⟩ := e.surjective (blk' i)
  · exact ⟨k, hk⟩
  · have h_eq : (inl k : ι ⊕ (B' ⊕ B)) = inr (inl i) := h_inj hk
    exact absurd h_eq inl_ne_inr
  · have h_eq : (inr (inr k) : ι ⊕ (B' ⊕ B)) = inr (inl i) := h_inj hk
    exact absurd (inr_injective h_eq) inr_ne_inl

omit [TopologicalSpace A] [MeasureSpace A] P in
/-- The product v* J y for v = `blockChart e' p'` and y = `blockChart e p`, two charts with the same
inner indices, where the rows of J at these indices and at the block of v are those of the identity
matrix and `out` locates that block among the outer indices of y. In a triple, p.1.1 is outer, p.1.2
inner and p.2 in the block. The product is that of the block of v with outer coordinates of y, plus
that of the inner coordinates, plus the term of the outer coordinates of v. -/
lemma star_blockChart_dotProduct_mulVec [DecidableEq κ] {η η' : Type} [Fintype η']
    (e : (η ⊕ ι) ⊕ B ≃ κ) (e' : (η' ⊕ ι) ⊕ B' ≃ κ) {J : Matrix κ κ A} {out : B' → η}
    (h_inner : e' ∘ inl ∘ inr = e ∘ inl ∘ inr)
    (h_out : ∀ i : B', e (inl (inl (out i))) = e' (inr i))
    (h_orth : ∀ (i : ι ⊕ B') (k : κ), J (((e ∘ inl ∘ inr) ⊕ᵥ (e' ∘ inr)) i) k =
      (1 : Matrix κ κ A) (((e ∘ inl ∘ inr) ⊕ᵥ (e' ∘ inr)) i) k)
    (p' : ((η' → A) × (ι → A)) × (B' → A)) (p : ((η → A) × (ι → A)) × (B → A)) :
    star (blockChart e' p') ⬝ᵥ J *ᵥ blockChart e p =
      star p'.2 ⬝ᵥ p.1.1 ∘ out + (star p'.1.2 ⬝ᵥ p.1.2 +
        star p'.1.1 ⬝ᵥ (J *ᵥ blockChart e p) ∘ e' ∘ inl ∘ inl) := by
  have h_row (i : ι ⊕ B') (x : κ → A) :
      (J *ᵥ x) (((e ∘ inl ∘ inr) ⊕ᵥ (e' ∘ inr)) i) = x (((e ∘ inl ∘ inr) ⊕ᵥ (e' ∘ inr)) i) := by
    simp only [mulVec, dotProduct, h_orth i]
    exact congrFun (one_mulVec x) _
  have h_inner_entry (i : ι) : (J *ᵥ blockChart e p) (e' (inl (inr i))) = p.1.2 i := by
    have h_index : e' (inl (inr i)) = e (inl (inr i)) := congrFun h_inner i
    have h_eq : (J *ᵥ blockChart e p) (e (inl (inr i))) = blockChart e p (e (inl (inr i))) :=
      h_row (inl i) _
    rw [h_index, h_eq]
    simp [blockChart]
  have h_block_entry (i : B') : (J *ᵥ blockChart e p) (e' (inr i)) = p.1.1 (out i) := by
    have h_eq : (J *ᵥ blockChart e p) (e' (inr i)) = blockChart e p (e' (inr i)) :=
      h_row (inr i) _
    rw [h_eq, ← h_out]
    simp [blockChart]
  rw [dotProduct, ← e'.sum_comp]
  simp [blockChart.eq_def e', dotProduct, h_inner_entry, h_block_entry, add_comm]

variable [Fintype B]

/-- Let ρ be solved in a block, that is, let it be the volume in the free coordinates times measures
of mass at most M on the box of R in the block, and let inner coordinates off the block be given.
The free coordinates split into the inner ones and the rest, the outer ones. In `blockChart`, ρ is
the volume in the outer and the inner coordinates times such measures. -/
lemma IsSolvedIn.exists_blockChart (h : IsSolvedIn blk ρ R M)
    (h_inj : Function.Injective (inner ⊕ᵥ blk)) :
    ∃ (η : Type) (_ : Fintype η) (e : (η ⊕ ι) ⊕ B ≃ κ)
      (ζ : Kernel ((η → A) × (ι → A)) (B → A)) (_ : IsSFiniteKernel ζ),
      e ∘ inl ∘ inr = inner ∧ e ∘ inr = blk ∧ card η = card κ - card ι - card B ∧
      MeasurePreserving (blockChart e) ((volume.prod volume) ⊗ₘ ζ) ρ ∧
      ∀ q : (η → A) × (ι → A), ζ q (coordinateBox B R) ≤ M := by
  classical
  obtain ⟨η₀, _, e₀, ζ, rfl, _, h_chart, h_mass⟩ := h
  -- Each inner index is a free index `j i`, and `f` lists the free indices.
  have h_free (i : ι) : ∃ k : η₀, e₀ (inl k) = inner i := by
    obtain ⟨k | k, hk⟩ := e₀.surjective (inner i)
    · exact ⟨k, hk⟩
    · have h_eq : (inr k : ι ⊕ B) = inl i := h_inj hk
      exact absurd h_eq inr_ne_inl
  choose j hj using h_free
  have hj_inj : Function.Injective j := fun i i' h_eq ↦ by
    have h_eq' : inner i = inner i' := by rw [← hj, ← hj, h_eq]
    have h_index : (inl i : ι ⊕ B) = inl i' := h_inj h_eq'
    exact inl_injective h_index
  obtain ⟨η, _, f, rfl⟩ := exists_equiv_comp_inr_eq hj_inj
  let e : (η ⊕ ι) ⊕ B ≃ κ := (f.sumCongr (.refl B)).trans e₀
  let join (q : (η → A) × (ι → A)) : η₀ → A := (q.1 ⊕ᵥ q.2) ∘ f.symm
  have h_join : MeasurePreserving join (volume.prod volume) volume :=
    ((volume_measurePreserving_piCongrLeft (fun _ : η ⊕ ι ↦ A) f.symm).symm _).comp
      measurePreserving_sumElim
  have h_base : MeasurePreserving (Prod.map join id)
      ((volume.prod volume) ⊗ₘ ζ.comap join h_join.measurable) (volume ⊗ₘ ζ) := by
    refine ⟨h_join.measurable.prodMap measurable_id, ext_of_lintegral _ fun F hF ↦ ?_⟩
    have h_meas : Measurable join := h_join.measurable
    rw [lintegral_map hF (by fun_prop), Measure.lintegral_compProd (by fun_prop),
      Measure.lintegral_compProd hF,
      ← h_join.lintegral_comp hF.lintegral_kernel_prod_right']
    simp only [Kernel.comap_apply, Prod.map_apply, id_eq]
  refine ⟨η, inferInstance, e, ζ.comap join h_join.measurable, inferInstance, funext hj, rfl, ?_,
    ?_, fun q ↦ h_mass (join q)⟩
  · rw [← card_congr e, card_sum, card_sum]
    lia
  · suffices h_eq : blockChart e =
        (fun p ↦ (p.1 ⊕ᵥ p.2) ∘ e₀.symm) ∘ Prod.map join id by
      rw [h_eq]
      exact h_chart.comp h_base
    ext p k
    obtain ⟨k | k, rfl⟩ := e₀.surjective k
    · simp [blockChart, e, join]
    · simp [blockChart, e, join]

/-- Let ρ be solved in a block with fibres of mass at most M on the box of R, that is, let it be the
volume in the coordinates off the block times such measures in the block. For a function G of inner
coordinates off the block, the integral over the box of R is at most the volume of the box in the
outer coordinates, times M, times the integral of G over the box in A^ι. -/
theorem IsSolvedIn.setLIntegral_le (h : IsSolvedIn blk ρ R M) (hR : MeasurableSet R)
    (h_inj : Function.Injective (inner ⊕ᵥ blk)) {G : (ι → A) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x : κ → A in coordinateBox κ R, G (x ∘ inner) ∂ρ ≤
      volume R ^ (card κ - card ι - card B) * M * ∫⁻ w : ι → A in coordinateBox ι R, G w := by
  obtain ⟨η, _, e, ζ, _, rfl, rfl, h_card, h_chart, h_mass⟩ := h.exists_blockChart h_inj
  calc ∫⁻ x : κ → A in coordinateBox κ R, G (x ∘ e ∘ inl ∘ inr) ∂ρ
    _ = ∫⁻ p : ((η → A) × (ι → A)) × (B → A) in
          (coordinateBox η R ×ˢ coordinateBox ι R) ×ˢ coordinateBox B R, G p.1.2
          ∂(volume.prod volume) ⊗ₘ ζ := by
      rw [← h_chart.setLIntegral_comp_preimage (measurableSet_coordinateBox κ hR) (by fun_prop),
        preimage_blockChart_coordinateBox]
      simp [blockChart, Function.comp_def]
    _ ≤ M * ∫⁻ q : (η → A) × (ι → A) in coordinateBox η R ×ˢ coordinateBox ι R, G q.2
          ∂volume.prod volume :=
      setLIntegral_comp_fst_le (F := fun q : (η → A) × (ι → A) ↦ G q.2)
        ((measurableSet_coordinateBox η hR).prod (measurableSet_coordinateBox ι hR))
        (measurableSet_coordinateBox B hR) h_mass (by fun_prop)
    _ = volume R ^ (card κ - card ι - card B) * M *
          ∫⁻ w : ι → A in coordinateBox ι R, G w := by
      rw [← prod_restrict, lintegral_prod _ (by fun_prop)]
      simp only [lintegral_const, restrict_apply_univ, volume_coordinateBox, h_card]
      ring

/-- Let ρ be solved in the block `blk`, meaning it is the volume in the other coordinates times an
s-finite kernel of block measures, each of mass at most M on the box of R (vectors with all
coordinates in R). Let ρ' be solved likewise in `blk'` with M' and a measurable R', and let the
inner coordinates and both blocks be pairwise disjoint. If the rows of J at the inner indices and at
`blk'` are those of the identity, then for a unit ξ the kernel ψ(ξ v* J y), with ψ the character of
the place, multiplies square norms from the box of R with ρ to the box of R' with ρ' by at most
(c / |ξ|) per inner coordinate (c = `kernelBound`, |·| = `modulus`), times M, M' and the volume of R
(resp. R') raised to the number of coordinates outside the inner ones and `blk` (resp. `blk'`). -/
theorem IsSolvedIn.fourierSqNormLe [DecidableEq ι] [DecidableEq κ] (h' : IsSolvedIn blk' ρ' R' M')
    (h : IsSolvedIn blk ρ R M) (hR' : MeasurableSet R')
    (h_inj : Function.Injective (inner ⊕ᵥ (blk' ⊕ᵥ blk))) {J : Matrix κ κ A}
    (h_orth : ∀ (i : ι ⊕ B') (k : κ),
      J ((inner ⊕ᵥ blk') i) k = (1 : Matrix κ κ A) ((inner ⊕ᵥ blk') i) k) (ξ : Aˣ) :
    FourierSqNormLe J ξ ρ' ρ (coordinateBox κ R') (coordinateBox κ R)
      (volume R' ^ (card κ - card ι - card B') * M' * (volume R ^ (card κ - card ι - card B) * M) *
        (P.kernelBound / P.modulus ξ) ^ card ι) := by
  -- As the blocks are disjoint and the rows of J at the block of `v` are those of the identity, the
  -- fibre variables of `v` and of `y` are not paired. So the kernel is a Fourier kernel in the
  -- inner coordinates times phases, and Cauchy–Schwarz handles the rest.
  intro φ hφ_meas hφ_int hφ_supp
  have h_inj' : Function.Injective (inner ⊕ᵥ blk') := by
    simpa [Sum.elim_comp_map] using
      h_inj.comp (Sum.map_injective.2 ⟨Function.injective_id, inl_injective⟩)
  obtain ⟨η', _, e', ζ', _, h_inner', rfl, h_card', h_chart', h_mass'⟩ :=
    h'.exists_blockChart h_inj'
  have h_inj_blk : Function.Injective (inner ⊕ᵥ blk) := by
    simpa [Sum.elim_comp_map] using
      h_inj.comp (Sum.map_injective.2 ⟨Function.injective_id, inr_injective⟩)
  obtain ⟨η, _, e, ζ, _, rfl, rfl, h_card, h_chart, h_mass⟩ := h.exists_blockChart h_inj_blk
  -- The block of `v` consists of outer coordinates of `y`.
  have h_outer : ∀ i : B', ∃ k : η, e (inl (inl k)) = e' (inr i) :=
    exists_inl_inl_eq_of_injective e h_inj
  choose out h_out using h_outer
  -- With the outer coordinates `y'` of `v` fixed, their term `a y'` of the product is a function
  -- of `y`. The term of the block of `v` involves only the outer coordinates of `y`.
  let a (y' : η' → A) (p : ((η → A) × (ι → A)) × (B → A)) : A :=
    star y' ⬝ᵥ (J *ᵥ blockChart e p) ∘ e' ∘ inl ∘ inl
  -- `f y'` is φ times that phase, and `H` the square norm, in the outer coordinates of `y`, of the
  -- Fourier transform in the inner ones of the integral of `f y'` over the block of `y`.
  let f (y' : η' → A) (p : ((η → A) × (ι → A)) × (B → A)) : ℂ :=
    P.ψ (ξ * a y' p) * φ (blockChart e p)
  let H (q' : (η' → A) × (ι → A)) : ℝ≥0∞ := ∫⁻ y : η → A,
    ‖∫ w : ι → A, P.ψ (ξ * star q'.2 ⬝ᵥ w) * ∫ z : B → A, f q'.1 ((y, w), z) ∂ζ (y, w)‖ₑ ^ 2
  let c : ℝ≥0∞ := (P.kernelBound / P.modulus ξ) ^ card ι
  let T (v : κ → A) : ℝ≥0∞ := ‖∫ y : κ → A, P.ψ (ξ * star v ⬝ᵥ J *ᵥ y) * φ y ∂ρ‖ₑ ^ 2
  have h_chart_meas : Measurable (blockChart e) := h_chart.measurable
  have h_box (p : ((η → A) × (ι → A)) × (B → A)) (hp : φ (blockChart e p) ≠ 0) :
      p ∈ (coordinateBox η R ×ˢ coordinateBox ι R) ×ˢ coordinateBox B R :=
    (preimage_blockChart_coordinateBox e R).subset (hφ_supp _ hp)
  have hH_meas : Measurable H :=
    measurable_lintegral_fourier_integral_kernel (ξ : A) (f := f) (by fun_prop)
  have h_schwarz (p' : ((η' → A) × (ι → A)) × (B' → A)) :
      T (blockChart e' p') ≤ volume (coordinateBox η R) * H p'.1 :=
    enorm_integral_fourier_sq_le h_chart hφ_meas hφ_int (fun p hp ↦ (mem_prod.1 (h_box p hp).1).1)
      ξ (blockChart e' p') _ (b := fun y : η → A ↦ star p'.2 ⬝ᵥ y ∘ out)
      (star_blockChart_dotProduct_mulVec e e' h_inner' h_out h_orth p')
  -- Plancherel's inequality in the inner coordinates, Cauchy–Schwarz in the block of `y`.
  have h_plancherel (y' : η' → A) :
      ∫⁻ w' : ι → A, H (y', w') ≤ c * (M * ∫⁻ y : κ → A, ‖φ y‖ₑ ^ 2 ∂ρ) := by
    have hf_int : Integrable (f y') ((volume.prod volume) ⊗ₘ ζ) :=
      (h_chart.integrable_comp_of_integrable hφ_int).bdd_mul (c := 1)
        (Measurable.aestronglyMeasurable (by fun_prop)) (by simp [norm_psi])
    have h_supp (p : ((η → A) × (ι → A)) × (B → A)) (hp : f y' p ≠ 0) :
        p.2 ∈ coordinateBox B R := by
      obtain ⟨-, h_mem⟩ := h_box p (right_ne_zero_of_mul hp)
      exact h_mem
    grw [lintegral_lintegral_fourier_integral_kernel_le ξ (by fun_prop) hf_int h_supp h_mass,
      ← h_chart.lintegral_comp (by fun_prop)]
    simp only [f, c, enorm_psi_mul, le_refl]
  have : SFinite ρ := by
    rw [← h_chart.map_eq]
    infer_instance
  have h_transform : Measurable T := measurable_enorm_integral_fourier_sq hφ_meas J ξ
  calc ∫⁻ v : κ → A in coordinateBox κ R', T v ∂ρ'
    _ = ∫⁻ p' : ((η' → A) × (ι → A)) × (B' → A) in
          (coordinateBox η' R' ×ˢ coordinateBox ι R') ×ˢ coordinateBox B' R',
          T (blockChart e' p') ∂(volume.prod volume) ⊗ₘ ζ' := by
      rw [← h_chart'.setLIntegral_comp_preimage (measurableSet_coordinateBox κ hR') h_transform,
        preimage_blockChart_coordinateBox]
    _ ≤ volume (coordinateBox η R) * (M' * (c * (M * ∫⁻ y : κ → A, ‖φ y‖ₑ ^ 2 ∂ρ) *
          volume (coordinateBox η' R'))) :=
      setLIntegral_le_of_le_comp_fst (measurableSet_coordinateBox η' hR')
        (measurableSet_coordinateBox ι hR') (measurableSet_coordinateBox B' hR') h_mass' hH_meas
        h_schwarz h_plancherel
    _ = volume R' ^ (card κ - card ι - card B') * M' * (volume R ^ (card κ - card ι - card B) * M) *
          c * ∫⁻ y : κ → A, ‖φ y‖ₑ ^ 2 ∂ρ := by
      rw [volume_coordinateBox, volume_coordinateBox, h_card, h_card']
      ring

end Place

end New.Floors
