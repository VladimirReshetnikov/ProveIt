import OAI.Combinatorics.Progressions.Estimates.RealTranslationEvaluationContinuity
import OAI.Combinatorics.Progressions.Estimates.RealificationModuleTopology
import OAI.Combinatorics.Progressions.Probability.RealificationRationalDensity

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
private theorem continuous_pair_pullback {X B : Type*} [TopologicalSpace X]
    [TopologicalSpace B] {f : X × B → ℝ} {b : X → B}
    (hf : Continuous f) (hb : Continuous b) :
    Continuous (fun z : X × X => f (z.1, b z.2)) :=
  hf.comp (continuous_id.prodMap hb)

omit [Fintype σ] in
private theorem continuous_pair_potential_difference {X B : Type*}
    [TopologicalSpace X] [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] {a b : X → B} {v : B → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) :
    Continuous (fun z : X × X => v (b z.2) - v (b z.2 - a z.1)) :=
  (hv.comp (hb.comp continuous_snd)).sub
    (hv.comp ((hb.comp continuous_snd).sub (ha.comp continuous_fst)))

omit [Fintype σ] in
theorem realification_pair_eq_of_rational
    {V Y : Type*} [AddCommGroup V] [Module ℚ V]
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [TopologicalSpace Y] [T2Space Y]
    (U : Submodule ℚ V)
    {f g : (ℝ ⊗[ℚ] V) × (ℝ ⊗[ℚ] V) → Y}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x y : U, f ((1 : ℝ) ⊗ₜ[ℚ] (x : V), (1 : ℝ) ⊗ₜ[ℚ] (y : V)) =
      g ((1 : ℝ) ⊗ₜ[ℚ] (x : V), (1 : ℝ) ⊗ₜ[ℚ] (y : V)))
    {x y : ℝ ⊗[ℚ] V} (hx : x ∈ U.baseChange ℝ) (hy : y ∈ U.baseChange ℝ) :
    f (x, y) = g (x, y) := by
  apply realification_submodule_eq_of_rational U
    (hf.comp (continuous_const.prodMk continuous_id))
    (hg.comp (continuous_const.prodMk continuous_id)) _ hy
  intro y
  exact realification_submodule_eq_of_rational U
    (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) (fun x => h x y) hx

omit [Fintype σ] in
theorem eval_real_map_at_rational (P : MvPolynomial σ ℚ) (z : σ → ℚ) :
    eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) P) =
      (eval z P : ℝ) := by
  rw [eval_map]
  exact (eval₂_comp (algebraMap ℚ ℝ) z P).symm

theorem bchRealTranslationHom_rational_eval_potential
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (x : weightedSubalgebra w d) (hx : x ∈ U) (z : σ → ℚ)
    (hz : z ∈ U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype)) :
    eval (fun i => (z i : ℝ))
        (bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩).polynomial =
      eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval ((fun i => (z i : ℝ)) -
          (bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  have hq := polynomialExponentialCoordinate_eval_potential_on_submodule
    (U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype))
    x.val.base ⟨x, hx, rfl⟩ x.val.polynomial V (hderiv x hx) z hz
  have hr : bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩ =
      PolynomialTranslationGroupOver.map (algebraMap ℚ ℝ)
        (PolynomialTranslationGroupOver.rationalEquiv
          (bchTranslationHom w d hw hwd ⟨x⟩)) :=
    bchRealTranslationHom_rational w d hw hwd ⟨x⟩
  rw [hr]
  change eval (fun i => (z i : ℝ))
    (MvPolynomial.map (algebraMap ℚ ℝ) (polynomialExponentialCoordinate x.val.base x.val.polynomial)) =
    eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
      eval ((fun i => (z i : ℝ)) - (fun i => (x.val.base i : ℝ)))
        (MvPolynomial.map (algebraMap ℚ ℝ) V)
  have hzsub : ((fun i => (z i : ℝ)) - (fun i => (x.val.base i : ℝ))) =
      (fun i => ((z - x.val.base) i : ℝ)) := by
    ext i
    simp only [Pi.sub_apply, Rat.cast_sub]
  rw [hzsub, eval_real_map_at_rational, eval_real_map_at_rational, eval_real_map_at_rational]
  exact_mod_cast hq

theorem bchRealTranslationHom_eval_potential_on_real_base_image
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (g : (weightedFiltration w d hwd).realification.Group)
    (hg : g.coord ∈ U.toSubmodule.baseChange ℝ) (b : σ → ℝ)
    (hb : b ∈ (U.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) :
    eval b (bchRealTranslationHom w d hwd g).polynomial =
      eval b (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval (b - (bchRealTranslationHom w d hwd g).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  let ℓ := baseLinear.comp (weightedSubalgebra w d).subtype
  let B := realifyCoordinateMap ℓ
  have hB : Continuous B := LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) B
  obtain ⟨y, hy, rfl⟩ := hb
  let f : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (ℝ ⊗[ℚ] weightedSubalgebra w d) → ℝ :=
    fun z => eval (B z.2) (bchRealTranslationHom w d hwd ⟨z.1⟩).polynomial
  let r : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (ℝ ⊗[ℚ] weightedSubalgebra w d) → ℝ :=
    fun z => eval (B z.2) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
      eval (B z.2 - (bchRealTranslationHom w d hwd ⟨z.1⟩).base)
        (MvPolynomial.map (algebraMap ℚ ℝ) V)
  have hf0 := continuous_bchRealTranslationHom_polynomial_eval w d hw hd hwd
  have hf : Continuous f := continuous_pair_pullback hf0 hB
  have hr : Continuous r := continuous_pair_potential_difference
    (continuous_bchRealTranslationHom_base w d hw hd hwd) hB
    (MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap ℚ ℝ) V))
  have hrat (x y : U.toSubmodule) :
      f ((1 : ℝ) ⊗ₜ[ℚ] (x : weightedSubalgebra w d),
        (1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) =
      r ((1 : ℝ) ⊗ₜ[ℚ] (x : weightedSubalgebra w d),
        (1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) := by
    have hBy : B ((1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) =
        (fun i => (y.val.val.base i : ℝ)) := by
      funext i
      exact (realifyCoordinateMap_tmul ℓ 1 y.val i).trans (one_mul _)
    dsimp only [f, r]
    rw [hBy]
    exact bchRealTranslationHom_rational_eval_potential w d hw hwd U V hderiv
      x.val x.property y.val.val.base ⟨y.val, y.property, rfl⟩
  exact realification_pair_eq_of_rational U.toSubmodule hf hr hrat hg hy

theorem bchRealTranslationHom_eval_potential
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (g : (weightedFiltration w d hwd).realification.Group)
    (hg : g.coord ∈ U.toSubmodule.baseChange ℝ) (b : σ → ℝ)
    (hb : b ∈ (U.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) :
    eval b (bchRealTranslationHom w d hwd g).polynomial =
      eval b (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval (b - (bchRealTranslationHom w d hwd g).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  exact bchRealTranslationHom_eval_potential_on_real_base_image
    w d hw hd hwd U V hderiv g hg b hb

end Erdos3.PolynomialTranslationLie

end

end OAI
