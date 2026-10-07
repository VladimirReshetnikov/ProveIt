import OAI.Combinatorics.Progressions.Estimates.ConstantCenterUniformLifts
import OAI.Combinatorics.Progressions.Geometry.PhysicalFactorCoordinates
import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityMeanConjugate
import OAI.Combinatorics.Progressions.Sampling.FiniteLawForecastModelTransfer

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical NNReal

structure NormalizedPolynomialTwist (X : Type*) [Fintype X]
    (Y : Type*) [Fintype Y] (periodCap coverCap : ℝ) (L : ℝ≥0) where
  modulus : ℕ
  modulus_pos : 0 < modulus
  modulus_bound : (modulus : ℝ) ≤ periodCap
  cover : ℕ
  cover_pos : 0 < cover
  cover_bound : (cover : ℝ) ≤ coverCap
  mask : (X → ZMod modulus) → ℂ
  mask_bound : ∀ z, ‖mask z‖ ≤ 1
  smooth : (X → ℝ) × (Y → UnitAddCircle) → ℂ
  smooth_bound : ∀ z, ‖smooth z‖ ≤ 1
  smooth_lipschitz : LipschitzWith L smooth

namespace NormalizedPolynomialTwist
variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def eval (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) : ℂ :=
  W.mask (fun i => (u i : ZMod W.modulus)) *
    W.smooth (fun i => (u i : ℝ) / N i, physicalGridFactorInput W.cover p (fun i => (u i : ℝ)))

theorem norm_eval_le (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    ‖W.eval N p u‖ ≤ 1 := by
  unfold eval
  rw [norm_mul]
  exact (mul_le_mul (W.mask_bound _) (W.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

noncomputable def mono {Y : Type*} [Fintype Y]
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    {periodCap' coverCap' : ℝ} {L' : ℝ≥0}
    (hp : periodCap ≤ periodCap') (hc : coverCap ≤ coverCap') (hL : L ≤ L') :
    NormalizedPolynomialTwist X Y periodCap' coverCap' L' :=
  { W with
    modulus_bound := W.modulus_bound.trans hp
    cover_bound := W.cover_bound.trans hc
    smooth_lipschitz := W.smooth_lipschitz.weaken hL }

@[simp] theorem eval_mono (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    {periodCap' coverCap' : ℝ} {L' : ℝ≥0}
    (hp : periodCap ≤ periodCap') (hc : coverCap ≤ coverCap') (hL : L ≤ L')
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.mono hp hc hL).eval N p u = W.eval N p u := rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal Classical

variable {X : Type*} {m : ℕ} {J : Fin m → Type*}

theorem physicalGridFactorInput_subtractConstant (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ) (t : X → ℝ) :
    physicalGridFactorInput period (fun j => subtractConstant (c j) (p j)) t =
      physicalGridFactorInput period p t -
        (fun a : Σ j, J j => ((c a.1 a.2 / period : ℝ) : UnitAddCircle)) := by
  funext a
  simp only [physicalGridFactorInput, eval_subtractConstant, Pi.sub_apply, sub_div,
    AddCircle.coe_sub]

namespace NormalizedPolynomialTwist

variable [Fintype X] [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def shiftConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) :
    NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L :=
  { W with
    smooth := fun z => W.smooth (z.1, z.2 -
      (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle)))
    smooth_bound := fun z => W.smooth_bound _
    smooth_lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Prod.dist_eq, dist_sub_right] using W.smooth_lipschitz.dist_le_mul
        (x.1, x.2 - (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle)))
        (y.1, y.2 - (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle))) }

@[simp] theorem shiftConstant_modulus
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).modulus = W.modulus := rfl

@[simp] theorem shiftConstant_cover
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).cover = W.cover := rfl

@[simp] theorem shiftConstant_mask
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).mask = W.mask := rfl

@[simp] theorem eval_shiftConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) (N : X → ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.shiftConstant c).eval N p u =
      W.eval N (fun j => subtractConstant (c j) (p j)) u := by
  simp only [eval, shiftConstant, physicalGridFactorInput_subtractConstant]
  rfl

end NormalizedPolynomialTwist

theorem twistedNativeSampleFunctions_subtractConstant_subset
    [Fintype X] [∀ j, Fintype (J j)] {Ω : Type*}
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) (budget : ℝ) :
    twistedNativeSampleFunctions w degree budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) t =>
        W.eval N (fun j => subtractConstant (c j) (p j)) (sample t)) ⊆
    twistedNativeSampleFunctions w degree budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) t =>
        W.eval N p (sample t)) := by
  rintro f (rfl | ⟨W, g, hg, rfl⟩)
  · exact Or.inl rfl
  · refine Or.inr ⟨W.shiftConstant c, g, hg, ?_⟩
    funext t
    simp only [NormalizedPolynomialTwist.eval_shiftConstant]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

theorem NativeSampleModel.exists_constant_of_degree_zero
    {σ Ω : Type*} {w : σ → ℕ} {p : ℝ} {sample : Ω → σ → ℤ} {f : Ω → ℂ}
    (F : NativeSampleModel w 0 p sample f) :
    ∃ c : ℂ, ‖c‖ ≤ 1 ∧ ∀ x, f x = c := by
  let c := F.test.observable (QuotientGroup.mk (1 : F.model.RealGroup))
  refine ⟨c, (F.test.norm_le _).trans F.norm, ?_⟩
  intro x
  rw [F.eval, RationalFilteredNilmanifold.Niltest.eval_step_zero]

namespace VectorPolynomial.NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def scaleMask
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (c : ℂ) (hc : ‖c‖ ≤ 1) : NormalizedPolynomialTwist X Y periodCap coverCap L :=
  { W with
    mask := fun z => c * W.mask z
    mask_bound := fun z => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (W.mask_bound z) }

@[simp] theorem scaleMask_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.scaleMask c hc).eval N poly u = c * W.eval N poly u := by
  simp only [eval, scaleMask, mul_assoc]
  rfl

theorem absorb_degree_zero {Ω : Type*} {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (budget : ℝ)
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    {g : Ω → ℂ} (G : NativeSampleModel w 0 budget sample g) :
    ∃ W' : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ∀ u, star (W.eval N poly (sample u)) * g u = star (W'.eval N poly (sample u)) := by
  obtain ⟨c, hc, hg⟩ := G.exists_constant_of_degree_zero
  refine ⟨W.scaleMask (star c) (by simpa only [norm_star] using hc), ?_⟩
  intro u
  rw [scaleMask_eval, star_mul, star_star, hg u]

end VectorPolynomial.NormalizedPolynomialTwist

namespace VectorPolynomial

theorem twistedNativeSampleFunctions_degree_zero
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (budget : ℝ) {f : Ω → ℂ}
    (hf : f ∈ twistedNativeSampleFunctions w 0 budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) u =>
        W.eval N poly (sample u))) :
    f = 0 ∨ ∃ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      f = fun u => star (W.eval N poly (sample u)) := by
  rcases hf with hzero | ⟨W, g, ⟨G⟩, hf⟩
  · exact Or.inl hzero
  · obtain ⟨W', hW'⟩ := W.absorb_degree_zero N poly sample w budget G
    exact Or.inr ⟨W', hf.trans (funext hW')⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

theorem subtractConstant_neg_cancel {X R V : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    (c : V) (p : VectorPolynomial X R V) :
    subtractConstant (-c) (subtractConstant c p) = p := by
  simp [subtractConstant, monomial, TensorProduct.tmul_neg]

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] {periodCap coverCap : ℝ} {L : ℝ≥0}

@[simp] theorem eval_shiftConstant_neg_subtractConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.shiftConstant (fun j => -c j)).eval N
      (fun j => subtractConstant (c j) (poly j)) u = W.eval N poly u := by
  rw [eval_shiftConstant]
  simp only [subtractConstant_neg_cancel]

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem degreeZero_finiteLaw_model_atom_comparison
    {X Ω T : Type*} [Fintype X] [Fintype Ω] [Fintype T]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (budget : ℝ)
    (left : FiniteProbabilityWeights Ω) (right : FiniteProbabilityWeights T)
    (ψ : T → Ω) (a : Ω → ℝ)
    {η : ℝ} (hη : 0 ≤ η)
    (hcompare : ∀ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ‖left.complexMean (fun x => (a x : ℂ) * W.eval N poly (sample x)) -
        right.complexMean (fun t => W.eval N poly (sample (ψ t)))‖ ≤ η)
    {f : Ω → ℂ}
    (hf : f ∈ twistedNativeSampleFunctions w 0 budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) x =>
        W.eval N poly (sample x))) :
    ‖left.complexMean (fun x => (a x : ℂ) * f x) -
      right.complexMean (fun t => f (ψ t))‖ ≤ η := by
  rcases twistedNativeSampleFunctions_degree_zero N poly sample w budget hf with rfl | ⟨W, rfl⟩
  · simpa only [Pi.zero_apply, mul_zero, FiniteProbabilityWeights.complexMean,
      Finset.sum_const_zero, sub_zero, norm_zero] using hη
  · have hleft : left.complexMean (fun x => (a x : ℂ) * star (W.eval N poly (sample x))) =
        star (left.complexMean (fun x => (a x : ℂ) * W.eval N poly (sample x))) := by
      rw [← FiniteProbabilityWeights.complexMean_star]
      congr 1
      funext x
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      exact mul_comm _ _
    rw [hleft, FiniteProbabilityWeights.complexMean_star, ← star_sub, norm_star]
    exact hcompare W

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped BigOperators NNReal

theorem finiteWeightedTest_star_real {Ω T : Type*} [Fintype T]
    (ψ : T → Ω) (w : T → ℝ) (f : Ω → ℂ) :
    finiteWeightedTest ψ (fun t => (w t : ℂ)) (fun x => star (f x)) =
      star (finiteWeightedTest ψ (fun t => (w t : ℂ)) f) := by
  change (𝔼 t, (w t : ℂ) * star (f (ψ t))) = star (𝔼 t, (w t : ℂ) * f (ψ t))
  rw [← expect_star]
  apply Finset.expect_congr rfl
  intro t _
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm]

namespace VectorPolynomial

theorem degreeZero_model_atom_comparison
    {X Ω T U : Type*} [Fintype X] [Fintype T] [Fintype U]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (budget : ℝ)
    (ψ : T → Ω) (φ : U → Ω) (a : T → ℝ) (b : U → ℝ)
    {η : ℝ} (hη : 0 ≤ η)
    (hcompare : ∀ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ‖(𝔼 t, (a t : ℂ) * W.eval N poly (sample (ψ t))) -
        (𝔼 u, (b u : ℂ) * W.eval N poly (sample (φ u)))‖ ≤ η)
    {f : Ω → ℂ}
    (hf : f ∈ twistedNativeSampleFunctions w 0 budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) u =>
        W.eval N poly (sample u))) :
    ‖(𝔼 t, (a t : ℂ) * f (ψ t)) - (𝔼 u, (b u : ℂ) * f (φ u))‖ ≤ η := by
  rcases twistedNativeSampleFunctions_degree_zero N poly sample w budget hf with rfl | ⟨W, rfl⟩
  · simpa using hη
  · change ‖finiteWeightedTest ψ (fun t => (a t : ℂ)) (fun x => star (W.eval N poly (sample x))) -
      finiteWeightedTest φ (fun u => (b u : ℂ)) (fun x => star (W.eval N poly (sample x)))‖ ≤ η
    rw [finiteWeightedTest_star_real, finiteWeightedTest_star_real, ← star_sub, norm_star]
    exact hcompare W

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_finiteLaw_degreeZero_forecast_transfer
    {H X U I F : Type*} [Fintype H] [Fintype X] [DecidableEq X]
    [Fintype U] [Fintype I]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (budget : ℝ)
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (localLaw : H → FiniteProbabilityWeights U) (ψ : H → U → integerBox N)
    (forecast : F → integerBox N → ℂ) (select : H → F)
    (hreal : ∀ h ∈ productive, ∀ x, ((forecast (select h) x).re : ℂ) = forecast (select h) x)
    (v : integerBox N → ℝ) (models : I → integerBox N → ℂ)
    (coeff : I → ℂ) (err : integerBox N → ℂ)
    (hmodels : ∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) 0 budget
      (fun x : integerBox N => x.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
        (x : integerBox N) => W.eval N poly x.val))
    (hmodel : (fun x => (v x : ℂ)) = (∑ i, coeff i • models i) + err)
    {τ ρ R T Q E u : ℝ} (hT : 0 ≤ T)
    (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-T) ≤ τ)
    (hu : R + T + 6 ≤ u) (hE : Q + (T + R) + 8 ≤ E)
    (hc : (∑ i, ‖coeff i‖) ≤ Real.exp Q) (hmass : τ ≤ law.mass productive)
    (hcompare : ∀ h ∈ productive,
      ∀ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ‖(localLaw h).complexMean (fun a => W.eval N poly (ψ h a).val) -
        (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).complexMean
          (fun x => W.eval N poly x.val * forecast (select h) x)‖ ≤ Real.exp (-E))
    (hforecast : ∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
      err (forecast f)‖ ≤ Real.exp (-u))
    (hlocal : law.mean (fun h => if h ∈ productive then
      ‖(localLaw h).complexMean (fun a => err (ψ h a))‖ else 0) ≤ Real.exp (-u))
    (hscore : ∀ h ∈ productive, ρ ≤ (localLaw h).mean (fun a => v (ψ h a))) :
    ∃ h ∈ productive, ρ / 2 ≤ 𝔼 x, (forecast (select h) x).re * v x := by
  let : Nonempty (integerBox N) := hN.to_subtype
  apply exists_finiteLaw_forecast_model_transfer law productive localLaw ψ
    (fun h x => (forecast (select h) x).re) v models coeff err hmodel
    hT hρ hτ hu hE hc hmass ?_ ?_ hlocal hscore
  · intro h hh i
    have hatom := degreeZero_finiteLaw_model_atom_comparison N poly
      (fun x : integerBox N => x.val) (1 : X → ℕ) budget
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hN)
      (localLaw h) (ψ h) (fun x => (forecast (select h) x).re)
      (Real.exp_nonneg (-E)) (fun W => ?_) (hmodels i)
    · simpa only [FiniteProbabilityWeights.uniformFinset,
        FiniteProbabilityWeights.uniform_complexMean] using hatom
    · simpa only [hreal h hh, mul_comm, norm_sub_rev] using hcompare h hh W
  · intro h hh
    have he := hforecast (select h)
    have hstar (x : integerBox N) : star (forecast (select h) x) = forecast (select h) x := by
      rw [← hreal h hh x]
      simp only [Complex.star_def, Complex.conj_ofReal]
    simpa only [FiniteProbabilityWeights.correlation_eq_complexMean,
      FiniteProbabilityWeights.uniformFinset, FiniteProbabilityWeights.uniform_complexMean,
      hstar, hreal h hh, mul_comm] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal

theorem exists_measure_degreeZero_twist_transfer
    {H X Ω T I : Type*} [MeasurableSpace H] [Fintype X] [Fintype Ω]
    [Fintype T] [Fintype I]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (budget : ℝ)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (productive bad : Set H) (hprod : MeasurableSet productive) (hbad : MeasurableSet bad)
    (Good : H → Prop) (hGood : ∀ᵐ h ∂μ, Good h)
    (ψ : H → T → Ω) (a : H → Ω → ℝ) (b : H → T → ℝ)
    (reference : H → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L → ℂ)
    (v : Ω → ℝ) (e : Ω → ℂ) (models : I → Ω → ℂ) (coeff : I → ℝ)
    (hmodels : ∀ i, models i ∈ twistedNativeSampleFunctions w 0 budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) x =>
        W.eval N poly (sample x)))
    (hmodel : (fun x => (v x : ℂ)) = (∑ i, coeff i • models i) + e)
    {τ ρ R P Q u E : ℝ} (hP : 0 ≤ P)
    (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-P) ≤ τ)
    (hu : R + P + 6 ≤ u) (hE : Q + R + 8 ≤ E)
    (hc : (∑ i, |coeff i|) ≤ Real.exp Q)
    (hmass : τ ≤ μ.real productive) (hbadmass : μ.real bad ≤ τ / 4)
    (hambient : ∀ h ∈ productive, h ∉ bad → Good h → ∀ W,
      ‖(𝔼 x, (a h x : ℂ) * W.eval N poly (sample x)) - reference h W‖ ≤ Real.exp (-E))
    (hslice : ∀ h ∈ productive, h ∉ bad → Good h → ∀ W,
      ‖(𝔼 t, (b h t : ℂ) * W.eval N poly (sample (ψ h t))) - reference h W‖ ≤ Real.exp (-E))
    (he : Integrable (fun h => 𝔼 t, (b h t : ℂ) * e (ψ h t)) μ)
    (hlocal : (∫ h, ‖𝔼 t, (b h t : ℂ) * e (ψ h t)‖ ∂μ) ≤ Real.exp (-u))
    (hforecast : ∀ h ∈ productive, h ∉ bad → Good h →
      ‖𝔼 x, (a h x : ℂ) * e x‖ ≤ Real.exp (-u))
    (hscore : ∀ h ∈ productive, h ∉ bad → Good h → ρ ≤ 𝔼 t, b h t * v (ψ h t)) :
    ∃ h ∈ productive, h ∉ bad ∧ Good h ∧ ρ / 2 ≤ 𝔼 x, a h x * v x := by
  let A := fun h => finiteWeightedTest id (fun x => (a h x : ℂ))
  let B := fun h => finiteWeightedTest (ψ h) (fun t => (b h t : ℂ))
  have hmodel' : (fun x => (v x : ℂ)) = (∑ i, (coeff i : ℂ) • models i) + e := by
    rw [hmodel]
    congr 1
  have hc' : (∑ i, ‖(coeff i : ℂ)‖) ≤ Real.exp Q := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hc
  have hatom : ∀ h ∈ productive, h ∉ bad → Good h → ∀ i,
      ‖A h (models i) - B h (models i)‖ ≤ 2 * Real.exp (-E) := by
    intro h hp hb hg i
    apply degreeZero_model_atom_comparison N poly sample w budget id (ψ h) (a h) (b h)
      (by positivity) ?_ (hmodels i)
    intro W
    simp only [id_eq]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (reference h W) _).trans (by
      rw [norm_sub_rev (reference h W)]
      linarith [hambient h hp hb hg W, hslice h hp hb hg W])
  have hprecision := model_transfer_residual_precision hP hρ hτ hu
  obtain ⟨h, hp, hb, hg, hs⟩ := exists_measure_model_transfer_of_uniform_good_comparison μ
    productive bad hprod hbad A B _ e models (fun i => (coeff i : ℂ)) hmodel' Good hGood
    ((Real.exp_pos _).trans_le hτ) ((Real.exp_pos _).trans_le hρ)
    (by positivity) hc' hmass hbadmass hatom he (hlocal.trans hprecision.1)
    (fun h hp hb hg => (hforecast h hp hb hg).trans hprecision.2)
    (model_transfer_atom_precision hρ le_rfl hE)
    (by simpa only [B, finiteWeightedTest_real] using hscore)
  exact ⟨h, hp, hb, hg, by simpa only [A, finiteWeightedTest_real, id_eq] using hs⟩

end Erdos3.VectorPolynomial

end

end OAI
