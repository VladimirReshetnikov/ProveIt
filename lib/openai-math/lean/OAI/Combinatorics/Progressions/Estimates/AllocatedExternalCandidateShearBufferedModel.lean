import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateShearBufferedScore
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalRetainedForecastModel

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

local instance : Nonempty A.Site := A.site_nonempty

theorem exists_fixedCenter_shear_buffered_model
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata precision C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcost : outputCost ≤ pSlice) (htest : 2 ≤ pTest)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp pSlice)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j) :
    let χ := majorPhasePlateauKernel tagCount
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
    let returned := patch.ofTaggedWeightedShearOrbit e out.ambient
    let score : integerBox N → ℝ := fun v =>
      bufferedScalarScore χ (fun x : integerBox N => coords x.val)
        (fun x lifts => returned.value
          (Sum.elim (fun i => (x.val i : ℝ)) (fun i => (lifts i : ℝ))))
        (fun x : integerBox N => f x.val) lam v
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      (fun v => (score v : ℂ)) = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      A.law.mean (fun z => if hz : z ∈ out.retained then
        ‖(out.siteLaw ⟨z, hz⟩).complexMean
          (fun t => model.residual (A.physicalBox hξone hmargin z t))‖ else 0) ≤ Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) ∧
      ∀ z : out.retained, outputScore ≤ (out.siteLaw z).mean
        (fun site => score (A.physicalBox hξone hmargin z.val site)) := by
  classical
  intro χ coords returned score commonBudget Qmodel native
  have hinput (v : integerBox N) : ‖(score v : ℂ)‖ ≤ Real.exp p :=
    norm_bufferedWeightedPatchScore_le_exp returned χ (fun x : integerBox N => coords x.val)
      (fun x : integerBox N => fun i => (x.val i : ℝ)) (fun x : integerBox N => f x.val)
      lam hp (fun x => hf x.val x.property) hlam v
  obtain ⟨model, hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩ :=
    out.exists_fixedCenter_retained_forecast_model hξone hmargin hu hp hbudget hNative
      hSliceLog hC hCp hCap hAccuracy hPrecision hdirect hexcess
      hSlice hcost htest hshort data (fun v => (score v : ℂ)) hinput
  refine ⟨model, hmodels, heq, hcoeff, hlocal, hforecast, hterms, ?_⟩
  intro z
  exact out.siteLaw_shear_buffered_score patch f lam hσ1 H hH hchart hsmall hpoly e z

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
