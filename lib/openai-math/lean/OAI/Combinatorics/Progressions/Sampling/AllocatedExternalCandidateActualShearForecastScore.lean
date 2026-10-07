/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateBoundedTwistComparison
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateShearBufferedModel
import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleModelAttachment

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

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

local instance : Nonempty A.Site := A.site_nonempty

theorem exists_retained_degreeZero_forecast_score
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {Forecast : Type} {Pnative forecastMassLog capLog Edata : ℝ}
    (data : Forecast → ActualForecastData N poly Pnative forecastMassLog capLog Edata)
    (select : A.Path → Forecast)
    (hreal : ∀ z : out.retained, ∀ x,
      (((data (select z.val)).target x).re : ℂ) = (data (select z.val)).target x)
    (v : integerBox N → ℝ) (model : CenteredForecastModel (integerBox N))
    {budget Q scoreLog massLogTransfer Ecompare u : ℝ}
    (hmodels : ∀ i, model.models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) 0 budget
      (fun x : integerBox N => x.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp budget) (Real.exp budget)
        ⟨Real.exp budget, Real.exp_nonneg _⟩) (x : integerBox N) => W.eval N poly x.val))
    (hmodel : (fun x => (v x : ℂ)) =
      (∑ i, model.coefficient i • model.models i) + model.residual)
    (hcoeff : (∑ i, |model.coefficient i|) ≤ Real.exp Q)
    (hT : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hu : scoreLog + massLogTransfer + 6 ≤ u)
    (hE : Q + (massLogTransfer + scoreLog) + 8 ≤ Ecompare)
    (hcompare : ∀ z : out.retained,
      ∀ W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp budget) (Real.exp budget)
        ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ‖(out.siteLaw z).complexMean (fun a => W.eval N poly
          (A.physicalBox hξone hmargin z.val a).val) -
        (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).complexMean
          (fun x => W.eval N poly x.val * (data (select z.val)).target x)‖ ≤
        Real.exp (-Ecompare))
    (hforecast : ∀ g,
      ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data g).target‖ ≤ Real.exp (-u))
    (hlocal : A.law.mean (fun z => if hz : z ∈ out.retained then
      ‖(out.siteLaw ⟨z, hz⟩).complexMean
        (fun t => model.residual (A.physicalBox hξone hmargin z t))‖ else 0) ≤ Real.exp (-u))
    (hscore : ∀ z : out.retained, outputScore ≤ (out.siteLaw z).mean
      (fun t => v (A.physicalBox hξone hmargin z.val t))) :
    ∃ z : out.retained, outputScore / 2 ≤
      𝔼 x : integerBox N, ((data (select z.val)).target x).re * v x := by
  classical
  have hcoeff' : (∑ i, ‖(model.coefficient i : ℂ)‖) ≤ Real.exp Q := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hcoeff
  have hmodel' : (fun x => (v x : ℂ)) =
      (∑ i, (model.coefficient i : ℂ) • model.models i) + model.residual := hmodel
  obtain ⟨z, hz, htransfer⟩ := exists_finiteLaw_degreeZero_forecast_transfer
    N A.integerBox_nonempty poly budget A.law out.retained out.allSiteLaw
    (A.physicalBox hξone hmargin) (fun g => (data g).target) select
    (fun z hz => hreal ⟨z, hz⟩) v model.models (fun i => (model.coefficient i : ℂ))
    model.residual hmodels hmodel' hT hscoreLower hmassLower hu hE hcoeff' out.mass
    (fun z hz W => by simpa only [out.allSiteLaw_of_mem z hz] using hcompare ⟨z, hz⟩ W)
    hforecast
    (by simpa only [out.allSiteLaw_restricted_residual_eq] using hlocal)
    (fun z hz => by simpa only [out.allSiteLaw_of_mem z hz] using hscore ⟨z, hz⟩)
  exact ⟨⟨z, hz⟩, htransfer⟩

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

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

theorem exists_shear_buffered_forecast_score
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative forecastMassLog capLog Edata precision C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 forecastMassLog + 20) + 32 ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcost : outputCost ≤ pSlice) (htest : 2 ≤ pTest)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp pSlice)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative forecastMassLog capLog Edata)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    (select : A.Path → Forecast)
    (hreal : ∀ z : out.retained, ∀ x,
      (((data (select z.val)).target x).re : ℂ) = (data (select z.val)).target x)
    {scoreLog massLogTransfer Ecompare : ℝ}
    (hTransferMass : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hU : scoreLog + massLogTransfer + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * Pnative + 3))
        (2 * u + 4 * p + max 0 forecastMassLog + 20) + 2 +
      massLogTransfer + scoreLog + 8 ≤ Ecompare)
    (hcompare : ∀ z : out.retained,
      ∀ W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (max localBudget (3 * Pnative + 3)))
        (Real.exp (max localBudget (3 * Pnative + 3)))
        ⟨Real.exp (max localBudget (3 * Pnative + 3)), Real.exp_nonneg _⟩,
      ‖(out.siteLaw z).complexMean
          (fun site => W.eval N poly (A.physical z.val site)) -
        (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).complexMean
          (fun x => W.eval N poly x.val * (data (select z.val)).target x)‖ ≤
        Real.exp (-Ecompare)) :
    let χ := majorPhasePlateauKernel tagCount
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
    let returned := patch.ofTaggedWeightedShearOrbit e out.ambient
    let score : integerBox N → ℝ := fun v =>
      bufferedScalarScore χ (fun x : integerBox N => coords x.val)
        (fun x lifts => returned.value
          (Sum.elim (fun i => (x.val i : ℝ)) (fun i => (lifts i : ℝ))))
        (fun x : integerBox N => f x.val) lam v
    ∃ z : out.retained, outputScore / 2 ≤
      𝔼 x : integerBox N, ((data (select z.val)).target x).re * score x := by
  classical
  intro χ coords returned score
  obtain ⟨model, hmodels, hmodel, hcoeff, hlocal, hforecast, _hterms, hscore⟩ :=
    out.exists_fixedCenter_shear_buffered_model patch f lam hξone hmargin
      hu hp hbudget hNative hSliceLog hC hCp hCap hAccuracy hPrecision hdirect hexcess
      hSlice hcost htest hshort data hf hlam hσ1 H hH hchart hsmall hpoly e
  have hE :
      (max (max localBudget (3 * Pnative + 3))
        (2 * u + 4 * p + max 0 forecastMassLog + 20) + 2) +
        (massLogTransfer + scoreLog) + 8 ≤ Ecompare := by
    simpa only [add_assoc] using hEcompare
  exact out.exists_retained_degreeZero_forecast_score hξone hmargin data select hreal
    score model hmodels hmodel hcoeff hTransferMass hscoreLower hmassLower hU hE
    hcompare hforecast hlocal hscore

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal TensorProduct Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

def actualForecastDataModelRequired (budget Pnative massLog u p : ℝ) : ℝ :=
  u + 2 * p + max (max budget (3 * Pnative + 3))
    (2 * u + 4 * p + max 0 massLog + 20) + 32

def PreparedActualSlicedForecastModelPacket (u p cap : ℝ) : Prop :=
    let Path := ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q
    ∃ data : Option Path → ActualForecastData physicalN originalpoly q.Pnative q.massLog q.capLog q.E,
      (∀ path, (data (some path)).target =
        path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data (some path)).centerConstant = fun j => (path.slice.path.center j).val) ∧
      (data none).target = (fun _ => 0) ∧
      (data none).centerConstant = (fun _ _ => 0) ∧
      (∀ f, (∑ i, ‖(data f).coefficient i‖) ≤ Real.exp (max 0 q.massLog)) ∧
      (∀ f v, ‖(data f).target v - ∑ i, (data f).coefficient i *
        ((data f).twists i).eval physicalN
          (fun j => subtractConstant ((data f).centerConstant j) (originalpoly j)) v.val‖ ≤
        Real.exp (-(2 * u + 4 * p + 12))) ∧
      (∀ f v, ‖(data f).target v‖ ≤ cap) ∧
      (∀ f (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (v : X → ℤ),
        ‖(match f with
            | none => 0
            | some path => path.slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ v) -
          ∑ t, (data f).coefficient t * ((data f).twists t).eval physicalN
            (fun j => subtractConstant ((data f).centerConstant j) (poly' j)) v‖ ≤
          Real.exp (-q.E)) ∧
      ∀ (qLate : ActualFixedSpatialSlicedForecastNumerics s),
        q.δ = qLate.δ → q.Hchild = qLate.Hchild → q.v = qLate.v → q.Ptail = qLate.Ptail →
        ∀ path : Path,
        ∃ lateData : ActualForecastData physicalN originalpoly
            qLate.Pnative qLate.massLog qLate.capLog qLate.E,
          lateData.target = (data (some path)).target ∧
          lateData.centerConstant = (data (some path)).centerConstant ∧
          ∀ (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
            (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (v : X → ℤ),
            ‖path.slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ v -
              ∑ t, lateData.coefficient t * (lateData.twists t).eval physicalN
                (fun j => subtractConstant (lateData.centerConstant j) (poly' j)) v‖ ≤
              Real.exp (-qLate.E)

theorem exists_preparedActualSlicedForecastModelPacket
    (u p cap : ℝ)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ q.E)
    (hCap : Real.exp q.capLog ≤ cap) :
    PreparedActualSlicedForecastModelPacket
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
      s q o bW hb originalpoly hmem u p cap := by
  unfold PreparedActualSlicedForecastModelPacket
  intro Path
  obtain ⟨data, hdata, hnone, hnoneCenter, hcap, hmass, happrox, hUniversal⟩ :=
    exists_actualFixedSpatialSlicedForecastUniversalFamily_option_of_numerics
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
      s q o bW hb originalpoly hmem
  refine ⟨data, hdata, hnone, hnoneCenter,
    (fun f => (hmass f).trans (Real.exp_le_exp.mpr (le_max_right _ _))),
    (fun f v => (happrox f v).trans (Real.exp_le_exp.mpr (neg_le_neg hAccuracy))),
    (fun f v => (hcap f v).trans hCap), hUniversal, ?_⟩
  intro qLate hδ hH hv hPtail path
  obtain ⟨lateData, hLateTarget, hLateCenter, hLateUniversal⟩ :=
    exists_actualSlicedForecast_late_data s q qLate o bW hb originalpoly hmem path
      hδ hH hv hPtail
  exact ⟨lateData, hLateTarget.trans (hdata path).1.symm,
    hLateCenter.trans (hdata path).2.symm, hLateUniversal⟩

theorem exists_preparedActualSlicedForecastModelPacket_from_setup
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail pSite w vchild localCap : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : s.Pcap ≤ Ptail) (hpSite : 0 ≤ pSite) (hw : 0 ≤ w)
    (hvc : 0 ≤ vchild) (hPp : Ptail ≤ Real.exp pSite)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild) :
    let capLog := actualSlicedForecastModelCapLog m Dmod (Fintype.card X)
      s.P s.Pscale s.Pbad s.Ppres s.Pκ kernelV pSite w vchild
    let pForecast := max 0 (max localCap capLog)
    0 ≤ pForecast ∧ localCap ≤ pForecast ∧
    ∀ (u : ℝ), 0 ≤ u →
    ∃ qEarly : ActualFixedSpatialSlicedForecastNumerics s,
      qEarly.δ = δ ∧ qEarly.Hchild = Hchild ∧ qEarly.v = kernelV ∧ qEarly.Ptail = Ptail ∧
      qEarly.E = 2 * u + 4 * pForecast + 12 ∧ qEarly.capLog = capLog ∧
      qEarly.capLog ≤ pForecast ∧ 0 ≤ qEarly.massLog ∧ 0 ≤ qEarly.capLog ∧
      PreparedActualSlicedForecastModelPacket
        (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
        (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
        s qEarly o bW hb originalpoly hmem u pForecast (Real.exp pForecast) := by
  intro capLog pForecast
  obtain ⟨hpForecast, hlocal, hprecision⟩ :=
    actualSlicedForecastModelPrecision s δ Hchild kernelV Ptail pSite w vchild localCap
      hδ hk hPtail hprimitive hpSite hw hvc hPp hδw hchild hR
  refine ⟨hpForecast, hlocal, ?_⟩
  intro u hu
  obtain ⟨_hE, _hSource, qEarly, hqδ, hqH, hqv, hqP, hqE, hqcap, hqcapP,
      hqmass, hqcap0, hqcapExp, _hqT⟩ := hprecision hu
  refine ⟨qEarly, hqδ, hqH, hqv, hqP, hqE, hqcap, hqcapP, hqmass, hqcap0, ?_⟩
  exact exists_preparedActualSlicedForecastModelPacket
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    s qEarly o bW hb originalpoly hmem u pForecast (Real.exp pForecast) hqE.ge hqcapExp

theorem exists_preparedActualSlicedForecastModelPacket_from_setup_with_cap_bound
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail pSite w vchild : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : s.Pcap ≤ Ptail) (hpSite : 0 ≤ pSite) (hw : 0 ≤ w)
    (hvc : 0 ≤ vchild) (hPp : Ptail ≤ Real.exp pSite)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (u p : ℝ) (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hCapLog : actualSlicedForecastModelCapLog m Dmod (Fintype.card X)
      s.P s.Pscale s.Pbad s.Ppres s.Pκ kernelV pSite w vchild ≤ p) :
    ∃ qEarly : ActualFixedSpatialSlicedForecastNumerics s,
      qEarly.δ = δ ∧ qEarly.Hchild = Hchild ∧ qEarly.v = kernelV ∧ qEarly.Ptail = Ptail ∧
      qEarly.E = 2 * u + 4 * p + 12 ∧
      qEarly.capLog = actualSlicedForecastModelCapLog m Dmod (Fintype.card X)
        s.P s.Pscale s.Pbad s.Ppres s.Pκ kernelV pSite w vchild ∧
      qEarly.capLog ≤ p ∧ 0 ≤ qEarly.massLog ∧ 0 ≤ qEarly.capLog ∧
      PreparedActualSlicedForecastModelPacket
        (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
        (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
        s qEarly o bW hb originalpoly hmem u p (Real.exp p) := by
  have hconstructed := exists_preparedActualSlicedForecastModelPacket_from_setup
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    s o bW hb originalpoly hmem δ Hchild kernelV Ptail pSite w vchild p
    hδ hk hPtail hprimitive hpSite hw hvc hPp hδw hchild
  simpa only [max_eq_left hCapLog, max_eq_right hp] using hconstructed.2.2 u hu

section AtLaw

variable [DecidableEq G]
variable {nX : ℕ} (N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
variable {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hbox : (integerBox N).Nonempty)
variable (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U → FiniteProbabilityWeights Path)
variable (hweight : ∀ z, Measurable (fun center => (law center).weight z))
local notation "Sites" => integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S))

theorem preparedFiniteScheduleModelsAtLaw_actualData
    (physical : Path → integerBox (Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S)) → integerBox N)
    (u p cap sliceLog testLog budget E : ℝ)
    (hModel : PreparedFiniteScheduleModelsAtLaw B U b S N Pdetect μ poly hbox law hweight
      physical u p cap sliceLog testLog budget E)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) 0 (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset Sites)
    (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (stepdetect : ∀ z, Tests z → ℕ)
    (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < stepdetect z j)
    (hSlices : ∀ z j, (slices z j).image Subtype.val =
      commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j))
    (hDense : ∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) sliceLog
      ((slices z j).image Subtype.val))
    (hnum : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)
    (hcomplex : ∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) testLog))
    (hcap : ∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1)
    {Forecast : Type} [Nonempty Forecast] {Pnative massLog capLog Edata : ℝ}
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (hNative : 0 ≤ Pnative)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hCap : Real.exp capLog ≤ cap)
    (hPrecision : actualForecastDataModelRequired budget Pnative massLog u p ≤ E)
    {Branch : Type} [Fintype Branch]
    (input : Branch → integerBox N → ℂ)
    (hinput : ∀ branch v, ‖input branch v‖ ≤ Real.exp p) :
    let tests : ∀ z, Tests z → Sites → ℂ := fun z j t => star ((Vdetect z j).eval
      (commonStrideIndex (cdetect z j) (stepdetect z j) t.val))
    let commonBudget := max budget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : Fin nX → ℕ) 0 commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : (integerBox N → ℂ) → ℝ := sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests
    let selectedLocal : (integerBox N → ℂ) →
      (CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) → Prop :=
      fun (err : integerBox N → ℂ)
      (errLocal : CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) =>
      ∀ center z, ∃ j, errLocal (center, z) =
        𝔼 t ∈ slices z j, err (physical z t) * tests z j t
    ∃ models : Branch → CenteredForecastModel (integerBox N),
      ∀ branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        native (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) (fun f => (data f).target)
        localSeminorm selectedLocal (input branch) (Real.exp (Qmodel + 2))
        (Real.exp (-u)) (Real.exp (2 * Qmodel + 2 * u + 4 * p + 34)) (models branch) :=
  hModel Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hSlices hDense hnum hcomplex hcap (fun f => (data f).target)
    hNative (le_max_left _ _) hPrecision
    (fun f => (data f).Term) (fun f => (data f).coefficient)
    (fun f => (data f).centerConstant) (fun f => (data f).twists)
    (fun f => (data f).mass.trans (Real.exp_le_exp.mpr (le_max_right _ _)))
    (fun f v => ((data f).approximation v).trans
      (Real.exp_le_exp.mpr (neg_le_neg hAccuracy)))
    (fun f v => ((data f).cap v).trans hCap) input hinput

end AtLaw
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem actualForecastDataModelRequired_sum_bound
    {budget Pnative massLog u p : ℝ}
    (hbudget : 0 ≤ budget) (hNative : 0 ≤ Pnative) (hMass : 0 ≤ massLog)
    (hu : 0 ≤ u) (hp : 0 ≤ p) :
    actualForecastDataModelRequired budget Pnative massLog u p ∈
      Set.Icc 0 (budget + 3 * Pnative + massLog + 3 * u + 6 * p + 55) := by
  have hcommon : max budget (3 * Pnative + 3) ≤ budget + 3 * Pnative + 3 :=
    max_le (by linarith only [hNative]) (by linarith only [hbudget])
  have hmax : max (max budget (3 * Pnative + 3))
      (2 * u + 4 * p + massLog + 20) ≤
      budget + 3 * Pnative + 3 + 2 * u + 4 * p + massLog + 20 :=
    max_le (by linarith only [hcommon, hu, hp, hMass])
      (by linarith only [hbudget, hNative])
  have hmax0 : 0 ≤ max (max budget (3 * Pnative + 3))
      (2 * u + 4 * p + massLog + 20) :=
    (by linarith only [hu, hp, hMass] : (0 : ℝ) ≤ 2 * u + 4 * p + massLog + 20).trans
      (le_max_right _ _)
  simp only [actualForecastDataModelRequired, max_eq_right hMass, Set.mem_Icc]
  exact ⟨by linarith only [hu, hp, hmax0], by linarith only [hmax]⟩

theorem actualForecastDataModelRequired_common_precision
    {Stage : Type*} (budget Pnative massLog u p : Stage → ℝ)
    {Bglobal allowance : ℝ}
    (hbudget : ∀ k, budget k ≤ Bglobal)
    (hrequired : ∀ k, actualForecastDataModelRequired
      (budget k) (Pnative k) (massLog k) (u k) (p k) ≤ budget k + allowance) :
    ∀ k, actualForecastDataModelRequired
      (budget k) (Pnative k) (massLog k) (u k) (p k) ≤ Bglobal + allowance := by
  intro k
  exact (hrequired k).trans (add_le_add (hbudget k) le_rfl)

theorem exists_actualForecastDataModelRequired_common_polynomial_budget
    (Cbudget Cpacket : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x Bglobal : ℝ}, 0 ≤ x →
      Bglobal ≤ (x + Cbudget) ^ Cbudget →
      Bglobal + (x + Cpacket) ^ Cpacket ≤ (x + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C Cbudget) ^ Cbudget +
    (Polynomial.X + Polynomial.C Cpacket) ^ Cpacket
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x Bglobal hx hBglobal
  have hpoly : (x + Cbudget) ^ Cbudget + (x + Cpacket) ^ Cpacket ≤ (x + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbound x hx
  exact (add_le_add hBglobal le_rfl).trans hpoly

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I J Eout : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {hmem : ∀ j d, coefficients (poly j) d ∈ U j}
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hmem
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
local instance : Nonempty A.Site := A.site_nonempty
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable {Fmark : NilpotentLieFiltration M t}
variable {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
variable {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le) Fmark φ marked
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost massThreshold scoreThreshold}
variable (out : P.Conclusion cost outputMass outputScore)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : out.retained, ActualFixedSpatialForecastPath (Eout := Eout)
  B U b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : out.retained, ∀ k,
  (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

local notation "input" z => out.denseSliceInput s qnum z (hkeep z) (ActualFixedSpatialForecastPath.commonTuple (path z))
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
local notation "member" z => ActualFixedSpatialForecastPath.toDenseSliceMember (path z) (input z)

include ν in

theorem exists_actual_shear_buffered_forecast_score
    (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
    (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : qnum.capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ qnum.E)
    (hPrecision : actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp qnum.capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    {scoreLog massLogTransfer : ℝ}
    (hTransferMass : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hU : scoreLog + massLogTransfer + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      massLogTransfer + scoreLog + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1)
        ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (sampleFn : out.retained → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : out.retained → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ z : out.retained, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
      poly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block Crecovered
      center (path z).center (path z).base (sampleFn z) (readFn z))
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hprimes : ∀ z, (path z).primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (hbase : ∀ z, (path z).base = z.val.1.val)
    (hnoise : ∀ z, (path z).noise = z.val.2.val)
    (hsample : ∀ z, (path z).sample = sampleFn z z.val.2.val)
    (hread : ∀ z, (path z).read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z z.val.2.val))) :
    let χ := majorPhasePlateauKernel tagCount
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
    let returned := patch.ofTaggedWeightedShearOrbit e out.ambient
    ∃ z : out.retained, outputScore / 2 ≤
      𝔼 x : integerBox N,
        ((member z).slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive
          o bW hb poly hmem s.κ x).re *
        bufferedScalarScore χ coords
          (fun u lifts => returned.value
            (Sum.elim (fun i => (u i : ℝ)) (fun i => (lifts i : ℝ)))) f lam x.val := by
  classical
  intro χ coords returned
  let Path := ActualFixedSpatialSlicedAdmissiblePath
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv)
    (Wsp := allocatedPhysicalRootBudget B U b S (fun _ => 0)) (Lsp := (S.value : ℝ))
    (physicalN := N) s qnum
  obtain ⟨data, hdata, _hnone, _hnoneCenter, _hcap, _hmass, _happrox⟩ :=
    exists_actualFixedSpatialSlicedForecastFamily_option_of_numerics
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv)
      (Wsp := allocatedPhysicalRootBudget B U b S (fun _ => 0)) (Lsp := (S.value : ℝ))
      (physicalN := N) s qnum o bW hb poly hmem
  let select : A.Path → Option Path := fun z =>
    if hz : z ∈ out.retained then some (member ⟨z,hz⟩) else none
  have hselect (z : out.retained) : select z.val = some (member z) := by
    simp only [select, dite_eq_left z.property]
  have hreal (z : out.retained) (x : integerBox N) :
      (((data (select z.val)).target x).re : ℂ) = (data (select z.val)).target x := by
    rw [hselect, (hdata (member z)).1]
    exact (member z).slice.target_real (allocatedShortIntegerSelection U b S.value)
      s.hBactive o bW hb s.κ poly hmem x
  have hPtest : 0 ≤ Ptest :=
    (hbudget.trans (le_max_left _ _)).trans hcommonTest
  have hsmall (j : Fin m) :
      s.inverse j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8 := by
    have hnonneg : 0 ≤ s.inverse j * (((Fintype.card (I j) : ℝ) + 1) * R j) :=
      mul_nonneg (s.hinverse j) (mul_nonneg (by positivity) (hR j).le)
    have hb := s.hbudget j
    have hr := s.hr3
    nlinarith only [hb, hr, hnonneg]
  have hshort (z : out.retained)
      (i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i}) :
      (A.sides i.val : ℝ) ≤ Real.exp pSlice :=
    (P.frozen_side ⟨z.val,out.subset z.property⟩ i).trans (Real.exp_le_exp.mpr hchartCost)
  have hcompare (z : out.retained)
      (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (max localBudget (3 * qnum.Pnative + 3)))
        (Real.exp (max localBudget (3 * qnum.Pnative + 3)))
        ⟨Real.exp (max localBudget (3 * qnum.Pnative + 3)), Real.exp_nonneg _⟩) :
      ‖(out.siteLaw z).complexMean (fun site => W.eval N poly (A.physical z.val site)) -
        (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).complexMean
          (fun x => W.eval N poly x.val * (data (select z.val)).target x)‖ ≤ Real.exp (-Ecompare) := by
    have htarget : (data (select z.val)).target = (member z).slice.target
        (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hmem s.κ := by
      rw [hselect]
      exact (hdata (member z)).1
    have hcenter : (data (select z.val)).centerConstant = fun j => ((path z).center j).val := by
      rw [hselect, (hdata (member z)).2]
      rfl
    exact out.siteLaw_ambient_bounded_original_twist_precision
      (s := s) (qnum := qnum) (qLate := qLate) (hδlate := hδlate) (hHlate := hHlate)
      (hvlate := hvlate) (hTaillate := hTaillate) (path := path z)
      (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := poly) (hmem := hmem)
      (hdegree := hpoly) (ξ := ξ) (hσbound := hσbound) (ν := ν) (hmargin := hmargin)
      (hκ := hκ) (hPtest := hPtest)
      (hLw := Real.exp_le_exp.mpr hcommonTest) (hpw := Real.exp_le_exp.mpr hcommonTest)
      (hcw := Real.exp_le_exp.mpr hcommonTest) (hEprec := hEprec) (hlarge := hlarge)
      (hRrank := hRrank) (hrank := hrank) (C := Crecovered) (hglobal := hglobal z)
      (hcost := hcost) (hE := hE) (hτ1 := hτ1) (hfloor := hfloor)
      (hξsmall := hξsmall) (hEdata := hEdata) (hNgrid := hNgrid)
      (earlyData := data (select z.val)) (hEarlyCenter := hcenter)
      (hprimes := hprimes z) (hexponent := hexponent z) (A := A) (z := z)
      (hkeep := hkeep z) (hkernel := hkernel) (hcutoff := hcutoff) (hlate := hlate)
      (hdensity := hdensity) (hlog := hlog) (hprescribed := hprescribed) (hstride := hstride)
      (hbase := hbase z) (hnoise := hnoise z) (hsample := hsample z) (hread := hread z)
      htarget
  obtain ⟨z, hz⟩ := out.exists_shear_buffered_forecast_score patch f lam hξone hmargin
    hu hp hbudget qnum.hPnative hSliceLog hC hCp hCap hAccuracy hPrecision hdirect hexcess
    hSlice hcostSlice htest hshort data hf hlam hσ1 s.inverse s.hinverse s.hchart hsmall hpoly e
    select hreal hTransferMass hscoreLower hmassLower hU hEcompare hcompare
  refine ⟨z, ?_⟩
  rw [hselect z, (hdata (member z)).1] at hz
  exact hz

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
