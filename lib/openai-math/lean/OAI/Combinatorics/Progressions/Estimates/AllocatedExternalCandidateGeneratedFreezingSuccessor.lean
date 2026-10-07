import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateCoveredFamilySuccessor
import OAI.Combinatorics.Progressions.Estimates.NativeMarkedFreezingPhysicalData
import OAI.Combinatorics.Progressions.Sampling.FrozenMarkedRightOrbitGrid

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

noncomputable def frozenMarkedPhysicalExponent (s : ℕ) : ℕ :=
  max (Classical.choose (exists_frozenMarkedLeftOrbit_exp_bound.{0, 0, 0, 0, 0} s))
    (Classical.choose (exists_frozenMarkedRightOrbit_grid_bound.{0, 0, 0, 0, 0} s))

theorem frozenMarkedPhysicalExponent_ge_two (s : ℕ) :
    2 ≤ frozenMarkedPhysicalExponent s :=
  (Classical.choose_spec
    (exists_frozenMarkedLeftOrbit_exp_bound.{0, 0, 0, 0, 0} s)).1.trans
      (le_max_left _ _)

private theorem frozenMarkedPhysical_exp_mono {p : ℝ} (hp : 0 ≤ p)
    {a C : ℕ} (ha : 2 ≤ a) (haC : a ≤ C) :
    Real.exp ((p + a) ^ a) ≤ Real.exp ((p + C) ^ C) := by
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (p + C) ^ a := pow_le_pow_left₀ (by positivity : 0 ≤ p + (a : ℝ))
      (add_le_add le_rfl (Nat.cast_le.mpr haC)) a
    _ ≤ _ := pow_le_pow_right₀ (by
      have hC : (2 : ℝ) ≤ C := Nat.cast_le.mpr (ha.trans haC)
      linarith) haC

theorem frozenMarkedPhysical_left_bound
    {σ ι κ L M : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H HS : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hdmark : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hHS : (HS : ℝ) ≤ Real.exp p)
    (hb : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hSheight : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) HS)
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (x : σ → ℤ)
    (hmarked : ∀ i, |(c.baseChange ℝ).repr
      (G.realification.polynomialOrbitEval w x marked).coord i| ≤ Real.exp p)
    (hcenter : ∀ i, |(b.baseChange ℝ).repr center.coord i| ≤ Real.exp p) (i : ι) :
    |(b.baseChange ℝ).repr
      (F.realification.polynomialOrbitEval w x
        (F.frozenMarkedLeftOrbit G w S hS marked center)).coord i| ≤
      Real.exp ((p + frozenMarkedPhysicalExponent s) ^ frozenMarkedPhysicalExponent s) := by
  have hleft := Classical.choose_spec
    (exists_frozenMarkedLeftOrbit_exp_bound.{0, 0, 0, 0, 0} s)
  exact (hleft.2 F G b c w S hS H HS p hp hd hdmark hH hHS hb hSheight
    marked center x hmarked hcenter i).trans
      (frozenMarkedPhysical_exp_mono hp hleft.1 (le_max_left _ _))

theorem exists_frozenMarkedPhysical_right_grid
    {σ ι κ L M : Type} [Fintype σ] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hb : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hlp : ((matrixDenominator (LinearMap.toMatrix c b S) * q * r : ℕ) : ℝ) ≤
      Real.exp p) :
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ≤ Real.exp ((p + frozenMarkedPhysicalExponent s) ^
        frozenMarkedPhysicalExponent s) ∧
      matrixDenominator (LinearMap.toMatrix c b S) * q * r ∣ m ∧
      ∀ marked : G.realification.PolynomialOrbit w,
        CoefficientGrid (c.baseChange ℝ) q marked.log →
        ∀ center : F.realification.Group,
          (b.baseChange ℝ).equivFun center.coord ∈ realDenominatorGrid r →
          ∀ x : σ → ℤ,
            (b.baseChange ℝ).equivFun
              (F.realification.polynomialOrbitEval w x
                (F.frozenMarkedRightOrbit G w S hS marked center)).coord ∈
              realDenominatorGrid m := by
  have hright := Classical.choose_spec
    (exists_frozenMarkedRightOrbit_grid_bound.{0, 0, 0, 0, 0} s)
  obtain ⟨m, hm, hmp, hdiv, hgrid⟩ := hright.2 F G b c w S hS H p hp hd hH hb q r hq hr hlp
  exact ⟨m, hm, hmp.trans
    (frozenMarkedPhysical_exp_mono hp hright.1 (le_max_right _ _)), hdiv, hgrid⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem frozenMarkedPhysical_bounds
    {κ : Type} [Fintype κ] [DecidableEq κ] (cF : Basis κ ℚ M)
    (sectionMap : M →ₗ[ℚ] L)
    (hSection : ∀ j, ∀ y ∈ Fmark.layer j, sectionMap y ∈ D.filtration.layer j) :
    let C := frozenMarkedPhysicalExponent s
    ∀ (H HS : ℕ) (p : ℝ), 0 ≤ p →
        (Fintype.card (Fin d) : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
        (H : ℝ) ≤ Real.exp p → (HS : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H) →
        (∀ i j, RationalHeightLE (LinearMap.toMatrix cF D.basis sectionMap i j) HS) →
        ∀ q r : ℕ, 0 < q → 0 < r →
          ((matrixDenominator (LinearMap.toMatrix cF D.basis sectionMap) * q * r : ℕ) : ℝ) ≤
            Real.exp p →
          ∃ mFull : ℕ, 0 < mFull ∧ (mFull : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            matrixDenominator (LinearMap.toMatrix cF D.basis sectionMap) * q * r ∣ mFull ∧
            ∀ leftMark rightMark : Fmark.realification.PolynomialOrbit
                (fullTaggedVariableWeight (X := X) J),
              (∀ x ∈ integerBox N, ∀ i, |(cF.baseChange ℝ).repr
                (Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                  (P.physicalIntegerPoint x) leftMark).coord i| ≤ Real.exp p) →
              CoefficientGrid (cF.baseChange ℝ) q rightMark.log →
              ∀ leftCenter rightCenter : D.filtration.realification.Group,
                (∀ i, |(D.basis.baseChange ℝ).repr leftCenter.coord i| ≤ Real.exp p) →
                (D.basis.baseChange ℝ).equivFun rightCenter.coord ∈ realDenominatorGrid r →
                (∀ x ∈ integerBox N, ∀ i, |(D.basis.baseChange ℝ).repr
                  (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                    (P.physicalIntegerPoint x)
                    (D.filtration.frozenMarkedLeftOrbit Fmark (fullTaggedVariableWeight J)
                      sectionMap hSection leftMark leftCenter)).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                (∀ x ∈ integerBox N, (D.basis.baseChange ℝ).equivFun
                  (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                    (P.physicalIntegerPoint x)
                    (D.filtration.frozenMarkedRightOrbit Fmark (fullTaggedVariableWeight J)
                      sectionMap hSection rightMark rightCenter)).coord ∈ realDenominatorGrid mFull) := by
  intro C H HS p hp hdim hdimF hH hHS hlie hsection q r hq hr hqr
  obtain ⟨mFull, hm, hmp, hdiv, hgrid⟩ :=
    exists_frozenMarkedPhysical_right_grid D.filtration Fmark D.basis cF
      (fullTaggedVariableWeight (X := X) J) sectionMap hSection
      H p hp hdim hH hlie q r hq hr hqr
  refine ⟨mFull, hm, hmp, hdiv, ?_⟩
  intro leftMark rightMark hleftMark hrightMark leftCenter rightCenter hleftCenter hrightCenter
  constructor
  · intro x hx i
    exact frozenMarkedPhysical_left_bound D.filtration Fmark D.basis cF
      (fullTaggedVariableWeight J) sectionMap hSection H HS p
      hp hdim hdimF hH hHS hlie hsection leftMark leftCenter
      (P.physicalIntegerPoint x) (hleftMark x hx) hleftCenter i
  · intro x _
    exact hgrid rightMark hrightMark rightCenter hrightCenter (P.physicalIntegerPoint x)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.RationalFilteredNilmanifold

noncomputable def allocatedRightDictionaryExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_native_grid_right_dictionary.{0} s)

noncomputable def allocatedCoveredLowerExponent (s k : ℕ) : ℕ :=
  Classical.choose (exists_allocated_marked_covered_lower_diagram.{0, 0} s k)

theorem allocatedCoveredLowerExponent_ge_two (s k : ℕ) :
    2 ≤ allocatedCoveredLowerExponent s k :=
  (Classical.choose_spec (exists_allocated_marked_covered_lower_diagram.{0, 0} s k)).1

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {inputDenominator k e : ℕ} {pGeo : ℝ}
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_generatedCovered_nativeReset_degreeRule
    {Bweight Bobs Lip densityCost p budgetLog massLog : ℝ}
    (C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt denominator
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (finiteFreezingInitialPrecision p) (Real.exp budgetLog))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * (Real.exp budgetLog) * max 1 (Real.exp budgetLog)) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hweightCap : Bweight ≤ Real.exp p) (hobsCap : Bobs ≤ Real.exp p)
    (hlipCap : Lip ≤ Real.exp p) (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ (p + C) ^ C) (hdensityInput : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C)
    (hcount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ (p + C) ^ C)
    (hmassLog : massLog ≤ (p + C) ^ C) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0) (hpGeo : 1 ≤ pGeo) (hDGeo : D.GeometryComplexityLE pGeo)
    (hpGeoInput : p ≤ pGeo)
    (hpGeoRec : pGeo ≤ finiteFreezingRecursiveParameter C p)
    (hcoveredRec : ((pGeo + RationalFilteredNilmanifold.allocatedCoveredLowerExponent s k) ^ RationalFilteredNilmanifold.allocatedCoveredLowerExponent s k) ≤ finiteFreezingRecursiveParameter C p)
    (hℓ : (ℓ : ℝ) ≤ Real.exp pGeo)
    (pRight : ℝ) (hpRight : 0 ≤ pRight) (hDRight : D.GeometryComplexityLE pRight)
    (hinputDenominator : 0 < inputDenominator)
    (hinputDenominatorBound : (inputDenominator : ℝ) ≤ Real.exp pRight)
    (hRightBudget : (pRight + RationalFilteredNilmanifold.allocatedRightDictionaryExponent (s + 1)) ^
      RationalFilteredNilmanifold.allocatedRightDictionaryExponent (s + 1) ≤ pGeo)
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hFGeo : Fmark.GeometryComplexityLE pGeo)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ pGeo)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ pGeo)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ pGeo)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr (generators i) j) ≤ pGeo)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pGeo + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (hfullLeft : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight J)
            sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1))).coord i| ≤
        Real.exp ((pGeo + 2) ^ k))
    (hfullRight : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight J)
            sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2))).coord ∈
        realDenominatorGrid inputDenominator)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s k e + 2)
      (finiteFreezingRecursiveParameter C p) outputCost) :
    Nonempty (P₀.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  obtain ⟨rightDictionary⟩ := (Classical.choose_spec
    (RationalFilteredNilmanifold.exists_native_grid_right_dictionary.{0} (s + 1))).2
    D pRight hpRight hDRight inputDenominator hinputDenominator hinputDenominatorBound
  have hdenominator : (rightDictionary.denominator : ℝ) ≤ Real.exp pGeo :=
    rightDictionary.denominator_bound.trans (Real.exp_le_exp.mpr hRightBudget)
  have hRightCount : (rightDictionary.count : ℝ) ≤ Real.exp (finiteFreezingRecursiveParameter C p) :=
    rightDictionary.count_bound.trans (Real.exp_le_exp.mpr (hRightBudget.trans hpGeoRec))
  have hsourceBasis (i j : Fin d) : rationalLogHeight (D.basis.repr (D.basis i) j) ≤ pGeo := by
    rw [Basis.repr_self]
    simp only [Finsupp.single_apply]
    split_ifs <;> simpa [rationalLogHeight] using (zero_le_one.trans hpGeo)
  obtain ⟨covered⟩ := (Classical.choose_spec
    (RationalFilteredNilmanifold.exists_allocated_marked_covered_lower_diagram.{0, 0} s k)).2
    D Fmark D.basis dw hdb c ν hF φ hφ hsurj W generators hspan hW hpGeo hDGeo hFGeo
    hgeneratorCount hsourceBasis hmarkedBasis hmarkHeight hgeneratorHeight htopKernel
    rightDictionary.denominator rightDictionary.denominator_pos hdenominator
  exact P₀.conclusion_of_covered_nativeReset_degreeRule Fmark φ hφ keep hkeep W
    rightDictionary covered sectionMap hSectionFilt c ν hF factors reset
    tests htests hσ1 H hH hchart hsmall hp C hp0 hC dictionary hslowMark hgrid hdensity hfloor
    hBweight hBobs hLip hweight hnorm hlip hweightCap hobsCap hlipCap hscoreInput
    hcostInput hdensityInput hbudgetLog0 hbudgetLog hcount hmassLog hmassInput
    hsection dw hdb hW hsurj hξ1 ℓ (zero_le_one.trans hpGeo) hDGeo
    hpGeoInput hpGeoRec hcoveredRec hℓ hRightCount hOriginalLip hpositive hOriginalNet
    hfullLeft hfullRight outputCost lowerIH

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {e : ℕ} {pGeo : ℝ}
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_generatedPhysical_nativeReset_degreeRule
    {Bweight Bobs Lip densityCost p budgetLog massLog : ℝ}
    (C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt denominator
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (finiteFreezingInitialPrecision p) (Real.exp budgetLog))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * (Real.exp budgetLog) * max 1 (Real.exp budgetLog)) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hweightCap : Bweight ≤ Real.exp p) (hobsCap : Bobs ≤ Real.exp p)
    (hlipCap : Lip ≤ Real.exp p) (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ (p + C) ^ C) (hdensityInput : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C)
    (hcount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ (p + C) ^ C)
    (hmassLog : massLog ≤ (p + C) ^ C) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0) (hpGeo : 1 ≤ pGeo) (hDGeo : D.GeometryComplexityLE pGeo)
    (hpGeoInput : p ≤ pGeo)
    (hpGeoRec : pGeo ≤ finiteFreezingRecursiveParameter C p)
    (hcoveredRec : ((pGeo + RationalFilteredNilmanifold.allocatedCoveredLowerExponent s 1) ^ RationalFilteredNilmanifold.allocatedCoveredLowerExponent s 1) ≤ finiteFreezingRecursiveParameter C p)
    (hℓ : (ℓ : ℝ) ≤ Real.exp pGeo)
    (Hbr Hsection : ℕ) (pOuter : ℝ) (hpOuter : 0 ≤ pOuter)
    (hDOuter : D.GeometryComplexityLE pOuter)
    (hmarkedDimension : (nMarkedBasis : ℝ) ≤ pOuter)
    (hHbr : (Hbr : ℝ) ≤ Real.exp pOuter)
    (hHsection : (Hsection : ℝ) ≤ Real.exp pOuter)
    (hbracket : ∀ i j z, RationalHeightLE (lieStructureConstants D.basis i j z) Hbr)
    (hsectionHeight : ∀ i j, RationalHeightLE (LinearMap.toMatrix c D.basis sectionMap i j) Hsection)
    (hdenominatorPos : 0 < denominator)
    (hsectionDenominators :
      ((matrixDenominator (LinearMap.toMatrix c D.basis sectionMap) * denominator *
        dictionary.denominator : ℕ) : ℝ) ≤ Real.exp pOuter)
    (hkernelCenters : budgetLog ≤ pOuter)
    (hmarkedPhysicalLeft : ∀ x ∈ integerBox N, ∀ i,
      |(c.baseChange ℝ).repr
        (Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x) reset.leftMark).coord i| ≤ Real.exp pOuter)
    (hPhysicalBudget : ((pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1)) ≤ pGeo)
    (hRightBudget : (((pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1)) + RationalFilteredNilmanifold.allocatedRightDictionaryExponent (s + 1)) ^
      RationalFilteredNilmanifold.allocatedRightDictionaryExponent (s + 1) ≤ pGeo)
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hFGeo : Fmark.GeometryComplexityLE pGeo)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ pGeo)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ pGeo)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ pGeo)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr (generators i) j) ≤ pGeo)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pGeo + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter C p) outputCost) :
    Nonempty (P₀.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  let pRight := (pOuter + frozenMarkedPhysicalExponent (s + 1)) ^
    frozenMarkedPhysicalExponent (s + 1)
  have hpRight : 0 ≤ pRight := by dsimp [pRight]; positivity
  have hpOuterRight : pOuter ≤ pRight := by
    have hC := frozenMarkedPhysicalExponent_ge_two (s + 1)
    apply (le_power_budget hpOuter (by omega : 1 ≤ frozenMarkedPhysicalExponent (s + 1))).trans
    simpa only [pRight, add_comm, Nat.cast_ofNat] using
      pow_le_pow_left₀ (by positivity)
        (add_le_add_left (Nat.cast_le.mpr hC) pOuter)
        (frozenMarkedPhysicalExponent (s + 1))
  obtain ⟨mFull, hmFull, hmFullBound, _, hvalue⟩ :=
    (P₀.withKeep keep hkeep).frozenMarkedPhysical_bounds c sectionMap hSectionFilt
      Hbr Hsection pOuter hpOuter (by simpa only [Fintype.card_fin] using hDOuter.1)
      (by simpa only [Fintype.card_fin] using hmarkedDimension)
      hHbr hHsection hbracket hsectionHeight denominator dictionary.denominator
      hdenominatorPos dictionary.denominator_pos hsectionDenominators
  have hrightCoeff : CoefficientGrid (c.baseChange ℝ) denominator reset.rightMark.log :=
    (Fmark.filtration.polynomialRationalGrid_iff_formal c (fullTaggedVariableWeight J)
      denominator factors.right).mp hgrid
  have hfull (ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) :=
    hvalue reset.leftMark reset.rightMark hmarkedPhysicalLeft hrightCoeff
      (dictionary.left ij.1) (dictionary.right ij.2)
      (fun i => ((dictionary.left_bounds ij.1).2 i).trans (Real.exp_le_exp.mpr hkernelCenters))
      (dictionary.right_bounds ij.2).2.2
  apply P₀.conclusion_of_generatedCovered_nativeReset_degreeRule Fmark φ hφ keep hkeep W
    sectionMap hSectionFilt c ν hF factors reset tests htests hσ1 H hH hchart hsmall hp
    C hp0 hC dictionary hslowMark hgrid hdensity hfloor hBweight hBobs hLip hweight hnorm hlip
    hweightCap hobsCap hlipCap hscoreInput hcostInput hdensityInput hbudgetLog0 hbudgetLog
    hcount hmassLog hmassInput hsection dw hdb hW hsurj hξ1 ℓ hpGeo hDGeo
    hpGeoInput hpGeoRec hcoveredRec hℓ pRight hpRight (hDOuter.mono D hpOuterRight)
    hmFull hmFullBound hRightBudget hOriginalLip hpositive hFGeo generators hspan
    hgeneratorCount hmarkedBasis hmarkHeight hgeneratorHeight htopKernel hOriginalNet
    (fun ij x hx i => ((hfull ij).1 x hx i).trans (Real.exp_le_exp.mpr (by
      simpa only [pow_one] using hPhysicalBudget.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)))))
    (fun ij => (hfull ij).2) outputCost lowerIH

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module Submodule NilpotentLieFiltration
open scoped TensorProduct

noncomputable def allocatedGeneratedRightDictionary
    {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {degree d : ℕ} (D : RationalFilteredNilmanifold L degree d)
    (p : ℝ) (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (q : ℕ) (hq : 0 < q) (hqp : (q : ℝ) ≤ Real.exp p) :
    D.NativeGridRightDictionary q
      (Real.exp ((p + allocatedRightDictionaryExponent degree) ^
        allocatedRightDictionaryExponent degree)) :=
  Classical.choice ((Classical.choose_spec (exists_native_grid_right_dictionary.{0} degree)).2
    D p hp hD q hq hqp)

noncomputable def allocatedGeneratedCoveredLowerDiagram
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d f nMarkedBasis : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (k : ℕ)
    (c : Basis (Fin nMarkedBasis) ℚ M) (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw
      W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    {pGeo : ℝ} (hpGeo : 1 ≤ pGeo) (hDGeo : D.GeometryComplexityLE pGeo)
    (hFGeo : Fmark.GeometryComplexityLE pGeo)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ pGeo)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ pGeo)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ pGeo)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr
        (generators i) j) ≤ pGeo)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) →
      φ x = 0 → x = 0)
    (q : ℕ) (hq : 0 < q) (hqp : (q : ℝ) ≤ Real.exp pGeo) :
    AllocatedMarkedCoveredLowerDiagram D Fmark φ hφ W k q pGeo
      ((pGeo + allocatedCoveredLowerExponent s k) ^ allocatedCoveredLowerExponent s k) :=
  Classical.choice (by
    have hsourceBasis (i j : Fin d) : rationalLogHeight (D.basis.repr (D.basis i) j) ≤ pGeo := by
      rw [Basis.repr_self]
      simp only [Finsupp.single_apply]
      split_ifs <;> simpa [rationalLogHeight] using (zero_le_one.trans hpGeo)
    exact (Classical.choose_spec (exists_allocated_marked_covered_lower_diagram.{0, 0} s k)).2
      D Fmark D.basis dw hdb c ν hF φ hφ hsurj W generators hspan hW hpGeo hDGeo hFGeo
      hgeneratorCount hsourceBasis hmarkedBasis hmarkHeight hgeneratorHeight htopKernel q hq hqp)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {e : ℕ} {pGeo : ℝ}
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem conclusion_of_generatedFreezing_nativeReset_degreeRule
    {densityCost p massLog : ℝ}
    (a C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (hDNative : D.GeometryComplexityLE p)
    (hRetainedCount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ p)
    (hMarkedDimension : (nMarkedBasis : ℝ) ≤ p)
    (hSectionMapHeight : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p)
    (hdenominatorPos : 0 < denominator)
    (hdenominatorBound : (denominator : ℝ) ≤ Real.exp p)
    (hSlowBound : slow ≤ Real.exp ((p + 2) ^ a))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * (Real.exp ((p + RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a) ^ RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a)) * max 1 (Real.exp ((p + RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a) ^ RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a))) ≤ (A.sides i.val : ℝ))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ (p + C) ^ C) (hdensityInput : densityCost ≤ (p + C) ^ C)
    (hbudgetLog : ((p + RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a) ^ RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a) ≤ (p + C) ^ C)
    (hmassLog : massLog ≤ (p + C) ^ C) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0) (hpGeo : 1 ≤ pGeo)
    (hpGeoInput : p ≤ pGeo)
    (hpGeoRec : pGeo ≤ finiteFreezingRecursiveParameter C p)
    (hcoveredRec : ((pGeo + RationalFilteredNilmanifold.allocatedCoveredLowerExponent s 1) ^ RationalFilteredNilmanifold.allocatedCoveredLowerExponent s 1) ≤ finiteFreezingRecursiveParameter C p)
    (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hmarkedPhysicalLeft : ∀ x ∈ integerBox N, ∀ i,
      |(c.baseChange ℝ).repr
        (Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x) reset.leftMark).coord i| ≤ Real.exp (RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter p (RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a)))
    (hPhysicalBudget : (((RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter p (RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a)) + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1)) ≤ pGeo)
    (hRightBudget : ((((RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter p (RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a)) + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1)) + RationalFilteredNilmanifold.allocatedRightDictionaryExponent (s + 1)) ^
      RationalFilteredNilmanifold.allocatedRightDictionaryExponent (s + 1) ≤ pGeo)
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hFGeo : Fmark.GeometryComplexityLE pGeo)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ pGeo)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ pGeo)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ pGeo)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr (generators i) j) ≤ pGeo)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pGeo + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter C p) outputCost) :
    Nonempty (P₀.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  let Cfree := RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a
  let budgetLog := (p + Cfree) ^ Cfree
  let pOuter := RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter p Cfree
  have hOuter := RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter_bounds hp0 Cfree
  have hpOuter : 0 ≤ pOuter := hp0.trans hOuter.1
  have hpC : p ≤ (p + C) ^ C := by
    have htwoC : (2 : ℝ) ≤ C := by exact_mod_cast hC
    exact (le_power_budget hp0 (by omega : 1 ≤ C)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) C)
  obtain ⟨data⟩ := D.exists_nativeMarkedFreezingPhysicalData
    (X := X → ℤ) Fmark.filtration c φ hφ
    (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) denominator
    (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow p
    a dw hdb ν hF hsurj (fun _ => by norm_num) hp0 hDNative hRetainedCount
    (by simpa only [Fintype.card_fin] using hMarkedDimension) hSectionMapHeight
    hdenominatorPos hdenominatorBound (fun i => by exact_mod_cast A.sides_pos i.val) hSlowBound
  have hcap (x : X → ℤ) (y : D.Space) : ‖observable x y‖ ≤ 1 := by
    simpa only [positiveClip_eq_self _ (hpositive x y)] using
      norm_positiveClip_le_one (observable x y)
  let tests : (X → ℤ) → D.Niltest
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) :=
    fun x => D.externalNetNiltest (observable x) ℓ (hcap x) (hOriginalLip x) 1
  have hbracket : ∀ i j z, RationalHeightLE (lieStructureConstants D.basis i j z) ⌈Real.exp p⌉₊ :=
    fun i j z => rationalHeightLE_ceil_exp (hDNative.2.2.1 i j z)
  have hHbr : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp pOuter :=
    (ceil_exp_le_exp_add_one hp0).trans (Real.exp_le_exp.mpr hOuter.2.2.2)
  exact P₀.conclusion_of_generatedPhysical_nativeReset_degreeRule Fmark φ hφ keep hkeep W
    data.sectionMap data.section_filtered c ν hF factors reset
    tests (fun _ => rfl) hσ1 H hH hchart hsmall hp C hp0 hC
    data.dictionary hslowMark hgrid hdensity hfloor
    (Real.exp_nonneg p) (by norm_num : (0 : ℝ) ≤ 1) (NNReal.coe_nonneg ℓ)
    hweight (fun _ => le_rfl) (fun _ => le_rfl)
    le_rfl (Real.one_le_exp_iff.mpr hp0) hℓ hscoreInput
    hcostInput hdensityInput (pow_nonneg (by positivity) Cfree) hbudgetLog
    (hRetainedCount.trans hpC) hmassLog hmassInput
    data.section_rightInverse dw hdb hW hsurj hξ1 ℓ hpGeo (hDNative.mono D hpGeoInput)
    hpGeoInput hpGeoRec hcoveredRec (hℓ.trans (Real.exp_le_exp.mpr hpGeoInput))
    ⌈Real.exp p⌉₊ (rationalKernelHeight (Fintype.card (Fin nMarkedBasis)) ⌈Real.exp p⌉₊)
    pOuter hpOuter (hDNative.mono D hOuter.1) (hMarkedDimension.trans hOuter.1)
    hHbr data.section_height_bound hbracket data.section_height hdenominatorPos
    data.denominator_bound hOuter.2.1 hmarkedPhysicalLeft hPhysicalBudget hRightBudget
    hOriginalLip hpositive hFGeo generators hspan hgeneratorCount hmarkedBasis hmarkHeight
    hgeneratorHeight htopKernel hOriginalNet outputCost lowerIH

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
