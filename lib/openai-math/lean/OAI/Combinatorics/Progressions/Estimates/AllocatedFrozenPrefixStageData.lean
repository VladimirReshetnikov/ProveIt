import OAI.Combinatorics.Progressions.Dynamics.AllocatedCandidateBudgetedTreeTerminal
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFrozenNativeFactors
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateFrozenStageDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCandidateStageBaseExponent (s m Cprimitive : ℕ) : ℕ :=
  max 2 (max (s + 3)
    (max (4 * allocatedCandidateTerminalControlConstant s m 1) Cprimitive))

noncomputable def allocatedCandidateStageSliceExponent (s m Cprimitive : ℕ) : ℕ :=
  Classical.choose (exists_allocatedCandidateStageSliceLog_budget s m
    (allocatedCandidateStageBaseExponent s m Cprimitive))

noncomputable def allocatedCandidateStageBase (s m Cprimitive : ℕ) (b : ℝ) : ℝ :=
  (b + allocatedCandidateStageBaseExponent s m Cprimitive) ^
    allocatedCandidateStageBaseExponent s m Cprimitive

noncomputable def allocatedCandidateStageSlice (s m Cprimitive : ℕ) (b : ℝ) : ℝ :=
  (b + allocatedCandidateStageSliceExponent s m Cprimitive) ^
    allocatedCandidateStageSliceExponent s m Cprimitive

 theorem allocatedCandidateStageBaseExponent_bounds (s m Cprimitive : ℕ) :
    2 ≤ allocatedCandidateStageBaseExponent s m Cprimitive ∧
    s + 3 ≤ allocatedCandidateStageBaseExponent s m Cprimitive ∧
    4 * allocatedCandidateTerminalControlConstant s m 1 ≤
      allocatedCandidateStageBaseExponent s m Cprimitive ∧
    Cprimitive ≤ allocatedCandidateStageBaseExponent s m Cprimitive := by
  unfold allocatedCandidateStageBaseExponent
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)⟩

 theorem allocatedCandidateStageBase_bounds (s m Cprimitive : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    2 ≤ allocatedCandidateStageBase s m Cprimitive b ∧
    b ≤ allocatedCandidateStageBase s m Cprimitive b := by
  let C := allocatedCandidateStageBaseExponent s m Cprimitive
  have hC : (2 : ℝ) ≤ C := Nat.cast_le.mpr (allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1
  have hbase : 1 ≤ b + C := by linarith
  have hp : b + C ≤ (b + C) ^ C := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase
      (show 1 ≤ C by have := (allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1; omega)
  change 2 ≤ (b + C) ^ C ∧ b ≤ (b + C) ^ C
  exact ⟨(show 2 ≤ b + C by linarith).trans hp, (le_add_of_nonneg_right (Nat.cast_nonneg C)).trans hp⟩

 theorem allocatedCandidateStage_primitive_le_base (s m Cprimitive : ℕ)
    {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) :
    (x + Cprimitive) ^ Cprimitive ≤ allocatedCandidateStageBase s m Cprimitive b := by
  let C := allocatedCandidateStageBaseExponent s m Cprimitive
  have hC := (allocatedCandidateStageBaseExponent_bounds s m Cprimitive).2.2.2
  have hCtwo : (2 : ℝ) ≤ C := Nat.cast_le.mpr
    (allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1
  change _ ≤ (b + C) ^ C
  exact (pow_le_pow_left₀ (add_nonneg hx (Nat.cast_nonneg _))
    (add_le_add hxb (Nat.cast_le.mpr hC)) Cprimitive).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ b + C) hC)

 theorem allocatedCandidateStage_control_le_base (s m Cprimitive d : ℕ)
    {b : ℝ} (hb : 0 ≤ b) (hd : (d : ℝ) ≤ b) :
    (allocatedCandidateForwardControlInput s d b + allocatedCandidateTerminalControlConstant s m 1) ^
      allocatedCandidateTerminalControlConstant s m 1 ≤ allocatedCandidateStageBase s m Cprimitive b := by
  have h := allocatedCandidateStageBaseExponent_bounds s m Cprimitive
  exact allocatedCandidateForwardControlInput_power_bound s d
    (allocatedCandidateTerminalControlConstant s m 1)
    (allocatedCandidateStageBaseExponent s m Cprimitive) hb hd h.1 h.2.1 h.2.2.1

 theorem allocatedCandidateStageSlice_bounds (s m Cprimitive : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    2 ≤ allocatedCandidateStageSliceExponent s m Cprimitive ∧
    allocatedCandidateStageSliceLog s m (allocatedCandidateStageBase s m Cprimitive b) ≤
      allocatedCandidateStageSlice s m Cprimitive b := by
  have h := Classical.choose_spec (exists_allocatedCandidateStageSliceLog_budget s m
    (allocatedCandidateStageBaseExponent s m Cprimitive))
  exact ⟨h.1, h.2 b hb⟩

 theorem allocatedCandidateStageBase_le_forwardWork (s m Cprimitive A : ℕ)
    (count : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hCA : allocatedCandidateStageBaseExponent s m Cprimitive ≤ A) :
    allocatedCandidateStageBase s m Cprimitive (preparedFiniteForwardParameter A count r x) ≤
      preparedFiniteForwardWork A count r x := by
  let b := preparedFiniteForwardParameter A count r x
  let C := allocatedCandidateStageBaseExponent s m Cprimitive
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A count r hx
  have hA : (2 : ℝ) ≤ A := Nat.cast_le.mpr
    ((allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1.trans hCA)
  rw [preparedFiniteForwardWork_eq]
  change (b + C) ^ C ≤ (b + A) ^ A
  exact (pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg _))
    (add_le_add (le_refl b) (Nat.cast_le.mpr hCA)) C).trans
      (pow_le_pow_right₀ (by linarith) hCA)

 theorem allocatedCandidateStageSlice_forward_bounds (s m Cprimitive A : ℕ)
    (count : ℕ → ℕ) (r dimCount : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hdimCount : (dimCount : ℝ) ≤ x)
    (hCA : allocatedCandidateStageSliceExponent s m Cprimitive + 1 ≤ A) :
    let pSlice := allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter A count r x)
    0 ≤ pSlice ∧ pSlice ≤ preparedFiniteForwardWork A count r x ∧
      pSlice * dimCount ≤ preparedFiniteForwardWork A count r x := by
  exact preparedFiniteForward_controlled_slice_bounds A
    (allocatedCandidateStageSliceExponent s m Cprimitive) count r dimCount
    (by have h := (allocatedCandidateStageSlice_bounds s m Cprimitive hx).1; omega)
    hCA hx hdimCount

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

theorem allocatedCandidateStage_cost_lt_slice (s m Cprimitive : ℕ)
    {x b cost : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive) :
    cost < allocatedCandidateStageSlice s m Cprimitive b := by
  have hb : 0 ≤ b := hx.trans hxb
  have hv := (allocatedCandidateStageBase_bounds s m Cprimitive hb).1
  have hcostBase := hcost.trans
    (allocatedCandidateStage_primitive_le_base s m Cprimitive hx hxb)
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hstrict : allocatedCandidateStageBase s m Cprimitive b <
      allocatedCandidateStageBase s m Cprimitive b + (s : ℝ) + 1 := by
    linarith only [hs0]
  have hraw := (allocatedCandidateStage_slice_bounds s m hv).2.2.1
  have hcanonical := (allocatedCandidateStageSlice_bounds s m Cprimitive hb).2
  exact hcostBase.trans_lt (hstrict.trans_le (hraw.trans hcanonical))

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    {D : RationalFilteredNilmanifold L s d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_axisFreezing_of_side_bounds
    (keep : LayerSamplerVariables G I n B → Prop) (pSlice : ℝ)
    (hcost : cost < pSlice)
    (hkept : ∀ i, keep i → Real.exp pSlice ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Real.exp pSlice) :
    Nonempty (P.AxisFreezing (fun _ => keep) pSlice) := by
  refine P.exists_axisFreezing (fun _ => keep) ?_ pSlice ?_
  · intro z i hi
    by_contra hnot
    have hupper := P.frozen_side z ⟨i, hnot⟩
    have hlower := (Real.exp_lt_exp.mpr hcost).trans_le (hkept i hi)
    exact (not_lt_of_ge hupper) hlower
  · intro z i hi
    exact hfrozen i.val hi

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_forward_axisFreezing
    (keep : LayerSamplerVariables G I n B → Prop)
    (Cprimitive scheduleExponent r : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (hkept : ∀ i, keep i →
      Real.exp (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤
      Real.exp (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x))) :
    Nonempty (P.AxisFreezing (fun _ => keep)
      (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x))) := by
  exact P.exists_axisFreezing_of_side_bounds keep _
    (allocatedCandidateStage_cost_lt_slice s m Cprimitive hx
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx) hcost)
    hkept hfrozen

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer allocatedFrozenCurrentGradeResetConstant

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

noncomputable def historyStageData_of_prefix_bounds
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Cprimitive : ℕ) (x b Bstage Rrank : ℝ) (C : ℕ)
    (hx : 0 ≤ x) (hxb : x ≤ b) (hBstage : Bstage ≤ b)
    (sliceCost : ℝ) (hSliceCost : sliceCost ≤ (x + Cprimitive) ^ Cprimitive)
    (hdense : ∀ z : P.productive, IsDenseCommonStrideBox (fun i : Vars => A.sides i.val)
      sliceCost ((Q).chart z).slice.integerPoints)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : (Fintype.card χ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hη : (Fintype.card η : ℝ) ≤ x)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pTest sourceNative α : ℝ)
    (hsourceNative : 0 ≤ sourceNative)
    (hkept : ∀ i, keep i → Real.exp (allocatedCandidateStageSlice s m Cprimitive b) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive b))
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive b) pTest sourceNative α)
    (hNmajor : ∀ i, Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := P) (keep := keep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage
        ((allocatedCandidateForwardControlInput s (Fintype.card η) b +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (allocatedCandidateNativeMajorBudget
          (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
          (allocatedCandidateStageBase s m Cprimitive b)) Rrank C := by
  have hb0 : 0 ≤ b := hx.trans hxb
  have hprimitive := allocatedCandidateStage_primitive_le_base s m Cprimitive hx hxb
  obtain ⟨hv, hbBase⟩ := allocatedCandidateStageBase_bounds s m Cprimitive hb0
  have hcontrol := allocatedCandidateStage_control_le_base s m Cprimitive
    (Fintype.card η) hb0 (hη.trans hxb)
  have hslice := (allocatedCandidateStageSlice_bounds s m Cprimitive hb0).2
  have hexp := Real.exp_le_exp.mpr hprimitive
  exact P.historyStageData_of_native_source keep hkeep bD ω hD bF ν hF hφ W
    eQ r hr Bstage
    ((allocatedCandidateForwardControlInput s (Fintype.card η) b +
      allocatedCandidateTerminalControlConstant s m 1) ^
      allocatedCandidateTerminalControlConstant s m 1)
    Rrank C (allocatedCandidateStageBase s m Cprimitive b) hv hcontrol
    (hBstage.trans hbBase) sliceCost (hSliceCost.trans hprimitive) hdense
    HMap l H Hθ qNative hHMap hl hH
    (hHMapExp.trans hexp) (hlExp.trans hexp) (hHExp.trans hexp) (hHθExp.trans hexp)
    (hqNative.trans hprimitive) hentries (hsource.trans hprimitive) (htarget.trans hprimitive)
    (hκ.trans hprimitive) (hχ.trans hprimitive) ((hη.trans hxb).trans hbBase)
    (htags.trans hprimitive) (hsampler.trans hprimitive) (fun j => (hJ j).trans hprimitive)
    hbracket vg hspan hvg hθ hfactor hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    (allocatedCandidateStageSlice s m Cprimitive b) pTest sourceNative α
    hslice hkept hfrozen hsourceNative hTest hα hdirect hNmajor hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration
open scoped Classical

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem allocatedCandidateStage_keep_subset_initialLong
    {σ : Type*} (side : σ → ℝ) (initialLong keep : σ → Prop)
    (s m Cprimitive scheduleExponent r : ℕ) {x initialShortCost : ℝ}
    (hx : 0 ≤ x)
    (hshortCost : initialShortCost ≤ (x + Cprimitive) ^ Cprimitive)
    (hshort : ∀ i, ¬initialLong i → side i ≤ Real.exp initialShortCost)
    (hkept : ∀ i, keep i →
      Real.exp (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ side i) :
    ∀ i, keep i → initialLong i := by
  intro i hi
  by_contra hnot
  have hstrict := Real.exp_lt_exp.mpr
    (allocatedCandidateStage_cost_lt_slice s m Cprimitive hx
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx) hshortCost)
  exact (not_lt_of_ge (hshort i hnot)) (hstrict.trans_le (hkept i hi))

theorem allocatedCandidateStage_canonical_masks
    {σ : Type*} (side : σ → ℝ) (initialLong : σ → Prop)
    (s m Cprimitive scheduleExponent : ℕ) {x initialShortCost : ℝ}
    (hx : 0 ≤ x)
    (hshortCost : initialShortCost ≤ (x + Cprimitive) ^ Cprimitive)
    (hshort : ∀ i, ¬initialLong i → side i ≤ Real.exp initialShortCost) :
    let slice := fun r => allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)
    let keep := fun r i => Real.exp (slice r) ≤ side i
    (∀ r i, keep r i → Real.exp (slice r) ≤ side i) ∧
      (∀ r i, ¬keep r i → side i ≤ Real.exp (slice r)) ∧
      (∀ r i, keep r i → initialLong i) := by
  intro slice keep
  refine ⟨fun _ _ hi => hi, ?_, ?_⟩
  · intro r i hi
    exact (lt_of_not_ge hi).le
  · intro r
    exact allocatedCandidateStage_keep_subset_initialLong side initialLong (keep r)
      s m Cprimitive scheduleExponent r hx hshortCost hshort (fun _ hi => hi)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    {D : RationalFilteredNilmanifold L s d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem expLongAxes_subset_keep {threshold : ℝ} (hcost : cost < threshold)
    (z : P.productive) (i : LayerSamplerVariables G I n B)
    (hi : Real.exp threshold ≤ (A.sides i : ℝ)) : (P.chart z).keep i := by
  by_contra hn
  have hupper := P.frozen_side z ⟨i, hn⟩
  have hlower := (Real.exp_lt_exp.mpr hcost).trans_le hi
  exact (not_lt_of_ge hupper) hlower

theorem exists_common_scalar_long_axis [Nonempty G] {threshold : ℝ}
    (hcost : cost < threshold) (hscale : Real.exp threshold ≤ (S.value : ℝ)) :
    ∃ i : LayerSamplerVariables G I n B,
      Real.exp threshold ≤ (A.sides i : ℝ) ∧ ∀ z : P.productive, (P.chart z).keep i := by
  let i : LayerSamplerVariables G I n B := Sum.inl (Classical.arbitrary G)
  have hi : Real.exp threshold ≤ (A.sides i : ℝ) := hscale
  exact ⟨i, hi, fun z => P.expLongAxes_subset_keep hcost z i hi⟩

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in

theorem expLongAxes_nonempty [Nonempty G] {threshold : ℝ}
    (hscale : Real.exp threshold ≤ (S.value : ℝ)) :
    Nonempty {i : LayerSamplerVariables G I n B // Real.exp threshold ≤ (A.sides i : ℝ)} := by
  exact ⟨⟨Sum.inl (Classical.arbitrary G), hscale⟩⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer allocatedFrozenCurrentGradeResetConstant

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {cost massThreshold scoreThreshold : ℝ}
    {P0 : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keepOld : P0.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P0.AxisFreezing keepOld shortCost)
    (commonKeep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : freezing.problem.productive,
      (freezing.problem.chart z).keep = commonKeep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // commonKeep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => freezing.problem.withKeep commonKeep hkeep

noncomputable def historyStageData_of_original_factors
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Cprimitive : ℕ) (x b Bstage Rrank : ℝ) (C : ℕ)
    (hx : 0 ≤ x) (hxb : x ≤ b) (hBstage : Bstage ≤ b)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : (Fintype.card χ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hη : (Fintype.card η : ℝ) ≤ x)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hOriginal : ∀ z : P0.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (P0.chart z).Variables => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (P0.candidate z).orbit))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pTest sourceNative α : ℝ)
    (hsourceNative : 0 ≤ sourceNative)
    (hkept : ∀ i, commonKeep i → Real.exp (allocatedCandidateStageSlice s m Cprimitive b) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬commonKeep i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive b))
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive b) pTest sourceNative α)
    (hNmajor : ∀ i, Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := freezing.problem) (keep := commonKeep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage
        ((allocatedCandidateForwardControlInput s (Fintype.card η) b +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (allocatedCandidateNativeMajorBudget
          (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
          (allocatedCandidateStageBase s m Cprimitive b)) Rrank C := by
  exact freezing.problem.historyStageData_of_prefix_bounds
    commonKeep hkeep bD ω hD bF ν hF hφ W eQ r hr
    Cprimitive x b Bstage Rrank C hx hxb hBstage
    cost hcost (fun z => freezing.withKeep_slice_dense commonKeep hkeep z)
    HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp
    hqNative hentries hsource htarget hκ hχ hη htags hsampler hJ
    hbracket vg hspan hvg hθ
    (fun z => freezing.withKeep_nativeFactors commonKeep hkeep bD ω hD qNative l W z
      (hOriginal z))
    hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    pTest sourceNative α hsourceNative hkept hfrozen hTest hα hdirect hNmajor hRrank hrank

end AllocatedExternalCandidateProblem.AxisFreezing
end Erdos3.VectorPolynomial

end

end OAI
