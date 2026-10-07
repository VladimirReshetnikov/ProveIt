/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.NativeTwistedSliceBudget
import OAI.Combinatorics.Progressions.Fourier.AllocatedRecoveredTagTorusVariation
import OAI.Combinatorics.Progressions.Geometry.NarrowSpatialSiteVariation
import OAI.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop
import OAI.Combinatorics.Progressions.Probability.AllocatedRecoveredChartMass

namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_polynomial_variation
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (x y : LayerSamplerVariables G I n B → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ k, |x k| ≤ layerSamplerBox B U b S k)
    (hy : ∀ k, |y k| ≤ layerSamplerBox B U b S k)
    (hxy : ∀ k, |x k - y k| ≤ layerSamplerBox B U b S k * δ) (i : J j) :
    |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x i -
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 y i| ≤
      (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) * δ := by
  rw [← mixedLiftPolynomial_eval, ← mixedLiftPolynomial_eval]
  apply abs_eval_sub_eval_normalized_mass_bound _ _
    (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)) x y
    (allocatedLayerSupported_normalized_mass_uniform B U b o hR hσ S hσ1 C hC hchart
      hsmall j a ha i) hδ hx hy hxy
  exact (mixedLiftPolynomial_degree (euclideanSubspace (U j)) (b j) (o j) Subtype.val
    a (fun d => d.property) i).trans (by omega)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist
open scoped NNReal

variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem eval_sub_eval_of_component_dist
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u v : X → ℤ) {ε : ℝ}
    (hres : (fun i => (u i : ZMod W.modulus)) = (fun i => (v i : ZMod W.modulus)))
    (hspatial : dist (fun i => (u i : ℝ) / N i) (fun i => (v i : ℝ) / N i) ≤ ε)
    (htag : dist (physicalGridFactorInput W.cover poly (fun i => (u i : ℝ)))
      (physicalGridFactorInput W.cover poly (fun i => (v i : ℝ))) ≤ ε) :
    ‖W.eval N poly u - W.eval N poly v‖ ≤ (L : ℝ) * ε := by
  have hdist := W.smooth_lipschitz.dist_le_mul
    (fun i => (u i : ℝ) / N i, physicalGridFactorInput W.cover poly (fun i => (u i : ℝ)))
    (fun i => (v i : ℝ) / N i, physicalGridFactorInput W.cover poly (fun i => (v i : ℝ)))
  have hbound : ‖W.smooth (fun i => (u i : ℝ) / N i,
      physicalGridFactorInput W.cover poly (fun i => (u i : ℝ))) -
      W.smooth (fun i => (v i : ℝ) / N i,
      physicalGridFactorInput W.cover poly (fun i => (v i : ℝ)))‖ ≤ (L : ℝ) * ε := by
    rw [dist_eq_norm, Prod.dist_eq] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_left (max_le hspatial htag) L.coe_nonneg)
  simp only [eval, hres, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right (W.mask_bound _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hbound)

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold BooleanCubeKernel
open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

theorem exists_native_twist_variation_slice_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {K : Type*}
      [Fintype K] [DecidableEq K] [Nonempty K]
      {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (_hq : 0 < q)
      (hlen : ∀ k, 0 < S.length k) {p : ℝ} (_hp : 0 ≤ p)
      (_hS : ∀ k, Real.exp (-p) * (P k : ℝ) ≤ S.length k)
      (_hP : ∀ k, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P k : ℝ))
      {M : ℕ} (_hM : 0 < M) (_hperiod : (M : ℝ) ≤ Real.exp p)
      (twist : integerBox P → ℂ) (_htwist : ∀ t, ‖twist t‖ ≤ 1)
      {variation : ℝ} (_hvariation_nonneg : 0 ≤ variation)
      (_hvariation_bound : variation ≤ Real.exp p)
      (_hvariation : ∀ u v : integerBox P,
        (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
        ∀ δ : ℝ, 0 ≤ δ →
        (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤ δ) →
        ‖twist u - twist v‖ ≤ variation * δ)
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      (V : D.Niltest (fun _ : K => 1)) (W : E.Niltest (fun _ : K => 1))
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
      (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (_hK : (Fintype.card K : ℝ) ≤ p)
      (_hbias : Real.exp (-p) ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
        star (twist t) *
          (V.eval t.val * W.eval t.val))‖),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤
          (p + 2 + C) ^ C) ∧
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η θ) (fun k => (P k : ℝ))
          (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
          ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_pair_affine_cell_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro K _ _ _ P q S hq hlen p hp hS hP M hM hperiod twist htwist
    variation hvariation_nonneg hvariation_bound hvariation
    LG MG _ _ _ _ d e _ _ _ _ _ _ _ _
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  have hbudget : 0 ≤ (p + 2 + C) ^ C := by positivity
  have hPfreeze (k : K) : Real.exp (p + (3 * (2 * p + 2) + 16)) ≤ (P k : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans (hP k)
  have hperiod' : ((M : ℕ) : ℝ) ≤ Real.exp (2 * p + 2) :=
    hperiod.trans (Real.exp_le_exp.mpr (by linarith))
  have hfreeze : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * (2 * p + 2))) / 4)) →
      ‖twist u - twist v‖ ≤ variation *
        (2 * (Real.exp (-(2 * (2 * p + 2))) / 4)) := by
    intro u v hres hnear
    exact hvariation u v hres _ (by positivity) hnear
  obtain ⟨T, hTq, hTlen, hTside, hcorr⟩ :=
    NormalizedPolynomialTwist.exists_niltest_pair_correlation_subrectangle_of_variation
      S hq hlen (by linarith : 0 ≤ 2 * p + 2) hS hPfreeze hM hperiod'
      twist htwist hfreeze V W hV hWnorm (Real.exp_pos (-p)) hbias
  have herror : Real.exp p *
      (variation * (2 * (Real.exp (-(2 * (2 * p + 2))) / 4))) ≤
      Real.exp (-p) / 4 := by
    convert nativeTwistedSlice_freezing_error hp hvariation_nonneg hvariation_bound
      (by norm_num : (0 : ℝ) ≤ 1) (le_refl (1 : ℝ)) using 1
    ring
  have hbias' : Real.exp (-(p + 2)) ≤ ‖𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
      V.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k) *
        W.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k)‖ :=
    (nativeTwistedSlice_bias_precision p).trans (by linarith)
  have hTside' (k : K) : Real.exp (-(7 * p + 22)) * (P k : ℝ) ≤ T.length k := by
    simpa only [show p + (3 * (2 * p + 2) + 16) = 7 * p + 22 by ring] using hTside k
  have hlong (k : K) : Real.exp ((p + 2 + C) ^ C) ≤ (T.length k : ℝ) := by
    calc
      _ = Real.exp (-(7 * p + 22)) * Real.exp ((p + 2 + C) ^ C + 7 * p + 22) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(7 * p + 22)) * (P k : ℝ) :=
        mul_le_mul_of_nonneg_left (hP k) (Real.exp_nonneg _)
      _ ≤ _ := hTside' k
  have hPpos (k : K) : (0 : ℝ) < P k := (Real.exp_pos _).trans_le (hP k)
  have hphysical (k : K) : Real.exp (-(7 * p + 22)) *
      ((P k : ℝ) / (q * M : ℕ)) ≤ T.length k := by
    apply le_trans _ (hTside' k)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact div_le_self (hPpos k).le (by exact_mod_cast hTq)
  obtain ⟨k₀⟩ := ‹Nonempty K›
  have htwo : 2 ≤ S.length k₀ := by
    have he := S.length_large_of_cost hS hPfreeze k₀
    have ht := Real.add_one_le_exp (3 * (2 * p + 2) + 16)
    have : (2 : ℝ) ≤ S.length k₀ := by linarith
    exact_mod_cast this
  have hstride : ((q * M : ℕ) : ℝ) ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (2 * Real.exp p) * Real.exp p :=
        mul_le_mul (S.stride_le_twice_exp_cost k₀ htwo (hS k₀)) hperiod
          (Nat.cast_nonneg _) (by positivity)
      _ ≤ Real.exp 1 * (Real.exp p * Real.exp p) := by
        have := Real.add_one_le_exp 1
        nlinarith [mul_pos (Real.exp_pos p) (Real.exp_pos p)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp' : p ≤ p + 2 := by linarith
  obtain ⟨b, ω, hF, hb, hf⟩ := hstep D E V W (by linarith : 2 ≤ p + 2)
    (by linarith : 0 ≤ 7 * p + 22) (by linarith : 0 ≤ 2 * p + 1)
    (hV.mono hp') (hW.mono hp') _ hTq hstride (fun k => (T.start k : ℤ)) η θ
    (fun i => (hηheight i).trans hp') (fun i => (hθheight i).trans hp') hη hθ
    0 T.length (fun k => (P k : ℝ)) hTlen hPpos (hK.trans hp') hlong hphysical hbias'
  refine ⟨b, ω, hF, hb, ?_⟩
  convert hf using 1; ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.twist_variation
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (x y : LayerSamplerVariables G I n B → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ k, |(x k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hy : ∀ k, |(y k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hxy : ∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ layerSamplerBox B U b S k * δ)
    (hmod : ∀ k, (x k : ZMod W.modulus) = (y k : ZMod W.modulus))
    (hcover : ∀ k, (x k : ZMod W.cover) = (y k : ZMod W.cover)) :
    ‖W.eval N poly (jointIntegerPhysicalSite x (a, v)) -
      W.eval N poly (jointIntegerPhysicalSite y (a, v))‖ ≤
      (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) * δ := by
  let D : ℝ := (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hε : 0 ≤ D * δ := mul_nonneg hD hδ
  have htag := h.integerFullChart_torus_dist B U b hb o S hR hσ poly hm hp c a v sample read
    W.cover W.cover_pos x y hcover hε
    (fun j i => allocatedLayerSupported_polynomial_variation B U b o hR hσ S hσ1 C hC hchart
      hsmall j (sample j) (h.2.2.1 j).2 _ _ hδ hx hy hxy i)
  have htag' : dist (physicalGridFactorInput W.cover poly (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)))
      (physicalGridFactorInput W.cover poly (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))) ≤ (1 + D) * δ := by
    apply htag.trans
    have hc : (1 : ℝ) ≤ W.cover := by exact_mod_cast W.cover_pos
    exact (div_le_self hε hc).trans (by nlinarith)
  have hspatial := narrowSpatial_jointPhysicalSite_normalized_dist_le_cell
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hτ1 hξ N hN
    (layerSamplerBox B U b S)
    (fun k => (by norm_num : (0 : ℝ) ≤ 1).trans (layerSamplerBox_one_le B U b S k))
    (layerSamplerBox_sum_le_zero_root_budget B U b S) a v hv x y hδ hxy
  have hres : (fun z => (jointIntegerPhysicalSite x (a, v) z : ZMod W.modulus)) =
      (fun z => (jointIntegerPhysicalSite y (a, v) z : ZMod W.modulus)) := by
    funext z
    simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
      Int.cast_add, Int.cast_sum, Int.cast_mul, hmod]
  have hout := W.eval_sub_eval_of_component_dist N poly _ _ hres
    (hspatial.trans (show δ ≤ (1 + D) * δ by nlinarith)) htag'
  exact hout.trans_eq (by dsimp [D]; ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.frozen_twist_variation
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val)
    (x y : integerBox (fun i : {i // keep i} =>
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val))
    (hres : ∀ i, (x.val i : ZMod (W.modulus * W.cover)) = (y.val i : ZMod (W.modulus * W.cover)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ i, |(x.val i : ℝ) /
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val : ℕ) : ℝ) -
      (y.val i : ℝ) /
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val : ℕ) : ℝ)| ≤ δ) :
    ‖W.eval N poly (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) x.val) -
      W.eval N poly (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) y.val)‖ ≤
      (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) * δ := by
  classical
  let xx := finiteSplitPoint keep x.val fixed
  let yy := finiteSplitPoint keep y.val fixed
  have hT : ∀ i, 0 < layerSamplerBox B U b S i :=
    fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S i)
  have hxy : ∀ i, |(xx i : ℝ) - (yy i : ℝ)| ≤ layerSamplerBox B U b S i * δ := by
    intro i
    by_cases hi : keep i
    · have hc := hcell ⟨i, hi⟩
      rw [← allocatedParameterBox_side_eq B U b S i, ← sub_div, abs_div,
        abs_of_pos (hT i)] at hc
      simpa only [xx, yy, finiteSplitPoint, dite_eq_left hi, mul_comm] using
        (div_le_iff₀ (hT i)).mp hc
    · simp only [xx, yy, finiteSplitPoint, dite_eq_right hi, sub_self, abs_zero]
      exact mul_nonneg (hT i).le hδ
  have hmod : ∀ i, (xx i : ZMod W.modulus) = (yy i : ZMod W.modulus) := by
    intro i
    by_cases hi : keep i
    · have hc := congrArg (ZMod.castHom (dvd_mul_right W.modulus W.cover) (ZMod W.modulus))
        (hres ⟨i, hi⟩)
      simpa only [map_intCast, xx, yy, finiteSplitPoint, dite_eq_left hi] using hc
    · simp only [xx, yy, finiteSplitPoint, dite_eq_right hi]
  have hcover : ∀ i, (xx i : ZMod W.cover) = (yy i : ZMod W.cover) := by
    intro i
    by_cases hi : keep i
    · have hc := congrArg (ZMod.castHom (dvd_mul_left W.cover W.modulus) (ZMod W.cover))
        (hres ⟨i, hi⟩)
      simpa only [map_intCast, xx, yy, finiteSplitPoint, dite_eq_left hi] using hc
    · simp only [xx, yy, finiteSplitPoint, dite_eq_right hi]
  rw [allocatedFrozenIntegerFullChart_spatial, allocatedFrozenIntegerFullChart_spatial]
  exact h.twist_variation B U b hb o S hR hσ poly hm hp c a N hN hτ hτ1 hξ v hv sample read
    hσ1 C hC hchart hsmall W xx yy hδ
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed x.val x.property)
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed y.val y.property)
    hxy hmod hcover

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

theorem exists_allocated_frozen_tagged_twist_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I Deck J : Fin m → Type*}
      [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      (hbtag : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j)))
      (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U btag R σ)
      (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j)
      (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (_hN : ∀ x, 0 < N x)
      {τ ξ : ℝ} (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hξ : ξ ≤ 1)
      (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
      (_hv : v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U btag S (fun _ => 0)) τ ξ N) 1)
      (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
      (_hread : AllocatedCenteredFramedRecoveredSampleAt B U btag hbtag o S hR hσ poly hm c a v sample read)
      (_hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (_hCgeo : ∀ j, 0 ≤ Cgeo j)
      (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
      (_hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      {p : ℝ} (_hp : 0 ≤ p)
      (_hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
      (_hvariationBound : (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
      (keep : LayerSamplerVariables G I n B → Prop) [Nonempty {i // keep i}]
      (fixed : {i // ¬keep i} → ℤ)
      (_hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U btag S) i.val),
      let P := fun i : {i // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U btag S) i.val
      let β := allocatedFrozenIntegerFullChart B U btag o poly hm c a v sample keep fixed
      ∀ {q : ℕ} (Q : ResidueBoxSlice P q) (_hq : 0 < q)
        (hlen : ∀ i, 0 < Q.length i)
        (_hQ : ∀ i, Real.exp (-p) * (P i : ℝ) ≤ Q.length i)
        (_hP : ∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P i : ℝ))
        {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
        {d e : ℕ}
        [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
        [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
        (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
        (V : D.Niltest (fun _ : {i // keep i} => 1))
        (W : E.Niltest (fun _ : {i // keep i} => 1))
        (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
        (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
        (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
        (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
        (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = CircleFourier.character
            ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
        (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = CircleFourier.character
            ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
        (_hK : (Fintype.card {i // keep i} : ℝ) ≤ p)
        (_hbias : Real.exp (-p) ≤ ‖(Q.fullSliceLaw hlen).complexMean (fun t =>
          star (twist.eval N poly (integerSampledSpatial β t.val)) *
            (V.eval t.val * W.eval t.val))‖),
        ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
          (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
          (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
            Submodule.span ℚ (b '' {i | k ≤ ω i})),
          (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤
            (p + 2 + C) ^ C) ∧
          (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
            (pairFrequency η θ) (fun k => (P k : ℝ))
            (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
            ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_twist_variation_slice_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro m G X _ _ I Deck J _ _ n B _ U btag hbtag o R σ S hR hσ poly hm hpoly
    c a N hN τ ξ hτ hτ1 hξ v hv sample read hread hσ1 Cgeo hCgeo hchart hsmall
    periodCap coverCap L twist p hp hperiod hvariationBound keep _ fixed hfixed
  dsimp only
  intro q Q hq hlen hQ hP LG MG _ _ _ _ d e _ _ _ _ _ _ _ _
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  have hsmallOne : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 :=
    fun j => (hsmall j).trans (by norm_num)
  apply hstep Q hq hlen hp hQ hP (mul_pos twist.modulus_pos twist.cover_pos)
    hperiod (fun t => twist.eval N poly (integerSampledSpatial
      (allocatedFrozenIntegerFullChart B U btag o poly hm c a v sample keep fixed) t.val))
    (fun _ => twist.norm_eval_le N poly _)
    (by positivity) hvariationBound ?_
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  intro x y hres δ hδ hcell
  exact hread.frozen_twist_variation B U btag hbtag o S hR hσ poly hm hpoly
    c a N hN hτ hτ1 hξ v hv sample read hσ1 Cgeo hCgeo hchart hsmallOne
    twist keep fixed hfixed x y hres hδ hcell

end Erdos3.VectorPolynomial

end

end OAI
