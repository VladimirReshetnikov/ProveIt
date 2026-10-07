import OAI.Combinatorics.Progressions.Probability.AllocatedConditionalSampledError

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
variable [NeZero q]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "laws" => allocatedWholeGridJetPMF B U b hR hσ S x rows y₀
local notation "residue" => fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q

variable (CM Cf : ℝ≥0) (hCM : 1 ≤ (CM : ℝ)) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x rows j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)

local notation "amplitude" => Real.toNNReal (coefficientDeckPeriodCap O Q q) *
  CM ^ Fintype.card (LayerSamplerAxis I n) * Cf

include hCM hfb hm in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] in
theorem allocatedWholeMaskedProfile_le_probability_majorant
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U O) :
    |allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y| ≤
      allocatedProbabilityMajorant B U b S o laws 1 amplitude d y := by
  let windows : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val) := fun _ => ∅
  have hW : ∀ a : {a // grid a}, False → (windows a).Nonempty := by
    intro a ha
    exact ha.elim
  have hweight : allocatedGridWindowWeight B U b S O (fun _ => False) windows laws =
      allocatedGridJetDensity B U b hR hσ S x (principalAxisRestrict grid y₀)
        (principalAxisRestrict (fun a => ¬grid a) y₀) rows := by
    funext z
    simp only [allocatedGridWindowWeight, allocatedGridWindowFactor, ↓reduceIte,
      allocatedWholeGridJetPMF_toReal, allocatedGridJetDensity]
  have hprob : allocatedGridWindowPMF B U b S O (fun _ => False) windows laws hW = laws := by
    funext a
    simp only [allocatedGridWindowPMF, ↓reduceDIte]
  have hF := allocatedLongProfileDensity_period_bound (Q := Q) B U b S x rows q residue
    (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)
    d q hperiod CM Cf hCM hm f hfb
  have h := allocatedGridlessWindow_le_probability_majorant B U b S x
    (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)
    rows hb o bW d (fun _ => False) windows laws hW
    (allocatedLongProfileDensity B U b S x rows q residue f)
    1 zero_le_one 1 amplitude (by simp) hF C V hC hV y
  rw [allocatedWholeMaskedCoveredProfile_grid_multiplier]
  simpa only [one_mul, hweight, hprob, allocatedWholeMaskedGridlessProfile] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
variable [NeZero q]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "laws" => allocatedWholeGridJetPMF B U b hR hσ S x rows y₀
local notation "residue" => fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q

variable (CM Cf : ℝ≥0) (hCM : 1 ≤ (CM : ℝ)) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x rows j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)

local notation "amplitude" => Real.toNNReal (coefficientDeckPeriodCap O Q q) *
  CM ^ Fintype.card (LayerSamplerAxis I n) * Cf

include hCM hfb hm in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] in
theorem allocatedWholeMaskedProfile_uniform_cap
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U O) :
    |allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y| ≤
      allocatedErrorKernelCap B U b S (O := O) 1 amplitude V := by
  exact (allocatedWholeMaskedProfile_le_probability_majorant B U b hR hσ S x rows hb o bW d q y₀ f
    CM Cf hCM hfb hm hperiod C V hC hV y).trans
    ((allocatedProbabilityTorusKernel_bounds B U b S o laws 1 amplitude C V hC hV).1
      (coveredJetAmbientTorus U d y)).2

end Erdos3.VectorPolynomial

namespace Erdos3

theorem finiteMeanModel_norm_le_of_uniform_approximation
    {Y Z : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (profile : Y → Z → ℝ) (model : Z → ℂ) {C ε : ℝ}
    (hprofile : ∀ y z, |profile y z| ≤ C)
    (happrox : ∀ z, ‖(law.mean (fun y => profile y z) : ℂ) - model z‖ ≤ ε)
    (hε : ε ≤ 1) (z : Z) : ‖model z‖ ≤ C + 1 := by
  have hmean : ‖(law.mean (fun y => profile y z) : ℂ)‖ ≤ C := by
    rw [← law.complexMean_ofReal]
    have hpoint (y : Y) : ‖(profile y z : ℂ)‖ ≤ C := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hprofile y z
    exact (law.norm_complexMean_le_mean_norm _).trans
      ((law.mean_mono hpoint).trans_eq (law.mean_const C))
  have ht : ‖model z‖ ≤ ‖model z - (law.mean (fun y => profile y z) : ℂ)‖ +
      ‖(law.mean (fun y => profile y z) : ℂ)‖ := norm_le_norm_sub_add _ _
  rw [norm_sub_rev] at ht
  linarith [happrox z]

end Erdos3

end

end OAI
