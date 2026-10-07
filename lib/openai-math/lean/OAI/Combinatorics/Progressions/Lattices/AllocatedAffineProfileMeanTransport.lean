import OAI.Combinatorics.Progressions.Geometry.AllocatedSlicedRowIdealSupport

namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem activeScaledSlicedIdeal_coordinate_support
    {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
    (R : (Σ d, O d) → ℝ) (hR : ∀ q, 0 < R q) {degree : ℕ} (hd : ∀ d, h d ≤ degree)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (v : (Σ d, O d) → ℝ)
    (hv : diagonalImageDensity R (activeAveragedSlicedProfileIdeal (G := G) (B := B)
      Z h P sets ρ center width) v ≠ 0) (q : Σ d, O d) :
    |v q| ≤ (partitionedIdealRadius α degree + 1) * R q := by
  have hn : ‖fun q => v q / R q‖ ≤ partitionedIdealRadius α degree + 1 := by
    by_contra hh
    apply hv
    unfold diagonalImageDensity
    rw [activeAveragedSlicedProfileIdeal_zero_outside (G := G) (B := B) Z h P sets
      hd ρ hρ hρ1 center width hw _ (lt_of_not_ge hh), mul_zero]
  have hc := (norm_le_pi_norm (fun q => v q / R q) q).trans hn
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hR q)] at hc
  exact (div_le_iff₀ (hR q)).mp hc

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR in
 theorem allocatedAffineIdeal_profile_integrable
    {P : ℝ} (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (center width : input → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ Cmask) :
    Integrable (allocatedLongProfileDensity B U basis S x rows modulus residue
      (diagonalImageDensity (fun o : output => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) grid (fun a => rows a.val.1) ρ center width)))
      (allocatedLongJetReference B U basis S O) := by
  have hRI (o : output) : |(R o.1.val.1)⁻¹| ≤ Real.exp P := by
    rw [abs_of_pos (inv_pos.mpr (hR o.1.val.1))]
    exact hRi _
  have hb := activeScaledSlicedIdeal_bounds (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => rows a.val.1) (fun o : output => R o.1.val.1)
    (C := ⟨Real.exp P, Real.exp_nonneg _⟩)
    hRI
    ρ hρ center width
  apply allocatedLongProfileDensity_integrable B U basis S x rows modulus residue
    _ hb.2.continuous.measurable
    (T := Real.exp P * (partitionedIdealRadius α m + 1))
    (mul_nonneg (Real.exp_nonneg _) (by have := partitionedIdealRadius_nonneg α m; linarith))
    ?_ hCmask (by positivity) hb.1 hmask
  exact activeScaledSlicedIdeal_zero_outside (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => rows a.val.1) (fun o : output => R o.1.val.1)
    (fun o => (hR o.1.val.1).ne') (Real.exp_nonneg P)
    (fun o => by simpa only [abs_of_pos (hR o.1.val.1)] using hRP o.1.val.1)
    (fun a => Nat.succ_le_of_lt a.1.isLt) ρ hρ hρone center width hw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
variable (hR : ∀ j, 0 < R j)
variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jetRows" => O
local notation "ideal" => diagonalImageDensity (fun q : Jet => R (Sigma.fst (Subtype.val (Sigma.fst q))))
  (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => rows (Sigma.fst (Subtype.val a))) ρ center width)
local notation "reference" => allocatedLongJetReference B U basis S jetRows

omit [∀ a, DecidableEq (B a)] in
theorem allocatedAffineCoveredProfile_test_integral
    [∀ a, DecidableEq (B a)]
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {P : ℝ}
    (hRbound : ∀ j, R j ≤ Real.exp P) (hInv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ Cmask)
    (hσ1 : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (F : EuclideanJetLayers U jetRows → ℂ) (hF : Measurable F)
    {CF : ℝ} (hFb : ∀ z, ‖F z‖ ≤ CF) :
    let f := allocatedLongProfileDensity B U basis S x rows modulus residue ideal
    (∫ a₀, ∫ z, (f z : ℂ) * allocatedCoveredFixedTest B U basis S x u v₀ rows
      Q hb o bW d (fun p => F p.2) a₀ z ∂reference ∂allocatedFrozenCoefficientSource B U basis hR hσ S) =
      ∫ y, (allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ rows hb o bW d
        (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) f y : ℂ) * F y
          ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) := by
  intro f
  have hIm : Measurable ideal := diagonalImageDensity_measurable
    (fun q : Jet => R q.1.val.1) (fun q => (hR q.1.val.1).ne')
    (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a => rows a.val.1) ρ hρ center width).2.1.continuous.measurable
  have hfm : Measurable f := allocatedLongProfileDensity_measurable B U basis S x rows
    modulus residue ideal hIm
  have hfi : Integrable f reference := allocatedAffineIdeal_profile_integrable B U basis hR S x rows
    hRbound hInv ρ hρ hρ1 center width hw modulus residue hCmask hmask
  have hf0 : ∀ z, 0 ≤ f z := allocatedLongProfileDensity_nonneg B U basis S x rows
    modulus residue ideal
      (diagonalImageDensity_nonneg _ (fun v => (activeAveragedSlicedProfileIdeal_spec
        (G := G) (B := B) (G × Option α) (layerSamplerDegree I n) grid
        (fun a => rows a.val.1) ρ hρ center width).1 v |>.1))
      (fun j z => (hmask j z).1)
  apply allocatedCoveredProfile_test_integral B U basis hR hσ S x u v₀ rows Q hb o bW d ν
    (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) f hfm hfi hf0 ?_ F hF hFb
  intro z hz
  by_contra hn
  apply hz
  apply allocatedGridlessWeightedKernel_quarter_support B U basis hR hσ S x u v₀ rows Q o d
    hσ1 T (fun j => (by have := partitionedIdealRadius_nonneg α m; have := hT j; linarith : 0 ≤ T j)) hsource C hC hchart hbudget f ?_ z hn
  intro w hwne a₀ t
  have hi := allocatedLongProfileDensity_ne_zero B U basis S x rows modulus residue ideal w hwne
  exact (activeScaledSlicedIdeal_coordinate_support (G := G) (Z := G × Option α) (B := B)
    (layerSamplerDegree I n) grid (fun a => rows a.val.1) (fun q : Jet => R q.1.val.1)
    (fun q => hR q.1.val.1) (fun a => Nat.succ_le_of_lt a.1.isLt)
    ρ hρ hρ1 center width hw _ hi ⟨a₀, t⟩).trans
      (mul_le_mul_of_nonneg_right (hT _) (hR _).le)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
variable (hR : ∀ j, 0 < R j)
variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jetRows" => O
local notation "ideal" => diagonalImageDensity (fun q : Jet => R (Sigma.fst (Subtype.val (Sigma.fst q))))
  (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => rows (Sigma.fst (Subtype.val a))) ρ center width)
local notation "reference" => allocatedLongJetReference B U basis S jetRows

theorem allocatedAffineCoveredProfile_mean_test_integral
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {P : ℝ}
    (hRbound : ∀ j, R j ≤ Real.exp P) (hInv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (modulus : ℕ)
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
      (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)))
    (residue : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
      (allocatedPrincipalSides B U basis S) → ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ u j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue u j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue u j) z ≤ Cmask)
    (hσ1 : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (F : EuclideanJetLayers U jetRows → ℂ) (hF : Measurable F)
    {CF : ℝ} (hFb : ∀ z, ‖F z‖ ≤ CF) :

    let f := fun u => allocatedLongProfileDensity B U basis S x rows modulus (residue u) ideal
    weights.complexMean (fun u => ∫ a₀, ∫ z, (f u z : ℂ) *
      allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d
        (fun p => F p.2) a₀ z ∂reference ∂allocatedFrozenCoefficientSource B U basis hR hσ S) =
      ∫ y, (weights.mean (fun u => allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ rows
        hb o bW d (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) (f u) y) : ℂ) * F y
          ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) := by
  intro f
  let profile := fun u => allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ rows
    hb o bW d (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) (f u)
  have hi u : Integrable (fun y => (profile u y : ℂ) * F y)
      (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) := by
    have hIm : Measurable ideal := diagonalImageDensity_measurable
      (fun q : Jet => R q.1.val.1) (fun q => (hR q.1.val.1).ne')
      (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) ρ hρ center width).2.1.continuous.measurable
    have hfm : Measurable (f u) := allocatedLongProfileDensity_measurable B U basis S x rows
      modulus (residue u) ideal hIm
    have hfi : Integrable (f u) reference := allocatedAffineIdeal_profile_integrable B U basis hR S x rows
      hRbound hInv ρ hρ hρ1 center width hw modulus (residue u) hCmask (hmask u)
    exact (allocatedCoveredProfileDensity_integrable B U basis hR hσ S x u v₀ rows hb o bW d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
      (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) ν (f u) hfm hfi).ofReal.mul_bdd
        hF.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
  calc
    _ = weights.complexMean (fun u => ∫ y, (profile u y : ℂ) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) := by
      apply congrArg weights.complexMean
      funext u
      exact allocatedAffineCoveredProfile_test_integral B U basis S rows x u hR ρ center width hσ v₀ Q hb o bW d ν
        hρ hρ1 hw hRbound hInv modulus (residue u) hCmask (hmask u)
        hσ1 T hT hsource C hC hchart hbudget F hF hFb
    _ = ∫ y, weights.complexMean (fun u => (profile u y : ℂ) * F y)
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) :=
      (weights.integral_complexMean _ _ hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => weights.complexMean_ofReal_mul _ _)

end Erdos3.VectorPolynomial

end

end OAI
