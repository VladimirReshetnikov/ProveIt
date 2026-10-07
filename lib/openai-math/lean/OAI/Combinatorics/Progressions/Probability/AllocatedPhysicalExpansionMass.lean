import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem allocatedFiniteModelPhysicalCoefficientMass_le
    {A : ℝ} (hA : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤ A)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)) :
    (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ∑ k, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k‖) ≤
      (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * A *
        ((2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) := by
  rw [finiteNestedSiteExpansion_mass]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_pow, htwo]
  have hA0 : 0 ≤ A := (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))).trans hA
  exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity))
    (coverSiteCoefficient_bound e he) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (by positivity) hA0)

include hb bW in

theorem allocatedFiniteModelPhysicalCoefficientMass_le_exp
    {M F A Pper Op : ℝ} (hM : 0 ≤ M)
    (hpref : ‖inverseNormalizer‖ *
      (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) ≤ Real.exp F)
    (hperiod : (period : ℝ) ≤ Real.exp Pper)
    (hA : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
      ‖inverseNormalizer‖ *
        ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
          Fintype.card (Finset (Fin dim)) *
          (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * Real.exp A))
    {Nt V Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Real.exp Op) Lg (Hs a)) :
    (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ∑ k, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k‖) ≤
      Real.exp (2 * Fintype.card (Finset (Fin dim)) + F +
        Fintype.card (Finset (Fin dim)) * ((∑ j, Fintype.card (J j) : ℕ) * Pper) + A +
        Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Op) := by
  let sites := Fintype.card (Finset (Fin dim))
  let labelLog : ℝ := sites * ((∑ j, Fintype.card (J j) : ℕ) * Pper)
  have hlabels := allocatedResidueLabels_le_exp (S := Finset (Fin dim)) U b hb bW period hperiod
  have hlong : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
      Real.exp (F + labelLog + A) := by
    apply hA.trans
    calc
      _ = (‖inverseNormalizer‖ *
          (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period)) *
          ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ sites * Real.exp A) := by ring
      _ ≤ Real.exp F * (Real.exp labelLog * Real.exp A) :=
        mul_le_mul hpref (mul_le_mul_of_nonneg_right hlabels (Real.exp_nonneg _))
          (by positivity) ((mul_nonneg (norm_nonneg _)
            (mul_nonneg (pow_nonneg hM _) (coefficientDeckPeriodCap_nonneg rowTypes E period))).trans hpref)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, add_assoc]
  have htwo : (2 : ℝ) ^ sites ≤ Real.exp sites := by
    rw [show (sites : ℝ) = sites * (1 : ℝ) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
  apply (allocatedFiniteModelPhysicalCoefficientMass_le B U b S x y₀ q d period e a hlong he).trans
  simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  calc
    _ ≤ (Real.exp sites * Real.exp (F + labelLog + A)) *
        (Real.exp sites * Real.exp (Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Op)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _))
        (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)) (by positivity) (by positivity)
    _ = _ := by simp only [← Real.exp_add]; congr 1; dsimp [sites, labelLog]; ring

end Erdos3.VectorPolynomial

end

end OAI
