/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison
import OAI.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension
import OAI.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
import OAI.Combinatorics.Progressions.Lattices.MixedCoveredIntegerReconstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

noncomputable def coefficientDeckPeriodCap {m : ℕ} (O B : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] (period : ℕ) : ℝ :=
  ∏ j, ∏ _i : B j, (period : ℝ) ^ Fintype.card (O j)

theorem coefficientDeckPeriodCap_nonneg {m : ℕ} (O B : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] (period : ℕ) :
    0 ≤ coefficientDeckPeriodCap O B period := by
  unfold coefficientDeckPeriodCap
  positivity

theorem coefficientDeckJetDensity_product {α K : Type*} [DecidableEq α] [Fintype K]
    {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (d : ℕ) [NeZero d] (r : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root D rows d r =
      ∏ j, ∏ i : B j, (d : ℝ) ^ Fintype.card (O j) *
        (((PMF.uniformOfFintype (BoundedCoefficientExponent K (j.val + 1) → ZMod d)).map
          (fun z => integerResidueMatrix
            (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ z)) (fun t => r j t i)).toReal := by
  have he : (coefficientDeckJetMap (B := B) root D rows d :
      CoefficientDeckResidues (K := K) B d → (∀ j, O j → B j → ZMod d)) =
      (fun x j t i => (integerResidueMatrix
        (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ
          (fun e => x j e i)) t) := by
    funext x j t i
    exact congrFun (coefficientDeckJetMap_coordinate root D rows d x j i) t
  have hc : (Fintype.card (∀ j, O j → B j → ZMod d) : ℝ) =
      ∏ j, ∏ _i : B j, (d : ℝ) ^ Fintype.card (O j) := by
    simp only [Fintype.card_pi, ZMod.card, Nat.cast_prod, Nat.cast_pow,
      Finset.prod_const, Finset.card_univ]
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  unfold coefficientDeckJetDensity
  rw [he, uniformPMF_transposed_images, hc]
  simp only [Finset.prod_mul_distrib]

theorem coefficientDeckJetDensity_period_bound {α K : Type*} [DecidableEq α] [Fintype K]
    {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (r : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root D rows d r ≤ coefficientDeckPeriodCap O B period := by
  have h := uniformResidueMatrix_family_density_bound
    (I := O) (J := fun j => BoundedCoefficientExponent K (j.val + 1)) (B := B)
    (fun j => boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d period hperiod r
  exact (coefficientDeckJetDensity_product root D rows d r).trans_le h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d]

noncomputable def coefficientDeckSmallPeriodDensity
    (r : ∀ j, O j → B j → ZMod period) : ℝ :=
  ∏ j, ∏ i : B j, uniformResidueSmallPeriodDensity
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d period (fun t => r j t i)

theorem coefficientDeckSmallPeriodDensity_apply [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (v : ∀ j, O j → B j → ℤ) :
    coefficientDeckSmallPeriodDensity root D rows d period (fun j t i => (v j t i : ZMod period)) =
      coefficientDeckJetDensity root D rows d (fun j t i => (v j t i : ZMod d)) := by
  rw [coefficientDeckJetDensity_product]
  unfold coefficientDeckSmallPeriodDensity
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  exact uniformResidueSmallPeriodDensity_apply
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d period (hperiod j) (fun t => v j t i)

theorem coefficientDeckSmallPeriodDensity_bounds [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (r : ∀ j, O j → B j → ZMod period) :
    0 ≤ coefficientDeckSmallPeriodDensity root D rows d period r ∧
      coefficientDeckSmallPeriodDensity root D rows d period r ≤ coefficientDeckPeriodCap O B period := by
  have hb (j : Fin m) (i : B j) := uniformResidueSmallPeriodDensity_bounds
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d period (hperiod j) (fun t => r j t i)
  constructor
  · exact Finset.prod_nonneg (fun j _ => Finset.prod_nonneg (fun i _ => (hb j i).1))
  · exact Finset.prod_le_prod₀
      (fun j _ => Finset.prod_nonneg (fun i _ => (hb j i).1))
      (fun j _ => Finset.prod_le_prod₀ (fun i _ => (hb j i).1) (fun i _ => (hb j i).2))

theorem coefficientDeckJetDensity_eq_of_period [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (v w : ∀ j, O j → B j → ℤ)
    (hvw : ∀ j t i, (v j t i : ZMod period) = (w j t i : ZMod period)) :
    coefficientDeckJetDensity root D rows d (fun j t i => (v j t i : ZMod d)) =
      coefficientDeckJetDensity root D rows d (fun j t i => (w j t i : ZMod d)) := by
  rw [← coefficientDeckSmallPeriodDensity_apply root D rows d period hperiod v,
    ← coefficientDeckSmallPeriodDensity_apply root D rows d period hperiod w]
  congr 1
  funext j t i
  exact hvw j t i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d] [NeZero period]

noncomputable def coefficientDeckSiteMask
    (r : Finset α → ∀ j, B j → ZMod period) : ℝ :=
  coefficientDeckSmallPeriodDensity root D rows d period (fun j t i =>
    (integerResidueMatrix (booleanJetExtractionMatrix (rows j)) period *ᵥ (fun s => r s j i)) t)

theorem coefficientDeckSiteMask_apply
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (v : Finset α → ∀ j, B j → ℤ) :
    coefficientDeckSiteMask root D rows d period (fun s j i => (v s j i : ZMod period)) =
      coefficientDeckJetDensity root D rows d
        (fun j t i => ((booleanCoefficient (fun s => v s j i) (rows j t) : ℤ) : ZMod d)) := by
  rw [← coefficientDeckSmallPeriodDensity_apply root D rows d period hperiod
    (fun j t i => booleanCoefficient (fun s => v s j i) (rows j t))]
  unfold coefficientDeckSiteMask
  congr 1
  funext j t i
  have h := congrFun (integerResidueMap_mulVec (booleanJetExtractionMatrix (rows j)) period
    (fun s => v s j i)) t
  simpa only [integerResidueMap, LinearMap.coe_mk, AddHom.coe_mk,
    booleanJetExtractionMatrix_mulVec] using h.symm

theorem coefficientDeckSiteMask_bounds
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (r : Finset α → ∀ j, B j → ZMod period) :
    0 ≤ coefficientDeckSiteMask root D rows d period r ∧
      coefficientDeckSiteMask root D rows d period r ≤ coefficientDeckPeriodCap O B period :=
  coefficientDeckSmallPeriodDensity_bounds root D rows d period hperiod _

theorem coefficientDeckSiteMask_expansion
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    {T V : Type*} [Fintype T] (lift : Finset α → V → ∀ j, B j → ℤ)
    (c : T → ℂ) (f : T → Finset α → V → ℂ) (u : Finset α → V) :
    (coefficientDeckJetDensity root D rows d
        (fun j t i => ((booleanCoefficient (fun s => lift s (u s) j i) (rows j t) : ℤ) : ZMod d)) : ℂ) *
      (∑ k, c k * ∏ s, f k s (u s)) =
    ∑ r : Finset α → ∀ j, B j → ZMod period, ∑ k,
      ((coefficientDeckSiteMask root D rows d period r : ℂ) * c k) *
        ∏ s, maskedSiteFactor (fun s v j i => (lift s v j i : ZMod period)) r f k s (u s) := by
  rw [maskedSiteExpansion_identity, coefficientDeckSiteMask_apply root D rows d period hperiod]

theorem coefficientDeckSiteMask_coefficient_sum
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    {T : Type*} [Fintype T] (c : T → ℂ) {C : ℝ} (hc : (∑ k, ‖c k‖) ≤ C) :
    (∑ r : Finset α → ∀ j, B j → ZMod period, ∑ k,
      ‖(coefficientDeckSiteMask root D rows d period r : ℂ) * c k‖) ≤
      (Fintype.card (∀ j, B j → ZMod period) : ℝ) ^ Fintype.card (Finset α) *
        coefficientDeckPeriodCap O B period * C := by
  apply maskedSiteExpansion_coefficient_sum _ c (coefficientDeckPeriodCap_nonneg O B period) _ hc
  intro r
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coefficientDeckSiteMask_bounds root D rows d period hperiod r).1]
  exact (coefficientDeckSiteMask_bounds root D rows d period hperiod r).2

theorem coefficientDeckSiteMask_reconstructed
    (hperiod : ∀ j : Fin m, integerScalarLattice (BoundedBooleanJet α (j.val + 1)) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1)
        (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)).mulVecLin.range)
    (z : ∀ j : Fin m, BoundedBooleanJet α (j.val + 1) → B j → ZMod d) :
    coefficientDeckSiteMask root D
      (fun j : Fin m => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) d period
      (fun s j i => ((∑ t, boundedBooleanReconstructionMatrix α (j.val + 1) s t • z j t i).val :
        ZMod period)) = coefficientDeckJetDensity root D
          (fun j : Fin m => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) d z := by
  let v : Finset α → ∀ j : Fin m, B j → ℤ := fun s j i =>
    ((∑ t, boundedBooleanReconstructionMatrix α (j.val + 1) s t • z j t i).val : ℤ)
  have hjet (j : Fin m) (t : BoundedBooleanJet α (j.val + 1)) (i : B j) :
      ((booleanCoefficient (fun s => v s j i) t.val : ℤ) : ZMod d) = z j t i := by
    rw [← booleanJetExtractionMatrix_mulVec
      (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α) (fun s => v s j i) t]
    change ((∑ s, booleanJetExtractionMatrix Subtype.val t s * v s j i : ℤ) : ZMod d) = _
    simp only [Int.cast_sum, Int.cast_mul, v, Int.cast_natCast, ZMod.natCast_zmod_val]
    simpa only [zsmul_eq_mul] using
      boundedBooleanReconstruction_zsmul_inverse (j.val + 1) (fun t => z j t i) t
  have h := coefficientDeckSiteMask_apply root D
    (fun j : Fin m => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) d period hperiod v
  simp only [hjet] at h
  simpa only [v, Int.cast_natCast] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

noncomputable def mixedCoveredBooleanSiteValue (d : ℕ)
    (z : MixedCoveredJetSource I jets Q n d) (s : Finset α) :
    MixedCoveredJetSource I (fun _ => Unit) Q n d :=
  mixedCoveredJetIntegerImage d
    (fun j (_ : Unit) => boundedBooleanReconstructionMatrix α (j.val + 1) s) z

omit [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)] in
theorem mixedCoveredBooleanSiteValue_mixed (d : ℕ)
    (z : MixedCoveredJetSource I jets Q n d) (s : Finset α) :
    (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredBooleanSiteValue d z s).1 j) ()) =
      mixedBooleanSiteValue z.1 s := rfl

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredBooleanSiteValue
    (y : EuclideanJetLayers U jets) (s : Finset α) : EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => ∑ r, boundedBooleanReconstructionMatrix α (j.val + 1) s r • y j r

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredBooleanSiteValue_chart (z : MixedCoveredJetSource I jets Q n d) (s : Finset α) :
    mixedCoveredJetChart U o b hb bW d (mixedCoveredBooleanSiteValue d z s) =
      coveredBooleanSiteValue U (mixedCoveredJetChart U o b hb bW d z) s := by
  funext j t
  exact mixedCoveredJetIntegerImage_chart U o b hb bW d
    (fun j (_ : Unit) => boundedBooleanReconstructionMatrix α (j.val + 1) s) z j t

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def rowRestrictedSiteMatrix (rows : Finset (Finset α)) :
    Matrix (Finset α) rows ℤ := fun s t => booleanReconstructionMatrix α s t.val

theorem integerBooleanSitesFromRows_eq_mulVec (rows : Finset (Finset α))
    (z : rows → ℤ) :
    integerBooleanSitesFromRows rows z = rowRestrictedSiteMatrix rows *ᵥ z := by
  funext s
  let F := fun t => booleanReconstructionMatrix α s t *
    (if ht : t ∈ rows then z ⟨t, ht⟩ else 0)
  have hsub : (∑ t ∈ rows, F t) = ∑ t : Finset α, F t := by
    apply Finset.sum_subset (Finset.subset_univ rows)
    intro t _ ht
    simp only [F, dite_eq_right ht, mul_zero]
  calc
    _ = ∑ t : Finset α, F t := rfl
    _ = ∑ t ∈ rows, F t := hsub.symm
    _ = ∑ t : rows, F t := Finset.sum_subtype rows (by simp) F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [F, dite_eq_left t.property, rowRestrictedSiteMatrix]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

noncomputable def mixedCoveredRowsSiteValue (d : ℕ)
    (z : MixedCoveredJetSource I rows E n d) (s : Finset α) :
    MixedCoveredJetSource I (fun _ => Unit) E n d :=
  mixedCoveredJetIntegerImage d (fun j (_ : Unit) => rowRestrictedSiteMatrix (rowSets j) s) z

omit [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)] in
theorem mixedCoveredRowsSiteValue_integer (d : ℕ)
    (z : MixedCoveredJetSource I rows E n d) (s : Finset α) (j : Fin m) (i : Fin (n j)) :
    ((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () =
      integerBooleanSitesFromRows (rowSets j) ((z.1 j).2 i) s := by
  rw [integerBooleanSitesFromRows_eq_mulVec]
  rfl

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredRowsSiteValue (y : EuclideanJetLayers U rows) (s : Finset α) :
    EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => ∑ t, rowRestrictedSiteMatrix (rowSets j) s t • y j t

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

omit [Fintype α] in
theorem mixedCoveredRowsSiteValue_chart (z : MixedCoveredJetSource I rows E n d) (s : Finset α) :
    mixedCoveredJetChart U o b hb bW d (mixedCoveredRowsSiteValue rowSets d z s) =
      coveredRowsSiteValue rowSets U (mixedCoveredJetChart U o b hb bW d z) s := by
  funext j t
  exact mixedCoveredJetIntegerImage_chart U o b hb bW d
    (fun j (_ : Unit) => rowRestrictedSiteMatrix (rowSets j) s) z j t

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α (Fin.val j + 1))
local notation "rows" => (fun j : Fin m => (Subtype.val : jets j → Finset α))

theorem coefficientDeckSiteMask_of_lifts
    (hperiod : ∀ j, integerScalarLattice (jets j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (z : ∀ j, jets j → Q j → ZMod d) (v : Finset α → ∀ j, Q j → ℤ)
    (hv : ∀ s j i, (v s j i : ZMod d) =
      ∑ t, boundedBooleanReconstructionMatrix α (j.val + 1) s t • z j t i) :
    coefficientDeckSiteMask root D rows d period (fun s j i => (v s j i : ZMod period)) =
      coefficientDeckJetDensity root D rows d z := by
  have hjet (j : Fin m) (t : jets j) (i : Q j) :
      ((booleanCoefficient (fun s => v s j i) t.val : ℤ) : ZMod d) = z j t i := by
    rw [← booleanJetExtractionMatrix_mulVec (rows j) (fun s => v s j i) t]
    change ((∑ s, booleanJetExtractionMatrix (rows j) t s * v s j i : ℤ) : ZMod d) = _
    simp only [Int.cast_sum, Int.cast_mul, hv]
    simpa only [zsmul_eq_mul] using
      boundedBooleanReconstruction_zsmul_inverse (j.val + 1) (fun t => z j t i) t
  have h := coefficientDeckSiteMask_apply root D rows d period hperiod v
  simpa only [hjet] using h

theorem coefficientDeckSiteMask_ambient_lifts
    (hperiod : ∀ j, integerScalarLattice (jets j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (z : MixedCoveredJetSource I jets Q n d) (u : Finset α → ∀ j, euclideanSubspace (U j))
    (hu : ∀ s j, (QuotientAddGroup.mk (u s j) : euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
      mixedCoveredJetChart U o b hb bW d (mixedCoveredBooleanSiteValue d z s) j ()) :
    ∃ v : Finset α → ∀ j, Q j → ℤ,
      (∀ s j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (b j) (hb j)
          ((mixedCoveredJetCoordinates U o d (mixedCoveredBooleanSiteValue d z s) j ()).1) +
        ((bW j).equivFun.symm (v s j)).val = (d : ℝ) • u s j) ∧
      (∀ s j, integerResidueMap (Q j) d (v s j) = (mixedCoveredBooleanSiteValue d z s).2 j ()) ∧
      coefficientDeckSiteMask root D rows d period (fun s j i => (v s j i : ZMod period)) =
        coefficientDeckJetDensity root D rows d z.2 := by
  have hex (s : Finset α) (j : Fin m) := exists_covered_representative_offset
    (euclideanSubspace (U j)) (bW j) (b j) (hb j) d (u s j)
    (mixedCoveredJetCoordinates U o d (mixedCoveredBooleanSiteValue d z s) j ()).1
    ((mixedCoveredBooleanSiteValue d z s).2 j ()) (hu s j)
  choose v hrep hres using hex
  refine ⟨v, hrep, hres, ?_⟩
  apply coefficientDeckSiteMask_of_lifts root D d period hperiod z.2 v
  intro s j i
  exact congrFun (hres s j) i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem arrayCoordinateEquiv_integerMatrixTorusMap {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (A : Matrix S I ℤ) (x : SubspaceArrayTorus I U) (s : S) :
    arrayCoordinateEquiv U (integerMatrixTorusMap U A x) s =
      ∑ i, A s i • arrayCoordinateEquiv U x i := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U)
      (fun _ : Unit => ∑ i, (A s i : ℝ) • v i) =
    ∑ i, A s i • QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) (fun _ : Unit => v i)
  simp only [← map_zsmul, ← map_sum]
  congr 1
  funext u
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl (fun i _ => Int.cast_smul_eq_zsmul ℝ (A s i) (v i))

namespace VectorPolynomial

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

theorem coveredBooleanSiteValue_eq_siteFromLow
    (y : EuclideanJetLayers U jets) (s : Finset α) (j : Fin m) :
    coveredBooleanSiteValue U y s j () =
      (euclideanSubspaceTorusEquiv (U j)).symm
        (arrayCoordinateEquiv (U j) (siteFromLowBooleanJets U ((euclideanJetEquiv U).symm y) j) s) := by
  change (∑ r, boundedBooleanReconstructionMatrix α (j.val + 1) s r • y j r) =
    (euclideanSubspaceTorusEquiv (U j)).symm
      (arrayCoordinateEquiv (U j) (integerMatrixTorusMap (U j)
        (boundedBooleanReconstructionMatrix α (j.val + 1)) ((euclideanJetEquiv U).symm y j)) s)
  rw [arrayCoordinateEquiv_integerMatrixTorusMap]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  change y j r = (euclideanSubspaceTorusEquiv (U j)).symm
    (arrayCoordinateEquiv (U j) ((arrayCoordinateEquiv (U j)).symm
      (fun t => euclideanSubspaceTorusEquiv (U j) (y j t))) r)
  rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

theorem coveredBooleanSiteValue_coefficient {K : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (x : CoefficientTorus (K := K) U)
    (s : Finset α) (j : Fin m) :
    coveredBooleanSiteValue U
        (euclideanJetEquiv U (coefficientBooleanJetTorusMap U root D (fun _j => Subtype.val) x)) s j () =
      (euclideanSubspaceTorusEquiv (U j)).symm
        (arrayCoordinateEquiv (U j) (coefficientSiteTorusMap U (integerAffineCube root D) x j) s) := by
  rw [coveredBooleanSiteValue_eq_siteFromLow, AddEquiv.symm_apply_apply,
    siteFromLowBooleanJets_coefficient]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem rowRestrictedExtraction_mul_reconstruction (rows : Finset (Finset α)) :
    booleanJetExtractionMatrix (Subtype.val : rows → Finset α) *
      rowRestrictedSiteMatrix rows = 1 := by
  ext s r
  change (booleanJetExtractionMatrix (Subtype.val : rows → Finset α) *ᵥ
    (fun t => if r.val ⊆ t then (1 : ℤ) else 0)) s = _
  rw [booleanJetExtractionMatrix_mulVec, booleanCoefficient_monomial]
  simp only [Matrix.one_apply, Subtype.val_inj]

theorem rowRestrictedReconstruction_zsmul_inverse {W : Type*} [AddCommGroup W]
    (rows : Finset (Finset α)) (x : rows → W) (r : rows) :
    (∑ s : Finset α, booleanJetExtractionMatrix Subtype.val r s •
      ∑ t : rows, rowRestrictedSiteMatrix rows s t • x t) = x r := by
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  change (∑ t, (booleanJetExtractionMatrix (Subtype.val : rows → Finset α) *
    rowRestrictedSiteMatrix rows) r t • x t) = x r
  rw [rowRestrictedExtraction_mul_reconstruction]
  simp [Matrix.one_apply]

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (rowSets : Fin m → Finset (Finset α))
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowMap" => (fun j => (Subtype.val : rows j → Finset α))

theorem coefficientDeckRowsSiteMask_of_lifts
    (hperiod : ∀ j, integerScalarLattice (rows j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rowMap j)).mulVecLin.range)
    (z : ∀ j, rows j → Q j → ZMod d) (v : Finset α → ∀ j, Q j → ℤ)
    (hv : ∀ s j i, (v s j i : ZMod d) =
      ∑ t, rowRestrictedSiteMatrix (rowSets j) s t • z j t i) :
    coefficientDeckSiteMask root D rowMap d period (fun s j i => (v s j i : ZMod period)) =
      coefficientDeckJetDensity root D rowMap d z := by
  have hjet (j : Fin m) (t : rows j) (i : Q j) :
      ((booleanCoefficient (fun s => v s j i) t.val : ℤ) : ZMod d) = z j t i := by
    rw [← booleanJetExtractionMatrix_mulVec (rowMap j) (fun s => v s j i) t]
    change ((∑ s, booleanJetExtractionMatrix (rowMap j) t s * v s j i : ℤ) : ZMod d) = _
    simp only [Int.cast_sum, Int.cast_mul, hv]
    simpa only [zsmul_eq_mul] using
      rowRestrictedReconstruction_zsmul_inverse (rowSets j) (fun t => z j t i) t
  have h := coefficientDeckSiteMask_apply root D rowMap d period hperiod v
  simpa only [hjet] using h

theorem coefficientDeckRowsSiteMask_reconstructed
    (hperiod : ∀ j, integerScalarLattice (rows j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rowMap j)).mulVecLin.range)
    {I : Fin m → Type*} {n : Fin m → ℕ}
    (z : MixedCoveredJetSource I rows Q n d) :
    coefficientDeckSiteMask root D rowMap d period
      (fun s j i => ((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val) =
      coefficientDeckJetDensity root D rowMap d z.2 := by
  have hv (s : Finset α) (j : Fin m) (i : Q j) :
      ((((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ℤ) : ZMod d) =
        ∑ t, rowRestrictedSiteMatrix (rowSets j) s t • z.2 j t i := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
    rfl
  have h := coefficientDeckRowsSiteMask_of_lifts root D rowSets d period hperiod z.2
    (fun s j i => ((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val) hv
  simpa only [Int.cast_natCast] using h

end VectorPolynomial
end Erdos3

end

end OAI
