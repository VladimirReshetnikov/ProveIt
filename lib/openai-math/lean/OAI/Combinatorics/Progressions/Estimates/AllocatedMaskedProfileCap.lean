import OAI.Combinatorics.Progressions.Linear.AllocatedSiteEnvelopeKernel
import OAI.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := O) a)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedLongProfileDensity_deck_bound
    (A Cf : ℝ≥0)
    (hA : ∀ (z : AllocatedLongJetRows B U b S O) (r : ∀ j, O j → Q j → ZMod d),
      |∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)| *
        coefficientDeckJetDensity root dirs rows d r ≤ A)
    (f : (output → ℝ) → ℝ) (hf : ∀ w, |f w| ≤ Cf)
    (z : AllocatedLongJetRows B U b S O) (r : ∀ j, O j → Q j → ZMod d) :
    coefficientDeckJetDensity root dirs rows d r *
      |allocatedLongProfileDensity B U b S x rows modulus residue f z| ≤
        ((A * Cf : ℝ≥0) : ℝ) / scale := by
  have hs : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  rw [allocatedLongProfileDensity, abs_div, abs_mul, abs_of_pos hs]
  calc
    _ = ((|∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)| *
        coefficientDeckJetDensity root dirs rows d r) *
        |f (allocatedLongJetRealCoordinates B U b S z)|) / scale := by ring
    _ ≤ ((A : ℝ) * Cf) / scale := div_le_div_of_nonneg_right
      (mul_le_mul (hA z r) (hf _) (abs_nonneg _) A.coe_nonneg) hs.le
    _ = _ := rfl

theorem allocatedLongProfileDensity_period_bound
    (period : ℕ) [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C Cf : ℝ≥0) (hC : 1 ≤ (C : ℝ))
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C)
    (f : (output → ℝ) → ℝ) (hf : ∀ w, |f w| ≤ Cf)
    (z : AllocatedLongJetRows B U b S O) (r : ∀ j, O j → Q j → ZMod d) :
    coefficientDeckJetDensity root dirs rows d r *
      |allocatedLongProfileDensity B U b S x rows modulus residue f z| ≤
      (((Real.toNNReal (coefficientDeckPeriodCap O Q period) *
        C ^ Fintype.card (LayerSamplerAxis I n) * Cf : ℝ≥0) : ℝ)) / scale := by
  apply allocatedLongProfileDensity_deck_bound B U b S x rows modulus residue u v d
    (Real.toNNReal (coefficientDeckPeriodCap O Q period) * C ^ Fintype.card (LayerSamplerAxis I n))
    Cf ?_ f hf z r
  intro w s
  have hp (j) : integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j]
    exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  have hd := coefficientDeckJetDensity_period_bound root dirs rows d period hp s
  have hmask := allocatedLongJetMask_product_bound B U b S x rows modulus residue hC hm w
  simp only [NNReal.coe_mul, NNReal.coe_pow,
    Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg O Q period)]
  exact (mul_le_mul hmask hd (coefficientDeckJetDensity_nonneg root dirs rows d s)
    (pow_nonneg C.coe_nonneg _)).trans_eq (mul_comm _ _)

end Erdos3.VectorPolynomial

end

end OAI
