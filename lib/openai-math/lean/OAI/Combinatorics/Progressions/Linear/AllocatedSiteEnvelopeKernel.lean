import OAI.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl
import OAI.Combinatorics.Progressions.Estimates.AllocatedSiteEnvelopeGain

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedSiteEnvelope_kernel_gain {D p : ℝ}
    (h : AllocatedComparisonDimensions (G := G) B α O D)
    (hQ : ∀ j, (Fintype.card (Q j) : ℝ) ≤ D) (hp : 0 ≤ p)
    {M : ℕ} {κ : ℝ} (hM : 0 < M) (hMp : (M : ℝ) ≤ Real.exp p)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j z, (rows j z).card ≤ j.val + 1)
    (period : ℕ) [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hperiod_size : period ≤ M ^ (m + 1))
    (d : ℕ) [NeZero d] (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) :
    let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p
    let Cm : ℝ≥0 := ⟨Real.exp w, (Real.exp_pos w).le⟩
    let A : ℝ≥0 := Real.toNNReal (coefficientDeckPeriodCap O Q period) *
      Cm ^ Fintype.card (LayerSamplerAxis I n)
    (A : ℝ) ≤ Real.exp (allocatedSiteEnvelopeGain m D p) ∧
      ∀ (z : AllocatedLongJetRows B U b S O) (r : ∀ j, O j → Q j → ZMod d),
        |∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)| *
          coefficientDeckJetDensity root dirs rows d r ≤ A := by
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p
  let Cm : ℝ≥0 := ⟨Real.exp w, (Real.exp_pos w).le⟩
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hp
  have hCm : 1 ≤ (Cm : ℝ) := Real.one_le_exp_iff.mpr hw
  have hm (j : Fin m) (z : O j → ℤ) :
      0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ Cm :=
    ⟨(allocatedIntegerKernelMask_bound B U b S x rows hM selection hx hq hinj hrows j modulus (residue j) z).1,
      allocatedIntegerKernelMask_le_exp B U b S x rows hM selection hx hq hinj hrows hMp j modulus (residue j) z⟩
  constructor
  · exact allocatedProfileGain_le_exp B h hQ M period hperiod_size Cm hp hw hMp le_rfl
  · intro z r
    have hphysical (j : Fin m) : integerScalarLattice (O j) (period : ℤ) ≤
        (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).mulVecLin.range := by
      rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j]
      exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
    have hd := coefficientDeckJetDensity_period_bound root dirs rows d period hphysical r
    have hmask := allocatedLongJetMask_product_bound B U b S x rows modulus residue hCm hm z
    change _ ≤ ((Real.toNNReal (coefficientDeckPeriodCap O Q period) *
      Cm ^ Fintype.card (LayerSamplerAxis I n) : ℝ≥0) : ℝ)
    simp only [NNReal.coe_mul, NNReal.coe_pow,
      Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg O Q period)]
    exact (mul_le_mul hmask hd (coefficientDeckJetDensity_nonneg root dirs rows d r)
      (pow_nonneg Cm.coe_nonneg _)).trans_eq (mul_comm _ _)

end Erdos3.VectorPolynomial

end

end OAI
