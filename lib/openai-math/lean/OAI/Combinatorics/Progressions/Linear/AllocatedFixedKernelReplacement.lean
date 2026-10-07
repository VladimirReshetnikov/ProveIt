import OAI.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
import OAI.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget

namespace OAI

section

namespace Erdos3

theorem coefficientFiberControl_change_decidableEq {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {d₁ d₂ : DecidableEq J}
    {A : Matrix I J ℤ} {s : I ↪ J} {S : J → ℝ} {H L C U M : ℝ} {h : ℕ}
    (hc : @CoefficientFiberControl I J _ _ _ d₁ A s S H L h C U M) :
    @CoefficientFiberControl I J _ _ _ d₂ A s S H L h C U M := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  exact hc

def layerKernelIndexBound (m B : ℕ) : ℕ := B^(m*2^(m+1))

theorem layerKernelIndexBound_row {m B : ℕ} {α O : Type*} [Fintype α] [Fintype O]
    (hB : 0 < B) (hq : Fintype.card α ≤ m+1) (rows : O → Finset α)
    (hinj : Function.Injective rows) (j : Fin m) :
    (B^(j.val+1))^Fintype.card O ≤ layerKernelIndexBound m B := by
  have hc : Fintype.card O ≤ 2^(m+1) := by
    have hr : Fintype.card O ≤ 2^Fintype.card α := by
      simpa only [Fintype.card_finset] using Fintype.card_le_of_injective rows hinj
    exact hr.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hq)
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hB (Nat.mul_le_mul (Nat.succ_le_of_lt j.isLt) hc)

theorem layerKernelIndexBound_le_exp (m : ℕ) {B : ℕ} {p : ℝ}
    (hB : (B : ℝ) ≤ Real.exp p) :
    (layerKernelIndexBound m B : ℝ) ≤ Real.exp ((m*2^(m+1) : ℕ)*p) := by
  unfold layerKernelIndexBound
  rw [Nat.cast_pow, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hB _

noncomputable def fixedKernelInverseBound {α G O : Type*}
    [Fintype α] [DecidableEq α] [Fintype G] [DecidableEq G] [Fintype O] [DecidableEq O]
    {L : ℕ} (hL : 0 < L) (x : G → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G degree)
    (hA : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) (κ : ℝ) : Prop :=
  ‖(scalarKernelFixedPivot hL x degree rows s hA).symm.toContinuousLinearMap‖ ≤
    kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card O) degree κ

namespace VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))

theorem allocatedPartitionedInput_bound
    (u : PrincipalAxisTuples (α := α) grid sides)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    ∀ k a, |((Sum.elim
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (principalTupleIntegers v) (input k a) : ℤ) : ℝ) / layerSamplerBox B U basis S k| ≤ 1 := by
  exact mappedPrincipal_normalized_bound
    (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val)
    (principalAxisLength (fun a => ¬grid a) sides)
    (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩) input
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (Sum.elim (fun ga : G × Option α => ((x ga.1 ga.2 : ℤ) : ℝ)/S.value)
      (principalTupleNormalized (principalAxisLength grid sides) u))
    (allocatedPartitionedInput_frozen_bound B U basis S x u) (layerSamplerBox B U basis S) v
    (allocatedPartitionedInput_normalized B U basis S x u v)

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedGoodKernel_controls {κ : ℝ} {M : ℕ}
    (selection : α ↪ G) (hκ : 0 < κ) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) :
    ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) κ) ∧
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) j (i : Fin (n j)),
      CoefficientFiberControl
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (allocatedNonkernelJetMatrix B U basis S x u rows j v))
        ((s j).trans Function.Embedding.inl)
        (Sum.elim (kernelJetCoefficientScale G (j.val+1) S.value (basisAxisScale (basis j) i))
          (fun d => (basisAxisScale (basis j) i : ℝ) /
            monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)))
        (basisAxisScale (basis j) i) S.value (j.val+1)
        (kernelJetEntryAllowance (Fintype.card α) (j.val+1))
        (kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) κ)
        (layerKernelIndexBound m M) := by
  have hM : 0 < M := by
    obtain ⟨a, ha, haM, _⟩ := hx.2
    exact ha.trans_le haM
  obtain ⟨s, hA, hi⟩ := goodKernel_fixed_pivots
    S.positive selection hκ x hx (fun j : Fin m => j.val+1) rows hinj hrows
  refine ⟨s, hA, hi, ?_⟩
  intro u v j i
  have hH : (0 : ℝ) < basisAxisScale (basis j) i := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hcontrol := fixedKernel_mapped_control S.positive selection x hx (j.val+1) (rows j)
    (hinj j) (hrows j) (s j) (hA j) (hi j) hH (allocatedNonkernelExponent B j) input
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (principalTupleIntegers v) (layerSamplerBox B U basis S)
    (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k))
    (layerSamplerBox_le B U basis S) (allocatedNonkernelExponent_degree B j)
    (allocatedPartitionedInput_bound B U basis S x u v)
    (show (((M^(j.val+1))^Fintype.card (O j) : ℕ) : ℝ) ≤ layerKernelIndexBound m M by
      exact_mod_cast layerKernelIndexBound_row hM hq (rows j) (hinj j) j)
  exact coefficientFiberControl_change_decidableEq hcontrol

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedFixedKernel_controls {κ : ℝ} {M : ℕ}
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) κ) :
    ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) j (i : Fin (n j)),
      CoefficientFiberControl
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (allocatedNonkernelJetMatrix B U basis S x u rows j v))
        ((s j).trans Function.Embedding.inl)
        (Sum.elim (kernelJetCoefficientScale G (j.val+1) S.value (basisAxisScale (basis j) i))
          (fun d => (basisAxisScale (basis j) i : ℝ) /
            monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)))
        (basisAxisScale (basis j) i) S.value (j.val+1)
        (kernelJetEntryAllowance (Fintype.card α) (j.val+1))
        (kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) κ)
        (layerKernelIndexBound m M) := by
  have hM : 0 < M := by
    obtain ⟨a, ha, haM, _⟩ := hx.2
    exact ha.trans_le haM
  intro u v j i
  have hH : (0 : ℝ) < basisAxisScale (basis j) i := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hcontrol := fixedKernel_mapped_control S.positive selection x hx (j.val+1) (rows j)
    (hinj j) (hrows j) (s j) (hA j) (hi j) hH (allocatedNonkernelExponent B j) input
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (principalTupleIntegers v) (layerSamplerBox B U basis S)
    (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k))
    (layerSamplerBox_le B U basis S) (allocatedNonkernelExponent_degree B j)
    (allocatedPartitionedInput_bound B U basis S x u v)
    (show (((M^(j.val+1))^Fintype.card (O j) : ℕ) : ℝ) ≤ layerKernelIndexBound m M by
      exact_mod_cast layerKernelIndexBound_row hM hq (rows j) (hinj j) j)
  exact coefficientFiberControl_change_decidableEq hcontrol

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem layerKernelIndexBound_row_withCutoff (d : ℕ)
    {m B : ℕ} {α O : Type*} [Fintype α] [Fintype O]
    (hB : 0 < B) (hq : Fintype.card α ≤ d + 1) (rows : O → Finset α)
    (hinj : Function.Injective rows) (j : Fin m) :
    (B ^ (j.val + 1)) ^ Fintype.card O ≤ layerKernelIndexBound (max m d) B := by
  let j' : Fin (max m d) := ⟨j.val, j.isLt.trans_le (le_max_left m d)⟩
  exact layerKernelIndexBound_row hB
    (hq.trans (Nat.succ_le_succ (le_max_right m d))) rows hinj j'

namespace VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val + 1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))

theorem allocatedGoodKernel_controls_withCutoff (d : ℕ) {κ : ℝ} {M : ℕ}
    (selection : α ↪ G) (hκ : 0 < κ) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ d + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val + 1) :
    ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) κ) ∧
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) j (i : Fin (n j)),
      CoefficientFiberControl
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val + 1) (rows j))
          (allocatedNonkernelJetMatrix B U basis S x u rows j v))
        ((s j).trans Function.Embedding.inl)
        (Sum.elim (kernelJetCoefficientScale G (j.val + 1) S.value (basisAxisScale (basis j) i))
          (fun e => (basisAxisScale (basis j) i : ℝ) /
            monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j e)))
        (basisAxisScale (basis j) i) S.value (j.val + 1)
        (kernelJetEntryAllowance (Fintype.card α) (j.val + 1))
        (kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card (O j))
          (j.val + 1) κ)
        (layerKernelIndexBound (max m d) M) := by
  have hM : 0 < M := by
    obtain ⟨a, ha, haM, _⟩ := hx.2
    exact ha.trans_le haM
  obtain ⟨s, hA, hi⟩ := goodKernel_fixed_pivots
    S.positive selection hκ x hx (fun j : Fin m => j.val + 1) rows hinj hrows
  refine ⟨s, hA, hi, ?_⟩
  intro u v j i
  have hH : (0 : ℝ) < basisAxisScale (basis j) i := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hcontrol := fixedKernel_mapped_control S.positive selection x hx (j.val + 1) (rows j)
    (hinj j) (hrows j) (s j) (hA j) (hi j) hH (allocatedNonkernelExponent B j) input
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (principalTupleIntegers v) (layerSamplerBox B U basis S)
    (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k))
    (layerSamplerBox_le B U basis S) (allocatedNonkernelExponent_degree B j)
    (allocatedPartitionedInput_bound B U basis S x u v)
    (show (((M ^ (j.val + 1)) ^ Fintype.card (O j) : ℕ) : ℝ) ≤
        layerKernelIndexBound (max m d) M by
      exact_mod_cast layerKernelIndexBound_row_withCutoff d hM hq (rows j) (hinj j) j)
  exact coefficientFiberControl_change_decidableEq hcontrol

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedIntegerKernelMask_bound {M : ℕ} {κ : ℝ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val + 1)
    (j : Fin m) (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (z : O j → ℤ) :
    0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus residue z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus residue z ≤ layerKernelIndexBound m M := by
  unfold allocatedIntegerKernelMask coefficientResidueMultiplier
  refine ⟨coefficientImageMultiplier_nonneg _ _, (coefficientImageMultiplier_le_index _ _).trans ?_⟩
  have hi := scalarKernelJet_extended_index selection x hx (j.val + 1) (rows j)
    (hinj j) (hrows j) (liftResidueMatrix residue)
  exact_mod_cast hi.trans (layerKernelIndexBound_row hM hq (rows j) (hinj j) j)

theorem allocatedIntegerKernelMask_le_exp {M : ℕ} {κ p : ℝ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val + 1) (hMp : (M : ℝ) ≤ Real.exp p)
    (j : Fin m) (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (z : O j → ℤ) :
    allocatedIntegerKernelMask B U basis S x rows j modulus residue z ≤
      Real.exp ((m * 2 ^ (m + 1) : ℕ) * p) :=
  (allocatedIntegerKernelMask_bound B U basis S x rows hM selection hx hq hinj hrows j modulus residue z).2.trans
    (layerKernelIndexBound_le_exp m hMp)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def allocatedKernelLog (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) : ℝ :=
  P + (m*2^(m+1) : ℕ)*P + (Fintype.card α : ℝ)*(m+1) +
    ∑ j, kernelInverseLog (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P

theorem allocatedKernelLog_bounds (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedKernelLog G α O P ∧ P ≤ allocatedKernelLog G α O P ∧
    (m*2^(m+1) : ℕ)*P ≤ allocatedKernelLog G α O P ∧
    (Fintype.card α : ℝ)*(m+1) ≤ allocatedKernelLog G α O P ∧
    ∀ j, kernelInverseLog (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P ≤
      allocatedKernelLog G α O P := by
  have hi (j : Fin m) : 0 ≤ kernelInverseLog
      (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P := by
    unfold kernelInverseLog
    positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hi j)
  have hidx : 0 ≤ (m*2^(m+1) : ℕ)*(P : ℝ) := by positivity
  have hentry : 0 ≤ (Fintype.card α : ℝ)*(m+1) := by positivity
  unfold allocatedKernelLog
  refine ⟨by positivity, by linarith, by linarith, by linarith, ?_⟩
  intro j
  have hj := Finset.single_le_sum (fun k _ => hi k) (Finset.mem_univ j)
  linarith

theorem allocatedKernelLog_allowances (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} {M : ℕ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P) :
    (layerKernelIndexBound m M : ℝ) ≤ Real.exp (allocatedKernelLog G α O P) ∧
    ∀ j, kernelJetEntryAllowance (Fintype.card α) (j.val+1) ≤ Real.exp (allocatedKernelLog G α O P) ∧
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1)
        (1/(M : ℝ)) ≤ Real.exp (allocatedKernelLog G α O P) := by
  have hb := allocatedKernelLog_bounds G α O hP
  refine ⟨(layerKernelIndexBound_le_exp m hMP).trans (Real.exp_le_exp.mpr hb.2.2.1), ?_⟩
  intro j
  constructor
  · apply (kernelJetEntryAllowance_le_exp (Fintype.card α) (j.val+1)).trans
    apply Real.exp_le_exp.mpr
    apply le_trans _ hb.2.2.2.1
    gcongr
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  · have hκ : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
    have hv := kernelJetInverseAllowance_le_exp (Fintype.card α) (Fintype.card G)
      (Fintype.card (O j)) (j.val+1) hκ hP (by simpa only [one_div, inv_inv] using hMP)
    exact hv.trans (Real.exp_le_exp.mpr (hb.2.2.2.2 j))

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedKernelReplacementLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P e : ℝ) : ℝ :=
  ∑ j, coefficientFrontLog (Fintype.card (O j))
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    (allocatedKernelLog G α O P) (4*(P+8)) e

theorem allocatedKernelReplacementLog_front_le (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P e : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (j : Fin m) :
    coefficientFrontLog (Fintype.card (O j))
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (allocatedKernelLog G α O P) (4*(P+8)) e ≤ allocatedKernelReplacementLog (G := G) B α O P e := by
  apply Finset.single_le_sum _ (Finset.mem_univ j)
  intro k _
  exact coefficientFrontLog_nonneg _ _ (allocatedKernelLog_bounds G α O hP).1 (by positivity) he

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedGoodKernel_replacement {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value) :
    ∃ (modulus : ℕ) (_hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
      (∀ v, p.weight v ≠ 0 → ∀ j,
        integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) →
      ∀ j i (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i),
      (∀ z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
        allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ layerKernelIndexBound m M) ∧
      ∀ v, p.weight v ≠ 0 → ∀ z,
        |(basisAxisScale (basis j) i : ℝ)^Fintype.card (O j) *
            (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous z).toReal -
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z *
            allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
              (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
              (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))| ≤ ε := by
  have hκ : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  obtain ⟨modulus, hm, hmB, hspatial, hperiod⟩ := goodKernel_common_period selection x hx (m+1)
    (Nat.succ_le_succ (Nat.zero_le m)) (fun j : Fin m => j.val+1)
    (fun j => (Nat.succ_le_of_lt j.isLt).trans (Nat.le_succ _)) rows hinj hrows
  obtain ⟨s, hA, hi, hcontrol⟩ := allocatedGoodKernel_controls B U basis S x rows selection hκ hx hq hinj hrows
  refine ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, ?_⟩
  intro u p residue hr j i henormous
  have hb := allocatedKernelLog_bounds G α O hP
  have ha := allocatedKernelLog_allowances G α O hP hM hMP
  have ht : 0 ≤ 4*(P+8) := by positivity
  have hf := (Real.exp_le_exp.mpr (allocatedKernelReplacementLog_front_le (G := G) B α O hP he j)).trans hlarge
  exact allocatedIntegerKernel_residue_family B U basis hR hσ S x u rows j i (s j) (hA j) (hσ1 j)
    henormous p modulus (residue j) (hperiod j) (fun v hv => hr v hv j)
    (kernelJetEntryAllowance_pos _ _).le (kernelJetInverseAllowance_nonneg _ _ _ _ hκ)
    (Nat.cast_nonneg _) (fun v _ => hcontrol u v j i)
    hb.1 ht hε ha.1 (ha.2 j).2 (ha.2 j).1 ((hRP j).trans (Real.exp_le_exp.mpr hb.2.1))
    (allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (allocatedInteger_replacementScale_le B U basis S j i (rows j) (hinj j) hq (s j)
      hb.1 ht he hε hεe hf henormous)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedFixedKernel_controls_withCutoff (d : ℕ) {κ : ℝ} {M : ℕ}
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ d+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) κ) :
    ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) j (i : Fin (n j)),
      CoefficientFiberControl
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (allocatedNonkernelJetMatrix B U basis S x u rows j v))
        ((s j).trans Function.Embedding.inl)
        (Sum.elim (kernelJetCoefficientScale G (j.val+1) S.value (basisAxisScale (basis j) i))
          (fun e => (basisAxisScale (basis j) i : ℝ) /
            monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j e)))
        (basisAxisScale (basis j) i) S.value (j.val+1)
        (kernelJetEntryAllowance (Fintype.card α) (j.val+1))
        (kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) κ)
        (layerKernelIndexBound (max m d) M) := by
  have hM : 0 < M := by
    obtain ⟨a, ha, haM, _⟩ := hx.2
    exact ha.trans_le haM
  intro u v j i
  have hH : (0 : ℝ) < basisAxisScale (basis j) i := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hcontrol := fixedKernel_mapped_control S.positive selection x hx (j.val+1) (rows j)
    (hinj j) (hrows j) (s j) (hA j) (hi j) hH (allocatedNonkernelExponent B j) input
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (principalTupleIntegers v) (layerSamplerBox B U basis S)
    (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k))
    (layerSamplerBox_le B U basis S) (allocatedNonkernelExponent_degree B j)
    (allocatedPartitionedInput_bound B U basis S x u v)
    (show (((M^(j.val+1))^Fintype.card (O j) : ℕ) : ℝ) ≤ layerKernelIndexBound (max m d) M by
      exact_mod_cast layerKernelIndexBound_row_withCutoff d hM hq (rows j) (hinj j) j)
  exact coefficientFiberControl_change_decidableEq hcontrol

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedFixedKernel_replacement {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) :
    ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
      (∀ v, p.weight v ≠ 0 → ∀ j,
        integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) →
      ∀ j i (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i),
      (∀ z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
        allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ layerKernelIndexBound m M) ∧
      ∀ v, p.weight v ≠ 0 → ∀ z,
        |(basisAxisScale (basis j) i : ℝ)^Fintype.card (O j) *
            (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous z).toReal -
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z *
            allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
              (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
              (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))| ≤ ε := by
  have hκ : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hcontrol := allocatedFixedKernel_controls B U basis S x rows selection hx hq hinj hrows s hA hi
  intro u p residue hr j i henormous
  have hb := allocatedKernelLog_bounds G α O hP
  have ha := allocatedKernelLog_allowances G α O hP hM hMP
  have ht : 0 ≤ 4*(P+8) := by positivity
  have hf := (Real.exp_le_exp.mpr (allocatedKernelReplacementLog_front_le (G := G) B α O hP he j)).trans hlarge
  exact allocatedIntegerKernel_residue_family B U basis hR hσ S x u rows j i (s j) (hA j) (hσ1 j)
    henormous p modulus (residue j) (hperiod j) (fun v hv => hr v hv j)
    (kernelJetEntryAllowance_pos _ _).le (kernelJetInverseAllowance_nonneg _ _ _ _ hκ)
    (Nat.cast_nonneg _) (fun v _ => hcontrol u v j i)
    hb.1 ht hε ha.1 (ha.2 j).2 (ha.2 j).1 ((hRP j).trans (Real.exp_le_exp.mpr hb.2.1))
    (allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (allocatedInteger_replacementScale_le B U basis S j i (rows j) (hinj j) hq (s j)
      hb.1 ht he hε hεe hf henormous)

end Erdos3.VectorPolynomial

end

end OAI
