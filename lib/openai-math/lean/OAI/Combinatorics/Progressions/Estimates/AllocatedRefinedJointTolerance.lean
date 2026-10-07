import OAI.Combinatorics.Progressions.Linear.AllocatedKernelJointComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedJointAccuracyLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P E : ℝ) : ℝ :=
  E + Fintype.card (LayerSamplerAxis I n) + 3 +
    Fintype.card (LayerSamplerAxis I n) *
      (2+(m*2^(m+1) : ℕ)*P+allocatedDensityLog (G := G) B α O P)

theorem allocatedJointAccuracyLog_nonneg (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ allocatedJointAccuracyLog (G := G) B α O P E := by
  have hQ := (allocatedDensityLog_bounds (G := G) B α O hP).1
  unfold allocatedJointAccuracyLog
  positivity

theorem allocatedJointAccuracy_spec (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P E η : ℝ} {M : ℕ}
    (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P) (hη : 0 < η) (hη1 : η ≤ 1)
    (hηE : η⁻¹ ≤ Real.exp E) :
    let ε := maskedProductAccuracy (Fintype.card (LayerSamplerAxis I n))
      (layerKernelIndexBound m M) (Real.exp (allocatedDensityLog (G := G) B α O P)) η
    0 < ε ∧ ε ≤ 1 ∧ ε⁻¹ ≤ Real.exp (allocatedJointAccuracyLog (G := G) B α O P E) := by
  dsimp only
  refine ⟨maskedProductAccuracy_pos _ (Nat.cast_nonneg _) (Real.exp_pos _).le hη,
    maskedProductAccuracy_le_one _ (Nat.cast_nonneg _) (Real.exp_pos _).le hη1, ?_⟩
  exact maskedProductAccuracy_inverse_exp _ (Nat.cast_nonneg _) (Real.exp_pos _).le hη
    (by positivity) (allocatedDensityLog_bounds (G := G) B α O hP).1
    (layerKernelIndexBound_le_exp m hMP) le_rfl hηE

noncomputable def allocatedJointTupleCutoff (α : Type*) [Fintype α] [DecidableEq α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) (M : ℕ) (η : ℝ) : ℕ :=
  scalarTupleToleranceCutoff α (PrincipalTupleIndex B (layerSamplerDegree I n)) (M^(m+1))
    (maskedJointTupleBudget α (Fintype.card (LayerSamplerAxis I n))
      (layerKernelIndexBound m M) (Real.exp (allocatedDensityLog (G := G) B α O P))) (η/2)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

theorem allocatedJointTupleCutoff_spec {P η : ℝ} {M modulus : ℕ}
    (hP : 0 ≤ P) (hM : 0 < M) (hη : 0 < η) (hη1 : η ≤ 1)
    (hmodulus : modulus ≤ M^(m+1))
    (hlarge : allocatedJointTupleCutoff (G := G) B α O P M η ≤ S.value) :
    let C : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
    let W : ℝ := layerKernelIndexBound m M
    let ε := maskedProductAccuracy (Fintype.card (LayerSamplerAxis I n)) W C η
    (∀ d, (Fintype.card α+1)*modulus ≤ lengths d) ∧
      (∀ d, scalarCubeGridBoundaryConstant α * ((modulus : ℝ)/lengths d) <
        volume.real (scalarCubeDomain α)) ∧
      Fintype.card {a // ¬grid a} * ε * (1+W*C+ε)^Fintype.card {a // ¬grid a} +
        W^Fintype.card {a // ¬grid a} * jointTupleQuadratureError (α := α)
          (fun a : {a // ¬grid a} => B a.val) (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)
          (Fintype.card {a // ¬grid a}) C C lengths modulus ≤ η := by
  let C : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
  let W : ℝ := layerKernelIndexBound m M
  let K := maskedJointTupleBudget α (Fintype.card (LayerSamplerAxis I n)) W C
  have hK : 0 ≤ K := maskedJointTupleBudget_nonneg α _ (Nat.cast_nonneg _) C.coe_nonneg
  have hc := principalAxisTupleIndex_card_le B (layerSamplerDegree I n) (fun a => ¬grid a)
  have hcard := scalarTupleToleranceCutoff_card_le α
    (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val))
    (PrincipalTupleIndex B (layerSamplerDegree I n)) hc modulus hK (half_pos hη).le
  have hmod := scalarTupleToleranceCutoff_mono_modulus α
    (PrincipalTupleIndex B (layerSamplerDegree I n)) hmodulus hK (half_pos hη).le
  have hlen (d) : scalarTupleToleranceCutoff α
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val))
      modulus K (η/2) ≤ lengths d := by
    rw [allocatedPrincipalSides_long_restricted]
    exact hcard.trans (hmod.trans hlarge)
  have ht := scalarTupleToleranceCutoff_spec α
    (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val))
    (half_pos hη) hlen
  refine ⟨ht.2.1, ht.2.2.1, ?_⟩
  have hn : Fintype.card {a // ¬grid a} ≤ Fintype.card (LayerSamplerAxis I n) := Fintype.card_subtype_le _
  have hW : 1 ≤ W := by
    change (1 : ℝ) ≤ (layerKernelIndexBound m M : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (show 0 < layerKernelIndexBound m M from pow_pos hM _)
  have hC : 1 ≤ C := by
    exact_mod_cast Real.one_le_exp_iff.mpr (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hr := maskedProductAccuracy_error hn (zero_le_one.trans hW) C.coe_nonneg hη hη1
  have hq := (maskedJointTupleQuadrature_le
    (fun a : {a // ¬grid a} => B a.val) (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)
    hn hW C hC lengths modulus).trans ht.2.2.2
  exact (add_le_add hr hq).trans (by linarith)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedRefinedJointTupleCutoff (α : Type*) [Fintype α] [DecidableEq α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) (M Q : ℕ) (η : ℝ) : ℕ :=
  scalarTupleToleranceCutoff α (PrincipalTupleIndex B (layerSamplerDegree I n)) Q
    (maskedJointTupleBudget α (Fintype.card (LayerSamplerAxis I n))
      (layerKernelIndexBound m M) (Real.exp (allocatedDensityLog (G := G) B α O P))) (η/2)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

theorem allocatedRefinedJointTupleCutoff_spec {P η : ℝ} {M modulus Q : ℕ}
    (hP : 0 ≤ P) (hM : 0 < M) (hη : 0 < η) (hη1 : η ≤ 1)
    (hmodulus : modulus ≤ Q)
    (hlarge : allocatedRefinedJointTupleCutoff (G := G) B α O P M Q η ≤ S.value) :
    let C : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
    let W : ℝ := layerKernelIndexBound m M
    let ε := maskedProductAccuracy (Fintype.card (LayerSamplerAxis I n)) W C η
    (∀ d, (Fintype.card α+1)*modulus ≤ lengths d) ∧
      (∀ d, scalarCubeGridBoundaryConstant α * ((modulus : ℝ)/lengths d) <
        volume.real (scalarCubeDomain α)) ∧
      Fintype.card {a // ¬grid a} * ε * (1+W*C+ε)^Fintype.card {a // ¬grid a} +
        W^Fintype.card {a // ¬grid a} * jointTupleQuadratureError (α := α)
          (fun a : {a // ¬grid a} => B a.val) (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)
          (Fintype.card {a // ¬grid a}) C C lengths modulus ≤ η := by
  let C : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
  let W : ℝ := layerKernelIndexBound m M
  let K := maskedJointTupleBudget α (Fintype.card (LayerSamplerAxis I n)) W C
  have hK : 0 ≤ K := maskedJointTupleBudget_nonneg α _ (Nat.cast_nonneg _) C.coe_nonneg
  have hc := principalAxisTupleIndex_card_le B (layerSamplerDegree I n) (fun a => ¬grid a)
  have hcard := scalarTupleToleranceCutoff_card_le α
    (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val))
    (PrincipalTupleIndex B (layerSamplerDegree I n)) hc modulus hK (half_pos hη).le
  have hmod := scalarTupleToleranceCutoff_mono_modulus α
    (PrincipalTupleIndex B (layerSamplerDegree I n)) hmodulus hK (half_pos hη).le
  have hlen (d) : scalarTupleToleranceCutoff α
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val))
      modulus K (η/2) ≤ lengths d := by
    rw [allocatedPrincipalSides_long_restricted]
    exact hcard.trans (hmod.trans hlarge)
  have ht := scalarTupleToleranceCutoff_spec α
    (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val))
    (half_pos hη) hlen
  refine ⟨ht.2.1, ht.2.2.1, ?_⟩
  have hn : Fintype.card {a // ¬grid a} ≤ Fintype.card (LayerSamplerAxis I n) := Fintype.card_subtype_le _
  have hW : 1 ≤ W := by
    change (1 : ℝ) ≤ (layerKernelIndexBound m M : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (show 0 < layerKernelIndexBound m M from pow_pos hM _)
  have hC : 1 ≤ C := by
    exact_mod_cast Real.one_le_exp_iff.mpr (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hr := maskedProductAccuracy_error hn (zero_le_one.trans hW) C.coe_nonneg hη hη1
  have hq := (maskedJointTupleQuadrature_le
    (fun a : {a // ¬grid a} => B a.val) (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)
    hn hW C hC lengths modulus).trans ht.2.2.2
  exact (add_le_add hr hq).trans (by linarith)

end Erdos3.VectorPolynomial

end

end OAI
