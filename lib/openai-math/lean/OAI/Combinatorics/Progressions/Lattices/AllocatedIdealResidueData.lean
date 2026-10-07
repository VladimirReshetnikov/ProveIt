import OAI.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

omit [DecidableEq G] in
theorem allocatedIdealScale_refined_window_size {dim : ℕ} {D p e w E P : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hbudget : (m + 1 : ℕ) * P + P ^ 2 + (dim + 1 : ℕ) ≤ p)
    {M modulus : ℕ} (hmodulus : modulus ≤ M ^ (m + 1)) (hM : (M : ℝ) ≤ Real.exp P)
    {X : Type*} [Fintype X] (hX : (Fintype.card X : ℝ) ≤ P)
    (q : X → ℕ) (hq : ∀ x, (q x : ℝ) ≤ Real.exp P) :
    let S := allocatedIdealScale (G := G) B U b hR hσ D p e w E
    ∀ a, (Fintype.card (Fin dim) + 1) * residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a := by
  intro S a
  have hmod : (modulus : ℝ) ≤ Real.exp ((m + 1 : ℕ) * P) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp P) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul P (m + 1)).symm
  have hrefined := residueRefinedPeriod_exp_bound modulus q hmod hq
  have hdim : ((dim + 1 : ℕ) : ℝ) ≤ Real.exp (dim + 1 : ℕ) := by
    linarith [Real.add_one_le_exp ((dim + 1 : ℕ) : ℝ)]
  have hcost : ((dim + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) * P + Fintype.card X * P) ≤ p := by
    nlinarith [mul_le_mul_of_nonneg_right hX hP]
  have hsize : ((dim + 1 : ℕ) : ℝ) * residueRefinedPeriod modulus q ≤ (S.value : ℝ) := by
    calc
      _ ≤ Real.exp (dim + 1 : ℕ) * Real.exp ((m + 1 : ℕ) * P + Fintype.card X * P) :=
        mul_le_mul hdim hrefined (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (((dim + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) * P + Fintype.card X * P)) :=
        (Real.exp_add _ _).symm
      _ ≤ Real.exp p := Real.exp_le_exp.mpr hcost
      _ ≤ _ := allocatedIdealScale_ge_exp B U b hR hσ hD hp he hw hE
  rw [allocatedPrincipalSides_long_restricted]
  simpa only [Fintype.card_fin] using (show (dim + 1) * residueRefinedPeriod modulus q ≤ S.value by
    exact_mod_cast hsize)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S

omit [DecidableEq G] [∀ j, Fintype (O j)] in
theorem allocated_refined_residue_data {modulus refined : ℕ}
    (hRefined : 0 < refined) (hdiv : modulus ∣ refined)
    (hsize : ∀ a, (Fintype.card α + 1) * refined ≤
      principalAxisLength (fun a => ¬grid a) sides a) :
    ∃ (reference : PrincipalAxisTuples (α := α) grid sides →
        (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined) →
        PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
      (residue : PrincipalAxisTuples (α := α) grid sides →
        (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined) →
        ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
      (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
      (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
        ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus =
          residue u r j) := by
  choose representative hrepresentative using
    (fun r => exists_allocatedLongResidueReference (α := α) B U b S refined hRefined r hsize)
  let residue := fun (u : PrincipalAxisTuples (α := α) grid sides) r j => integerResidueMatrix
    (integerMappedJetMatrix (allocatedNonkernelExponent B j)
      (partitionedPrincipalInput grid (fun g a => (g, a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (rows j) (principalResidueLift refined r)) modulus
  refine ⟨fun _ r => representative r, residue, fun _ r => hrepresentative r, ?_⟩
  intro u r v hv j
  apply integerResidueMatrix_reduce _ _ hdiv
  exact allocatedLongResidueWeights_matrix B U b S refined hRefined r hsize x u rows
    (principalResidueLift refined r) (principalResidueLift_spec refined r) j v hv

end Erdos3.VectorPolynomial

end

end OAI
