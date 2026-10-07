import OAI.Combinatorics.Progressions.Dynamics.CoefficientFrontBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientReindex
import OAI.Combinatorics.Progressions.Lattices.JointAffineUnitSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

noncomputable def kernelExponentEmbedding (G X : Type*) (h : ℕ) :
    BoundedIntegerExponent G h ↪ BoundedCoefficientExponent (G ⊕ X) h where
  toFun d := ⟨d.val.embDomain Function.Embedding.inl, by
    change (d.val.embDomain Function.Embedding.inl).sum (fun _ n => n) ≤ h
    rw [Finsupp.sum_embDomain]
    exact d.property⟩
  inj' := by
    intro d e hde
    exact Subtype.ext ((Finsupp.embDomain_injective Function.Embedding.inl) (congrArg Subtype.val hde))

abbrev NonkernelCoefficient (G X : Type*) (h : ℕ) :=
  UnselectedColumn (kernelExponentEmbedding G X h)

noncomputable def kernelCoefficientEquiv (G X : Type*) [Fintype G] (h : ℕ) :
    BoundedIntegerExponent G h ⊕ NonkernelCoefficient G X h ≃ BoundedCoefficientExponent (G ⊕ X) h :=
  selectedColumnEquiv (kernelExponentEmbedding G X h)

theorem kernelCoefficientEquiv_inl (G X : Type*) [Fintype G] (h : ℕ) (d : BoundedIntegerExponent G h) :
    kernelCoefficientEquiv G X h (.inl d) = kernelExponentEmbedding G X h d := rfl

theorem kernelCoefficientEquiv_inr (G X : Type*) [Fintype G] (h : ℕ) (d : NonkernelCoefficient G X h) :
    kernelCoefficientEquiv G X h (.inr d) = d.val := rfl

theorem monomialScale_kernelExponent {G X : Type*} {h : ℕ} (T : G ⊕ X → ℝ)
    (d : BoundedIntegerExponent G h) :
    monomialScale T (kernelExponentEmbedding G X h d).val =
      monomialScale (fun g => T (.inl g)) d.val :=
  Finsupp.prod_embDomain

theorem kernelExponent_eval_monomial {G X : Type*} {h : ℕ} (x : G ⊕ X → ℤ)
    (d : BoundedIntegerExponent G h) :
    MvPolynomial.eval x (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1) =
      MvPolynomial.eval (fun g => x (.inl g)) (MvPolynomial.monomial d.val 1) := by
  change MvPolynomial.eval x (MvPolynomial.monomial (d.val.embDomain Function.Embedding.inl) 1) = _
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_embDomain]
  rfl

theorem integerMappedCubeTuple_kernel {G X Z Y α : Type*}
    (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (t : Finset α) :
    (fun g => integerMappedCubeTuple input z y t (.inl g)) =
      integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t := by
  funext g
  simp only [integerMappedCubeTuple, integerAffineCube, hfixed, scalarCubeDifferenceMatrix, sampledColumnMatrix]

theorem integerMappedJetMatrix_kernel {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelExponentEmbedding G X h) = scalarKernelIntegerJet x h rows := by
  ext o d
  change booleanCoefficient (fun t => MvPolynomial.eval (integerMappedCubeTuple input z y t)
      (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1)) (rows o) =
    booleanCoefficient (fun t => MvPolynomial.eval
      (integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t)
      (MvPolynomial.monomial d.val 1)) (rows o)
  apply congrArg (fun f : Finset α → ℤ => booleanCoefficient f (rows o))
  funext t
  rw [kernelExponent_eval_monomial, integerMappedCubeTuple_kernel input z y x hfixed t]

theorem integerMappedJetMatrix_kernel_split {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelCoefficientEquiv G X h) =
      Matrix.fromCols (scalarKernelIntegerJet x h rows)
        (integerMappedJetMatrix (fun d : NonkernelCoefficient G X h => d.val.val) input z rows y) := by
  ext o d
  cases d with
  | inl d => exact congrFun (congrFun (integerMappedJetMatrix_kernel h input z y x hfixed rows) o) d
  | inr d => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem normalizedIntegerColumns_eq_of_instances {I J : Type*}
    [Fintype I] [instI : DecidableEq I] [Fintype J] [instJ : DecidableEq J]
    {dI : DecidableEq I} {dJ : DecidableEq J}
    {M : Matrix I J ℤ} {T : J → ℝ} {P : I → ℝ} {A : Matrix I J ℝ}
    (h : @normalizedIntegerColumns I J ‹Fintype I› dI ‹Fintype J› dJ M T P = A) :
    @normalizedIntegerColumns I J ‹Fintype I› instI ‹Fintype J› instJ M T P = A := by
  have hi : dI = instI := Subsingleton.elim _ _
  have hj : dJ = instJ := Subsingleton.elim _ _
  cases hi
  cases hj
  exact h

theorem kernelExponent_eval_real {G X : Type*} {h : ℕ} (x : G ⊕ X → ℝ)
    (d : BoundedIntegerExponent G h) :
    MvPolynomial.eval x (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1) =
      MvPolynomial.eval (fun g => x (.inl g)) (MvPolynomial.monomial d.val 1) := by
  change MvPolynomial.eval x (MvPolynomial.monomial (d.val.embDomain Function.Embedding.inl) 1) = _
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_embDomain]
  rfl

theorem normalizedMappedKernelJet_eq {G X Z Y α O : Type*}
    [Fintype G] [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℝ) (y : Y → ℝ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℝ) / L)
    (rows : O → Finset α) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
        (kernelJetCoefficientScale G h L H) (fun _ => H) =
      realJetMatrix (fun d => MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1)
        (normalizedCubeTuple input z y) rows := by
  have hc (t : Finset α) : (fun g => normalizedCubeTuple input z y t (.inl g)) =
      realAffineCube (fun g => (x g none : ℝ) / L)
        (fun a g => (x g (some a) : ℝ) / L) t := by
    funext g
    simp only [normalizedCubeTuple, hfixed, Fintype.sum_option, booleanFeature,
      one_mul, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, realAffineCube]
  apply (normalizedScalarKernelJet_eq x h rows hH).trans
  funext o d
  change booleanCoefficient (fun t => MvPolynomial.eval
      (realAffineCube (fun g => (x g none : ℝ) / L) (fun a g => (x g (some a) : ℝ) / L) t)
      (MvPolynomial.monomial d.val 1)) (rows o) = _
  apply congrArg (fun f : Finset α → ℝ => booleanCoefficient f (rows o))
  funext t
  rw [kernelExponent_eval_real, hc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal

theorem normalizedJoinedMatrix_affineJetUnitMap {Z X K α O J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix O J ℤ) (C : Matrix O N ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : O → Finset α) (x : X → ℝ)
    (hC : matrixSupCLM (normalizedIntegerColumns C T (fun _ => 1)) =
      polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x)
    (c w r : J ⊕ N → ℝ) :
    normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) (fun _ => 1) *ᵥ
      (fun j => c j+w j*r j) =
      affineJetUnitMap s
        (normalizedPivotEquiv (A.submatrix id s) hA (fun j => S (s j)) (fun _ => 1)
          (fun j => hS (s j)) (fun _ => zero_lt_one))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
          (fun j => S j.val) (fun _ => 1))) e input z rows c w x r := by
  let v : J ⊕ N → ℝ := fun j => c j+w j*r j
  have hv : selectedSplitCoefficients s ((selectedSplitMeasurableEquiv s).symm v) = v :=
    (selectedSplitMeasurableEquiv s).apply_symm_apply v
  have hm := selectedSplitCoefficients_normalized_matrix A C s hA S T (fun _ => 1) hS
    (fun _ => zero_lt_one) ((selectedSplitMeasurableEquiv s).symm v)
  rw [hv, hC] at hm
  simpa only [v, selectedSplitMeasurableEquiv_symm_apply, splitFreeColumns_apply,
    Sum.elim_inl, Sum.elim_inr, affineJetUnitMap, add_assoc] using hm

theorem normalizedJoinedMatrix_affineDensity_law {Z X K α O J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix O J ℤ) (C : Matrix O N ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : O → Finset α) (x : X → ℝ)
    (hC : matrixSupCLM (normalizedIntegerColumns C T (fun _ => 1)) =
      polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    (unitCoefficientSource (J ⊕ N)).map (fun r =>
      normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) (fun _ => 1) *ᵥ
        (fun j => c j+w j*r j)) =
      realDensityMeasure volume
        (affineSelectedJetDensity s
          (normalizedPivotEquiv (A.submatrix id s) hA (fun j => S (s j)) (fun _ => 1)
            (fun j => hS (s j)) (fun _ => zero_lt_one))
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
            (fun j => S j.val) (fun _ => 1))) e input z rows c w x) := by
  simp_rw [normalizedJoinedMatrix_affineJetUnitMap A C s hA S T hS e input z rows x hC]
  exact affineSelectedJetDensity_unit_law s _ _ e input z rows c w hw R hsupport x

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

abbrev AllocatedNonkernelCoefficient (j : Fin m) :=
  NonkernelCoefficient G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1)

noncomputable def allocatedKernelCoefficientEquiv (j : Fin m) :
    BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j ≃
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) :=
  kernelCoefficientEquiv G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1)

def allocatedNonkernelExponent (j : Fin m) (d : AllocatedNonkernelCoefficient (G := G) B j) :
    LayerSamplerVariables G I n B →₀ ℕ := d.val.val

omit [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] in
theorem allocatedNonkernelExponent_degree (j : Fin m) (d : AllocatedNonkernelCoefficient (G := G) B j) :
    (allocatedNonkernelExponent B j d).sum (fun _ r => r) ≤ j.val+1 := d.val.property

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedKernelCoefficientScale (j : Fin m) (i : Fin (n j))
    (d : BoundedIntegerExponent G (j.val+1)) :
    allocatedIntegerProfileScales B U basis S j i (allocatedKernelCoefficientEquiv B j (.inl d)) =
      kernelJetCoefficientScale G (j.val+1) S.value (basisAxisScale (basis j) i) d := by
  change (basisAxisScale (basis j) i : ℝ) /
      monomialScale (layerSamplerBox B U basis S)
        (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1) d).val = _
  rw [monomialScale_kernelExponent]
  rfl

theorem allocatedKernelCoefficientScales_split (j : Fin m) (i : Fin (n j)) :
    allocatedIntegerProfileScales B U basis S j i ∘ allocatedKernelCoefficientEquiv B j =
      Sum.elim (kernelJetCoefficientScale G (j.val+1) S.value (basisAxisScale (basis j) i))
        (fun d => (basisAxisScale (basis j) i : ℝ) /
          monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)) := by
  funext d
  cases d with
  | inl d => exact allocatedKernelCoefficientScale B U basis S j i d
  | inr d => rfl

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

include hR hσ hσ1 in
theorem allocatedKernelProfile_bound (d) : |centers d|+widths d ≤ R j :=
  (allocatedProfile_term_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerIntegerPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

include hR hσ hσ1 henormous in
theorem allocatedKernelProfile_sum_pos :
    0 < coefficientWeightSum (affineProductProfile (centers ∘ reindex) (widths ∘ reindex)) (scales ∘ reindex) := by
  rw [affineCoefficientWeightSum_reindex]
  exact allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous

theorem allocatedKernel_image_law {O : Type*} [Fintype O]
    (A : Matrix O (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) ℤ) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩).map (fun a => A *ᵥ a) =
      (coefficientImagePMF (A.submatrix id reindex) (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
        (affineProductProfile_nonneg _ _ (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)))
        (scales ∘ reindex) (fun d => allocatedIntegerProfileScales_pos B U basis S j i (reindex d))
        (affineProductProfile_zero_outside _ _
          (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) (hR j).le
          (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)))
        (allocatedKernelProfile_sum_pos B U basis hR hσ S j i hσ1 henormous)).toMeasure := by
  rw [allocatedEnormous_image_law B U basis hR hσ S j i hσ1 henormous]
  have hlaw := coefficientImagePMF_affine_reindex A reindex centers widths scales
    (allocatedIntegerProfileWidths_pos B hR hσ j i) (allocatedIntegerProfileScales_pos B U basis S j i)
    (hR j).le (allocatedKernelProfile_bound B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)
  exact congrArg PMF.toMeasure hlaw.symm

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedKernelJet_split {α O : Type*} [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
      (partitionedPrincipalInput grid (fun g a => (g, a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v).submatrix id reindex =
      Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
        (integerMappedJetMatrix (allocatedNonkernelExponent B j)
          (partitionedPrincipalInput grid (fun g a => (g, a)))
          (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v) :=
  integerMappedJetMatrix_kernel_split (j.val+1) _ _ _ x (fun _ _ => rfl) rows

theorem allocatedKernelJet_full_image {α O : Type*} [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
      (integerMappedJetMatrix (allocatedNonkernelExponent B j)
        (partitionedPrincipalInput grid (fun g a => (g, a)))
        (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v)).mulVecLin.range =
      (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
        (partitionedPrincipalInput grid (fun g a => (g, a)))
        (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v).mulVecLin.range := by
  rw [← allocatedKernelJet_split B U basis S j x u v rows]
  exact integerColumnEquiv_range _ reindex

theorem allocatedKernelJet_image_law {α O : Type*} [DecidableEq α] [Fintype O]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩).map
      (fun a => integerMappedJetMatrix
        (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
        (partitionedPrincipalInput grid (fun g a => (g, a)))
        (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v *ᵥ a) =
      (coefficientImagePMF
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
          (integerMappedJetMatrix (allocatedNonkernelExponent B j)
            (partitionedPrincipalInput grid (fun g a => (g, a)))
            (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v))
        (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
        (affineProductProfile_nonneg _ _ (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)))
        (scales ∘ reindex) (fun d => allocatedIntegerProfileScales_pos B U basis S j i (reindex d))
        (affineProductProfile_zero_outside _ _
          (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) (hR j).le
          (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)))
        (allocatedKernelProfile_sum_pos B U basis hR hσ S j i hσ1 henormous)).toMeasure := by
  have hlaw := allocatedKernel_image_law B U basis hR hσ S j i hσ1 henormous
    (integerMappedJetMatrix
      (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
      (partitionedPrincipalInput grid (fun g a => (g, a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v)
  rw [allocatedKernelJet_split B U basis S j x u v rows] at hlaw
  exact hlaw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedContinuousProfileCenters (R : Fin m → ℝ) (j : Fin m) (i : I j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileCenter (layerContinuousPrincipalSlots B j i)
    (principalProfileSize (R j) (layerContinuousPrincipalSlots (G := G) B j i).card)

noncomputable def allocatedContinuousProfileWidths (R σ : Fin m → ℝ) (j : Fin m) (i : I j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileWidth (layerContinuousPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (R j/4) (principalProfileSize (R j) (layerContinuousPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedContinuousProfileScales (j : Fin m) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  fun d => 1 / monomialScale (layerSamplerBox B U basis S) d.val

theorem allocatedContinuousProfileScales_pos (j : Fin m) (d) :
    0 < allocatedContinuousProfileScales B U basis S j d :=
  one_div_pos.mpr (monomialScale_pos _
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v)) d.val)

include hR hσ in
theorem allocatedContinuousProfileWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num))
    (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _) d

include hR hσ in
theorem allocatedContinuousProfile_bound (j : Fin m) (i : I j) (hσ1 : σ j ≤ 1) (d) :
    |allocatedContinuousProfileCenters (G := G) B R j i d| +
      allocatedContinuousProfileWidths B R σ j i d ≤ R j :=
  (allocatedProfile_term_bound (layerContinuousPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerContinuousPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

theorem allocatedLayerCenters_scale (j : Fin m) (i : I j) (d) :
    allocatedLayerCenters B U basis S j i d =
      allocatedContinuousProfileScales B U basis S j d * allocatedContinuousProfileCenters B R j i d := by
  unfold allocatedLayerCenters allocatedArrayCenters allocatedContinuousProfileScales
    allocatedContinuousProfileCenters
  ring

theorem allocatedLayerWidths_scale (j : Fin m) (i : I j) (d) :
    allocatedLayerWidths B U basis S j i d =
      allocatedContinuousProfileScales B U basis S j d * allocatedContinuousProfileWidths B R σ j i d := by
  unfold allocatedLayerWidths allocatedArrayWidths allocatedContinuousProfileScales
    allocatedContinuousProfileWidths
  ring

theorem allocatedContinuousProfileScales_split (j : Fin m) :
    allocatedContinuousProfileScales B U basis S j ∘ allocatedKernelCoefficientEquiv B j =
      Sum.elim (kernelJetCoefficientScale G (j.val+1) S.value 1)
        (fun d => 1 / monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)) := by
  funext d
  cases d with
  | inl d =>
    change 1 / monomialScale (layerSamplerBox B U basis S)
      (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1) d).val = _
    rw [monomialScale_kernelExponent]
    rfl
  | inr d => rfl

variable (j : Fin m) (i : I j)

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedContinuousProfileScales B U basis S j
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

theorem allocatedContinuous_reindexed_image_law {O : Type*} [Fintype O] [DecidableEq O]
    (A : Matrix O (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) ℤ) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inl i⟩).map
      (fun a => A.map (Int.cast : ℤ → ℝ) *ᵥ a) =
      (unitCoefficientSource (BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient B j)).map
        (fun r => normalizedIntegerColumns (A.submatrix id reindex) (scales ∘ reindex) (fun _ => 1) *ᵥ
          (fun d => centers (reindex d)+widths (reindex d)*r d)) := by
  change (Measure.pi (fun d => affineCoefficientMeasure
    (allocatedLayerCenters B U basis S j i d) (allocatedLayerWidths B U basis S j i d))).map _ = _
  simp_rw [allocatedLayerCenters_scale, allocatedLayerWidths_scale]
  exact affineCoefficientProduct_scaled_image reindex A centers widths scales
    (allocatedContinuousProfileWidths_pos B hR hσ j i) (allocatedContinuousProfileScales_pos B U basis S j)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1

omit [Fintype α] [DecidableEq α] in
theorem allocatedPartitionedInput_normalized
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (k : LayerSamplerVariables G I n B) (a : Option α) :
    ((Sum.elim fixedInteger (principalTupleIntegers v) (input k a) : ℤ) : ℝ) /
      layerSamplerBox B U basis S k =
      Sum.elim fixedReal (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
        (input k a) := by
  have hbox : layerSamplerBox B U basis S =
      Sum.elim (fun _ : G => (S.value : ℝ)) (fun d => (sides d : ℝ)) := by
    funext k
    cases k <;> rfl
  rw [hbox]
  exact partitionedPrincipalInput_normalized grid (fun g a => (g, a))
    (fun ga : G × Option α => (x ga.1 ga.2 : ℤ))
    (fun ga : G × Option α => ((x ga.1 ga.2 : ℤ) : ℝ) / (S.value : ℝ))
    (fun _ => (S.value : ℝ)) (fun _ _ => rfl) sides u v k a

noncomputable def allocatedContinuousKernelDensity
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (O → ℝ) → ℝ :=
  affineSelectedJetDensity s
    (normalizedPivotEquiv ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s) hA
      (fun o => kernelScale (s o)) (fun _ => 1)
      (fun o => kernelJetCoefficientScale_pos G (j.val+1) (by exact_mod_cast S.positive) zero_lt_one (s o))
      (fun _ => zero_lt_one))
    (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
      (fun d => kernelScale d.val) (fun _ => 1)))
    (allocatedNonkernelExponent B j) input fixedReal rows (centers ∘ reindex) (widths ∘ reindex) y

theorem allocatedContinuousKernel_image_law (hσ1 : σ j ≤ 1)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inl i⟩).map
      (fun a => (integerMappedJetMatrix
        (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
        input fixedInteger rows (principalTupleIntegers v)).map (Int.cast : ℤ → ℝ) *ᵥ a) =
      realDensityMeasure volume
        (allocatedContinuousKernelDensity B U basis S j i x u rows s hA
          (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)) := by
  rw [allocatedContinuous_reindexed_image_law B U basis hR hσ S j i,
    allocatedKernelJet_split B U basis S j x (principalTupleIntegers u) (principalTupleIntegers v) rows,
    allocatedContinuousProfileScales_split]
  have hn := integerMappedCubeTuple_normalized input fixedInteger (principalTupleIntegers v) fixedReal
    (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v) (layerSamplerBox B U basis S)
    (allocatedPartitionedInput_normalized B U basis S x u v)
  have hc := normalizedIntegerJetColumns_eq (allocatedNonkernelExponent B j) input fixedReal rows
    (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
    (integerMappedCubeTuple input fixedInteger (principalTupleIntegers v)) (layerSamplerBox B U basis S)
    hn (H := 1) one_ne_zero
  have hlaw := normalizedJoinedMatrix_affineDensity_law (scalarKernelIntegerJet x (j.val+1) rows)
    (integerMappedJetMatrix (allocatedNonkernelExponent B j) input fixedInteger rows (principalTupleIntegers v))
    s hA kernelScale (fun d => 1 / monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d))
    (kernelJetCoefficientScale_pos G (j.val+1) (by exact_mod_cast S.positive) zero_lt_one)
    (allocatedNonkernelExponent B j) input fixedReal rows
    (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v) hc
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d))
    ⟨R j, (hR j).le⟩ (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d))
  refine Eq.trans ?_ hlaw
  congr 1
  funext r
  apply congrArg (fun M => M *ᵥ (fun d => centers (reindex d)+widths (reindex d)*r d))
  congr 1
  exact Subsingleton.elim _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedInteger_replacementScale_le {α O : Type*} [Fintype α] [Fintype O]
    (j : Fin m) (i : Fin (n j)) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hq : Fintype.card α ≤ m+1) (s : O ↪ BoundedIntegerExponent G (j.val+1))
    {b t e ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hε : 0 < ε)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hfront : Real.exp (coefficientFrontLog (Fintype.card O)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))) b t e) ≤ S.value)
    (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) :
    coefficientReplacementScale
      (J := BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j)
      (s.trans Function.Embedding.inl) b t ε S.value (j.val+1) ≤ (basisAxisScale (basis j) i : ℝ) := by
  have hcard := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  have hf : Real.exp (coefficientFrontLog (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j))
      b t e) ≤ S.value := by simpa only [hcard] using hfront
  have hL : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hd := layerTailDegree_row_bound rows hinj (Nat.succ_le_of_lt j.isLt) hq
  apply (coefficientReplacementScale_le_power (s.trans Function.Embedding.inl) (j.val+1)
    hb ht he hε (zero_le_one.trans hL) hεe hf).trans
  calc
    _ ≤ (S.value : ℝ)^(layerTailDegree m+1) :=
      pow_le_pow_right₀ hL (Nat.succ_le_of_lt hd)
    _ ≤ (basisAxisScale (basis j) i : ℝ) := by exact_mod_cast henormous.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

noncomputable def allocatedUnitProfileWidth (R σ : ℝ) (a : ℕ) : ℝ :=
  allocatedWidthFloor R σ 1 0 a

theorem allocatedUnitProfileWidth_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (a : ℕ) :
    0 < allocatedUnitProfileWidth R σ a :=
  allocatedWidthFloor_pos hR hσ zero_lt_one 0 a

theorem allocatedUnitProfileWidth_le {J : Type*} [Fintype J] (P : Finset J) (j₀ : J)
    {R σ : ℝ} (hR : 0 < R) (j : J) :
    allocatedUnitProfileWidth R σ (Fintype.card J) ≤
      coefficientProfileWidth P j₀ (R/4) (principalProfileSize R P.card)
        (tailProfileSize R σ (Fintype.card J)) j := by
  have hp : principalProfileSize R (Fintype.card J) ≤ principalProfileSize R P.card := by
    unfold principalProfileSize
    apply div_le_div_of_nonneg_left hR.le (by positivity)
    gcongr
    exact_mod_cast P.card_le_univ
  simp only [allocatedUnitProfileWidth, allocatedWidthFloor, pow_zero, div_one]
  unfold coefficientProfileWidth
  split_ifs
  · exact min_le_left _ _
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
      (div_le_div_of_nonneg_right hp (by norm_num))
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem allocatedUnitProfileWidth_inverse_exp (a : ℕ) {R σ P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P) (haP : (a : ℝ)+1 ≤ Real.exp P) :
    (allocatedUnitProfileWidth R σ a)⁻¹ ≤ Real.exp (4*(P+8)) := by
  let X := Real.exp (P+8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have hLX : ((1 : ℕ) : ℝ) ≤ X := by norm_num; linarith
  have h := allocatedWidthFloor_inverse_power_bound 1 0 0 a le_rfl hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) (haP.trans hPX) hLX
  simpa only [allocatedUnitProfileWidth, X, ← Real.exp_nat_mul, Nat.zero_add, Nat.cast_ofNat] using h

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

include hR in
theorem allocatedContinuousProfileWidths_floor (d) :
    unitWidth ≤ allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  allocatedUnitProfileWidth_le _ _ (hR j) d

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => 1))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" => NNReal.mk unitWidth (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

theorem allocatedPartitionedInput_frozen_bound (t) : |fixedReal t| ≤ 1 := by
  apply partitionedPrincipalInput_frozen_bound grid _ _ sides (allocatedPrincipalSides_pos B U basis S) u t
  intro ga
  have h := (norm_le_pi_norm (fun a => ((x ga.1 a : ℤ) : ℝ)/(S.value : ℝ)) ga.2).trans
    (integerScalarCubeBox_normalized_norm_le S.positive (x ga.1))
  simpa only [Real.norm_eq_abs] using h

include hR hσ in
theorem allocatedContinuousKernelDensity_measurable (hσ1 : σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedContinuousKernelDensity B U basis S j i x u rows s hA)) := by
  have hw (d) := allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)
  have hb (d) := allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)
  exact normalizedJetDensity_measurable pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz s).continuous)
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun d => hw (.inl d)) (hR j).le (fun d => hb (.inl d))))
    (affineProductProfile_zero_outside _ _ (fun d => hw (.inr d)) (hR j).le (fun d => hb (.inr d)))

include hR hσ in
theorem allocatedContinuousKernelDensity_probability_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (∀ v, 0 ≤ allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v) ∧
      Integrable (allocatedContinuousKernelDensity B U basis S j i x u rows s hA y) ∧
      (∫ v, allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v) = 1 :=
  affineSelectedJetDensity_probability_data s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)) y

include hR hσ in
theorem allocatedContinuousKernelDensity_bounds (hσ1 : σ j ≤ 1) (v : O → ℝ) :
    (∀ y, |allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v| ≤
      pivotKernelCap (UnselectedColumn s) pivot radius
        (delta⁻¹^Fintype.card (BoundedIntegerExponent G (j.val+1)))) ∧
      LipschitzOnWith
        (pivotKernelLip (UnselectedColumn s) pivot radius
          (affineProductProfileLip (BoundedIntegerExponent G (j.val+1)) delta) *
          (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) *
            polynomialBoxLip
              (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
                (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1))) * radius)
        (fun y => allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v)
        (Metric.closedBall 0 1) := by
  have hδ : 0 < delta := allocatedUnitProfileWidth_pos (hR j) (hσ j) _
  have he := affineSelectedJetDensity_bounds s pivot free (allocatedNonkernelExponent B j)
    input fixedReal (allocatedPartitionedInput_frozen_bound B U basis S x u) rows
    (allocatedNonkernelExponent_degree B j) (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)) hδ
    (fun d => allocatedContinuousProfileWidths_floor B hR j i (reindex (.inl d))) radius
    (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)) v
  simpa only [allocatedContinuousKernelDensity, Real.norm_eq_abs] using he

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

def AllocatedTailCutoffCompatible (L d : ℕ) : Prop :=
  ∀ j (i : Fin (n j)), L ^ (layerTailDegree m + 1) < basisAxisScale (basis j) i →
    L ^ (layerTailDegree (max m d) + 1) < basisAxisScale (basis j) i

theorem allocatedTailCutoffCompatible_of_le (L d : ℕ) (hd : d ≤ m) :
    AllocatedTailCutoffCompatible U basis L d := by
  unfold AllocatedTailCutoffCompatible
  simpa only [max_eq_left hd] using
    (fun j (i : Fin (n j)) (h : L ^ (layerTailDegree m + 1) < basisAxisScale (basis j) i) => h)

theorem allocatedTailCutoffCompatible_of_moderate (L d : ℕ)
    (hmoderate : ∀ j (i : Fin (n j)), basisAxisScale (basis j) i ≤ L ^ (layerTailDegree m + 1)) :
    AllocatedTailCutoffCompatible U basis L d := by
  intro j i h
  exact False.elim (Nat.not_lt_of_ge (hmoderate j i) h)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedInteger_replacementScale_le_withCutoff (d : ℕ) {α O : Type*} [Fintype α] [Fintype O]
    (j : Fin m) (i : Fin (n j)) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hq : Fintype.card α ≤ d+1) (s : O ↪ BoundedIntegerExponent G (j.val+1))
    {b t e ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hε : 0 < ε)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hfront : Real.exp (coefficientFrontLog (Fintype.card O)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))) b t e) ≤ S.value)
    (henormous : S.value^(layerTailDegree (max m d)+1) < basisAxisScale (basis j) i) :
    coefficientReplacementScale
      (J := BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j)
      (s.trans Function.Embedding.inl) b t ε S.value (j.val+1) ≤ (basisAxisScale (basis j) i : ℝ) := by
  have hcard := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  have hf : Real.exp (coefficientFrontLog (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j))
      b t e) ≤ S.value := by simpa only [hcard] using hfront
  have hL : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hd := layerTailDegree_row_bound rows hinj
    ((Nat.succ_le_of_lt j.isLt).trans (le_max_left m d))
    (hq.trans (Nat.succ_le_succ (le_max_right m d)))
  apply (coefficientReplacementScale_le_power (s.trans Function.Embedding.inl) (j.val+1)
    hb ht he hε (zero_le_one.trans hL) hεe hf).trans
  calc
    _ ≤ (S.value : ℝ)^(layerTailDegree (max m d)+1) :=
      pow_le_pow_right₀ hL (Nat.succ_le_of_lt hd)
    _ ≤ (basisAxisScale (basis j) i : ℝ) := by exact_mod_cast henormous.le

end Erdos3.VectorPolynomial

end

end OAI
