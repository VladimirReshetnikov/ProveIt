/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use weightedHomogeneousSubmodule.sub_mem for chart homogeneity because
the newer IsWeightedHomogeneous.sub lemma is unavailable.
All upstream theorem statements are unchanged. -/
import OAI.Compat.Core
import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory

namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

noncomputable def polynomialTagLinearEmbedding (E : B → I → ℝ) :
    U ⊕ B → MvPolynomial (U ⊕ I) ℝ :=
  Sum.elim (fun u => X (Sum.inl u))
    (fun b => ∑ i, C (E b i) * X (Sum.inr i))

@[simp] theorem polynomialTagLinearEmbedding_inl (E : B → I → ℝ) (u : U) :
    polynomialTagLinearEmbedding E (Sum.inl u) = X (Sum.inl u) := rfl

@[simp] theorem polynomialTagLinearEmbedding_inr (E : B → I → ℝ) (b : B) :
    polynomialTagLinearEmbedding (U := U) E (Sum.inr b) =
      ∑ i, C (E b i) * X (Sum.inr i) := rfl

theorem polynomialTagLinearEmbedding_rename (E : B → I → ℝ)
    (p : MvPolynomial U ℝ) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
      (rename (Sum.inl : U → U ⊕ B) p) = rename (Sum.inl : U → U ⊕ I) p := by
  rw [aeval_rename, rename_eq_aeval]
  rfl

theorem normalizedRealPolynomialChart_linear_restriction_coordinate
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (A' : I → MvPolynomial U ℝ)
    (E : B → I → ℝ) (hA : ∀ b, A b = ∑ i, C (E b i) * A' i)
    (j : U ⊕ B) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
        (normalizedRealPolynomialChart H A j) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H A')
        (polynomialTagLinearEmbedding E j) := by
  classical
  cases j with
  | inl u => simp
  | inr b =>
    simp only [normalizedRealPolynomialChart_inr, map_sub, aeval_X,
      polynomialTagLinearEmbedding_inr, polynomialTagLinearEmbedding_rename,
      map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    rw [hA b]
    simp only [map_sum, map_mul, rename_C]
    simp only [mul_sub, Finset.sum_sub_distrib]

theorem normalizedRealPolynomialChart_linear_restriction
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (A' : I → MvPolynomial U ℝ)
    (E : B → I → ℝ) (hA : ∀ b, A b = ∑ i, C (E b i) * A' i)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) p) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H A')
        (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) := by
  have h : (aeval (R := ℝ) (polynomialTagLinearEmbedding E)).comp
      (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) =
      (aeval (R := ℝ) (normalizedRealPolynomialChart H A')).comp
        (aeval (R := ℝ) (polynomialTagLinearEmbedding E)) := by
    ext j : 1
    simpa only [AlgHom.comp_apply, aeval_X] using
      normalizedRealPolynomialChart_linear_restriction_coordinate H A A' E hA j
  exact AlgHom.congr_fun h p

theorem polynomialTagLinearEmbedding_eval (E : B → I → ℝ)
    (u : U → ℝ) (v : I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ) :
    eval (Sum.elim u v) (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) =
      eval (Sum.elim u (fun b => ∑ i, E b i * v i)) p := by
  change aeval (R := ℝ) (Sum.elim u v)
    (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) =
      aeval (R := ℝ) (Sum.elim u (fun b => ∑ i, E b i * v i)) p
  rw [comp_aeval_apply]
  congr 1
  ext j : 1
  cases j <;> simp [polynomialTagLinearEmbedding]

theorem normalizedChart_decomposition_linear_restriction
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (A' : I → MvPolynomial U ℝ)
    (E : B → I → ℝ) (hA : ∀ b, A b = ∑ i, C (E b i) * A' i)
    (p slow rat : MvPolynomial (U ⊕ B) ℝ)
    (h : p = aeval (R := ℝ) (normalizedRealPolynomialChart H A) slow + rat) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E) p =
      aeval (R := ℝ) (normalizedRealPolynomialChart H A')
        (aeval (R := ℝ) (polynomialTagLinearEmbedding E) slow) +
      aeval (R := ℝ) (polynomialTagLinearEmbedding E) rat := by
  rw [h, map_add, normalizedRealPolynomialChart_linear_restriction H A A' E hA]

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {B I U : Type*} [Fintype B] [Fintype I]
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)

include hA

private theorem normalizedChart_coefficients_mem (α : U →₀ ℕ) :
    coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A) α ∈ K := by
  have heq : coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A) α =
      fun b => (A b).coeff α := by
    funext b
    exact coefficients_ofCoordinates_basisFun A α b
  rw [heq]
  exact hA α

noncomputable def normalizedChartSubspaceCoordinates : I → MvPolynomial U ℝ :=
  fun i => coordinate (e.coord i).toAddMonoidHom
    (restrictCoefficients K (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A)
      (normalizedChart_coefficients_mem K A hA))

omit [Fintype I] in
theorem normalizedChartSubspaceCoordinates_coeff (α : U →₀ ℕ) (i : I) :
    (normalizedChartSubspaceCoordinates K e A hA i).coeff α =
      e.repr ⟨fun b => (A b).coeff α, hA α⟩ i := by
  unfold normalizedChartSubspaceCoordinates
  rw [coeff_coordinate]
  change e.repr (coefficients
    (restrictCoefficients K (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A)
      (normalizedChart_coefficients_mem K A hA)) α) i = _
  congr 1
  apply congrArg e.repr
  apply Subtype.ext
  rw [coefficients_restrictCoefficients]
  funext b
  exact coefficients_ofCoordinates_basisFun A α b

theorem normalizedChartSubspaceCoordinates_reconstruct (b : B) :
    A b = ∑ i, (e i : B → ℝ) b • normalizedChartSubspaceCoordinates K e A hA i := by
  classical
  ext α
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    normalizedChartSubspaceCoordinates_coeff, smul_eq_mul]
  have heq := congrArg (fun z : K => (z : B → ℝ) b)
    (e.sum_repr ⟨fun c => (A c).coeff α, hA α⟩)
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm] using heq.symm

theorem normalizedChartSubspaceCoordinates_eval_mem (x : U → ℝ) :
    (fun b => MvPolynomial.eval x (A b)) ∈ K := by
  let P := ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A
  let Q := restrictCoefficients K P (normalizedChart_coefficients_mem K A hA)
  have heval : (eval (V := K) x Q : B → ℝ) = eval x P :=
    eval_restrictCoefficients K P (normalizedChart_coefficients_mem K A hA) x
  have hcoord : eval x P = fun b => MvPolynomial.eval x (A b) := by
    have h := eval₂_ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A x
    have he : eval₂ x P = eval x P := by
      simpa using (eval₂_algebraMap (S := ℝ) x P)
    rw [he] at h
    simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
      using h
  rw [← hcoord, ← heval]
  exact (eval (V := K) x Q).property

theorem exists_normalizedChartSubspaceCoordinates :
    ∃ A' : I → MvPolynomial U ℝ,
      (∀ b, A b = ∑ i, (e i : B → ℝ) b • A' i) ∧
      ∀ x : U → ℝ, (fun b => MvPolynomial.eval x (A b)) ∈ K :=
  ⟨normalizedChartSubspaceCoordinates K e A hA,
    normalizedChartSubspaceCoordinates_reconstruct K e A hA,
    normalizedChartSubspaceCoordinates_eval_mem K A hA⟩

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype B] [Fintype I]

noncomputable def polynomialSubspaceRestriction (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) : MvPolynomial (U ⊕ B) ℝ →ₐ[ℝ] MvPolynomial (U ⊕ I) ℝ :=
  aeval (R := ℝ) (polynomialTagLinearEmbedding (fun b i => (e i : B → ℝ) b))

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (v : I → ℝ) :
    eval (Sum.elim u v) (polynomialSubspaceRestriction K e p) =
      eval (Sum.elim u (fun b => ∑ i, (e i : B → ℝ) b * v i)) p :=
  polynomialTagLinearEmbedding_eval _ u v p

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eq_of_eval (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p q : MvPolynomial (U ⊕ B) ℝ)
    (h : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) p = eval (Sum.elim u b) q) :
    polynomialSubspaceRestriction K e p = polynomialSubspaceRestriction K e q := by
  classical
  apply MvPolynomial.funext
  intro x
  let u : U → ℝ := fun a => x (Sum.inl a)
  let v : I → ℝ := fun a => x (Sum.inr a)
  have hx : x = Sum.elim u v := by funext a; cases a <;> rfl
  rw [hx, polynomialSubspaceRestriction_eval, polynomialSubspaceRestriction_eval]
  apply h
  have he : (fun b => ∑ i, (e i : B → ℝ) b * v i) =
      ((∑ i, v i • e i : K) : B → ℝ) := by
    ext b
    simp [mul_comm]
  rw [he]
  exact (∑ i, v i • e i : K).property

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval_basis (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (b : K) :
    eval (Sum.elim u (fun i => e.repr b i)) (polynomialSubspaceRestriction K e p) =
      eval (Sum.elim u (b : B → ℝ)) p := by
  rw [polynomialSubspaceRestriction_eval]
  have he : (fun c => ∑ i, (e i : B → ℝ) c * e.repr b i) = (b : B → ℝ) := by
    funext c
    have h := congrArg (fun z : K => (z : B → ℝ) c) (e.sum_repr b)
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, mul_comm] using h
  rw [he]

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval_eq (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p q : MvPolynomial (U ⊕ B) ℝ)
    (h : polynomialSubspaceRestriction K e p = polynomialSubspaceRestriction K e q)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) p = eval (Sum.elim u b) q := by
  rw [← polynomialSubspaceRestriction_eval_basis K e p u ⟨b, hb⟩, h,
    polynomialSubspaceRestriction_eval_basis]

theorem normalizedChartSubspaceCoordinates_reconstruct_C
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K) (b : B) :
    A b = ∑ i, C ((e i : B → ℝ) b) * normalizedChartSubspaceCoordinates K e A hA i := by
  simpa only [MvPolynomial.smul_eq_C_mul] using
    normalizedChartSubspaceCoordinates_reconstruct K e A hA b

theorem polynomialSubspaceRestriction_normalizedChart
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    polynomialSubspaceRestriction K e
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) p) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H
        (normalizedChartSubspaceCoordinates K e A hA))
        (polynomialSubspaceRestriction K e p) :=
  normalizedRealPolynomialChart_linear_restriction H A _ _
    (normalizedChartSubspaceCoordinates_reconstruct_C K e A hA) p

theorem polynomialSubspaceRestriction_normalizedChart_eval_eq
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)
    (p q : MvPolynomial (U ⊕ B) ℝ)
    (h : polynomialSubspaceRestriction K e p = polynomialSubspaceRestriction K e q)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) (aeval (R := ℝ) (normalizedRealPolynomialChart H A) p) =
      eval (Sum.elim u b) (aeval (R := ℝ) (normalizedRealPolynomialChart H A) q) := by
  apply polynomialSubspaceRestriction_eval_eq K e _ _ _ u b hb
  rw [polynomialSubspaceRestriction_normalizedChart K e H A hA,
    polynomialSubspaceRestriction_normalizedChart K e H A hA, h]

theorem normalizedChart_subspace_decomposition
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)
    (p slow rat : MvPolynomial (U ⊕ B) ℝ)
    (h : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) p =
        eval (Sum.elim (fun i => u i / H i)
          (fun i => b i - eval u (A i))) slow + eval (Sum.elim u b) rat) :
    polynomialSubspaceRestriction K e p =
      aeval (R := ℝ) (normalizedRealPolynomialChart H
        (normalizedChartSubspaceCoordinates K e A hA))
        (polynomialSubspaceRestriction K e slow) +
      polynomialSubspaceRestriction K e rat := by
  have he : polynomialSubspaceRestriction K e p =
      polynomialSubspaceRestriction K e
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) slow + rat) := by
    apply polynomialSubspaceRestriction_eq_of_eval
    intro u b hb
    rw [map_add]
    exact (h u b hb).trans (by
      congr 1
      exact (eval_normalizedRealPolynomialChart_substitution H A u b slow).symm)
  rw [he, map_add, polynomialSubspaceRestriction_normalizedChart]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedMajorTopCoordinates
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (a : Σ j, J j) : MvPolynomial X ℝ :=
  homogeneousComponent (a.1.val + 1)
    (coordinate (LinearMap.proj a.2 : (J a.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly a.1))

theorem majorTranslationTopCoordinates_lowTagged_eq (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    majorTranslationTopCoordinates (lowTaggedWeight J k)
        (fun i => lowTaggedPolynomial J k poly i - C (c i)) i =
      fullTaggedMajorTopCoordinates J poly (lowTaggedIndex J k i) := by
  have hc : homogeneousComponent (lowTaggedWeight J k i)
      (C (c i) : MvPolynomial X ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simpa using lowTaggedWeight_pos J k i
  change homogeneousComponent (lowTaggedWeight J k i)
      (lowTaggedPolynomial J k poly i - C (c i)) =
    homogeneousComponent (lowTaggedWeight J k i) (lowTaggedPolynomial J k poly i)
  rw [map_sub, hc, sub_zero]

theorem lowTaggedMajorChart_rename (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (H : X → ℝ)
    (i : X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) :
    rename (lowTaggedVariableEmbedding J k)
      (normalizedRealPolynomialChart H
        (majorTranslationTopCoordinates (lowTaggedWeight J k)
          (fun i => lowTaggedPolynomial J k poly i - C (c i))) i) =
      normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)
        (lowTaggedVariableEmbedding J k i) := by
  cases i with
  | inl i => simp only [normalizedRealPolynomialChart_inl, lowTaggedVariableEmbedding_inl,
      map_mul, rename_C, rename_X]
  | inr i =>
    simp only [normalizedRealPolynomialChart_inr, lowTaggedVariableEmbedding_inr,
      map_sub, rename_X, rename_rename, majorTranslationTopCoordinates_lowTagged_eq]
    rfl

omit [∀ j, Fintype (J j)] in

theorem fullTaggedMajorChart_homogeneous
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (i : X ⊕ (Σ j, J j)) :
    (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly) i).IsWeightedHomogeneous
      (fullTaggedVariableWeight J) (fullTaggedVariableWeight J i) := by
  cases i with
  | inl x =>
    exact (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inl x)).C_mul _
  | inr a =>
    apply (weightedHomogeneousSubmodule ℝ (fullTaggedVariableWeight J) (a.1.val + 1)).sub_mem
      (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr a))
    apply majorParameterRename_homogeneous (fun _ : X => 1)
      (fun a : Σ j, J j => a.1.val + 1)
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem lowTaggedVectorExtend_majorChart (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (H : X → ℝ)
    (slow : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ V) :
    lowTaggedVectorExtend J k
        (realChartSubstitute (normalizedRealPolynomialChart H
          (majorTranslationTopCoordinates (lowTaggedWeight J k)
            (fun i => lowTaggedPolynomial J k poly i - C (c i)))) slow) =
      realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
        (lowTaggedVectorExtend J k slow) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub, lowTaggedVectorExtend_eval₂, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute, lowTaggedVectorExtend_eval₂]
  apply sub_eq_zero.mpr
  apply congrArg (fun t => eval₂ t slow)
  funext i
  change MvPolynomial.eval (x ∘ lowTaggedVariableEmbedding J k) _ =
    MvPolynomial.eval x _
  rw [← MvPolynomial.eval_rename, lowTaggedMajorChart_rename]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

omit [∀ j, Fintype (J j)] in
theorem fullTaggedMajorTopCoordinates_coefficients_mem_of_all
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j) :
    ∀ ex j, (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff ex) ∈ U j := by
  intro ex j
  classical
  simp only [fullTaggedMajorTopCoordinates, coeff_homogeneousComponent]
  split_ifs with h
  · simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, LinearMap.proj_apply] using hm j ex
  · exact (U j).zero_mem

theorem RationalTaggedConstraintCertificate.exists_actual_normalized_chart_coordinates
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {blocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p blocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (blocks : ℝ) ≤ p)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hret : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j) :
    ∃ (n : Fin m → ℕ) (Ktag : Submodule ℝ ((Σ j, J j) → ℝ))
      (b : Basis (Σ j, Fin (n j)) ℝ Ktag)
      (matrix : (Σ j, Fin (n j)) → (Σ j, J j) → ℚ)
      (A' : (Σ j, Fin (n j)) → MvPolynomial X ℝ),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ a x, (b a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ)) ∧
      (∀ a x, x.1 ≠ a.1 → matrix a x = 0) ∧
      (∀ a x, rationalLogHeight (matrix a x) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} ∧
      (∀ ex, (fun x => (fullTaggedMajorTopCoordinates J poly x).coeff ex) ∈ Ktag) ∧
      ∀ (H : X → ℝ) (P : MvPolynomial (X ⊕ (Σ j, J j)) ℝ),
        polynomialSubspaceRestriction Ktag b
          (aeval (R := ℝ) (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)) P) =
        aeval (R := ℝ) (normalizedRealPolynomialChart H A')
          (polynomialSubspaceRestriction Ktag b P) := by
  obtain ⟨n, Ktag, b, matrix, hn, hb, hzero, hheight, hK, _⟩ :=
    hcert.exists_bounded_chart_tag_basis hp hdim hblocks
  have hA : ∀ ex, (fun x => (fullTaggedMajorTopCoordinates J poly x).coeff ex) ∈ Ktag :=
    retained_tag_polynomial_coefficients_mem K Ktag hK U hret
      (fullTaggedMajorTopCoordinates J poly) (fullTaggedMajorTopCoordinates_coefficients_mem_of_all J U poly hm)
  refine ⟨n, Ktag, b, matrix,
    normalizedChartSubspaceCoordinates Ktag b (fullTaggedMajorTopCoordinates J poly) hA,
    hn, hb, hzero, hheight, hK, hA, ?_⟩
  intro H P
  exact polynomialSubspaceRestriction_normalizedChart Ktag b H
    (fullTaggedMajorTopCoordinates J poly) hA P

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem fullTaggedMajorTopCoordinates_coefficients_mem_tag
    {m : ℕ} {X : Type*} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (α : X →₀ ℕ) (j : Fin m) :
    (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) ∈ U j := by
  classical
  by_cases hα : α.degree = j.val + 1
  · have hne : α ≠ 0 := by
      intro hz
      simp [hz] at hα
    have heq : (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) =
        coefficients (poly j) α := by
      funext i
      rw [fullTaggedMajorTopCoordinates, MvPolynomial.coeff_homogeneousComponent,
        ite_eq_left hα, coeff_coordinate]
      rfl
    rw [heq]
    exact hcoeff j α hne
  · have heq : (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) = 0 := by
      funext i
      rw [fullTaggedMajorTopCoordinates, MvPolynomial.coeff_homogeneousComponent, ite_eq_right hα]
      rfl
    rw [heq]
    exact (U j).zero_mem

theorem fullTaggedMajorTopCoordinates_coefficients_mem
    {m : ℕ} {X : Type*} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (K : Submodule ℝ ((Σ j, J j) → ℝ))
    (hU : ∀ x, (∀ j, (fun i => x ⟨j, i⟩) ∈ U j) → x ∈ K)
    (α : X →₀ ℕ) :
    (fun a => (fullTaggedMajorTopCoordinates J poly a).coeff α) ∈ K := by
  apply hU
  exact fun j => fullTaggedMajorTopCoordinates_coefficients_mem_tag J poly U hcoeff α j

end Erdos3.VectorPolynomial

end

end OAI
