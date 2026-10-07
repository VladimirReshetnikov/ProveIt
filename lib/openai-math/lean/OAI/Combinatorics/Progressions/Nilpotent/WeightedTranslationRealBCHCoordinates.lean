import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Estimates.TranslationShearExponentialOver
import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationBaseGrading
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTranslationExponentialSeries

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem exponentialElement_action_eq_shear (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) :
    PolynomialTranslationGroup.actionMonoidHom
      (PolynomialTranslationGroup.exponentialElement x.val.base x.val.polynomial) =
      (polynomialShearExpAut (weightedShearEmbedding w d x)).val := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
      change PolynomialTranslationGroup.actionHom _ (X (Sum.inl i)) =
        (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inl i))
      rw [PolynomialTranslationGroup.actionHom_X_inl, weightedShearExp_X_inl]
      rfl
  | inr u =>
      cases u
      change PolynomialTranslationGroup.actionHom _ (X (Sum.inr ())) =
        (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inr ()))
      rw [PolynomialTranslationGroup.actionHom_X_inr,
        weightedShearExp_X_inr w d x (d+1) (Nat.le_succ d)]
      congr 2
      exact polynomialTranslate_exponentialCoordinate_series w hw x.val.base
        (weightedSupportDrop_le x.property.2)

noncomputable def bchTranslationHom (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).Group →* PolynomialTranslationGroup σ where
  toFun g := PolynomialTranslationGroup.exponentialElement g.coord.val.base g.coord.val.polynomial
  map_one' := by
    apply PolynomialTranslationGroup.actionMonoidHom_injective
    change PolynomialTranslationGroup.actionMonoidHom
      (PolynomialTranslationGroup.exponentialElement (0 : weightedSubalgebra w d).val.base
        (0 : weightedSubalgebra w d).val.polynomial) = PolynomialTranslationGroup.actionMonoidHom 1
    rw [exponentialElement_action_eq_shear w d hw 0]
    change (weightedShearGroupHom w d hwd 1).val = PolynomialTranslationGroup.actionMonoidHom 1
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply PolynomialTranslationGroup.actionMonoidHom_injective
    rw [map_mul, exponentialElement_action_eq_shear w d hw,
      exponentialElement_action_eq_shear w d hw, exponentialElement_action_eq_shear w d hw]
    change (weightedShearGroupHom w d hwd (g*h)).val =
      (weightedShearGroupHom w d hwd g).val * (weightedShearGroupHom w d hwd h).val
    rw [map_mul]
    rfl

@[simp] theorem bchTranslationHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchTranslationHom w d hw hwd g =
      PolynomialTranslationGroup.exponentialElement g.coord.val.base g.coord.val.polynomial := rfl

@[simp] theorem bchTranslationHom_action (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    PolynomialTranslationGroup.actionMonoidHom (bchTranslationHom w d hw hwd g) =
      (weightedShearGroupHom w d hwd g).val :=
  exponentialElement_action_eq_shear w d hw g.coord

theorem bchTranslationHom_injective (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    Function.Injective (bchTranslationHom w d hw hwd) := by
  intro g h heq
  apply weightedShearGroupHom_injective w d hwd
  apply Subtype.ext
  rw [← bchTranslationHom_action w d hw hwd, ← bchTranslationHom_action w d hw hwd, heq]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open MvPolynomial

private theorem eval_translate_rational {σ : Type*} (z h : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    eval z (polynomialTranslate h P) = eval (z + h) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Pi.add_apply]

theorem polynomialExponentialCoordinate_eval_potential_on_submodule
    {σ : Type*} [Fintype σ] (K : Submodule ℚ (σ → ℚ))
    (x : σ → ℚ) (hx : x ∈ K) (P V : MvPolynomial σ ℚ)
    (hderiv : ∀ z ∈ K, eval z (scalarDirectionalDerivative x V) = eval z P)
    (z : σ → ℚ) (hz : z ∈ K) :
    eval z (polynomialExponentialCoordinate x P) = eval z V - eval (z - x) V := by
  classical
  let A : (Fin 2 → ℚ) →ₗ[ℚ] (σ → ℚ) :=
    { toFun := fun t => t 0 • x + t 1 • z
      map_add' := by intros; simp only [Pi.add_apply, add_smul]; abel
      map_smul' := by
        intros
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul] }
  have hAx : A ![1, 0] = x := by simp [A]
  have hAz : A ![0, 1] = z := by simp [A]
  have hAK (t : Fin 2 → ℚ) : A t ∈ K :=
    K.add_mem (K.smul_mem _ hx) (K.smul_mem _ hz)
  have hres : scalarDirectionalDerivative ![1, 0] (polynomialLinearRestriction A V) =
      polynomialLinearRestriction A P := by
    apply MvPolynomial.funext
    intro t
    rw [scalarDirectionalDerivative_linearRestriction, hAx,
      eval_polynomialLinearRestriction, eval_polynomialLinearRestriction]
    exact hderiv _ (hAK t)
  have h := polynomialLinearRestriction_exponentialCoordinate A ![1, 0] P
  rw [hAx, ← hres, polynomialExponentialCoordinate_potential] at h
  have he := congrArg (eval ![0, 1]) h
  rw [eval_polynomialLinearRestriction, hAz, map_sub,
    eval_polynomialLinearRestriction, hAz, eval_translate_rational,
    eval_polynomialLinearRestriction, map_add, map_neg, hAz, hAx] at he
  simpa only [sub_eq_add_neg] using he

namespace PolynomialTranslationLie

theorem bchTranslationHom_eval_potential_on_base_image
    {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map baseLinear,
      eval z (scalarDirectionalDerivative x.base V) = eval z x.polynomial)
    (g : (weightedFiltration w d hwd).Group) (hg : g.coord.val ∈ U)
    (z : σ → ℚ) (hz : z ∈ U.toSubmodule.map baseLinear) :
    eval z (bchTranslationHom w d hw hwd g).polynomial =
      eval z V - eval (z - (bchTranslationHom w d hw hwd g).base) V := by
  exact polynomialExponentialCoordinate_eval_potential_on_submodule
    (U.toSubmodule.map baseLinear) g.coord.val.base ⟨g.coord.val, hg, rfl⟩
    g.coord.val.polynomial V (hderiv _ hg) z hz

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

theorem existsUnique_bchRealTranslation (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    ∃! q : PolynomialTranslationGroupOver ℝ σ,
      PolynomialTranslationGroupOver.actionMonoidHom q = (weightedShearRealGroupHom w d hwd g).val := by
  obtain ⟨b, P, hb, hP⟩ := realShearEmbedding_shape w d g.coord
  exact existsUnique_translation_of_shear_exp (realShearEmbedding w d g.coord) b P hb hP

noncomputable def bchRealTranslationElement (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver ℝ σ :=
  (existsUnique_bchRealTranslation w d hwd g).exists.choose

theorem bchRealTranslationElement_action (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationElement w d hwd g) =
      (weightedShearRealGroupHom w d hwd g).val :=
  (existsUnique_bchRealTranslation w d hwd g).exists.choose_spec

noncomputable def bchRealTranslationHom (w : σ → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).realification.Group →* PolynomialTranslationGroupOver ℝ σ where
  toFun := bchRealTranslationElement w d hwd
  map_one' := by
    apply PolynomialTranslationGroupOver.actionMonoidHom_injective
    rw [bchRealTranslationElement_action, map_one, map_one]
    rfl
  map_mul' g h := by
    apply PolynomialTranslationGroupOver.actionMonoidHom_injective
    rw [map_mul, bchRealTranslationElement_action, bchRealTranslationElement_action,
      bchRealTranslationElement_action, map_mul]
    rfl

@[simp] theorem bchRealTranslationHom_action (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group) :
    PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationHom w d hwd g) =
      (weightedShearRealGroupHom w d hwd g).val :=
  bchRealTranslationElement_action w d hwd g

theorem bchRealTranslationHom_injective (w : σ → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d) :
    Function.Injective (bchRealTranslationHom w d hwd) := by
  intro g h heq
  apply weightedShearRealGroupHom_injective w d hwd
  apply Subtype.ext
  rw [← bchRealTranslationHom_action, ← bchRealTranslationHom_action, heq]

theorem bchRealTranslationHom_rational (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchRealTranslationHom w d hwd (NilpotentLieBCHGroup.realificationHom g) =
      PolynomialTranslationGroupOver.map (algebraMap ℚ ℝ)
        (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  have hrat : PolynomialTranslationGroupOver.actionMonoidHom
      (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) =
      (weightedShearGroupHom w d hwd g).val := by
    rw [PolynomialTranslationGroupOver.rationalEquiv_action, bchTranslationHom_action]
  have hmap := PolynomialTranslationGroupOver.map_actionHom (algebraMap ℚ ℝ)
    (PolynomialTranslationGroupOver.rationalEquiv (bchTranslationHom w d hw hwd g)) (X i)
  have hreal := weightedShearRealGroupHom_rational w d hwd g (X i)
  simp only [MvPolynomial.map_X] at hmap hreal
  change (weightedShearRealGroupHom w d hwd
    (NilpotentLieBCHGroup.realificationHom g)).val (X i) =
    PolynomialTranslationGroupOver.actionHom _ (X i)
  rw [hreal, ← hmap]
  congr 1
  exact (congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
    MvPolynomial (σ ⊕ Unit) ℚ => f (X i)) hrat).symm

end Erdos3.PolynomialTranslationLie

end

end OAI
