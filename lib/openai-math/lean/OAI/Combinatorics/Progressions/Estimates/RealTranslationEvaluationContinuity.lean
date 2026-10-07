import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.MvPolynomial
import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationRealBCHCoordinates

namespace OAI

section

namespace Erdos3

open MvPolynomial Module
open scoped TensorProduct

theorem continuous_weightedSupportLE_eval {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ) :
    let := moduleTopology ℝ (weightedSupportLE (R := ℝ) w n)
    Continuous fun z : weightedSupportLE (R := ℝ) w n × (σ → ℝ) =>
      eval z.2 z.1.val := by
  classical
  let W := weightedSupportLE (R := ℝ) w n
  let instTopoW : TopologicalSpace W := moduleTopology ℝ W
  let instFiniteW : Module.Finite ℝ W := weightedSupportLE_moduleFinite w hw n
  let b := Module.finBasis ℝ W
  have hb : Continuous fun z : W × (σ → ℝ) =>
      ∑ i, b.repr z.1 i * eval z.2 (b i).val := by
    apply continuous_finsetSum
    intro i _
    exact ((IsModuleTopology.continuous_of_linearMap
      ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_fst).mul
      ((MvPolynomial.continuous_eval (b i).val).comp continuous_snd)
  convert hb using 1
  ext z
  have h := congrArg (fun Q : W => eval z.2 Q.val) (b.sum_repr z.1)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eval,
    smul_eq_mul] using h.symm

theorem continuous_polynomialShearExp_eval {σ X : Type*} [Fintype σ]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X] [FiniteDimensional ℝ X]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (D : X →ₗ[ℝ] PolynomialShearLieAlgebra w ℝ) (P : MvPolynomial σ ℝ) :
    Continuous fun z : X × (σ → ℝ) => eval z.2 (polynomialShearExp (D z.1) P) := by
  classical
  let n := P.weightedTotalDegree w
  let W := weightedSupportLE (R := ℝ) w n
  let instFiniteW : Module.Finite ℝ W := weightedSupportLE_moduleFinite w hw n
  let instTopoW : TopologicalSpace W := moduleTopology ℝ W
  let instTopAddW : IsTopologicalAddGroup W := IsModuleTopology.isTopologicalAddGroup ℝ W
  let p : W := ⟨P, (mem_weightedSupportLE_iff w n P).mpr le_rfl⟩
  let L : X →ₗ[ℝ] Module.End ℝ W :=
    { toFun := fun x => polynomialShearEnd (D x) n
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro Q
        apply Subtype.ext
        change (D (x + y)).val Q.val = _
        rw [map_add]
        rfl
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro Q
        apply Subtype.ext
        change (D (c • x)).val Q.val = _
        rw [map_smul]
        rfl }
  let instModuleTopoX : IsModuleTopology ℝ X := isModuleTopologyOfFiniteDimensional
  have hL : Continuous (fun z : X × W => L z.1 z.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left L
  have hpower (k : ℕ) : Continuous fun x : X => (L x ^ k) p := by
    induction k with
    | zero => simpa only [pow_zero, Module.End.one_apply] using
        (continuous_const : Continuous fun _ : X => p)
    | succ k ih =>
      simpa only [pow_succ', Module.End.mul_apply, Function.comp_def, id_eq] using
        hL.comp (continuous_id.prodMk ih)
  have hexp : Continuous fun x : X =>
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹) • (L x ^ k) p := by
    apply continuous_finsetSum
    intro k _
    exact (hpower k).const_smul ((k.factorial : ℝ)⁻¹)
  have heval := (continuous_weightedSupportLE_eval w hw n).comp
    ((hexp.comp continuous_fst).prodMk continuous_snd)
  convert heval using 1
  ext z
  rw [polynomialShearExp_eq_sum (D z.1) p.property]
  simp only [Function.comp_apply, Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show ((L z.1 ^ k) p : MvPolynomial σ ℝ) =
    ((D z.1).val.toLinearMap ^ k) P from polynomialShearEnd_pow_coe _ _ _ _]
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [smul_eval, Rat.cast_inv, Rat.cast_natCast]
  rfl

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem bchRealTranslationHom_polynomial_eval (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group)
    (a : σ → ℝ) :
    eval a (bchRealTranslationHom w d hwd g).polynomial =
      -eval (Sum.elim a (fun _ : Unit => (0 : ℝ)))
        (polynomialShearExp (-realShearEmbedding w d g.coord) (X (Sum.inr ()))) := by
  have h := PolynomialTranslationGroupOver.action_inverse_X_inr_eval
    (bchRealTranslationHom w d hwd g) a 0
  have hi : (PolynomialTranslationGroupOver.actionMonoidHom
      (bchRealTranslationHom w d hwd g)).symm =
      PolynomialTranslationGroupOver.actionMonoidHom
        (bchRealTranslationHom w d hwd g⁻¹) := by
    rw [map_inv]
    exact (map_inv PolynomialTranslationGroupOver.actionMonoidHom _).symm
  rw [hi, bchRealTranslationHom_action] at h
  change eval (Sum.elim a (fun _ : Unit => (0 : ℝ)))
    (polynomialShearExp (realShearEmbedding w d (-g.coord)) (X (Sum.inr ()))) =
    0 - eval a (bchRealTranslationHom w d hwd g).polynomial at h
  rw [map_neg] at h
  linarith

theorem continuous_bchRealTranslationHom_polynomial_eval
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)] :
    Continuous fun z : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (σ → ℝ) =>
      eval z.2 (bchRealTranslationHom w d hwd ⟨z.1⟩).polynomial := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  have hpos : ∀ i, 0 < shearWeight w d i := by
    intro i
    cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  have hc := continuous_polynomialShearExp_eval (shearWeight w d) hpos
    (-(realShearEmbedding w d).toLinearMap) (X (Sum.inr ()))
  have he : Continuous fun z : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (σ → ℝ) =>
      (z.1, Sum.elim z.2 (fun _ : Unit => (0 : ℝ))) := by
    apply continuous_fst.prodMk
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact (continuous_apply i).comp continuous_snd
    | inr _ => exact continuous_const
  convert (hc.comp he).neg using 1
  ext z
  exact bchRealTranslationHom_polynomial_eval w d hwd ⟨z.1⟩ z.2

theorem continuous_bchRealTranslationHom_base
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)] :
    Continuous fun x : ℝ ⊗[ℚ] weightedSubalgebra w d =>
      (bchRealTranslationHom w d hwd ⟨x⟩).base := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  have hpos : ∀ i, 0 < shearWeight w d i := by
    intro i
    cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  apply continuous_pi
  intro i
  have hc := continuous_polynomialShearExp_eval (shearWeight w d) hpos
    (realShearEmbedding w d).toLinearMap (X (Sum.inl i))
  have he := hc.comp (continuous_id.prodMk
    (continuous_const : Continuous fun _ : ℝ ⊗[ℚ] weightedSubalgebra w d =>
      (0 : σ ⊕ Unit → ℝ)))
  convert he using 1
  ext x
  have ha := bchRealTranslationHom_action w d hwd ⟨x⟩
  have hx := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℝ ≃ₐ[ℝ]
    MvPolynomial (σ ⊕ Unit) ℝ => eval 0 (f (X (Sum.inl i)))) ha
  change eval 0 (PolynomialTranslationGroupOver.actionHom
    (bchRealTranslationHom w d hwd ⟨x⟩) (X (Sum.inl i))) =
    eval 0 (polynomialShearExp (realShearEmbedding w d x) (X (Sum.inl i))) at hx
  simpa only [PolynomialTranslationGroupOver.actionHom_X_inl, map_add, eval_X,
    Pi.zero_apply, eval_C, zero_add, Function.comp_apply, id_eq, LieHom.coe_toLinearMap] using hx

end PolynomialTranslationLie
end Erdos3

end

end OAI
