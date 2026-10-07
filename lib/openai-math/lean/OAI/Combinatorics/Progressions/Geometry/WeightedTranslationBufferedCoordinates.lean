/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.BufferedTranslationIncrement

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem weightedShearEmbedding_coordinate_row (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : PolynomialShearIndex (shearWeight w d)) :
    (∀ x, (polynomialShearBasis (R := ℚ) (shearWeight w d)).repr
      (weightedShearEmbedding w d x) a = 0) ∨
    ∃ i : WeightedBasisIndex w d, ∀ x,
      (polynomialShearBasis (R := ℚ) (shearWeight w d)).repr
        (weightedShearEmbedding w d x) a = (weightedBasis w d hw).repr x i := by
  classical
  rcases a with ⟨i, a, ha⟩
  cases i with
  | inl i =>
      by_cases ha0 : a = 0
      · right
        refine ⟨Sum.inl i, fun x => ?_⟩
        rw [polynomialShearBasis_repr, weightedBasis_repr_inl]
        change (shearDerivation x.val (X (Sum.inl i))).coeff a = _
        rw [shearDerivation_X_inl, ha0]
        simp
      · left
        intro x
        rw [polynomialShearBasis_repr]
        change (shearDerivation x.val (X (Sum.inl i))).coeff a = 0
        rw [shearDerivation_X_inl]
        simp [MvPolynomial.coeff_C, Ne.symm ha0]
  | inr u =>
      by_cases hb : ∃ b : σ →₀ ℕ, b.mapDomain Sum.inl = a
      · obtain ⟨b, rfl⟩ := hb
        have hweight : Finsupp.weight (shearWeight w d) (b.mapDomain Sum.inl) =
            Finsupp.weight w b := by
          change Finsupp.linearCombination ℕ (shearWeight w d) (b.mapDomain Sum.inl) =
            Finsupp.linearCombination ℕ w b
          rw [Finsupp.linearCombination_mapDomain]
          rfl
        have hb : Finsupp.weight w b < d := by
          change Finsupp.weight (shearWeight w d) (b.mapDomain Sum.inl) + 1 ≤ d at ha
          rw [hweight] at ha
          omega
        right
        refine ⟨Sum.inr ⟨b, hb⟩, fun x => ?_⟩
        rw [polynomialShearBasis_repr, weightedBasis_repr_inr]
        change (shearDerivation x.val (X (Sum.inr u))).coeff (b.mapDomain Sum.inl) = _
        rw [shearDerivation_X_inr, coeff_rename_mapDomain Sum.inl Sum.inl_injective]
      · left
        intro x
        rw [polynomialShearBasis_repr]
        change (shearDerivation x.val (X (Sum.inr u))).coeff a = 0
        rw [shearDerivation_X_inr]
        apply coeff_rename_eq_zero
        intro b hba
        exact (hb ⟨b, hba⟩).elim

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem realificationLieHom_repr_zero (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (k : κ) (h : ∀ x, e.repr (φ x) k = 0) (x : ℝ ⊗[ℚ] L) :
    (e.baseChange ℝ).repr (realificationLieHom φ x) k = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul, h, zero_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

theorem realificationLieHom_repr_coordinate (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (k : κ) (i : ι)
    (h : ∀ x, f.repr (φ x) k = e.repr x i) (x : ℝ ⊗[ℚ] L) :
    (f.baseChange ℝ).repr (realificationLieHom φ x) k = (e.baseChange ℝ).repr x i := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul, h]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem realShearEmbedding_repr (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (a : PolynomialShearIndex (shearWeight w d)) :
    (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a =
      ((polynomialShearBasis (R := ℚ) (shearWeight w d)).baseChange ℝ).repr
        (realificationLieHom (weightedShearEmbedding w d) x) a := by
  exact congrArg (fun c => c a) (polynomialShearRealificationEquiv_repr (shearWeight w d)
    (realificationLieHom (weightedShearEmbedding w d) x))

theorem realShearEmbedding_coordinate_row (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : PolynomialShearIndex (shearWeight w d)) :
    (∀ x, (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (realShearEmbedding w d x) a = 0) ∨
    ∃ i : WeightedBasisIndex w d, ∀ x,
      (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
        (realShearEmbedding w d x) a = ((weightedBasis w d hw).baseChange ℝ).repr x i := by
  rcases weightedShearEmbedding_coordinate_row w d hw a with hzero | ⟨i, hi⟩
  · left
    intro x
    rw [realShearEmbedding_repr]
    exact realificationLieHom_repr_zero (polynomialShearBasis (shearWeight w d))
      (weightedShearEmbedding w d) a hzero x
  · right
    refine ⟨i, fun x => ?_⟩
    rw [realShearEmbedding_repr]
    exact realificationLieHom_repr_coordinate (weightedBasis w d hw)
      (polynomialShearBasis (shearWeight w d)) (weightedShearEmbedding w d) a i hi x

theorem realShearEmbedding_coordinate_abs_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, |((weightedBasis w d hw).baseChange ℝ).repr x i| ≤ δ)
    (a : PolynomialShearIndex (shearWeight w d)) :
    |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a| ≤
      δ := by
  rcases realShearEmbedding_coordinate_row w d hw a with hzero | ⟨i, hi⟩
  · simpa only [hzero x, abs_zero] using hδ
  · rw [hi x]
    exact hx i

theorem realShearEmbedding_coefficient_abs_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, |((weightedBasis w d hw).baseChange ℝ).repr x i| ≤ δ)
    (i : σ ⊕ Unit) (a : (σ ⊕ Unit) →₀ ℕ) :
    |((realShearEmbedding w d x).val (MvPolynomial.X i)).coeff a| ≤ δ := by
  by_cases ha : Finsupp.weight (shearWeight w d) a + 1 ≤ shearWeight w d i
  · exact realShearEmbedding_coordinate_abs_le w d hw x hδ hx ⟨i, a, ha⟩
  · have hz : ((realShearEmbedding w d x).val (MvPolynomial.X i)).coeff a = 0 := by
      by_contra hne
      exact ha ((realShearEmbedding w d x).property i (MvPolynomial.mem_support_iff.mpr hne))
    simpa only [hz, abs_zero] using hδ

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ]

theorem bchRealTranslation_inverse_action_X (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group)
    (i : σ ⊕ Unit) :
    (PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationHom w d hwd g)).symm (X i) =
      polynomialShearExp (-(realShearEmbedding w d g.coord)) (X i) := by
  calc
    _ = PolynomialTranslationGroupOver.actionMonoidHom
        (bchRealTranslationHom w d hwd g⁻¹) (X i) := by
      rw [map_inv, map_inv]
      rfl
    _ = (weightedShearRealGroupHom w d hwd g⁻¹).val (X i) := by
      rw [bchRealTranslationHom_action]
    _ = _ := by
      change polynomialShearExp (realShearEmbedding w d g⁻¹.coord) (X i) = _
      rw [coord_inv, map_neg]

theorem bchRealTranslation_bounds_of_shear_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hg : ∀ a, |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (realShearEmbedding w d g.coord) a| ≤ δ) :
    let K := polynomialShearDisplacementBound d (Fintype.card (σ ⊕ Unit)) 1
    (∀ i, |(bchRealTranslationHom w d hwd g).base i| ≤ (K : ℝ) * δ) ∧
      ∀ x : σ → ℝ, (∀ i, |x i| ≤ 1) →
        |eval x (bchRealTranslationHom w d hwd g).polynomial| ≤ (K : ℝ) * δ := by
  let K := polynomialShearDisplacementBound d (Fintype.card (σ ⊕ Unit)) 1
  have hpos : ∀ i, 1 ≤ shearWeight w d i := by
    intro i; cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  have hgn (a) : |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (-(realShearEmbedding w d g.coord)) a| ≤ δ := by
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hg a
  have hpoint (x : σ → ℝ) (hx : ∀ i, |x i| ≤ 1) (i : σ ⊕ Unit) :
      |eval (Sum.elim x (fun _ : Unit => (0 : ℝ)))
        ((PolynomialTranslationGroupOver.actionMonoidHom
          (bchRealTranslationHom w d hwd g)).symm (X i)) -
        Sum.elim x (fun _ : Unit => (0 : ℝ)) i| ≤ (K : ℝ) * δ := by
    rw [bchRealTranslation_inverse_action_X]
    have hh := polynomialShearExp_X_displacement (-(realShearEmbedding w d g.coord))
      hpos (shearWeight_le w d hwd) hδ hδone le_rfl hgn
      (Sum.elim x (fun _ : Unit => (0 : ℝ))) (by
        intro j; cases j with
        | inl j => exact hx j
        | inr _ => simp) i
    convert hh using 1
    · simp only [aeval_eq_eval]
    · simp [K, polynomialShearDisplacementBound, mul_assoc, mul_left_comm, mul_comm]
  constructor
  · intro i
    have hh := hpoint 0 (by simp) (Sum.inl i)
    rw [PolynomialTranslationGroupOver.action_inverse_X_inl_eval] at hh
    simpa [K] using hh
  · intro x hx
    have hh := hpoint x hx (Sum.inr ())
    rw [PolynomialTranslationGroupOver.action_inverse_X_inr_eval] at hh
    simpa [K] using hh

section Metric

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  [Fintype (WeightedBasisIndex w d)]
  [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedBasis_real_log_coordinates_bound (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    let C := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
    (C : ℝ) * dist 1 g < 1 →
      ∀ a, |((weightedBasis w d hw).baseChange ℝ).repr g.coord a| ≤ (C : ℝ) * dist 1 g := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
  dsimp only
  intro hnear a
  have hlog : ‖basisHomeomorph ((weightedOrderedBasis w d hw).baseChange ℝ) g‖ ≤
      (C : ℝ) * dist 1 g := by
    have hh := norm_coordinates_le_of_near_one
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
      (lieStructureConstants (weightedOrderedBasis w d hw))
      (fun i j k => (realLieBasis_structure (weightedOrderedBasis w d hw) i j k).symm)
      (weightedOrderedBasis_structure_height w d hw) 1 le_rfl g
    simp only [Fintype.card_fin, NNReal.coe_one] at hh
    exact hh hnear
  have hh := (norm_le_pi_norm
    (basisHomeomorph ((weightedOrderedBasis w d hw).baseChange ℝ) g)
    (weightedIndexOrder w d a)).trans hlog
  have he : (weightedOrderedBasis w d hw).baseChange ℝ =
      ((weightedBasis w d hw).baseChange ℝ).reindex (weightedIndexOrder w d) := by
    ext j
    simp only [weightedOrderedBasis, Basis.baseChange_apply, Basis.reindex_apply]
  simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs,
    he, Basis.repr_reindex_apply, Equiv.symm_apply_apply] using hh

noncomputable def weightedTranslationDisplacementConstant (d n m : ℕ) : ℝ :=
  2 * ((polynomialShearDisplacementBound d (n+1) 1 : ℝ) + 1) *
    ((bchLogMetricConstant d m (2*d+1) 1 : ℝ) + 1)

theorem weightedTranslationDisplacementConstant_pos (d n m : ℕ) :
    0 < weightedTranslationDisplacementConstant d n m := by
  unfold weightedTranslationDisplacementConstant
  positivity

theorem bchRealTranslation_bounds_near_one (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    let C := weightedTranslationDisplacementConstant d (Fintype.card σ)
      (Fintype.card (WeightedBasisIndex w d))
    dist 1 g ≤ 1 / C →
      (∀ i, |(bchRealTranslationHom w d hwd g).base i| ≤ C * dist 1 g) ∧
      ∀ x : σ → ℝ, (∀ i, |x i| ≤ 1) →
        |eval x (bchRealTranslationHom w d hwd g).polynomial| ≤ C * dist 1 g := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let K : ℝ := polynomialShearDisplacementBound d (Fintype.card σ + 1) 1
  let L : ℝ := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
  let C := weightedTranslationDisplacementConstant d (Fintype.card σ)
    (Fintype.card (WeightedBasisIndex w d))
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hC : 0 < C := weightedTranslationDisplacementConstant_pos _ _ _
  have hCeq : C = 2 * (K+1) * (L+1) := rfl
  have hLC : 2 * L ≤ C := by nlinarith [mul_nonneg hK hL]
  have hKC : K * L ≤ C := by nlinarith [mul_nonneg hK hL]
  dsimp only
  intro hnear
  have hdist : 0 ≤ dist 1 g := dist_nonneg
  have hCd : C * dist 1 g ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp hnear
    simpa only [mul_comm] using hh
  have hlognear : L * dist 1 g < 1 := by
    have hh := mul_le_mul_of_nonneg_right hLC hdist
    nlinarith
  have hcoords := weightedBasis_real_log_coordinates_bound w d hw hwd g hlognear
  have hshear := realShearEmbedding_coordinate_abs_le w d hw g.coord
    (mul_nonneg hL hdist) hcoords
  have hbounds := bchRealTranslation_bounds_of_shear_coordinates w d hw hd hwd g
    (mul_nonneg hL hdist) hlognear.le hshear
  have hprod : K * (L * dist 1 g) ≤ C * dist 1 g := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hKC hdist
  constructor
  · intro i
    apply le_trans ?_ hprod
    simpa [K] using hbounds.1 i
  · intro x hx
    apply le_trans ?_ hprod
    simpa [K] using hbounds.2 x hx

end Metric

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped NNReal TensorProduct

variable {m : ℕ}

theorem buffered_translation_term_of_shear_coordinates
    (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    {M : ℝ} (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (z g : (weightedFiltration w d hwd).realification.Group)
    (β : Fin m → ℤ) {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hz : ∀ a, |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (realShearEmbedding w d z.coord) a| ≤ δ)
    (hsmall : (polynomialShearDisplacementBound d (Fintype.card (Fin m ⊕ Unit)) 1 : ℝ) * δ ≤ 1 / 4) :
    ‖bufferedTranslationTerm Ψ D₀ (bchRealTranslationHom w d hwd (z * g)) β -
      bufferedTranslationTerm Ψ D₀ (bchRealTranslationHom w d hwd g) β‖ ≤
      (Ψ.lip + (2 * Real.pi) * (1 + M * m * d)) *
        (polynomialShearDisplacementBound d (Fintype.card (Fin m ⊕ Unit)) 1 : ℝ) * δ := by
  obtain ⟨hbase, heval⟩ := bchRealTranslation_bounds_of_shear_coordinates w d hw hd hwd
    z hδ hδone hz
  rw [map_mul]
  have h := bufferedTranslationTerm_increment_bound Ψ D₀
    (bchRealTranslationHom w d hwd z) (bchRealTranslationHom w d hwd g) β
    (mul_nonneg (NNReal.coe_nonneg _) hδ) hsmall hdegree hD hbase heval
  exact h.trans_eq (by ring)

end Erdos3.PolynomialTranslationLie

end

end OAI
