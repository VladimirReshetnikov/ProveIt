import OAI.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
import OAI.Combinatorics.Progressions.Estimates.SeparatedPositiveSum
import OAI.Combinatorics.Progressions.Estimates.UnitRangeLocalLipschitz
import OAI.Combinatorics.Progressions.Geometry.SpatialOutputChoice
import OAI.Combinatorics.Progressions.Geometry.SupportedBoxLipschitz
import OAI.Combinatorics.Progressions.Nilpotent.PolynomialShearNilmanifold
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse

namespace OAI

section

namespace Erdos3

theorem shifted_power_le_fixed_base {p : ℝ} (hp : 0 ≤ p) (C : ℕ) (hC : 2 ≤ C) :
    (p + C) ^ C ≤ (p + 2) ^ ((C + 1) * C) := by
  have hbase : 0 ≤ p + 2 := by linarith
  have hpTerm : p ≤ (p + 2) ^ C := le_power_budget hp (by omega)
  have htwo : (C : ℝ) ≤ (2 : ℝ) ^ C := by
    exact_mod_cast (show C < 2 ^ C from Nat.lt_two_pow_self).le
  have hCTerm : (C : ℝ) ≤ (p + 2) ^ C :=
    htwo.trans (pow_le_pow_left₀ (by norm_num) (by linarith) C)
  have hsum : p + C ≤ (p + 2) ^ (C + 1) := by
    calc
      _ ≤ 2 * (p + 2) ^ C := by linarith
      _ ≤ (p + 2) * (p + 2) ^ C :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hbase _)
      _ = _ := (pow_succ' _ _).symm
  calc
    _ ≤ ((p + 2) ^ (C + 1)) ^ C := pow_le_pow_left₀ (by positivity) hsum C
    _ = _ := (pow_mul _ _ _).symm

theorem exists_natPolynomial_fixed_power_budget (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨(C + 1) * C, by nlinarith, ?_⟩
  intro p hp
  exact (hbound p hp).trans (shifted_power_le_fixed_base hp C hC)

theorem exists_natPolynomial_affine_budget (P : Polynomial ℕ) (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) ((A : ℝ) * (p + 1)) ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (P.comp (Polynomial.C A * (Polynomial.X + 1)))
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [Polynomial.eval₂_comp] using hbound p hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def relativeInductionBudgetPolynomial (b₀ c : ℕ) : ℕ → Polynomial ℕ
  | 0 => (Polynomial.X + 2) ^ b₀
  | q + 1 => (2 + (2 + Polynomial.X +
      (relativeInductionBudgetPolynomial b₀ c q).comp ((Polynomial.X + 2) ^ c)) ^ c) ^ c

@[simp] theorem relativeInductionBudgetPolynomial_eval_zero (b₀ c : ℕ) (p : ℝ) :
    (relativeInductionBudgetPolynomial b₀ c 0).eval₂ (Nat.castRingHom ℝ) p = (p + 2) ^ b₀ := by
  simp [relativeInductionBudgetPolynomial, Polynomial.eval₂_pow]

@[simp] theorem relativeInductionBudgetPolynomial_eval_succ (b₀ c q : ℕ) (p : ℝ) :
    (relativeInductionBudgetPolynomial b₀ c (q + 1)).eval₂ (Nat.castRingHom ℝ) p =
      (2 + (2 + p + (relativeInductionBudgetPolynomial b₀ c q).eval₂
        (Nat.castRingHom ℝ) ((p + 2) ^ c)) ^ c) ^ c := by
  simp only [relativeInductionBudgetPolynomial, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_X, Polynomial.eval₂_comp]

theorem relativeInductionBudgetPolynomial_nonneg (b₀ c q : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ (relativeInductionBudgetPolynomial b₀ c q).eval₂ (Nat.castRingHom ℝ) p :=
  natPolynomial_eval_nonneg _ hp

theorem exists_relativeInductionPolynomialBudget (b₀ c maxstage : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ q : ℕ, q ≤ maxstage → ∀ p : ℝ, 0 ≤ p →
      0 ≤ (relativeInductionBudgetPolynomial b₀ c q).eval₂ (Nat.castRingHom ℝ) p ∧
      (relativeInductionBudgetPolynomial b₀ c q).eval₂ (Nat.castRingHom ℝ) p ≤ (p + 2) ^ E := by
  let majorant : Polynomial ℕ :=
    ∑ q ∈ Finset.range (maxstage + 1), relativeInductionBudgetPolynomial b₀ c q
  obtain ⟨E, hE, hbound⟩ := exists_natPolynomial_fixed_power_budget majorant
  refine ⟨E, hE, ?_⟩
  intro q hq p hp
  refine ⟨relativeInductionBudgetPolynomial_nonneg b₀ c q hp, ?_⟩
  apply le_trans _ (hbound p hp)
  dsimp only [majorant]
  rw [Polynomial.eval₂_finsetSum]
  exact Finset.single_le_sum (fun i _ => relativeInductionBudgetPolynomial_nonneg b₀ c i hp)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))

noncomputable def relativeInductionBudgetValue (b₀ c q : ℕ) (p : ℝ) : ℝ :=
  (relativeInductionBudgetPolynomial b₀ c q).eval₂ (Nat.castRingHom ℝ) p

@[simp] theorem relativeInductionBudgetValue_zero (b₀ c : ℕ) (p : ℝ) :
    relativeInductionBudgetValue b₀ c 0 p = (p + 2) ^ b₀ :=
  relativeInductionBudgetPolynomial_eval_zero b₀ c p

@[simp] theorem relativeInductionBudgetValue_succ (b₀ c q : ℕ) (p : ℝ) :
    relativeInductionBudgetValue b₀ c (q + 1) p =
      (2 + (2 + p + relativeInductionBudgetValue b₀ c q ((p + 2) ^ c)) ^ c) ^ c :=
  relativeInductionBudgetPolynomial_eval_succ b₀ c q p

theorem relativeInductionBudgetValue_majorizes (b₀ c maxstage : ℕ)
    (F : ℕ → ℝ → ℝ) (hF : ∀ q p, 0 ≤ p → 0 ≤ F q p)
    (hbase : ∀ p, 0 ≤ p → F 0 p ≤ (p + 2) ^ b₀)
    (hstep : ∀ q, q < maxstage → ∀ p, 0 ≤ p →
      F (q + 1) p ≤ (2 + (2 + p + F q ((p + 2) ^ c)) ^ c) ^ c) :
    ∀ q, q ≤ maxstage → ∀ p, 0 ≤ p → F q p ≤ relativeInductionBudgetValue b₀ c q p := by
  intro q
  induction q with
  | zero =>
    intro _ p hp
    simpa only [relativeInductionBudgetValue_zero] using hbase p hp
  | succ q ih =>
    intro hq p hp
    have hchild : 0 ≤ (p + 2) ^ c := by positivity
    have hFchild := hF q ((p + 2) ^ c) hchild
    have hrec := ih (Nat.le_of_succ_le hq) ((p + 2) ^ c) hchild
    apply (hstep q (Nat.lt_of_succ_le hq) p hp).trans
    rw [relativeInductionBudgetValue_succ]
    apply pow_le_pow_left₀ (by positivity)
    apply add_le_add le_rfl
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add le_rfl hrec

theorem exists_relativeInductionBudget_majorization (b₀ c maxstage : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ F : ℕ → ℝ → ℝ,
      (∀ q p, 0 ≤ p → 0 ≤ F q p) →
      (∀ p, 0 ≤ p → F 0 p ≤ (p + 2) ^ b₀) →
      (∀ q, q < maxstage → ∀ p, 0 ≤ p →
        F (q + 1) p ≤ (2 + (2 + p + F q ((p + 2) ^ c)) ^ c) ^ c) →
      ∀ q, q ≤ maxstage → ∀ p, 0 ≤ p → F q p ≤ (p + 2) ^ E := by
  obtain ⟨E, hE, hbudget⟩ := exists_relativeInductionPolynomialBudget b₀ c maxstage
  refine ⟨E, hE, ?_⟩
  intro F hF hbase hstep q hq p hp
  exact (relativeInductionBudgetValue_majorizes b₀ c maxstage F hF hbase hstep q hq p hp).trans
    (hbudget q hq p hp).2

end Erdos3

end

section

namespace Erdos3

theorem polynomialBudget_four_slack (A : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p+2)^A+4 ≤ (p+2)^(A+3) := by
  have hbase : (2 : ℝ) ≤ p+2 := by linarith
  have hA : (1 : ℝ) ≤ (p+2)^A := one_le_pow₀ (by linarith)
  have hcube : (8 : ℝ) ≤ (p+2)^3 := by
    simpa only [show (2 : ℝ)^3 = 8 by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase 3
  calc
    _ ≤ (p+2)^A*8 := by linarith
    _ ≤ (p+2)^A*(p+2)^3 := mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := (pow_add _ _ _).symm

theorem quarterAccuracy_polynomial_budget (A : ℕ) {p τ : ℝ} (hp : 0 ≤ p)
    (hτ : τ⁻¹ ≤ Real.exp ((p+2)^A)) :
    (τ/4)⁻¹ ≤ Real.exp ((p+2)^(A+3)) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ = 4*τ⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ 4*Real.exp ((p+2)^A) := mul_le_mul_of_nonneg_left hτ (by norm_num)
    _ ≤ Real.exp 4*Real.exp ((p+2)^A) :=
      mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = Real.exp ((p+2)^A+4) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr (polynomialBudget_four_slack A hp)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShearExp_sub_mass (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ A * δ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass (polynomialShearExp D P - P) ≤
      n * δ * (1 + Fintype.card σ * A * n) ^ n * realPolynomialMass P := by
  classical
  let B : ℝ := Fintype.card σ * A * n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpow (k : ℕ) (hk : k < n) :
      realPolynomialMass ((D.val.toLinearMap ^ (k + 1)) P) ≤
        δ * (1 + B) ^ n * realPolynomialMass P := by
    have hmass := polynomialShear_pow_mass D hpos (mul_nonneg hA hδ) hD hP (k + 1)
    have he : (Fintype.card σ : ℝ) * (A * δ) * n = B * δ := by dsimp [B]; ring
    rw [he, mul_pow] at hmass
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ (realPolynomialMass_nonneg P)
    have hd : δ ^ (k + 1) ≤ δ := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hδ (pow_le_one₀ hδ hδone)
    have hb : B ^ (k + 1) ≤ (1 + B) ^ n :=
      (pow_le_pow_left₀ hB (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    calc
      _ ≤ (1 + B) ^ n * δ := mul_le_mul hb hd (pow_nonneg hδ _) (by positivity)
      _ = _ := mul_comm _ _
  rw [polynomialShearExp_eq_sum D hP, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
    one_smul, add_sub_cancel_right]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range n, δ * (1 + B) ^ n * realPolynomialMass P := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← Rat.cast_smul_eq_qsmul ℝ, realPolynomialMass_smul]
      simp only [Rat.cast_inv, Rat.cast_natCast]
      have hf : (1 : ℝ) ≤ (k + 1).factorial := by exact_mod_cast Nat.factorial_pos (k + 1)
      have hc : |((k + 1).factorial : ℝ)⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
        exact inv_le_one_of_one_le₀ hf
      calc
        _ ≤ 1 * realPolynomialMass ((D.val.toLinearMap ^ (k + 1)) P) :=
          mul_le_mul_of_nonneg_right hc (realPolynomialMass_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using hpow k (Finset.mem_range.mp hk)
    _ = _ := by simp [B]; ring

theorem polynomialShearExp_displacement (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {A δ B : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hδone : δ ≤ 1) (hB : 1 ≤ B)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ A * δ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    |aeval x (polynomialShearExp D P) - aeval x P| ≤
      n * δ * (1 + Fintype.card σ * A * n) ^ n * realPolynomialMass P * B ^ n := by
  rw [← map_sub]
  have hdegree := totalDegree_le_of_positive_weightedSupport w hpos
    ((weightedSupportLE w n).sub_mem (polynomialShearExp_degree D hP) hP)
  exact (abs_aeval_le_mass_box _ x hB hx hdegree).trans
    (mul_le_mul_of_nonneg_right (polynomialShearExp_sub_mass D hpos hA hδ hδone hD hP)
      (pow_nonneg (by linarith) _))

theorem polynomialShearExp_X_displacement (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {s : ℕ} (hw : ∀ i, w i ≤ s)
    {δ B : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hB : 1 ≤ B)
    (hD : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr D a| ≤ δ)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) (i : σ) :
    |aeval x (polynomialShearExp D (X i)) - x i| ≤
      s * δ * (1 + Fintype.card σ * ((s + 1) * (Fintype.card σ + 1) ^ s : ℕ) * s) ^ s * B ^ s := by
  have h := polynomialShearExp_displacement D hpos (by positivity) hδ hδone hB
    (polynomialShear_X_mass_of_coordinates D hpos hw hδ hD)
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)) x hx
  simpa only [aeval_X, realPolynomialMass_X, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

def polynomialShearDisplacementBound (s d : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  s * (1 + d * ((s + 1) * (d + 1) ^ s : ℕ) * s) ^ s * B ^ s

theorem polynomialShearRealPointAction_eq_exp (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) (x : σ → ℝ) (i : σ) :
    polynomialShearRealPointAction w s hw g x i =
      aeval x (polynomialShearExp (-(polynomialShearRealificationEquiv w g.coord)) (X i)) := by
  change aeval x ((polynomialShearRealAutEquiv w s hw g).val.symm (X i)) = _
  have he := congrArg (fun e : WeightedLoweringAut w ℝ => aeval x (e.val (X i)))
    (polynomialShearRealAutEquiv_apply w s hw g⁻¹)
  simpa only [map_inv, Subgroup.coe_inv, AlgEquiv.aut_inv, NilpotentLieBCHGroup.coord_inv,
    map_neg, polynomialShearExpAut_apply] using he

theorem polynomialShearRealPointAction_displacement (s : ℕ)
    (hpos : ∀ i, 1 ≤ w i) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) (B : ℝ≥0) (hB : 1 ≤ B)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hg : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w g.coord) a| ≤ δ)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    dist (polynomialShearRealPointAction w s hw g x) x ≤
      (polynomialShearDisplacementBound s (Fintype.card σ) B : ℝ) * δ := by
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) hδ)).mpr
  intro i
  rw [Real.dist_eq, polynomialShearRealPointAction_eq_exp]
  have hgn (a) : |(polynomialShearBasis (R := ℝ) w).repr (-(polynomialShearRealificationEquiv w g.coord)) a| ≤ δ := by
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hg a
  have h := polynomialShearExp_X_displacement (-(polynomialShearRealificationEquiv w g.coord))
    hpos hw hδ hδone (show (1 : ℝ) ≤ B from hB) hgn x hx i
  convert h using 1
  simp only [polynomialShearDisplacementBound, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one,
    Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  ring

variable [Fintype (PolynomialShearIndex w)]

theorem polynomialShearRealification_ordered_repr
    (D : ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w D) a =
      ((polynomialShearOrderedBasis w).baseChange ℝ).repr D (polynomialShearIndexOrder w a) := by
  rw [polynomialShearRealificationEquiv_repr]
  have he : (polynomialShearOrderedBasis w).baseChange ℝ =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).reindex (polynomialShearIndexOrder w) := by
    ext j
    simp only [polynomialShearOrderedBasis, Basis.baseChange_apply, Basis.reindex_apply]
  rw [he, Basis.repr_reindex_apply, Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]

theorem polynomialShearRealPointAction_near_one (s : ℕ)
    (hpos : ∀ i, 1 ≤ w i) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group)
    (B : ℝ≥0) (hB : 1 ≤ B) (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis w).baseChange ℝ)
    let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex w)) (2 * s + 1) 1
    (C : ℝ) * dist 1 g < 1 →
      dist (polynomialShearRealPointAction w s hw g x) x ≤
        (polynomialShearDisplacementBound s (Fintype.card σ) B * C : ℝ≥0) * dist 1 g := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis w).baseChange ℝ)
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex w)) (2 * s + 1) 1
  dsimp only
  intro hnear
  have hc := polynomialShearOrderedBasis_structure_height w s (fun i => lt_of_lt_of_le Nat.zero_lt_one (hpos i)) hw
  have hlog : ‖basisHomeomorph ((polynomialShearOrderedBasis w).baseChange ℝ) g‖ ≤
      (C : ℝ) * dist 1 g := by
    have hr := norm_coordinates_le_of_near_one
      (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis w).baseChange ℝ)
      (lieStructureConstants (polynomialShearOrderedBasis w))
      (fun i j k => (realLieBasis_structure (polynomialShearOrderedBasis w) i j k).symm)
      hc 1 le_rfl g
    simp only [Fintype.card_fin, NNReal.coe_one] at hr
    exact hr hnear
  have hg (a : PolynomialShearIndex w) :
      |(polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w g.coord) a| ≤
        (C : ℝ) * dist 1 g := by
    rw [polynomialShearRealification_ordered_repr]
    have h := (norm_le_pi_norm
      (basisHomeomorph ((polynomialShearOrderedBasis w).baseChange ℝ) g)
      (polynomialShearIndexOrder w a)).trans hlog
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using h
  have h := polynomialShearRealPointAction_displacement w s hpos hw g B hB
    (mul_nonneg C.coe_nonneg dist_nonneg) hnear.le hg x hx
  simpa only [NNReal.coe_mul, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualPoint_lipschitzOn_box (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s) (M B : ℝ≥0)
    (hB : 1 ≤ B) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) :
    LipschitzOnWith ((1 + M) * d * s * B ^ (s * (d + 1)))
      (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom)
      {x | ∀ i, |x i| ≤ B} := by
  have hmass (i : Fin d) : realPolynomialMass (A.topResidualEquiv (X i)) ≤ (1 + M : ℝ≥0) := by
    exact A.topResidualEquiv_X_mass hA i
  have hdegree (i : Fin d) : (A.topResidualEquiv (X i)).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport w hpos
      (A.topResidualEquiv_degree (weightedSupportLE_X w i))).trans (hw i)
  change LipschitzOnWith ((1 + M) * d * s * B ^ (s * (d + 1)))
    (fun x : Fin d → ℝ => fun i => aeval x (A.topResidualEquiv (X i))) _
  simpa only [Fintype.card_fin] using
    lipschitzOn_realPolynomialVector_mass_box (fun i : Fin d => A.topResidualEquiv (X i))
      (1 + M) B hB hmass hdegree

theorem topResidualInversePoint_lipschitzOn_box (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s) (M B : ℝ≥0)
    (hB : 1 ≤ B) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) :
    LipschitzOnWith ((1 + M) ^ (s * d) * d * s * B ^ (s * (d + 1)))
      (polynomialSubstitutionPoint A.topResidualEquiv.symm.toAlgHom)
      {x | ∀ i, |x i| ≤ B} := by
  have hmass (i : Fin d) : realPolynomialMass (A.topResidualEquiv.symm (X i)) ≤
      ((1 + M) ^ (s * d) : ℝ≥0) := by
    exact A.topResidualEquiv_inverse_X_mass hpos s hw M.coe_nonneg hA i
  have hdegree (i : Fin d) : (A.topResidualEquiv.symm (X i)).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport w hpos
      (A.topResidualEquiv_inverse_degree (weightedSupportLE_X w i))).trans (hw i)
  change LipschitzOnWith ((1 + M) ^ (s * d) * d * s * B ^ (s * (d + 1)))
    (fun x : Fin d → ℝ => fun i => aeval x (A.topResidualEquiv.symm (X i))) _
  simpa only [Fintype.card_fin] using
    lipschitzOn_realPolynomialVector_mass_box (fun i : Fin d => A.topResidualEquiv.symm (X i))
      ((1 + M) ^ (s * d)) B hB hmass hdegree

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearKernel_lipschitzOn_box (A : PolynomialPatch σ s d) (M B : ℝ≥0)
    (hB : 1 ≤ B) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    LipschitzOnWith (A.kernel.lip * ((1 + M) * d * s * B ^ (s * (d + 1)))) A.shearKernel
      {x | ∀ i, |x i| ≤ B} := by
  exact A.kernel.lipschitz.comp_lipschitzOnWith
    (A.form.topResidualPoint_lipschitzOn_box A.weight_pos s A.weight_le M B hB hA)

noncomputable def shearKernelLipBound (A : PolynomialPatch σ s d) (M : ℝ≥0) : ℝ≥0 :=
  max 1 (A.kernel.lip * ((1 + M) * d * s *
    ((1 + M) ^ (s * d) + 1) ^ (s * (d + 1))))

theorem shearKernel_lipschitz (A : PolynomialPatch σ s d) (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    LipschitzWith (A.shearKernelLipBound M) A.shearKernel := by
  unfold shearKernelLipBound
  apply lipschitzWith_of_unit_range_support_box A.shearKernel ((1 + M) ^ (s * d))
    (A.kernel.lip * ((1 + M) * d * s * ((1 + M) ^ (s * d) + 1) ^ (s * (d + 1))))
  · intro x
    exact A.kernel.nonneg _
  · intro x
    exact A.kernel.le_one _
  · intro x hx i
    simpa only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_support_bound M.coe_nonneg hA x hx i
  · simpa only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_lipschitzOn_box M ((1 + M) ^ (s * d) + 1) (le_add_of_nonneg_left zero_le) hA

theorem normalized_shearKernel_lipschitz [Fintype σ] (A : PolynomialPatch σ s d)
    (hA : ∀ i α, |(A.form.center i).coeff α| ≤ 1 / 2) :
    let M : ℝ≥0 := ((s + 1) * (Fintype.card σ + d + 1) ^ s : ℕ)
    LipschitzWith (A.shearKernelLipBound M) A.shearKernel := by
  dsimp only
  apply A.shearKernel_lipschitz
  intro i
  simpa only [NNReal.coe_natCast] using
    A.form.center_mass_le_of_normalized A.weight_pos s A.weight_le hA i

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]

noncomputable def shearObservableLipBound (M : ℝ≥0) : ℝ≥0 :=
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1
  max C (A.shearKernelLipBound M *
    polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) * C)

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem shearSummand_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) (b : Fin d → ℝ) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
    LipschitzWith (A.shearObservableLipBound M)
      (fun g => A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g b)) := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1
  let R : ℝ≥0 := (1 + M) ^ (s * d)
  let T := polynomialShearDisplacementBound s d R
  let K := A.shearKernelLipBound M
  let ρ := polynomialShearRealPointAction A.weight s A.weight_le
  change LipschitzWith (max C (K * T * C)) (fun g => A.shearKernel (ρ g b))
  apply lipschitzWith_of_unit_range_near_nonzero _ C (K * T * C)
    (fun _ => A.kernel.nonneg _) (fun _ => A.kernel.le_one _)
  intro g h hg hnear
  let z := h * g⁻¹
  have hdist : dist 1 z = dist g h := by
    simpa only [mul_inv_cancel] using
      (rightMetricSpace_isometry_mul_right ((polynomialShearOrderedBasis A.weight).baseChange ℝ) g⁻¹).dist_eq g h
  have hR : 1 ≤ R := one_le_pow₀ (le_add_of_nonneg_right zero_le)
  have hx (i : Fin d) : |ρ g b i| ≤ R := by
    simpa only [R, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_support_bound M.coe_nonneg hA (ρ g b) hg i
  have hmove := polynomialShearRealPointAction_near_one A.weight s A.weight_pos A.weight_le
    z R hR (ρ g b) hx (by simpa only [hdist] using hnear)
  have hz : ρ z (ρ g b) = ρ h b := by
    simp only [z, map_mul, map_inv, Equiv.Perm.mul_apply]
    exact congrArg (ρ h) ((ρ g).symm_apply_apply b)
  change dist (ρ z (ρ g b)) (ρ g b) ≤
    (polynomialShearDisplacementBound s (Fintype.card (Fin d)) R * C : ℝ≥0) * dist 1 z at hmove
  rw [hz, hdist, Fintype.card_fin, dist_comm (ρ h b) (ρ g b)] at hmove
  have hkernel := (A.shearKernel_lipschitz M hA).dist_le_mul (ρ g b) (ρ h b)
  rw [Real.dist_eq] at hkernel
  apply hkernel.trans
  simpa only [NNReal.coe_mul, mul_assoc] using mul_le_mul_of_nonneg_left hmove K.coe_nonneg

theorem shearOrbitSum_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
    LipschitzWith (A.shearObservableLipBound M)
      (polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel) := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
  exact separated_tsum_lipschitz
    (fun (b : Fin d → ℤ) g => A.shearKernel
      (polynomialShearRealPointAction A.weight s A.weight_le g (fun i => (b i : ℝ))))
    (fun b => A.shearSummand_lipschitz M hA (fun i => (b i : ℝ)))
    (fun _ _ => A.kernel.nonneg _)
    (fun g _ _ hb hc => A.shearSummand_unique g hb hc)

theorem shearObservable_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    letI : MetricSpace ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) :=
      (polynomialShearNilmanifold A.weight s A.weight_le).metricSpace
    LipschitzWith (A.shearObservableLipBound M) A.shearObservable := by
  let e := (polynomialShearOrderedBasis A.weight).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift (polynomialShearRealLattice s A.weight_le)
    (polynomialShearRealLattice_closed_discrete s A.weight_le).1 A.shearObservable
    (A.shearOrbitSum_lipschitz M hA)

theorem normalized_shearObservable_lipschitz [Fintype σ]
    (hA : ∀ i α, |(A.form.center i).coeff α| ≤ 1 / 2) :
    let M : ℝ≥0 := ((s + 1) * (Fintype.card σ + d + 1) ^ s : ℕ)
    letI : MetricSpace ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) :=
      (polynomialShearNilmanifold A.weight s A.weight_le).metricSpace
    LipschitzWith (A.shearObservableLipBound M) A.shearObservable := by
  dsimp only
  apply A.shearObservable_lipschitz (((s + 1) * (Fintype.card σ + d + 1) ^ s : ℕ) : ℝ≥0)
  intro i
  simpa only [NNReal.coe_natCast] using
    A.form.center_mass_le_of_normalized A.weight_pos s A.weight_le hA i

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open scoped NNReal

def shearKernelLogBudget (s d : ℕ) (M u : ℝ) : ℝ :=
  u + M + d + s + ((s * d : ℕ) * M + 1) * (s * (d + 1) : ℕ)

def shearActionLogBudget (s d : ℕ) (M : ℝ) : ℝ :=
  s + s * ((d * ((s + 1) * (d + 1) ^ s) * s : ℕ) : ℝ) +
    s * ((s * d : ℕ) * M)

theorem shearKernelLogBudget_nonneg (s d : ℕ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 ≤ u) :
    0 ≤ shearKernelLogBudget s d M u := by unfold shearKernelLogBudget; positivity

theorem shearActionLogBudget_nonneg (s d : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ shearActionLogBudget s d M := by unfold shearActionLogBudget; positivity

theorem shearRadius_le_exp (s d : ℕ) (M : ℝ≥0) :
    (((1 + M) ^ (s * d) : ℝ≥0) : ℝ) ≤ Real.exp ((s * d : ℕ) * (M : ℝ)) := by
  simp only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one]
  calc
    _ ≤ (Real.exp (M : ℝ)) ^ (s * d) := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [Real.add_one_le_exp (M : ℝ)]
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem shearKernelLipBound_le_exp {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    (M : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) (hA : (A.kernel.lip : ℝ) ≤ Real.exp u) :
    (A.shearKernelLipBound M : ℝ) ≤ Real.exp (shearKernelLogBudget s d M u) := by
  have hM : 1 + (M : ℝ) ≤ Real.exp (M : ℝ) := by linarith [Real.add_one_le_exp (M : ℝ)]
  have hd : (d : ℝ) ≤ Real.exp (d : ℝ) := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hs : (s : ℝ) ≤ Real.exp (s : ℝ) := by linarith [Real.add_one_le_exp (s : ℝ)]
  have hR : (((1 + M) ^ (s * d) + 1 : ℝ≥0) : ℝ) ≤
      Real.exp ((s * d : ℕ) * (M : ℝ) + 1) := by
    have h := add_le_exp_add_one (by positivity : 0 ≤ (s * d : ℕ) * (M : ℝ))
      (le_refl (0 : ℝ)) (shearRadius_le_exp s d M) (by simp : (1 : ℝ) ≤ Real.exp 0)
    simpa only [NNReal.coe_add, NNReal.coe_one, add_zero] using h
  change max (1 : ℝ) ((A.kernel.lip : ℝ) *
    ((1 + M) * d * s * ((((1 + M) ^ (s * d) + 1 : ℝ≥0) : ℝ) ^ (s * (d + 1))))) ≤ _
  apply max_le (Real.one_le_exp (shearKernelLogBudget_nonneg s d M.coe_nonneg hu))
  calc
    _ ≤ Real.exp u * (Real.exp (M : ℝ) * Real.exp (d : ℝ) * Real.exp (s : ℝ) *
        (Real.exp ((s * d : ℕ) * (M : ℝ) + 1)) ^ (s * (d + 1))) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      unfold shearKernelLogBudget
      ring

theorem shearDisplacementBound_le_exp (s d : ℕ) (M : ℝ≥0) :
    (polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) : ℝ) ≤
      Real.exp (shearActionLogBudget s d M) := by
  have hs : (s : ℝ) ≤ Real.exp (s : ℝ) := by linarith [Real.add_one_le_exp (s : ℝ)]
  let J : ℝ := d * ((s + 1) * (d + 1) ^ s) * s
  have hB : 1 + J ≤ Real.exp J := by linarith [Real.add_one_le_exp J]
  have hR := shearRadius_le_exp s d M
  have he : (polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) : ℝ) =
      (s : ℝ) * (1 + J) ^ s * ((((1 + M) ^ (s * d) : ℝ≥0) : ℝ) ^ s) := by
    simp [polynomialShearDisplacementBound, J]
  rw [he]
  calc
    _ ≤ Real.exp (s : ℝ) * (Real.exp J) ^ s *
        (Real.exp ((s * d : ℕ) * (M : ℝ))) ^ s := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [J, shearActionLogBudget]
      push_cast
      ring

theorem shearObservable_log_bound {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    [Fintype (PolynomialShearIndex A.weight)] (M : ℝ≥0) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA : (A.kernel.lip : ℝ) ≤ Real.exp u)
    (hC : (bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1 : ℝ) ≤ Real.exp v) :
    Real.log (3 + (A.shearObservableLipBound M : ℝ)) ≤
      shearKernelLogBudget s d M u + shearActionLogBudget s d M + v + 3 := by
  let E := shearKernelLogBudget s d M u + shearActionLogBudget s d M + v
  have hk := shearKernelLipBound_le_exp A M hu hA
  have ht := shearDisplacementBound_le_exp s d M
  have hE : 0 ≤ E := add_nonneg
    (add_nonneg (shearKernelLogBudget_nonneg s d M.coe_nonneg hu)
      (shearActionLogBudget_nonneg s d M.coe_nonneg)) hv
  have hL : (A.shearObservableLipBound M : ℝ) ≤ Real.exp E := by
    change max _ _ ≤ _
    apply max_le
    · apply hC.trans (Real.exp_le_exp.mpr ?_)
      dsimp [E]
      linarith [shearKernelLogBudget_nonneg s d M.coe_nonneg hu, shearActionLogBudget_nonneg s d M.coe_nonneg]
    · calc
        _ ≤ Real.exp (shearKernelLogBudget s d M u) * Real.exp (shearActionLogBudget s d M) * Real.exp v := by
          exact mul_le_mul (mul_le_mul hk ht (NNReal.coe_nonneg _) (Real.exp_nonneg _))
            hC (NNReal.coe_nonneg _) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 4 * Real.exp E := by linarith [Real.one_le_exp hE]
    _ ≤ Real.exp 3 * Real.exp E := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [E]; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_shear_parameter_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n d D : ℕ) (p : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (d : ℝ) ≤ p → D ≤ d * (d + 1) ^ s →
      let M : ℝ := ((s + 1) * (n + d + 1) ^ s : ℕ)
      ∃ t : ℝ, 0 ≤ t ∧ p ≤ t ∧
        (D + s.factorial + 2 * s + 1 : ℕ) ≤ t ∧ M ≤ t ∧
        t + shearKernelLogBudget s d M p + shearActionLogBudget s d M + (t + a) ^ a + 4 ≤
          (p + 2) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := 1 + X + Polynomial.C (s.factorial + 2 * s + 1) +
    X * (X + 1) ^ s + Polynomial.C (s + 1) * (2 * X + 1) ^ s
  let K := Q + Q + Q + Polynomial.C s +
    (Polynomial.C s * Q * Q + 1) * (Polynomial.C s * (Q + 1))
  let T := Polynomial.C s + Polynomial.C s *
    (Q * (Polynomial.C (s + 1) * (Q + 1) ^ s) * Polynomial.C s) +
    Polynomial.C s * (Polynomial.C s * Q * Q)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (Q + K + T + (Q + Polynomial.C a) ^ a + 4)
  refine ⟨C, hC, ?_⟩
  intro n d D p hp hn hd hD
  dsimp only
  let M : ℝ := ((s + 1) * (n + d + 1) ^ s : ℕ)
  let t : ℝ := 1 + p + (s.factorial + 2 * s + 1 : ℕ) +
    p * (p + 1) ^ s + (s + 1) * (2 * p + 1) ^ s
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    have h1 : 0 ≤ p * (p + 1) ^ s := by positivity
    have h2 : 0 ≤ ((s : ℝ) + 1) * (2 * p + 1) ^ s := by positivity
    dsimp [t]
    linarith [Nat.cast_nonneg (α := ℝ) (s.factorial + 2 * s + 1)]
  have hdt : (d : ℝ) ≤ t := hd.trans hpt
  have hDb : (D : ℝ) ≤ p * (p + 1) ^ s := by
    apply (Nat.cast_le.mpr hD).trans
    push_cast
    gcongr
  have hMt : M ≤ t := by
    have hm : M ≤ ((s : ℝ) + 1) * (2 * p + 1) ^ s := by
      dsimp [M]
      push_cast
      gcongr
      linarith
    have h1 : 0 ≤ p * (p + 1) ^ s := by positivity
    dsimp [t]
    linarith [Nat.cast_nonneg (α := ℝ) (s.factorial + 2 * s + 1)]
  have hgeo : ((D + s.factorial + 2 * s + 1 : ℕ) : ℝ) ≤ t := by
    have h2 : 0 ≤ ((s : ℝ) + 1) * (2 * p + 1) ^ s := by positivity
    dsimp [t]
    push_cast at *
    linarith
  have hK : shearKernelLogBudget s d M p ≤
      t + t + t + s + ((s : ℝ) * t * t + 1) * ((s : ℝ) * (t + 1)) := by
    unfold shearKernelLogBudget
    push_cast
    gcongr
  have hT : shearActionLogBudget s d M ≤
      s + (s : ℝ) * (t * (((s : ℝ) + 1) * (t + 1) ^ s) * s) +
        s * ((s : ℝ) * t * t) := by
    unfold shearActionLogBudget
    push_cast
    gcongr
  have htotal : t +
      (t + t + t + s + ((s : ℝ) * t * t + 1) * ((s : ℝ) * (t + 1))) +
      (s + (s : ℝ) * (t * (((s : ℝ) + 1) * (t + 1) ^ s) * s) +
        s * ((s : ℝ) * t * t)) + (t + a) ^ a + 4 ≤ (p + 2) ^ C := by
    simpa [X, Q, K, T, t, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul] using hbound p hp
  refine ⟨t, ht0, hpt, hgeo, hMt, ?_⟩
  linarith

end Erdos3

end

end OAI
