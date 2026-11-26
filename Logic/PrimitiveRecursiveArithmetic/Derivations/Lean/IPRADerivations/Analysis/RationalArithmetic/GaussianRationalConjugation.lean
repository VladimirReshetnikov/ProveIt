import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalPhaseCertificate
import IPRADerivations.Analysis.Exponential.GaussianRationalPolynomialExponential
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianEmbedding
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual normalized Gaussian-rational conjugation

The original component conjugation and the original Gaussian addition
normalizer give a total canonical program on raw independent-denominator
points. Algebra and metric transport concern those actual programs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianRationalConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul represents canonical canonical_unique represents_congr positive_product)
open GaussianRationalReciprocal (conjugate re_conjugate im_conjugate)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_mul im_mul re_zero im_zero re_one im_one re_scale im_scale)
open ComplexLogarithmRemainder (zeroCode oneCode add mul scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (q : PTm n) : PTm n := qadd qzero (GaussianRationalPhaseCertificate.conjugatePoint q)
@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (point q) = point (Syn.subst σ q) := by simp [point]
theorem point_canonical (q : PTm n) : Γ ⊢[PRAAx] canonical (point q) := GaussianRationalHorner.qadd_canonical _ _
theorem point_congr {q r : PTm n} (e : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] point q ≐ point r := by
  ipra_congr (point (var 0) : PTm 1) with [e]

theorem point_represents (q g E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hq : Γ ⊢[PRAAx] represents q g E) : Γ ⊢[PRAAx] represents (point q) (conjugate g) E := by
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _)
    (h := GaussianRationalHorner.qadd_represents qzero (GaussianRationalPhaseCertificate.conjugatePoint q)
      zeroCode (conjugate g) E hE (GaussianRationalHorner.zero_represents E)
      (GaussianRationalPhaseCertificate.conjugate_represents q g E hq))
  apply equal_of_values <;> simp only [re_add,im_add,re_zero,im_zero] <;> ring

theorem native_add (g h : PTm n) : Γ ⊢[PRAAx] equal (conjugate (add g h)) (add (conjugate g) (conjugate h)) := by
  apply equal_of_values <;> simp only [re_conjugate,im_conjugate,re_add,im_add] <;> ring
theorem native_mul (g h : PTm n) : Γ ⊢[PRAAx] equal (conjugate (mul g h)) (mul (conjugate g) (conjugate h)) := by
  apply equal_of_values <;> simp only [re_conjugate,im_conjugate,re_mul,im_mul] <;> ring
theorem native_scale (g E : PTm n) : Γ ⊢[PRAAx] equal (conjugate (scale E g)) (scale E (conjugate g)) := by
  apply equal_of_values <;> simp only [re_conjugate,im_conjugate,re_scale,im_scale] <;> ring
theorem native_zero : Γ ⊢[PRAAx] equal (conjugate (zeroCode : PTm n)) zeroCode := by
  apply equal_of_values <;> simp only [re_conjugate,im_conjugate,re_zero,im_zero] <;> ring
theorem native_one : Γ ⊢[PRAAx] equal (conjugate (oneCode : PTm n)) oneCode := by
  apply equal_of_values <;> simp only [re_conjugate,im_conjugate,re_one,im_one] <;> ring
theorem native_involution (g : PTm n) : Γ ⊢[PRAAx] equal (conjugate (conjugate g)) g := by
  apply equal_of_values <;> simp only [re_conjugate,im_conjugate] <;> ring

theorem of_gaussian (g E : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    point (GaussianRationalHorner.ofGaussian g E) ≐ GaussianRationalHorner.ofGaussian (conjugate g) E :=
  canonical_unique _ _ _ _ (point_canonical _) (GaussianRationalHorner.ofGaussian_canonical _ _ hE) hE
    (point_represents _ g E hE (GaussianRationalHorner.ofGaussian_represents g E hE))
    (GaussianRationalHorner.ofGaussian_represents _ _ hE)

theorem add_same_representation (q r g h E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hq : Γ ⊢[PRAAx] represents q g E) (hr : Γ ⊢[PRAAx] represents r h E) : Γ ⊢[PRAAx]
    point (qadd q r) ≐ qadd (point q) (point r) := by
  have lhs := point_represents _ (add g h) E hE (GaussianRationalHorner.qadd_represents q r g h E hE hq hr)
  have rhs := GaussianRationalHorner.qadd_represents _ _ _ _ E hE (point_represents q g E hE hq) (point_represents r h E hE hr)
  exact canonical_unique _ _ _ _ (point_canonical _) (GaussianRationalHorner.qadd_canonical _ _) hE
    (represents_congr (.eqRefl _) (native_add g h) (.eqRefl _) lhs) rhs

theorem point_add (q r : PTm n) : Γ ⊢[PRAAx] point (qadd q r) ≐ qadd (point q) (point r) := by
  let E := rawDen q*rawDen r
  have hE := positive_product (Γ := Γ) _ _ (raw_den_positive q) (raw_den_positive r)
  exact add_same_representation q r (scale (rawDen r) (rawGaussian q)) (scale (rawDen q) (rawGaussian r)) E hE
    (GaussianRationalHorner.represents_rescale q _ _ (rawDen r) (raw_represents q))
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _)
      (GaussianRationalHorner.represents_rescale r _ _ (rawDen q) (raw_represents r)))

theorem point_mul (q r : PTm n) : Γ ⊢[PRAAx] point (qmul q r) ≐ qmul (point q) (point r) := by
  let E := rawDen q
  let F := rawDen r
  have e := raw_den_positive (Γ := Γ) q
  have f := raw_den_positive (Γ := Γ) r
  have lhs := point_represents _ (mul (rawGaussian q) (rawGaussian r)) (E*F) (positive_product _ _ e f)
    (GaussianRationalHorner.qmul_represents q r _ _ E F e f (raw_represents q) (raw_represents r))
  have rhs := GaussianRationalHorner.qmul_represents _ _ _ _ E F e f
    (point_represents q _ E e (raw_represents q)) (point_represents r _ F f (raw_represents r))
  exact canonical_unique _ _ _ _ (point_canonical _) (GaussianRationalHorner.qmul_canonical _ _) (positive_product _ _ e f)
    (represents_congr (.eqRefl _) (native_mul _ _) (.eqRefl _) lhs) rhs

theorem point_zero : Γ ⊢[PRAAx] point (qzero : PTm n) ≐ qzero :=
  canonical_unique _ _ _ _ (point_canonical _) (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl one)
    (represents_congr (.eqRefl _) native_zero (.eqRefl _)
      (point_represents _ zeroCode one (le_refl _) (GaussianRationalHorner.zero_represents _)))
    (GaussianRationalHorner.zero_represents _)
theorem point_one : Γ ⊢[PRAAx] point (GaussianRationalSyntheticDivision.qone : PTm n) ≐ GaussianRationalSyntheticDivision.qone :=
  canonical_unique _ _ _ _ (point_canonical _) GaussianRationalSyntheticDivision.qone_canonical (le_refl one)
    (represents_congr (.eqRefl _) native_one (.eqRefl _)
      (point_represents _ oneCode one (le_refl _) (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))))
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))

theorem native_negative (g : PTm n) : Γ ⊢[PRAAx]
    equal (conjugate (ComplexLogarithmRemainder.neg g)) (ComplexLogarithmRemainder.neg (conjugate g)) := by
  apply equal_of_values <;> simp only [re_conjugate,im_conjugate,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg]

theorem point_negative (q : PTm n) : Γ ⊢[PRAAx]
    point (GaussianRationalMetric.qnegative q) ≐ GaussianRationalMetric.qnegative (point q) := by
  let E := rawDen q
  have e := raw_den_positive (Γ := Γ) q
  have lhs := point_represents _ _ E e (GaussianRationalMetric.qnegative_represents q _ E (raw_represents q))
  have rhs := GaussianRationalMetric.qnegative_represents _ _ E (point_represents q _ E e (raw_represents q))
  exact canonical_unique _ _ _ _ (point_canonical _) (GaussianRationalMetric.qnegative_canonical _) e
    (represents_congr (.eqRefl _) (native_negative _) (.eqRefl _) lhs) rhs

theorem point_sub (q r : PTm n) : Γ ⊢[PRAAx]
    point (GaussianRationalMetric.qsub q r) ≐ GaussianRationalMetric.qsub (point q) (point r) :=
  (point_add q (GaussianRationalMetric.qnegative r)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (point_negative r))

theorem point_bound (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B) : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (point q) A B := by
  let E := rawDen q
  have e := raw_den_positive (Γ := Γ) q
  have old := (GaussianRationalMetric.bounded_iff q (rawGaussian q) E A B e hB (raw_represents q)).iffMp hq
  exact (GaussianRationalMetric.bounded_iff _ (conjugate (rawGaussian q)) E A B e hB
    (point_represents q _ E e (raw_represents q))).iffMpr
      (le_congr (congrMul (.eqRefl (B*B)) (GaussianRationalReciprocal.norm_conjugate _)).eqSymm (.eqRefl _) old)

theorem point_distance (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded q r A B) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (point q) (point r) A B :=
  GaussianRationalReciprocal.bound_congr (point_sub q r) (.eqRefl _) (.eqRefl _)
    (point_bound (GaussianRationalMetric.qsub q r) A B hB hq)

theorem point_bound_reflect (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (point q) A B) : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B := by
  let E := rawDen q
  have e := raw_den_positive (Γ := Γ) q
  have fresh := (GaussianRationalMetric.bounded_iff _ (conjugate (rawGaussian q)) E A B e hB
    (point_represents q _ E e (raw_represents q))).iffMp hq
  exact (GaussianRationalMetric.bounded_iff q (rawGaussian q) E A B e hB (raw_represents q)).iffMpr
    (le_congr (congrMul (.eqRefl (B*B)) (GaussianRationalReciprocal.norm_conjugate _)) (.eqRefl _) fresh)

theorem point_distance_reflect (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (point q) (point r) A B) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded q r A B :=
  point_bound_reflect (GaussianRationalMetric.qsub q r) A B hB
    (GaussianRationalReciprocal.bound_congr (point_sub q r).eqSymm (.eqRefl _) (.eqRefl _) hq)

theorem distance_iff (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    Fm.iff (GaussianRationalMetric.distanceBounded (point q) (point r) A B) (GaussianRationalMetric.distanceBounded q r A B) :=
  .andI (.impI (point_distance_reflect q r A B hB.wk Prf.hyp0)) (.impI (point_distance q r A B hB.wk Prf.hyp0))

theorem point_involution_canonical (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] point (point q) ≐ q :=
  canonical_unique _ _ _ _ (point_canonical _) hq (raw_den_positive q)
    (represents_congr (.eqRefl _) (native_involution _) (.eqRefl _)
      (point_represents _ _ _ (raw_den_positive q) (point_represents q _ _ (raw_den_positive q) (raw_represents q))))
    (raw_represents q)

theorem native_real (a : ZT n) : Γ ⊢[PRAAx]
    equal (conjugate (RationalGaussianEmbedding.native a)) (RationalGaussianEmbedding.native a) := by
  apply equal_of_values
  · rw [re_conjugate]
  · rw [im_conjugate]
    simp [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]

theorem point_embed (q : PTm n) : Γ ⊢[PRAAx] point (RationalGaussianEmbedding.embed q) ≐ RationalGaussianEmbedding.embed q := by
  have hE := RationalArgmin.denominator_positive (Γ := Γ) q
  have rep := RationalGaussianEmbedding.embed_represents (Γ := Γ) q
  exact canonical_unique _ _ _ _ (point_canonical _) (RationalGaussianEmbedding.embed_canonical q) hE
    (represents_congr (.eqRefl _) (native_real _) (.eqRefl _) (point_represents _ _ _ hE rep)) rep

theorem inverse_factorial (j : PTm n) : Γ ⊢[PRAAx]
    point (GaussianRationalPolynomialExponential.inverseFactorial j) ≐ GaussianRationalPolynomialExponential.inverseFactorial j := by
  have hj := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) j
  have rep := GaussianRationalPolynomialExponential.inverse_factorial_represents (Γ := Γ) j
  exact canonical_unique _ _ _ _ (point_canonical _) (GaussianRationalPolynomialExponential.inverse_factorial_canonical j) hj
    (represents_congr (.eqRefl _) native_one (.eqRefl _) (point_represents _ oneCode _ hj rep)) rep

theorem power_zero (q : PTm n) : Γ ⊢[PRAAx]
    point (GaussianRationalReciprocal.power q zero) ≐ GaussianRationalReciprocal.power (point q) zero :=
  (point_congr (GaussianRationalReciprocal.power_zero q)).eqTrans (point_one.eqTrans (GaussianRationalReciprocal.power_zero _).eqSymm)
theorem power_step (q k : PTm n)
    (ih : Γ ⊢[PRAAx] point (GaussianRationalReciprocal.power q k) ≐ GaussianRationalReciprocal.power (point q) k) : Γ ⊢[PRAAx]
    point (GaussianRationalReciprocal.power q (succ k)) ≐ GaussianRationalReciprocal.power (point q) (succ k) :=
  (point_congr (GaussianRationalReciprocal.power_succ q k)).eqTrans ((point_mul _ _).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr ih (.eqRefl _)).eqTrans (GaussianRationalReciprocal.power_succ _ _).eqSymm))

/-- Genuine QF induction on the original scalar power fold. -/
theorem point_power (q k : PTm n) : Γ ⊢[PRAAx]
    point (GaussianRationalReciprocal.power q k) ≐ GaussianRationalReciprocal.power (point q) k := by
  have all : Γ ⊢[PRAAx] .all (point (GaussianRationalReciprocal.power (Syn.shift q) (var 0)) ≐
      GaussianRationalReciprocal.power (point (Syn.shift q)) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq,subst_point,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using power_zero (Γ := Γ) q
    · simpa only [Fm.subst_eq,subst_point,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        power_step (Syn.shift q) (var 0) (Prf.hyp0 (Ax := PRAAx))
  simpa only [Fm.subst_eq,subst_point,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem scalar_sum_zero (q : PTm n) : Γ ⊢[PRAAx]
    point (GaussianRationalPolynomialExponential.scalarSum q zero) ≐ GaussianRationalPolynomialExponential.scalarSum (point q) zero :=
  (point_congr (GaussianRationalPolynomialExponential.scalar_sum_zero q)).eqTrans
    (point_one.eqTrans (GaussianRationalPolynomialExponential.scalar_sum_zero _).eqSymm)
theorem scalar_sum_step (q k : PTm n)
    (ih : Γ ⊢[PRAAx] point (GaussianRationalPolynomialExponential.scalarSum q k) ≐ GaussianRationalPolynomialExponential.scalarSum (point q) k) : Γ ⊢[PRAAx]
    point (GaussianRationalPolynomialExponential.scalarSum q (succ k)) ≐ GaussianRationalPolynomialExponential.scalarSum (point q) (succ k) :=
  (point_congr (GaussianRationalPolynomialExponential.scalar_sum_succ q k)).eqTrans ((point_add _ _).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_congr ih ((point_mul _ _).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (inverse_factorial _) (point_power q _)))).eqTrans
        (GaussianRationalPolynomialExponential.scalar_sum_succ _ _).eqSymm))

/-- The original finite Taylor scalarSum commutes with conjugation at
every numerical cutoff, with no realness or canonical input premise. -/
theorem point_scalar_sum (q k : PTm n) : Γ ⊢[PRAAx]
    point (GaussianRationalPolynomialExponential.scalarSum q k) ≐ GaussianRationalPolynomialExponential.scalarSum (point q) k := by
  have all : Γ ⊢[PRAAx] .all (point (GaussianRationalPolynomialExponential.scalarSum (Syn.shift q) (var 0)) ≐
      GaussianRationalPolynomialExponential.scalarSum (point (Syn.shift q)) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq,subst_point,GaussianRationalPolynomialExponential.subst_scalarSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using scalar_sum_zero (Γ := Γ) q
    · simpa only [Fm.subst_eq,subst_point,GaussianRationalPolynomialExponential.subst_scalarSum,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        scalar_sum_step (Syn.shift q) (var 0) (Prf.hyp0 (Ax := PRAAx))
  simpa only [Fm.subst_eq,subst_point,GaussianRationalPolynomialExponential.subst_scalarSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

def pointF : PR 1 := PTm.toPR (point (var 0))
def run (q : PTm n) : PTm n := PTm.app pointF ![q]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (run q) = run (Syn.subst σ q) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (q : PTm n) : Γ ⊢[PRAAx] run q ≐ point q := by
  simpa [run,pointF] using toPR_eq (Γ := Γ) (point (var 0) : PTm 1) ![q]

theorem actual_raw_conjugation_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (canonical (point (var 0))) := closeUniv 1 (point_canonical _)
theorem original_positive_denominator_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ represents (var 0) (var 1) (var 2) ⟶ represents (point (var 0)) (conjugate (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (point_represents _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_conjugation_add_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (point (qadd (var 0) (var 1)) ≐ qadd (point (var 0)) (point (var 1))) := closeUniv 2 (point_add _ _)
theorem actual_conjugation_multiply_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (point (qmul (var 0) (var 1)) ≐ qmul (point (var 0)) (point (var 1))) := closeUniv 2 (point_mul _ _)
theorem original_conjugation_distance_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ Fm.iff (GaussianRationalMetric.distanceBounded (point (var 0)) (point (var 1)) (var 2) (var 3))
      (GaussianRationalMetric.distanceBounded (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (.impI (distance_iff _ _ _ _ Prf.hyp0))
theorem actual_conjugation_scalar_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (point (GaussianRationalReciprocal.power (var 0) (var 1)) ≐ GaussianRationalReciprocal.power (point (var 0)) (var 1)) := closeUniv 2 (point_power _ _)
theorem actual_conjugation_finite_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (point (GaussianRationalPolynomialExponential.scalarSum (var 0) (var 1)) ≐
      GaussianRationalPolynomialExponential.scalarSum (point (var 0)) (var 1)) := closeUniv 2 (point_scalar_sum _ _)
theorem actual_conjugation_original_rational_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (point (RationalGaussianEmbedding.embed (var 0)) ≐ RationalGaussianEmbedding.embed (var 0)) := closeUniv 1 (point_embed _)
theorem actual_conjugation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (run (var 0) ≐ point (var 0)) := closeUniv 1 (program_at _)

end LeanProofs.IPRA.Analysis.GaussianRationalConjugation
