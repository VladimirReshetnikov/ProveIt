import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianL1
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalMetric
import IPRADerivations.Analysis.RationalArithmetic.RationalAlgebra
import IPRADerivations.Core.LinearCombination

/-!
# Actual rational coefficient L1 norm and initial residual bound

The two components retain independent decoded positive denominators. The
actual scalar absolute values and their normalized sum represent the L1
norm of the decoded Gaussian value. The computed bound max(1, ||q||1)
dominates its squared Euclidean norm. Neither a clearing representation nor
an initial residual estimate is a premise of the final bound.
-/

set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalL1

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (code re im normSq eval_re_code eval_im_code)
open LeanProofs.IPRA.Analysis.GaussianL1
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (scalar_congr scalar_add_same positive_product)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value positivePart)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE left denominator_positive)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def scalarAbs (c : PTm n) : PTm n := normalize (ZT.ofNat (zabs (numeratorOf c))) (denominatorOf c)
def qL1 (q : PTm n) : PTm n := RationalArithmetic.add (scalarAbs (fstT q)) (scalarAbs (sndT q))
def oneCode : PTm n := normalize (ZT.ofNat one) one
def baseBound (q : PTm n) : PTm n := RationalArithmetic.maximum oneCode (qL1 q)
def rawDen (q : PTm n) : PTm n := denominatorOf (fstT q)*denominatorOf (sndT q)
def rawGaussian (q : PTm n) : PTm n := code
  (numeratorOf (fstT q)*ZT.ofNat (denominatorOf (sndT q)))
  (numeratorOf (sndT q)*ZT.ofNat (denominatorOf (fstT q)))

@[simp] theorem subst_scalarAbs {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    Syn.subst σ (scalarAbs c) = scalarAbs (Syn.subst σ c) := by
  simp [scalarAbs,zabs,Probability.Variance.ad,ZT.subst,numeratorOf,ZT.ofNat]
@[simp] theorem subst_qL1 {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (qL1 q) = qL1 (Syn.subst σ q) := by simp [qL1]
@[simp] theorem subst_oneCode {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (oneCode : PTm n) = (oneCode : PTm m) := by simp [oneCode]
@[simp] theorem subst_baseBound {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (baseBound q) = baseBound (Syn.subst σ q) := by simp [baseBound]
@[simp] theorem subst_rawDen {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (rawDen q) = rawDen (Syn.subst σ q) := by simp [rawDen]
@[simp] theorem subst_rawGaussian {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (rawGaussian q) = rawGaussian (Syn.subst σ q) := by simp [rawGaussian]

theorem raw_den_positive (q : PTm n) : Γ ⊢[PRAAx] le one (rawDen q) :=
  positive_product _ _ (denominator_positive _) (denominator_positive _)

theorem raw_represents (q : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents q (rawGaussian q) (rawDen q) := by
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  all_goals
    simp only [RationalArithmetic.represents,rawGaussian,rawDen,ZT.toZ_mul,ZT.toZ_ofNat,eval_re_code,eval_im_code]
    ipra_simps
    ring

theorem scalar_abs_represents (c : PTm n) (a : ZT n) (E : PTm n)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents c a E) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (scalarAbs c) (ZT.ofNat (zabs a)) E := by
  have ab := zabs_congr (ZT.toZ_eq h)
  have ab' : Γ ⊢[PRAAx] zabs a*denominatorOf c ≐ zabs (numeratorOf c)*E :=
    ((abs_multiply _ _).eqTrans (congrMul (.eqRefl _) (abs_ofNat _))).eqSymm.eqTrans
      (ab.eqTrans ((abs_multiply _ _).eqTrans (congrMul (.eqRefl _) (abs_ofNat _))))
  have value : Γ ⊢[PRAAx] RationalArithmetic.represents (scalarAbs c)
      (ZT.ofNat (zabs (numeratorOf c))) (denominatorOf c) :=
    normalize_preserves_value _ _ (denominator_positive c)
  apply RationalNormalForm.positive_integer_cancel (denominatorOf c) _ _ (denominator_positive c)
  ipra_lc [RationalArithmetic.represents] 𝔞(denominatorOf (scalarAbs c))*natEq ab'+𝔞(E)*ZT.toZ_eq value

theorem qL1_represents (q a E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hq : Γ ⊢[PRAAx] GaussianRationalHorner.represents q a E) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (qL1 q) (ZT.ofNat (norm1 a)) E := by
  have h := scalar_add_same _ _ _ _ _ hE
    (scalar_abs_represents _ _ _ (Prf.andE₁ hq)) (scalar_abs_represents _ _ _ (Prf.andE₂ hq))
  refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) h
  apply ZT.derive
  simp only [norm1,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_add,map_add]

theorem qL1_guard (q : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (qL1 q) :=
  RationalArithmetic.add_guard _ _

theorem nonnegative_of_representation (c N E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat N) E) :
    Γ ⊢[PRAAx] le (numeratorOf c).neg (numeratorOf c).pos := by
  apply RationalValueBounds.positive_cancel hE
  refine le_of_eq_add (d := N*denominatorOf c) ?_
  have e := ZT.toZ_eq hc
  apply deriveNat
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at e
  simp only [ZT.toZ] at e
  ipra_simps
  linear_combination -e

theorem nonnegative_of_lower (a b : PTm n)
    (ha : Γ ⊢[PRAAx] le (numeratorOf a).neg (numeratorOf a).pos)
    (hab : Γ ⊢[PRAAx] rationalLE a b) :
    Γ ⊢[PRAAx] le (numeratorOf b).neg (numeratorOf b).pos := by
  apply RationalValueBounds.positive_cancel (denominator_positive a)
  let gap := monus (left b a) (left a b)
  have ord : Γ ⊢[PRAAx] left b a ≐ left a b+gap := eq_add_of_le hab
  have e := natEq ord
  have pa := natEq (eq_add_of_le ha)
  refine le_of_eq_add (d := monus (numeratorOf a).pos (numeratorOf a).neg*denominatorOf b+gap) ?_
  apply deriveNat
  unfold left at e
  ipra_simps
  linear_combination e+𝔞(denominatorOf b)*pa

theorem square_monotone (a b : PTm n)
    (ha : Γ ⊢[PRAAx] le (numeratorOf a).neg (numeratorOf a).pos)
    (hab : Γ ⊢[PRAAx] rationalLE a b) : Γ ⊢[PRAAx]
    rationalLE (RationalArithmetic.multiply a a) (RationalArithmetic.multiply b b) := by
  have h1 := RationalArithmetic.multiply_monotone a a b ha hab
  have h2 := RationalArithmetic.multiply_monotone b a b (nonnegative_of_lower a b ha hab) hab
  exact RationalArgmin.transitive h1
    (RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_commutative b a) (.eqRefl _) h2)

theorem qL1_nonnegative (q : PTm n) : Γ ⊢[PRAAx] le (numeratorOf (qL1 q)).neg (numeratorOf (qL1 q)).pos :=
  nonnegative_of_representation _ _ _ (raw_den_positive q)
    (qL1_represents q (rawGaussian q) (rawDen q) (raw_den_positive q) (raw_represents q))

theorem normSq_le_qL1_square (q : PTm n) : Γ ⊢[PRAAx]
    rationalLE (GaussianRationalMetric.qnormSq q) (RationalArithmetic.multiply (qL1 q) (qL1 q)) := by
  have h := qL1_represents (Γ := Γ) q (rawGaussian q) (rawDen q) (raw_den_positive q) (raw_represents q)
  have hm := RationalRepresentations.represents_multiply _ _ _ _ _ _ h h
  apply GaussianRationalMetric.comparison_of_cleared _ _ (normSq (rawGaussian q))
    (norm1 (rawGaussian q)*norm1 (rawGaussian q)) (rawDen q*rawDen q) (rawDen q*rawDen q)
    (positive_product _ _ (raw_den_positive q) (raw_den_positive q))
    (positive_product _ _ (raw_den_positive q) (raw_den_positive q))
    (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive q) (raw_represents q))
    (scalar_congr (.eqRefl _) (by apply ZT.derive; simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]) (.eqRefl _) hm)
  exact le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right _ (normSq_le_norm1_square _))

theorem base_bounds (q : PTm n) : Γ ⊢[PRAAx]
    rationalLE oneCode (baseBound q) ⋏ rationalLE (qL1 q) (baseBound q) :=
  RationalArithmetic.maximum_bounds _ _

theorem base_nonnegative (q : PTm n) : Γ ⊢[PRAAx]
    le (numeratorOf (baseBound q)).neg (numeratorOf (baseBound q)).pos :=
  nonnegative_of_lower _ _ (qL1_nonnegative q) (Prf.andE₂ (base_bounds q))

theorem initial_residual_bound (q : PTm n) : Γ ⊢[PRAAx]
    rationalLE (GaussianRationalMetric.qnormSq q) (RationalArithmetic.multiply (baseBound q) (baseBound q)) :=
  RationalArgmin.transitive (normSq_le_qL1_square q)
    (square_monotone _ _ (qL1_nonnegative q) (Prf.andE₂ (base_bounds q)))

theorem base_natural_representation (q : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (baseBound q)
      (ZT.ofNat (positivePart (numeratorOf (baseBound q)))) (denominatorOf (baseBound q)) := by
  have e := natEq (eq_add_of_le (base_nonnegative (Γ := Γ) q))
  apply ZT.derive
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ,positivePart]
  ipra_simps
  linear_combination -𝔞(denominatorOf (baseBound q))*e

theorem initial_bounded (q : PTm n) : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q
    (positivePart (numeratorOf (baseBound q))) (denominatorOf (baseBound q)) := by
  have hp := base_natural_representation (Γ := Γ) q
  have hm := RationalRepresentations.represents_multiply _ _ _ _ _ _ hp hp
  have ht := GaussianRationalMetric.squared_tolerance_represents
    (Γ := Γ) (positivePart (numeratorOf (baseBound q))) (denominatorOf (baseBound q)) (denominator_positive _)
  have eq := RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (positive_product _ _ (denominator_positive _) (denominator_positive _)))
    hm ht (positive_product _ _ (denominator_positive _) (denominator_positive _))
    (positive_product _ _ (denominator_positive _) (denominator_positive _)) (by
      apply ZT.derive
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul])
  exact RationalArgmin.rationalLE_congr (.eqRefl _) eq (initial_residual_bound q)

def output (q : PTm n) : PTm n := pairT (qL1 q) (baseBound q)
def outputF : PR 1 := PTm.toPR (output (var 0))
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (output q) = output (Syn.subst σ q) := by simp [output]
theorem output_program (q : PTm n) : Γ ⊢[PRAAx] ap1 outputF q ≐ output q := by
  simpa [outputF,ap1] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![q]

theorem rational_l1_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (rationalLE oneCode (baseBound (var 0)) ⋏
      (rationalLE (qL1 (var 0)) (baseBound (var 0)) ⋏
        GaussianRationalMetric.bounded (var 0) (positivePart (numeratorOf (baseBound (var 0))))
          (denominatorOf (baseBound (var 0))))) :=
  closeUniv 1 (.andI (Prf.andE₁ (base_bounds _)) (.andI (Prf.andE₂ (base_bounds _)) (initial_bounded _)))

theorem rational_l1_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 outputF (var 0) ≐ output (var 0)) := closeUniv 1 (output_program _)

end LeanProofs.IPRA.Analysis.GaussianRationalL1
