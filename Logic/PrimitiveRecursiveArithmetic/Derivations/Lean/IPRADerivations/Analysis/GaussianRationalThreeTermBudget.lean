import IPRADerivations.Analysis.GaussianResidualDecreaseWeights
import IPRADerivations.Analysis.GaussianRationalRelativeNormAlgebra
import IPRADerivations.Analysis.GaussianRationalSyntheticDivision
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination

/-!
# Three actual Gaussian-rational terms in the residual budget

The original four point codes determine a common positive denominator.
The actual nested addition has a derived representation; two native relative
triangles and the computed alpha weights give the exact source contraction.
No sum representation, square-root weight, or final decrease is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalThreeTermBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (represents positive_product qadd qadd_represents represents_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq squaredTolerance)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalNormClearing (weightedNorm weighted_norm_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalRelativeNormAlgebra (relative)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq normSq_eval normSq_scale)
open LeanProofs.IPRA.Analysis.GaussianResidualDecreaseWeights
  (mainWeight errorWeight otherWeight sumWeight rateDen rateNum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sum (u v w : PTm n) : PTm n := qadd (qadd u v) w
def nativeSum (a b c : PTm n) : PTm n :=
  ComplexLogarithmRemainder.add (ComplexLogarithmRemainder.add a b) c
def budget (u v w base D : PTm n) : Fm PTm n := RationalArgmin.rationalLE (qnormSq (sum u v w))
  (RationalArithmetic.multiply (squaredTolerance (rateNum D) (rateDen D)) (qnormSq base))
def denominator (u v w base : PTm n) : PTm n := GaussianRationalSyntheticDivision.remainingDen u v w base
def numerator0 (u v w base : PTm n) : PTm n :=
  ComplexLogarithmRemainder.scale (rawDen v*rawDen w*rawDen base) (rawGaussian u)
def numerator1 (u v w base : PTm n) : PTm n :=
  ComplexLogarithmRemainder.scale (rawDen u*rawDen w*rawDen base) (rawGaussian v)
def numerator2 (u v w base : PTm n) : PTm n :=
  ComplexLogarithmRemainder.scale (rawDen u*rawDen v*rawDen base) (rawGaussian w)
def numeratorBase (u v w base : PTm n) : PTm n :=
  ComplexLogarithmRemainder.scale (rawDen u*rawDen v*rawDen w) (rawGaussian base)

@[simp] theorem subst_sum {m : ℕ} (σ : Fin n → PTm m) (u v w : PTm n) :
    Syn.subst σ (sum u v w) = sum (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) := by simp [sum]
@[simp] theorem subst_nativeSum {m : ℕ} (σ : Fin n → PTm m) (a b c : PTm n) :
    Syn.subst σ (nativeSum a b c) = nativeSum (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) := by simp [nativeSum]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (u v w base D : PTm n) :
    (budget u v w base D).subst σ = budget (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ base) (Syn.subst σ D) := by simp [budget]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (u v w base : PTm n) :
    Syn.subst σ (denominator u v w base) = denominator (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ base) := by simp [denominator,GaussianRationalSyntheticDivision.remainingDen]
@[simp] theorem subst_numerator0 {m : ℕ} (σ : Fin n → PTm m) (u v w base : PTm n) :
    Syn.subst σ (numerator0 u v w base) = numerator0 (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ base) := by simp [numerator0]
@[simp] theorem subst_numerator1 {m : ℕ} (σ : Fin n → PTm m) (u v w base : PTm n) :
    Syn.subst σ (numerator1 u v w base) = numerator1 (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ base) := by simp [numerator1]
@[simp] theorem subst_numerator2 {m : ℕ} (σ : Fin n → PTm m) (u v w base : PTm n) :
    Syn.subst σ (numerator2 u v w base) = numerator2 (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ base) := by simp [numerator2]
@[simp] theorem subst_numeratorBase {m : ℕ} (σ : Fin n → PTm m) (u v w base : PTm n) :
    Syn.subst σ (numeratorBase u v w base) = numeratorBase (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ base) := by simp [numeratorBase]

theorem denominator_positive (u v w base : PTm n) : Γ ⊢[PRAAx] le one (denominator u v w base) :=
  GaussianRationalSyntheticDivision.remaining_den_positive _ _ _ _

theorem first_represents (u v w base : PTm n) : Γ ⊢[PRAAx]
    represents u (numerator0 u v w base) (denominator u v w base) :=
  GaussianRationalSyntheticDivision.rescale_to u (rawGaussian u) (rawDen u) (rawDen v*rawDen w*rawDen base) _
    (raw_represents u) (by unfold denominator GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
theorem second_represents (u v w base : PTm n) : Γ ⊢[PRAAx]
    represents v (numerator1 u v w base) (denominator u v w base) :=
  GaussianRationalSyntheticDivision.rescale_to v (rawGaussian v) (rawDen v) (rawDen u*rawDen w*rawDen base) _
    (raw_represents v) (by unfold denominator GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
theorem third_represents (u v w base : PTm n) : Γ ⊢[PRAAx]
    represents w (numerator2 u v w base) (denominator u v w base) :=
  GaussianRationalSyntheticDivision.rescale_to w (rawGaussian w) (rawDen w) (rawDen u*rawDen v*rawDen base) _
    (raw_represents w) (by unfold denominator GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
theorem base_represents (u v w base : PTm n) : Γ ⊢[PRAAx]
    represents base (numeratorBase u v w base) (denominator u v w base) :=
  GaussianRationalSyntheticDivision.rescale_to base (rawGaussian base) (rawDen base) (rawDen u*rawDen v*rawDen w) _
    (raw_represents base) (by unfold denominator GaussianRationalSyntheticDivision.remainingDen; ipra_ring)

theorem sum_represents (u v w a b c E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hu : Γ ⊢[PRAAx] represents u a E) (hv : Γ ⊢[PRAAx] represents v b E)
    (hw : Γ ⊢[PRAAx] represents w c E) : Γ ⊢[PRAAx] represents (sum u v w) (nativeSum a b c) E :=
  qadd_represents _ _ _ _ _ hE (qadd_represents _ _ _ _ _ hE hu hv) hw

theorem native_three_triangle (a b c A B C R : PTm n)
    (ha : Γ ⊢[PRAAx] le (normSq a) (A*A*R))
    (hb : Γ ⊢[PRAAx] le (normSq b) (B*B*R))
    (hc : Γ ⊢[PRAAx] le (normSq c) (C*C*R)) : Γ ⊢[PRAAx]
    le (normSq (nativeSum a b c)) ((A+B+C)*(A+B+C)*R) :=
  GaussianRelativeNormTriangle.relative_triangle _ _ _ _ _
    (GaussianRelativeNormTriangle.relative_triangle _ _ _ _ _ ha hb) hc

theorem native_scale_sum (L a b c : PTm n) : Γ ⊢[PRAAx]
    normSq (nativeSum (ComplexLogarithmRemainder.scale L a) (ComplexLogarithmRemainder.scale L b)
      (ComplexLogarithmRemainder.scale L c)) ≐ L*L*normSq (nativeSum a b c) := by
  ipra_lc [nativeSum, normSq_eval, GaussianRootAlgebra.re_add, GaussianRootAlgebra.im_add, GaussianRootAlgebra.re_scale, GaussianRootAlgebra.im_scale]

theorem from_representations (u v w base a b c d E A B C L X Y : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hL : Γ ⊢[PRAAx] le one L) (hY : Γ ⊢[PRAAx] le one Y)
    (hu : Γ ⊢[PRAAx] represents u a E) (hv : Γ ⊢[PRAAx] represents v b E)
    (hw : Γ ⊢[PRAAx] represents w c E) (hb : Γ ⊢[PRAAx] represents base d E)
    (h0 : Γ ⊢[PRAAx] relative u A L base) (h1 : Γ ⊢[PRAAx] relative v B L base)
    (h2 : Γ ⊢[PRAAx] relative w C L base)
    (hBudget : Γ ⊢[PRAAx] le (Y*(A+B+C)) (X*L)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (sum u v w))
      (RationalArithmetic.multiply (squaredTolerance X Y) (qnormSq base)) := by
  have r0 := GaussianRationalRelativeNormAlgebra.relative_to_cleared u base a d E A L hE hu hb h0
  have r1 := GaussianRationalRelativeNormAlgebra.relative_to_cleared v base b d E B L hE hv hb h1
  have r2 := GaussianRationalRelativeNormAlgebra.relative_to_cleared w base c d E C L hE hw hb h2
  have n0 : Γ ⊢[PRAAx] le (normSq (ComplexLogarithmRemainder.scale L a)) (A*A*normSq d) :=
    le_congr (normSq_scale L a).eqSymm (.eqRefl _) r0
  have n1 : Γ ⊢[PRAAx] le (normSq (ComplexLogarithmRemainder.scale L b)) (B*B*normSq d) :=
    le_congr (normSq_scale L b).eqSymm (.eqRefl _) r1
  have n2 : Γ ⊢[PRAAx] le (normSq (ComplexLogarithmRemainder.scale L c)) (C*C*normSq d) :=
    le_congr (normSq_scale L c).eqSymm (.eqRefl _) r2
  have sumBound := le_congr (native_scale_sum L a b c) (.eqRefl _)
    (native_three_triangle _ _ _ A B C (normSq d) n0 n1 n2)
  have first : Γ ⊢[PRAAx] le (L*L*Y*Y*normSq (nativeSum a b c))
      ((Y*(A+B+C))*(Y*(A+B+C))*normSq d) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (Y*Y) sumBound)
  have second : Γ ⊢[PRAAx] le ((Y*(A+B+C))*(Y*(A+B+C))*normSq d)
      ((X*L)*(X*L)*normSq d) := mul_le_mul_right (normSq d) (sq_le_sq hBudget)
  have cleared : Γ ⊢[PRAAx] le (Y*Y*normSq (nativeSum a b c)) (X*X*normSq d) :=
    RationalValueBounds.positive_cancel (positive_product L L hL hL)
      (le_congr (by ipra_ring) (by ipra_ring) (le_trans first second))
  have hEE := positive_product E E hE hE
  have hYY := positive_product Y Y hY hY
  have actualSum := sum_represents u v w a b c E hE hu hv hw
  have product := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (GaussianRationalMetric.squared_tolerance_represents X Y hY)
    (GaussianRationalMetric.qnormSq_represents base d E hE hb)
  have product' : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.multiply (squaredTolerance X Y) (qnormSq base))
      (ZT.ofNat (X*X*normSq d)) ((Y*Y)*(E*E)) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := product)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hEE (positive_product _ _ hYY hEE)
    (GaussianRationalMetric.qnormSq_represents _ _ _ hE actualSum) product'
    (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (E*E) cleared))

/-- All common-denominator representations are produced from the four
original Gaussian codes, including a zero or noncanonical base. -/
theorem from_budget (u v w base A B C L X Y : PTm n)
    (hL : Γ ⊢[PRAAx] le one L) (hY : Γ ⊢[PRAAx] le one Y)
    (h0 : Γ ⊢[PRAAx] relative u A L base) (h1 : Γ ⊢[PRAAx] relative v B L base)
    (h2 : Γ ⊢[PRAAx] relative w C L base)
    (hBudget : Γ ⊢[PRAAx] le (Y*(A+B+C)) (X*L)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (sum u v w))
      (RationalArithmetic.multiply (squaredTolerance X Y) (qnormSq base)) :=
  from_representations u v w base (numerator0 u v w base) (numerator1 u v w base)
    (numerator2 u v w base) (numeratorBase u v w base) (denominator u v w base) A B C L X Y
    (denominator_positive u v w base) hL hY (first_represents u v w base) (second_represents u v w base)
    (third_represents u v w base) (base_represents u v w base) h0 h1 h2 hBudget

/-- The final weight budget is derived from the actual alpha guards;
only the three legitimate individual norm comparisons remain inputs. -/
theorem from_alpha (u v w base D P Q : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hQ : Γ ⊢[PRAAx] le one Q)
    (hPQ : Γ ⊢[PRAAx] le P Q) (hLower : Γ ⊢[PRAAx] GaussianResidualDecreaseWeights.lowerBound D P Q)
    (h0 : Γ ⊢[PRAAx] relative u (mainWeight P Q) (GaussianResidualDecreaseWeights.scale Q) base)
    (h1 : Γ ⊢[PRAAx] relative v (errorWeight P) (GaussianResidualDecreaseWeights.scale Q) base)
    (h2 : Γ ⊢[PRAAx] relative w (otherWeight P) (GaussianResidualDecreaseWeights.scale Q) base) : Γ ⊢[PRAAx]
    budget u v w base D :=
  from_budget u v w base (mainWeight P Q) (errorWeight P) (otherWeight P)
    (GaussianResidualDecreaseWeights.scale Q) (rateNum D) (rateDen D)
    (GaussianResidualDecreaseWeights.scale_positive Q hQ) (GaussianResidualDecreaseWeights.rate_den_positive D hD)
    h0 h1 h2 (GaussianResidualDecreaseWeights.contraction_budget D P Q hD hPQ hLower)

theorem from_alpha_input (u v w base D P Q : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianResidualDecreaseWeights.input D P Q)
    (h0 : Γ ⊢[PRAAx] relative u (mainWeight P Q) (GaussianResidualDecreaseWeights.scale Q) base)
    (h1 : Γ ⊢[PRAAx] relative v (errorWeight P) (GaussianResidualDecreaseWeights.scale Q) base)
    (h2 : Γ ⊢[PRAAx] relative w (otherWeight P) (GaussianResidualDecreaseWeights.scale Q) base) : Γ ⊢[PRAAx]
    budget u v w base D :=
  from_alpha u v w base D P Q (Prf.andE₁ hInput) (Prf.andE₁ (Prf.andE₂ hInput))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hInput))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hInput))) h0 h1 h2

theorem norm_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] qnormSq a ≐ qnormSq b := by
  ipra_congr (qnormSq (var 0) : PTm 1) with [h]

/-- Literal output/evaluator equalities transport the actual sum bound. -/
theorem budget_of_sum {u v w z base D : PTm n} (hSum : Γ ⊢[PRAAx] sum u v w ≐ z)
    (h : Γ ⊢[PRAAx] budget u v w base D) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq z)
      (RationalArithmetic.multiply (squaredTolerance (rateNum D) (rateDen D)) (qnormSq base)) :=
  RationalArgmin.rationalLE_congr (norm_congr hSum) (.eqRefl _) h

def sumF : PR 3 := PTm.toPR (sum (var 0) (var 1) (var 2))
def output (u v w D : PTm n) : PTm n := pairT (sum u v w) (pairT (rateNum D) (rateDen D))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (u v w D : PTm n) : PTm n := PTm.app outputF ![u,v,w,D]
def returnedBudget (u v w base D : PTm n) : Fm PTm n :=
  RationalArgmin.rationalLE (qnormSq (fstT (run u v w D)))
    (RationalArithmetic.multiply
      (squaredTolerance (fstT (sndT (run u v w D))) (sndT (sndT (run u v w D)))) (qnormSq base))

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (u v w D : PTm n) :
    Syn.subst σ (output u v w D) = output (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ D) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (u v w D : PTm n) :
    Syn.subst σ (run u v w D) = run (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ D) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_returnedBudget {m : ℕ} (σ : Fin n → PTm m) (u v w base D : PTm n) :
    (returnedBudget u v w base D).subst σ = returnedBudget (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ w) (Syn.subst σ base) (Syn.subst σ D) := by simp [returnedBudget]

theorem sum_program (u v w : PTm n) : Γ ⊢[PRAAx] ap3 sumF u v w ≐ sum u v w := by
  simpa [sumF,ap3] using toPR_eq (Γ := Γ) (sum (var 0) (var 1) (var 2) : PTm 3) ![u,v,w]
theorem program_at (u v w D : PTm n) : Γ ⊢[PRAAx] run u v w D ≐ output u v w D := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![u,v,w,D]

theorem returned_sum (u v w D : PTm n) : Γ ⊢[PRAAx] fstT (run u v w D) ≐ sum u v w :=
  (congrFst (program_at u v w D)).eqTrans (fst_pair _ _)
theorem returned_rate_num (u v w D : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run u v w D)) ≐ rateNum D :=
  (congrFst ((congrSnd (program_at u v w D)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_rate_den (u v w D : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run u v w D)) ≐ rateDen D :=
  (congrSnd ((congrSnd (program_at u v w D)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem tolerance_congr {X X' Y Y' : PTm n} (hX : Γ ⊢[PRAAx] X ≐ X') (hY : Γ ⊢[PRAAx] Y ≐ Y') : Γ ⊢[PRAAx]
    squaredTolerance X Y ≐ squaredTolerance X' Y' := by
  ipra_congr (squaredTolerance (var 0) (var 1) : PTm 2) with [hX, hY]

theorem returned_certificate (u v w base D P Q : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianResidualDecreaseWeights.input D P Q)
    (h0 : Γ ⊢[PRAAx] relative u (mainWeight P Q) (GaussianResidualDecreaseWeights.scale Q) base)
    (h1 : Γ ⊢[PRAAx] relative v (errorWeight P) (GaussianResidualDecreaseWeights.scale Q) base)
    (h2 : Γ ⊢[PRAAx] relative w (otherWeight P) (GaussianResidualDecreaseWeights.scale Q) base) : Γ ⊢[PRAAx]
    returnedBudget u v w base D :=
  RationalArgmin.rationalLE_congr (norm_congr (returned_sum u v w D).eqSymm)
    (RationalAlgebra.multiply_congr
      (tolerance_congr (returned_rate_num u v w D).eqSymm (returned_rate_den u v w D).eqSymm) (.eqRefl _))
    (from_alpha_input u v w base D P Q hInput h0 h1 h2)

theorem three_actual_relative_terms_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianResidualDecreaseWeights.input (var 4) (var 5) (var 6) ⟶
      relative (var 0) (mainWeight (var 5) (var 6)) (GaussianResidualDecreaseWeights.scale (var 6)) (var 3) ⟶
      relative (var 1) (errorWeight (var 5)) (GaussianResidualDecreaseWeights.scale (var 6)) (var 3) ⟶
      relative (var 2) (otherWeight (var 5)) (GaussianResidualDecreaseWeights.scale (var 6)) (var 3) ⟶
      budget (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (from_alpha_input _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_sum_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 sumF (var 0) (var 1) (var 2) ≐ sum (var 0) (var 1) (var 2)) := closeUniv 3 (sum_program _ _ _)

theorem actual_contraction_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)

theorem returned_three_term_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianResidualDecreaseWeights.input (var 4) (var 5) (var 6) ⟶
      relative (var 0) (mainWeight (var 5) (var 6)) (GaussianResidualDecreaseWeights.scale (var 6)) (var 3) ⟶
      relative (var 1) (errorWeight (var 5)) (GaussianResidualDecreaseWeights.scale (var 6)) (var 3) ⟶
      relative (var 2) (otherWeight (var 5)) (GaussianResidualDecreaseWeights.scale (var 6)) (var 3) ⟶
      returnedBudget (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (returned_certificate _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalThreeTermBudget
