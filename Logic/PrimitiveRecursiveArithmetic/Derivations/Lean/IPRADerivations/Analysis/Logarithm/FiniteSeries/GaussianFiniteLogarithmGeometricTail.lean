import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalUnitDiskHornerNorm
import IPRADerivations.Analysis.Logarithm.FiniteSeries.GaussianFiniteLogarithmCompositionTail
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalTravelScaling

/-!
# A uniform geometric tail for the actual original finite C4 composition

The original half disk is rescaled to radius9/10 in the actual5/9 dilation.
Actual power-expansion entries identify its low sum with the SAME original
composition low sum. Raw query recovery is only to recode(w); the existing
Horner query-properness theorem and contextual addition remove that normal
form. The actual high part therefore bounds the original residual by
11*9^(h+1)/10^(h+1), with the original1<=h<=d,K cutoff guards retained.
Dyadic scheduling and the analytic named C4 identity remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmGeometricTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul evaluate horner)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (power bound_congr)
open GaussianTranslatedNonconstant (recode recode_canonical recode_eq)
open GaussianRationalUnitDiskHornerNorm (sourceBuffer query)
open GaussianFiniteLogarithmWeightedNorm (point)
open GaussianFiniteLogarithmPolynomial (composition)
open GaussianFiniteLogarithmCompositionTail (linearValue)
open GaussianRationalPowerExpansion (partialSum)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem query_product (w : PTm n) : Γ ⊢[PRAAx] qmul point (query w) ≐ recode w := by
  have h5 : Γ ⊢[PRAAx] le one (num 5 : PTm n) := le_of_eq_add (d := num 4) (by ipra_ring)
  have h9 : Γ ⊢[PRAAx] le one (num 9 : PTm n) := le_of_eq_add (d := num 8) (by ipra_ring)
  have inverse : Γ ⊢[PRAAx] qmul point (GaussianDominantPairAlgebra.radiusPoint (num 9) (num 5)) ≐ qone :=
    (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianRationalTravelScaling.inverse_radius (num 5) (num 9) h5 h9)
  have unit : Γ ⊢[PRAAx] qmul qone w ≐ recode w :=
    (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      ((GaussianRationalSyntheticCoefficientValues.qmul_recode_left w qone).eqSymm.eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (recode_canonical w)))
  exact (GaussianReciprocalHorner.qmul_associative point (GaussianDominantPairAlgebra.radiusPoint (num 9) (num 5)) w).eqSymm.eqTrans
    ((qmul_congr inverse (.eqRefl _)).eqTrans unit)

theorem query_recode (w : PTm n) : Γ ⊢[PRAAx] recode (qmul point (query w)) ≐ recode w :=
  (recode_eq _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans (query_product w)

/-- The actual dilation at its actual rescaled query evaluates to the
original composed buffer at the original raw query, without raw eta. -/
theorem source_evaluation (d K w : PTm n) : Γ ⊢[PRAAx]
    evaluate (sourceBuffer d K) (query w) ≐ evaluate (composition d K) w :=
  (GaussianRationalPolynomialDilation.dilation_evaluation _ _ _ _
    (GaussianRationalPolynomialExponential.polynomial_length _ _ _)).eqTrans
      (GaussianRationalValueEquality.horner_query_proper _ _ _ _ (query_recode w))

/-- The existing finite power-expansion entries and original Bell low sum
are used literally; no further coefficient induction or formal series law. -/
theorem source_low_sum (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K) : Γ ⊢[PRAAx]
    partialSum (sourceBuffer d K) (K*d) (query w) (succ h) ≐ linearValue w := by
  have hN := GaussianFiniteLogarithmCompositionTail.cutoff_degree d K h h1 hd hK
  have range : Γ ⊢[PRAAx] le (succ h) (succ (K*d)) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hN)
  have same : Γ ⊢[PRAAx] partialSum (sourceBuffer d K) (K*d) (query w) (succ h) ≐
      partialSum (composition d K) (K*d) (qmul point (query w)) (succ h) :=
    GaussianRationalSumSegments.prefix_entries_congr _ _ (succ (K*d)) (succ h)
      (GaussianRationalPolynomialDilation.expansion_entries (composition d K) (K*d) point (query w)) range
  exact same.eqTrans ((GaussianFiniteLogarithmCompositionTail.low_sum d K h (qmul point (query w)) h1 hd hK).eqTrans
    ((qadd_congr (.eqRefl _) (query_product w)).eqTrans
      (GaussianRationalSyntheticCoefficientValues.qadd_recode_right qone w)))

def residual (d K w : PTm n) : PTm n := qsub (evaluate (composition d K) w) (linearValue w)
def highPart (d K h w : PTm n) : PTm n := qmul (horner (sourceBuffer d K) (query w) (monus (K*d) h))
  (power (query w) (succ h))
def numerator (h : PTm n) : PTm n := num 11*pw (num 9) (succ h)
def denominator (h : PTm n) : PTm n := pw (num 10) (succ h)
@[simp] theorem subst_residual {l : ℕ} (σ : Fin n → PTm l) (d K w : PTm n) :
    Syn.subst σ (residual d K w) = residual (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ w) := by simp [residual]
@[simp] theorem subst_highPart {l : ℕ} (σ : Fin n → PTm l) (d K h w : PTm n) :
    Syn.subst σ (highPart d K h w) = highPart (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ h) (Syn.subst σ w) := by simp [highPart]
@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (h : PTm n) :
    Syn.subst σ (numerator h) = numerator (Syn.subst σ h) := by simp [numerator]
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (h : PTm n) :
    Syn.subst σ (denominator h) = denominator (Syn.subst σ h) := by simp [denominator]

/-- Exact high-part identity of the original finite composition, derived
from the SAME stored dilation and the actual finite conservation theorem. -/
theorem residual_identity (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K) : Γ ⊢[PRAAx]
    residual d K w ≐ highPart d K h w :=
  (qsub_congr (source_evaluation d K w).eqSymm (source_low_sum d K h w h1 hd hK).eqSymm).eqTrans
    (GaussianFiniteLogarithmCompositionTail.tail_identity _ _ h (query w)
      (GaussianRationalUnitDiskHornerNorm.source_length d K) (GaussianFiniteLogarithmCompositionTail.cutoff_degree d K h h1 hd hK))

theorem high_part_bound (d K h w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    bounded (highPart d K h w) (numerator h) (denominator h) := by
  have h10 : Γ ⊢[PRAAx] le one (num 10 : PTm n) := le_of_eq_add (d := num 9) (by ipra_ring)
  have prefixBound := GaussianRationalUnitDiskHornerNorm.source_prefix_bound d K w (monus (K*d) h) hw
    (le_trans (GaussianMonicResidualRadius.monus_le_left _ _) (le_succ_self _))
  have powerBound := GaussianRationalReciprocal.bounded_power (query w) (num 9) (num 10) (succ h) h10
    (GaussianRationalUnitDiskHornerNorm.query_bound w hw)
  exact bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl _)
      (GaussianFactorBudget.power_positive _ _ h10) prefixBound powerBound)

/-- Uniform original finite C4 residual estimate. Only the original
Euclidean half disk and original1<=h<=d,K cutoff guards are inputs. -/
theorem composition_error (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (composition d K) w) (linearValue w) (numerator h) (denominator h) :=
  bound_congr (residual_identity d K h w h1 hd hK).eqSymm (.eqRefl _) (.eqRefl _) (high_part_bound d K h w hw)


theorem denominator_positive (h : PTm n) : Γ ⊢[PRAAx] le one (denominator h) :=
  GaussianFactorBudget.power_positive _ _ (le_of_eq_add (d := num 9) (by ipra_ring))

/-! Actual PR4 data binds original source coefficient buffer, literal
residual, actual high part and both genuine finite geometric budget fields. -/
def output (d K h w : PTm n) : PTm n := pairT (composition d K)
  (pairT (residual d K w) (pairT (highPart d K h w) (pairT (numerator h) (denominator h))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (d K h w : PTm n) : PTm n := PTm.app outputF ![d,K,h,w]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d K h w : PTm n) :
    Syn.subst σ (output d K h w) = output (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ h) (Syn.subst σ w) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d K h w : PTm n) :
    Syn.subst σ (run d K h w) = run (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ h) (Syn.subst σ w) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (d K h w : PTm n) : Γ ⊢[PRAAx] run d K h w ≐ output d K h w := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![d,K,h,w]
theorem returned_composition (d K h w : PTm n) : Γ ⊢[PRAAx] fstT (run d K h w) ≐ composition d K :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (d K h w : PTm n) : Γ ⊢[PRAAx] sndT (run d K h w) ≐
    pairT (residual d K w) (pairT (highPart d K h w) (pairT (numerator h) (denominator h))) :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_residual (d K h w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d K h w)) ≐ residual d K w :=
  (congrFst (returned_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_rest (d K h w : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d K h w)) ≐
    pairT (highPart d K h w) (pairT (numerator h) (denominator h)) :=
  (congrSnd (returned_tail _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_high (d K h w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d K h w))) ≐ highPart d K h w :=
  (congrFst (returned_rest _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_pair (d K h w : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d K h w))) ≐
    pairT (numerator h) (denominator h) :=
  (congrSnd (returned_rest _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_numerator (d K h w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run d K h w)))) ≐ numerator h :=
  (congrFst (returned_pair _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_denominator (d K h w : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run d K h w)))) ≐ denominator h :=
  (congrSnd (returned_pair _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_identity (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K) : Γ ⊢[PRAAx]
    fstT (sndT (run d K h w)) ≐ fstT (sndT (sndT (run d K h w))) :=
  (returned_residual d K h w).eqTrans ((residual_identity d K h w h1 hd hK).eqTrans (returned_high d K h w).eqSymm)
theorem returned_bound (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    bounded (fstT (sndT (run d K h w))) (fstT (sndT (sndT (sndT (run d K h w)))))
      (sndT (sndT (sndT (sndT (run d K h w))))) :=
  bound_congr (returned_residual d K h w).eqSymm (returned_numerator d K h w).eqSymm
    (returned_denominator d K h w).eqSymm (composition_error d K h w h1 hd hK hw)

theorem actual_raw_query_recovery_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qmul point (query (var 0)) ≐ recode (var 0)) := closeUniv 1 (query_product _)
theorem actual_dilated_source_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (sourceBuffer (var 0) (var 1)) (query (var 2)) ≐ evaluate (composition (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (source_evaluation _ _ _)
theorem original_dilated_low_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      partialSum (sourceBuffer (var 0) (var 1)) (var 1*var 0) (query (var 3)) (succ (var 2)) ≐ linearValue (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (source_low_sum _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem original_composition_high_part_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      residual (var 0) (var 1) (var 3) ≐ highPart (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (residual_identity _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem original_half_disk_high_part_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 3) one two ⟶ bounded (highPart (var 0) (var 1) (var 2) (var 3)) (numerator (var 2)) (denominator (var 2))) :=
  closeUniv 4 (.impI (high_part_bound _ _ _ _ Prf.hyp0))
theorem original_half_disk_composition_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ bounded (var 3) one two ⟶
      distanceBounded (evaluate (composition (var 0) (var 1)) (var 3)) (linearValue (var 3)) (numerator (var 2)) (denominator (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (composition_error _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_geometric_tail_denominator_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (denominator (var 0))) := closeUniv 1 (denominator_positive _)
theorem actual_geometric_tail_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem returned_geometric_tail_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (.impI (.impI (returned_identity _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem returned_geometric_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ bounded (var 3) one two ⟶
      bounded (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))))
        (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))
        (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (returned_bound _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmGeometricTail
