import IPRADerivations.Analysis.GaussianGammaRecurrenceSourceObservations
import IPRADerivations.Analysis.GaussianGammaRecurrenceCoefficientBounds
import IPRADerivations.Analysis.GaussianRationalRiemannRefinement

/-!
# The original recurrence sum against canonical coefficient observations

The literal finite sum uses the SAME global coefficient names and the
literal full original gamma/zeta weight samples at a common query p.
Original source coefficient and weight observation errors, the unchanged
coefficient mass bound, and an actual finite maximum of full weight name
bounds give computed errors for every actual product term. The genuine
finite Gaussian sum program adds those errors. No term/sum comparison or
recurrence is assumed as an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalRecurrenceTerms

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianGammaHigherCoefficientName (sample)
open GaussianGammaRecurrenceWeights (weight)
open GaussianGammaRecurrenceSourceObservations (precision sourceRadius sourceCoefficient sourceSum cap denominator_positive)
open GaussianGammaRecurrenceCoefficientBounds (uniformWeightBound)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientBound (e : PTm n) : PTm n := GaussianGammaUnitCoefficientMass.budget (sourceRadius e)
def queryFactor (e : PTm n) : PTm n := coefficientBound e+uniformWeightBound e
def sourceFactor (e : PTm n) : PTm n := coefficientBound e+uniformWeightBound e*cap e
def termNumerator (t p e : PTm n) : PTm n := sourceFactor e*unit p+queryFactor e*unit t
def sourceTerm (t e j : PTm n) : PTm n := GaussianGammaFixedCoefficientRecurrence.term (precision t e) (sourceRadius e) e j
def canonicalTerm (p e j : PTm n) : PTm n := qmul (weight p zero (monus e j)) (sample p j)
def data (p e : PTm n) : PTm n := pairT p e
def body : PTm 2 := canonicalTerm (fstT (var 1)) (sndT (var 1)) (var 0)
def canonicalSum (p e : PTm n) : PTm n := GaussianRationalFiniteSum.sum body e (data p e)
@[simp] theorem subst_coefficientBound {l : ℕ} (σ : Fin n → PTm l) (e : PTm n) :
    Syn.subst σ (coefficientBound e) = coefficientBound (Syn.subst σ e) := by simp [coefficientBound]
@[simp] theorem subst_queryFactor {l : ℕ} (σ : Fin n → PTm l) (e : PTm n) :
    Syn.subst σ (queryFactor e) = queryFactor (Syn.subst σ e) := by simp [queryFactor]
@[simp] theorem subst_sourceFactor {l : ℕ} (σ : Fin n → PTm l) (e : PTm n) :
    Syn.subst σ (sourceFactor e) = sourceFactor (Syn.subst σ e) := by simp [sourceFactor]
@[simp] theorem subst_termNumerator {l : ℕ} (σ : Fin n → PTm l) (t p e : PTm n) :
    Syn.subst σ (termNumerator t p e) = termNumerator (Syn.subst σ t) (Syn.subst σ p) (Syn.subst σ e) := by simp [termNumerator]
@[simp] theorem subst_sourceTerm {l : ℕ} (σ : Fin n → PTm l) (t e j : PTm n) :
    Syn.subst σ (sourceTerm t e j) = sourceTerm (Syn.subst σ t) (Syn.subst σ e) (Syn.subst σ j) := by simp [sourceTerm]
@[simp] theorem subst_canonicalTerm {l : ℕ} (σ : Fin n → PTm l) (p e j : PTm n) :
    Syn.subst σ (canonicalTerm p e j) = canonicalTerm (Syn.subst σ p) (Syn.subst σ e) (Syn.subst σ j) := by simp [canonicalTerm]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (p e : PTm n) :
    Syn.subst σ (data p e) = data (Syn.subst σ p) (Syn.subst σ e) := by simp [data]
@[simp] theorem subst_canonicalSum {l : ℕ} (σ : Fin n → PTm l) (p e : PTm n) :
    Syn.subst σ (canonicalSum p e) = canonicalSum (Syn.subst σ p) (Syn.subst σ e) := by simp [canonicalSum]

theorem source_radius_positive (e : PTm n) : Γ ⊢[PRAAx] le one (sourceRadius e) :=
  GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive (succ e) (zero_lt_succ e)

theorem original_source_coefficient_bound (t e j : PTm n) : Γ ⊢[PRAAx]
    bounded (sourceCoefficient t e j) (coefficientBound e) one :=
  GaussianGammaRecurrenceCoefficientBounds.original_fixed_sample_bound _ _ _ (source_radius_positive e)

theorem original_term_error (t p e j : PTm n) (hj : Γ ⊢[PRAAx] le j e) : Γ ⊢[PRAAx]
    distanceBounded (sourceTerm t e j) (canonicalTerm p e j) (termNumerator t p e) (unit t*unit p) :=
  distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)
    (by unfold termNumerator sourceFactor queryFactor; ipra_ring) (.eqRefl _)
      (GaussianNameArithmetic.product_distance _ _ _ _ _ _ _ _ _ (denominator_positive t p)
        (GaussianGammaRecurrenceSourceObservations.original_weight_error t p e (monus e j))
        (GaussianGammaRecurrenceSourceObservations.original_coefficient_error t p e j hj)
        (original_source_coefficient_bound t e j)
        (GaussianGammaRecurrenceCoefficientBounds.original_full_weight_sample_bound p e (monus e j)
          (GaussianRationalMonicReconstruction.monus_le_left _ _)))

theorem canonical_term_congr {p q e f j k : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q)
    (he : Γ ⊢[PRAAx] e ≐ f) (hj : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx] canonicalTerm p e j ≐ canonicalTerm q f k := by
  simpa only [subst_canonicalTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (canonicalTerm (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,e,j]) (σ' := ![q,f,k]) (fun i => by fin_cases i; exact hp; exact he; exact hj)

theorem canonical_term_at (p e j : PTm n) : Γ ⊢[PRAAx] inst2 body j (data p e) ≐ canonicalTerm p e j := by
  simp only [body,inst2,subst_canonicalTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact canonical_term_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)

theorem original_terms_error (t p e : PTm n) : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.termsDistance
    GaussianGammaFixedCoefficientRecurrence.body body e
      (GaussianGammaFixedCoefficientRecurrence.sumData (precision t e) (sourceRadius e) e) (data p e)
        (termNumerator t p e) (unit t*unit p) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift e) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := le_of_lt Prf.hyp0
  have h := distance_congr
    (GaussianGammaFixedCoefficientRecurrence.term_at (Γ := Δ) (precision (Syn.shift t) (Syn.shift e))
      (sourceRadius (Syn.shift e)) (Syn.shift e) (var 0)).eqSymm
    (canonical_term_at (Syn.shift p) (Syn.shift e) (var 0)).eqSymm (.eqRefl _) (.eqRefl _)
      (original_term_error _ _ _ _ hi)
  simpa only [Δ,Syn.shift,GaussianGammaFixedCoefficientRecurrence.subst_sumData,
    GaussianGammaRecurrenceSourceObservations.subst_precision,GaussianGammaRecurrenceSourceObservations.subst_sourceRadius,
    subst_data,subst_termNumerator,GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul] using h

theorem original_sum_error (t p e : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (sourceSum t e) (canonicalSum p e) (e*termNumerator t p e) (unit t*unit p) :=
  GaussianRationalRiemannRefinement.sum_distance _ _ _ _ _ _ _ (denominator_positive t p) (original_terms_error t p e)

theorem original_Gamma_recurrence_source_to_canonical_product_terms_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 2) ⟶ distanceBounded (sourceTerm (var 0) (var 2) (var 3)) (canonicalTerm (var 1) (var 2) (var 3))
      (termNumerator (var 0) (var 1) (var 2)) (unit (var 0)*unit (var 1))) :=
  closeUniv 4 (.impI (original_term_error _ _ _ _ Prf.hyp0))

theorem original_Gamma_recurrence_actual_source_sum_to_canonical_named_sum_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (distanceBounded (sourceSum (var 0) (var 2)) (canonicalSum (var 1) (var 2))
        (var 2*termNumerator (var 0) (var 1) (var 2)) (unit (var 0)*unit (var 1))) :=
  closeUniv 3 (original_sum_error _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalRecurrenceTerms
