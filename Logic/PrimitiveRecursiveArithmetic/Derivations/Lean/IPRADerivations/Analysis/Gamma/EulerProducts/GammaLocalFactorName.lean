import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GammaCanonicalRemainder
import IPRADerivations.Analysis.Logarithm.DyadicComplexLogarithm
import IPRADerivations.Core.LinearCombination

/-!
# A regular local canonical factor name with its sharp cutoff certificate

The observations round the ORIGINAL finite factor from Gamma (C3), with
Taylor length `p+4` and denominator `2^(p+4)`.  The generic signed quotient
rounder and the original factor discrepancy supply their regularity.
Every fixed cutoff is compared with cofinal observations using the exact
degree-dependent C3 bound and the actual quotient rounding error.

All input codes and cutoffs are numerical, including arbitrary raw signed
coordinates.  This constructs the local power-series factor name; its
exponential identity and full Euler/Gamma construction remain separate.
-/

namespace LeanProofs.IPRA.Analysis.GammaLocalFactorName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder
  (re im add mul scale normSq bounded bounded_scale bounded_add bounded_neg bounded_mono
    normSq_eval eval_re_code eval_im_code congr_normSq)
open DyadicComplexLogarithm
  (rounded roundingError rounding_bound roundedDifference crossDifference
    cancel_bounded_scale rounded_comparison precision unit unit_add congr_add congr_scale congr_neg congr_rounded)
open GammaCanonicalFactors
  (factorNumerator factorDenominator factorDifference factorDenominator_positive finite_factor_cauchy finite_factor_bound)
open GammaCanonicalRemainder (tailScale finite_factor_remainder)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem factor_numerator_congr (z N : PTm n) {L K : PTm n} (h : Γ ⊢[PRAAx] L ≐ K) :
    Γ ⊢[PRAAx] factorNumerator z N L ≐ factorNumerator z N K := by
  simpa only [GammaCanonicalFactors.subst_factorNumerator, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    (Prf.eqCongr (Γ := Γ) (factorNumerator (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![z,N,L]) (σ' := ![z,N,K])
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact h))

theorem factor_denominator_congr (N : PTm n) {L K : PTm n} (h : Γ ⊢[PRAAx] L ≐ K) :
    Γ ⊢[PRAAx] factorDenominator N L ≐ factorDenominator N K :=
  congrMul (.eqRefl _) (ComplexLogarithmCauchy.congr_denominator h)

def observationTerm (p z _R N : PTm n) : PTm n :=
  rounded (factorNumerator z N (precision p)) (factorDenominator N (precision p)) (unit p)
def observationF : PR 4 := PTm.toPR (observationTerm (var 0) (var 1) (var 2) (var 3))
def observation (p z R N : PTm n) : PTm n := PTm.app observationF ![p,z,R,N]

@[simp] theorem subst_observationTerm {m : ℕ} (σ : Fin n → PTm m) (p z R N : PTm n) :
    Syn.subst σ (observationTerm p z R N) = observationTerm
      (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by simp [observationTerm]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R N : PTm n) :
    Syn.subst σ (observation p z R N) = observation
      (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by
  simp only [observation, ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem observation_compute (p z R N : PTm n) :
    Γ ⊢[PRAAx] observation p z R N ≐ observationTerm p z R N := by
  simpa [observation, observationF] using toPR_eq (Γ := Γ)
    (observationTerm (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,z,R,N]

theorem observation_later (p k z R N : PTm n) : Γ ⊢[PRAAx] observation (p+k) z R N ≐
    rounded (factorNumerator z N (precision p+k)) (factorDenominator N (precision p+k)) (unit p*pw two k) :=
  (observation_compute _ _ _ _).eqTrans (congr_rounded
    (factor_numerator_congr z N (DyadicComplexLogarithm.precision_add p k))
    (factor_denominator_congr N (DyadicComplexLogarithm.precision_add p k)) (unit_add p k))

def discrepancy (p k z R N : PTm n) : PTm n :=
  add (observation (p+k) z R N) (ComplexLogarithmRemainder.neg (scale (pw two k) (observation p z R N)))
@[simp] theorem subst_discrepancy {m : ℕ} (σ : Fin n → PTm m) (p k z R N : PTm n) :
    Syn.subst σ (discrepancy p k z R N) = discrepancy (Syn.subst σ p) (Syn.subst σ k)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by simp [discrepancy]

theorem discrepancy_compute (p k z R N : PTm n) : Γ ⊢[PRAAx] discrepancy p k z R N ≐
    roundedDifference (factorNumerator z N (precision p)) (factorNumerator z N (precision p+k))
      (factorDenominator N (precision p)) (factorDenominator N (precision p+k)) (unit p) (pw two k) :=
  congr_add (observation_later p k z R N) (congr_neg (congr_scale (observation_compute p z R N)))

theorem regular_bound (p k z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    bounded (discrepancy p k z R N) (two+num 3*pw two k) := by
  have hD := factorDenominator_positive N (precision p) hN
  have hE := factorDenominator_positive N (precision p+k) hN
  have hs : Γ ⊢[PRAAx] bounded (scale (unit p) (crossDifference
      (factorNumerator z N (precision p)) (factorNumerator z N (precision p+k))
      (factorDenominator N (precision p)) (factorDenominator N (precision p+k))))
      (factorDenominator N (precision p)*factorDenominator N (precision p+k)) := by
    simpa only [unit, crossDifference, factorDifference] using finite_factor_cauchy z N R (precision p) k hz hN hR
  exact le_congr (congr_normSq (discrepancy_compute p k z R N)).eqSymm (.eqRefl _)
    (rounded_comparison _ _ _ _ _ (pw two k) hD hE hs)

theorem regular_dyadic_bound (p k z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    bounded (discrepancy p k z R N) (num 5*pw two k) := by
  have hp := natEq (eq_add_of_le (ComplexLogarithmCauchy.power_positive two k
    (le_of_eq_add (d := one) (by ipra_ring) : Γ ⊢[PRAAx] le one two)))
  refine bounded_mono (regular_bound p k z R N hN hz hR) ?_
  refine le_of_eq_add (d := two*monus (pw two k) one) ?_
  ipra_lc 2*hp

theorem observation_congr {p q : PTm n} (z R N : PTm n) (h : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] observation p z R N ≐ observation q z R N := by
  apply congrApp observationF
  intro i
  fin_cases i
  · exact h
  · exact .eqRefl _
  · exact .eqRefl _
  · exact .eqRefl _

def endpointDifference (p q z R N : PTm n) : PTm n :=
  add (observation q z R N)
    (ComplexLogarithmRemainder.neg (scale (pw two (monus q p)) (observation p z R N)))
@[simp] theorem subst_endpointDifference {m : ℕ} (σ : Fin n → PTm m) (p q z R N : PTm n) :
    Syn.subst σ (endpointDifference p q z R N) = endpointDifference (Syn.subst σ p) (Syn.subst σ q)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by simp [endpointDifference]

theorem regular_endpoints (p q z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N)
    (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    bounded (endpointDifference p q z R N) (num 5*pw two (monus q p)) := by
  have e : Γ ⊢[PRAAx] endpointDifference p q z R N ≐ discrepancy p (monus q p) z R N :=
    congr_add (observation_congr z R N (eq_add_of_le hpq)) (.eqRefl _)
  exact le_congr (congr_normSq e).eqSymm (.eqRefl _)
    (regular_dyadic_bound p (monus q p) z R N hN hz hR)

def observationError (p z R N : PTm n) : PTm n :=
  add (scale (factorDenominator N (precision p)) (observation p z R N))
    (ComplexLogarithmRemainder.neg (scale (unit p) (factorNumerator z N (precision p))))
@[simp] theorem subst_observationError {m : ℕ} (σ : Fin n → PTm m) (p z R N : PTm n) :
    Syn.subst σ (observationError p z R N) = observationError
      (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by simp [observationError]

theorem observation_rounding (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (observationError p z R N) (two*factorDenominator N (precision p)) := by
  have e : Γ ⊢[PRAAx] observationError p z R N ≐ roundingError
      (factorNumerator z N (precision p)) (factorDenominator N (precision p)) (unit p) :=
    congr_add (congr_scale (observation_compute p z R N)) (.eqRefl _)
  exact le_congr (congr_normSq e).eqSymm (.eqRefl _)
    (rounding_bound _ _ _ (factorDenominator_positive N (precision p) hN))

theorem observation_disk_identity (p z R N : PTm n) : Γ ⊢[PRAAx]
    normSq (scale (factorDenominator N (precision p)) (scale (N*N) (observation p z R N))) ≐
      normSq (add (scale (N*N) (observationError p z R N))
        (scale (unit p) (scale (N*N) (factorNumerator z N (precision p))))) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [observationError, add, scale, ComplexLogarithmRemainder.neg,
    eval_re_code, eval_im_code, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  ring

/-- The actual dyadic value is in the source disk plus its two rounding
units: `|O_p/2^(p+4)| <= R²/N² + 2/2^(p+4)`. -/
theorem observation_disk_bound (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    bounded (scale (N*N) (observation p z R N)) (R*R*unit p+two*N*N) := by
  have first := bounded_scale (N*N) (observation_rounding p z R N hN)
  have second := bounded_scale (unit p) (finite_factor_bound z N R (precision p) hz hN hR)
  have total : Γ ⊢[PRAAx] bounded
      (scale (factorDenominator N (precision p)) (scale (N*N) (observation p z R N)))
      (factorDenominator N (precision p)*(R*R*unit p+two*N*N)) :=
    le_congr (observation_disk_identity p z R N).eqSymm (by ipra_ring) (bounded_add first second)
  exact cancel_bounded_scale (factorDenominator_positive N (precision p) hN) total

theorem cofinal_precision (p L : PTm n) : Γ ⊢[PRAAx] precision (p+L) ≐ L+precision p := by
  unfold precision
  ipra_ring

theorem observation_at_cutoff (p z R N L : PTm n) : Γ ⊢[PRAAx] observation (p+L) z R N ≐
    rounded (factorNumerator z N (L+precision p)) (factorDenominator N (L+precision p)) (unit (p+L)) :=
  (observation_compute _ _ _ _).eqTrans (congr_rounded
    (factor_numerator_congr z N (cofinal_precision p L))
    (factor_denominator_congr N (cofinal_precision p L)) (.eqRefl _))

def cutoffError (p z R N L : PTm n) : PTm n :=
  add (scale (factorDenominator N (L+precision p)) (observation (p+L) z R N))
    (ComplexLogarithmRemainder.neg (scale (unit (p+L)) (factorNumerator z N (L+precision p))))
@[simp] theorem subst_cutoffError {m : ℕ} (σ : Fin n → PTm m) (p z R N L : PTm n) :
    Syn.subst σ (cutoffError p z R N L) = cutoffError
      (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ L) := by simp [cutoffError]

theorem cutoff_rounding (p z R N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (cutoffError p z R N L) (two*factorDenominator N (L+precision p)) := by
  have e : Γ ⊢[PRAAx] cutoffError p z R N L ≐ roundingError
      (factorNumerator z N (L+precision p)) (factorDenominator N (L+precision p)) (unit (p+L)) :=
    congr_add (congr_scale (observation_at_cutoff p z R N L)) (.eqRefl _)
  exact le_congr (congr_normSq e).eqSymm (.eqRefl _)
    (rounding_bound _ _ _ (factorDenominator_positive N (L+precision p) hN))

/-- Cleared comparison of a cofinal actual name observation with the
ORIGINAL finite polynomial of degree `L+2`. -/
def cutoffDifference (p z R N L : PTm n) : PTm n :=
  add (scale (factorDenominator N L) (observation (p+L) z R N))
    (ComplexLogarithmRemainder.neg (scale (unit (p+L)) (factorNumerator z N L)))
@[simp] theorem subst_cutoffDifference {m : ℕ} (σ : Fin n → PTm m) (p z R N L : PTm n) :
    Syn.subst σ (cutoffDifference p z R N L) = cutoffDifference
      (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ L) := by simp [cutoffDifference]

theorem cutoff_decomposition (p z R N L : PTm n) : Γ ⊢[PRAAx]
    normSq (scale (factorDenominator N (L+precision p))
      (scale (tailScale L R N) (cutoffDifference p z R N L))) ≐
      normSq (add (scale (tailScale L R N*factorDenominator N L) (cutoffError p z R N L))
        (scale (unit (p+L)) (scale (tailScale L R N) (factorDifference z N L (precision p))))) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [cutoffDifference, cutoffError, factorDifference, add, scale, ComplexLogarithmRemainder.neg,
    eval_re_code, eval_im_code, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  ring

/-- Exact C3 for the actual name, with only its explicit quotient-rounding
allowance.  Dividing this formula by its positive denominator gives
`|O_(p+L)/2^(p+L+4)-factor_L| <= R^(L+3)/tailScale + 2/2^(p+L+4)`.
No cutoff convergence or output bound is a premise. -/
theorem sharp_cutoff_bound (p z R N L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hRN : Γ ⊢[PRAAx] le R N) : Γ ⊢[PRAAx]
    bounded (scale (tailScale L R N) (cutoffDifference p z R N L))
      (factorDenominator N L*(unit (p+L)*pw R (L+LogarithmRemainder.three)+two*tailScale L R N)) := by
  have first := bounded_scale (tailScale L R N*factorDenominator N L) (cutoff_rounding p z R N L hN)
  have second := bounded_scale (unit (p+L)) (finite_factor_remainder z N L R (precision p) hz hRN)
  have total : Γ ⊢[PRAAx] bounded
      (scale (factorDenominator N (L+precision p)) (scale (tailScale L R N) (cutoffDifference p z R N L)))
      (factorDenominator N (L+precision p)*
        (factorDenominator N L*(unit (p+L)*pw R (L+LogarithmRemainder.three)+two*tailScale L R N))) :=
    le_congr (cutoff_decomposition p z R N L).eqSymm (by ipra_ring) (bounded_add first second)
  exact cancel_bounded_scale (factorDenominator_positive N (L+precision p) hN) total

/-- The original half-disk and positive divisor give the strictly positive
geometric denominator, even at radius zero. -/
theorem half_disk_strict (R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx] lt R N := by
  refine .orE (zero_or_succ R) ?_ ?_
  · exact le_congr (congrSucc Prf.hyp0).eqSymm (.eqRefl _) hN.wk
  · have hp : ((R ≐ succ (PTm.pred R)) :: Γ) ⊢[PRAAx] le one R :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have step : ((R ≐ succ (PTm.pred R)) :: Γ) ⊢[PRAAx] le (succ R) (two*R) :=
      le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl R) hp)
    exact le_trans step hR.wk

theorem source_cutoff_certificate (p z R N L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    le one (tailScale L R N) ⋏ (le one (factorDenominator N L) ⋏
      bounded (scale (tailScale L R N) (cutoffDifference p z R N L))
        (factorDenominator N L*(unit (p+L)*pw R (L+LogarithmRemainder.three)+two*tailScale L R N))) := by
  have strict := half_disk_strict R N hN hR
  exact .andI (GammaCanonicalRemainder.scale_positive L R N strict) (.andI
    (factorDenominator_positive N L hN) (sharp_cutoff_bound p z R N L hN hz (le_of_lt strict)))

theorem unit_congr {p q : PTm n} (h : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx] unit p ≐ unit q :=
  congrAp2 powF (congrAdd h (.eqRefl (num 4))) (.eqRefl two)

def pairDifference (p q z R N : PTm n) : PTm n :=
  add (scale (unit p) (observation q z R N))
    (ComplexLogarithmRemainder.neg (scale (unit q) (observation p z R N)))
@[simp] theorem subst_pairDifference {m : ℕ} (σ : Fin n → PTm m) (p q z R N : PTm n) :
    Syn.subst σ (pairDifference p q z R N) = pairDifference
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by simp [pairDifference]

theorem ordered_pair_identity (p q z R N : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    normSq (pairDifference p q z R N) ≐ normSq (scale (unit p) (endpointDifference p q z R N)) := by
  have e := natEq ((unit_congr (Γ := Γ) (eq_add_of_le h)).eqTrans (unit_add p (monus q p)))
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [pairDifference, endpointDifference, add, scale, ComplexLogarithmRemainder.neg,
    eval_re_code, eval_im_code, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at e ⊢
  rw [e]
  ring

theorem pair_reverse_norm (p q z R N : PTm n) : Γ ⊢[PRAAx]
    normSq (pairDifference p q z R N) ≐ normSq (pairDifference q p z R N) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [pairDifference, add, scale, ComplexLogarithmRemainder.neg,
    eval_re_code, eval_im_code, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
  ring

theorem ordered_pair_bound (p q z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N)
    (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    bounded (pairDifference p q z R N) (num 5*(unit p+unit q)) := by
  have budget : Γ ⊢[PRAAx] le (unit p*(num 5*pw two (monus q p))) (num 5*(unit p+unit q)) := by
    refine le_of_eq_add (d := num 5*unit p) ?_
    ipra_lc 5*natEq ((unit_congr (Γ := Γ) (eq_add_of_le hpq)).eqTrans (unit_add p (monus q p)))
  exact le_congr (ordered_pair_identity p q z R N hpq).eqSymm (.eqRefl _)
    (bounded_mono (bounded_scale (unit p) (regular_endpoints p q z R N hN hz hR hpq)) budget)

theorem pair_bound (p q z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    bounded (pairDifference p q z R N) (num 5*(unit p+unit q)) := by
  refine .orE (le_total p q) (ordered_pair_bound _ _ _ _ _ hN.wk hz.wk hR.wk Prf.hyp0) ?_
  exact le_congr (pair_reverse_norm p q z R N).eqSymm (by ipra_ring)
    (ordered_pair_bound q p z R N hN.wk hz.wk hR.wk Prf.hyp0)

theorem unit_standard (p : PTm n) : Γ ⊢[PRAAx] unit p ≐ num 16*pw two p := by
  have e₂ : Γ ⊢[PRAAx] pw two two ≐ num 4 :=
    (pw_succ two one).eqTrans ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))
  have e₃ : Γ ⊢[PRAAx] pw two (num 3) ≐ num 8 :=
    (pw_succ two two).eqTrans ((congrMul e₂ (.eqRefl _)).eqTrans (by ipra_ring))
  have e₄ : Γ ⊢[PRAAx] pw two (num 4) ≐ num 16 :=
    (pw_succ two (num 3)).eqTrans ((congrMul e₃ (.eqRefl _)).eqTrans (by ipra_ring))
  exact (pw_add two p (num 4)).eqTrans ((congrMul (.eqRefl _) e₄).eqTrans (by ipra_ring))

/-- The source regular-name inequality at arbitrary independent precisions,
with the dyadic fractions fully cleared. -/
theorem regular_pair (p q z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    bounded (scale (pw two p*pw two q) (pairDifference p q z R N))
      (unit p*unit q*(pw two p+pw two q)) := by
  have e := natEq (unit_standard (Γ := Γ) p)
  have f := natEq (unit_standard (Γ := Γ) q)
  refine bounded_mono (bounded_scale (pw two p*pw two q) (pair_bound p q z R N hN hz hR)) ?_
  refine le_of_eq_add (d := num 176*pw two p*pw two q*(pw two p+pw two q)) ?_
  apply deriveNat
  ipra_simps
  rw [e,f]
  ring

theorem unit_positive (p : PTm n) : Γ ⊢[PRAAx] le one (unit p) :=
  ComplexLogarithmCauchy.power_positive two (precision p)
    (le_of_eq_add (d := one) (by ipra_ring))

theorem actual_local_factor_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (observation (var 0) (var 1) (var 2) (var 3) ≐
      rounded (factorNumerator (var 1) (var 3) (precision (var 0)))
        (factorDenominator (var 3) (precision (var 0))) (unit (var 0))) :=
  closeUniv 4 (observation_compute _ _ _ _)

theorem actual_local_factor_rounding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ (le one (unit (var 0)) ⋏
      (le one (factorDenominator (var 3) (precision (var 0))) ⋏
        bounded (observationError (var 0) (var 1) (var 2) (var 3))
          (two*factorDenominator (var 3) (precision (var 0)))))) :=
  closeUniv 4 (.impI (.andI (unit_positive _) (.andI
    (factorDenominator_positive _ _ Prf.hyp0) (observation_rounding _ _ _ _ Prf.hyp0))))

theorem regular_local_factor_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ bounded (var 2) (var 3) ⟶ le (two*var 3) (var 4) ⟶
      bounded (discrepancy (var 0) (var 1) (var 2) (var 3) (var 4)) (num 5*pw two (var 1))) :=
  closeUniv 5 (.impI (.impI (.impI (regular_dyadic_bound _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem ordered_local_factor_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ bounded (var 2) (var 3) ⟶ le (two*var 3) (var 4) ⟶ le (var 0) (var 1) ⟶
      bounded (endpointDifference (var 0) (var 1) (var 2) (var 3) (var 4))
        (num 5*pw two (monus (var 1) (var 0)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (regular_endpoints _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem arbitrary_precision_local_factor_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ bounded (var 2) (var 3) ⟶ le (two*var 3) (var 4) ⟶
      bounded (scale (pw two (var 0)*pw two (var 1))
        (pairDifference (var 0) (var 1) (var 2) (var 3) (var 4)))
        (unit (var 0)*unit (var 1)*(pw two (var 0)+pw two (var 1)))) :=
  closeUniv 5 (.impI (.impI (.impI (regular_pair _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem local_factor_name_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ bounded (var 1) (var 2) ⟶ le (two*var 2) (var 3) ⟶
      bounded (scale (var 3*var 3) (observation (var 0) (var 1) (var 2) (var 3)))
        (var 2*var 2*unit (var 0)+two*var 3*var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (observation_disk_bound _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_cofinal_factor_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (observation (var 0+var 4) (var 1) (var 2) (var 3) ≐
      rounded (factorNumerator (var 1) (var 3) (var 4+precision (var 0)))
        (factorDenominator (var 3) (var 4+precision (var 0))) (unit (var 0+var 4))) :=
  closeUniv 5 (observation_at_cutoff _ _ _ _ _)

/-- The actual regular name is compared with every original finite C3
cutoff, at a cofinal sample and with an explicit vanishing rounding term. -/
theorem sharp_local_factor_name_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (var 1) (var 2) ⟶ le (two*var 2) (var 3) ⟶
      (le one (tailScale (var 4) (var 2) (var 3)) ⋏
        (le one (factorDenominator (var 3) (var 4)) ⋏
          bounded (scale (tailScale (var 4) (var 2) (var 3))
            (cutoffDifference (var 0) (var 1) (var 2) (var 3) (var 4)))
            (factorDenominator (var 3) (var 4)*
              (unit (var 0+var 4)*pw (var 2) (var 4+LogarithmRemainder.three)+
                two*tailScale (var 4) (var 2) (var 3)))))) :=
  closeUniv 5 (.impI (.impI (.impI (source_cutoff_certificate _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GammaLocalFactorName
