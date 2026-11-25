import IPRADerivations.Analysis.GammaCanonicalFactors
import IPRADerivations.Core.LinearCombination

/-!
# Exact degree-dependent finite canonical Gamma remainder

Section 2, (C3), of `analysis/gamma_ipra` bounds the tail after degree
`d` by `|w|^(d+1)/((d+1)(1-|w|))`.  Here `d=L+2` and `w=z/N`.
The numerator programs are the original finite canonical factors.  A
genuine quantifier-free induction on the additional cutoff proves the
sharp geometric remainder, retaining `N-R` instead of replacing it by
`N/2`.  No logarithm, exponential, or limiting output law is assumed.

All radii, divisors, cutoffs and raw Gaussian numerator codes are numerical
inputs.  This is a finite certificate uniform in the later cutoff, not an
identification of the analytic logarithm or a construction of Gamma.
-/

namespace LeanProofs.IPRA.Analysis.GammaCanonicalRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.LogarithmRemainder
  (three denominator denominator_succ denominator_positive)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (scale bounded bounded_scale bounded_mono normSq normSq_eval eval_re_code eval_im_code)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.Analysis.Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The exact denominator of the source tail bound after degree `L+2`. -/
def tailScale (L R N : PTm n) : PTm n :=
  (L+three)*pw N (L+two)*monus N R

@[simp] theorem subst_tailScale {m : ℕ} (σ : Fin n → PTm m) (L R N : PTm n) :
    Syn.subst σ (tailScale L R N) =
      tailScale (Syn.subst σ L) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [tailScale]

/-- The unused geometric tail is kept in the induction invariant. -/
def strong (L R N K : PTm n) : Fm PTm n :=
  le (tailScale L R N*ComplexLogarithmCauchy.positive L R N K +
      denominator N L*fact (L+K+two)*pw N (L+two)*pw R (L+K+three))
    (pw R (L+three)*denominator N L*denominator N (L+K))

@[simp] theorem subst_strong {m : ℕ} (σ : Fin n → PTm m) (L R N K : PTm n) :
    (strong L R N K).subst σ = strong
      (Syn.subst σ L) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ K) := by
  simp [strong, fact]

theorem strong_zero (L R N : PTm n) : Γ ⊢[PRAAx] strong L R N zero := by
  have a := natEq (ComplexLogarithmCauchy.positive_zero (Γ := Γ) L R N)
  have f := natEq (congrAp2 (Γ := Γ) factF
    (congrAdd (add_zero L) (.eqRefl two)) (.eqRefl zero))
  have p := natEq (congrAp2 (Γ := Γ) powF
    (congrAdd (add_zero L) (.eqRefl three)) (.eqRefl R))
  have d := natEq (ComplexLogarithmCauchy.congr_denominator (N := N) (Γ := Γ) (add_zero L))
  unfold strong
  refine le_of_eq_add (d := zero) ?_
  apply deriveNat
  ipra_simps
  rw [a, f, p, d]
  simp only [denominator, Q.mk_mul, map_mul]
  ring

/-- The next stage leaves precisely a nonnegative `K*(N-R)` tail slack. -/
theorem strong_step {L R N K : PTm n} (hRN : Γ ⊢[PRAAx] le R N)
    (ih : Γ ⊢[PRAAx] strong L R N K) : Γ ⊢[PRAAx] strong L R N (succ K) := by
  have d := natEq ((ComplexLogarithmCauchy.congr_denominator (N := N) (Γ := Γ) (add_succ L K)).eqTrans
    (denominator_succ N (L+K)))
  have e₂ : Γ ⊢[PRAAx] L+succ K+two ≐ succ (L+K+two) := by ipra_ring
  have e₃ : Γ ⊢[PRAAx] L+succ K+three ≐ succ (L+K+three) := by ipra_ring
  unfold strong at *
  refine le_of_eq_add (d :=
    (L+K+three)*N*monus
      (pw R (L+three)*denominator N L*denominator N (L+K))
      (tailScale L R N*ComplexLogarithmCauchy.positive L R N K +
        denominator N L*fact (L+K+two)*pw N (L+two)*pw R (L+K+three)) +
    K*monus N R*denominator N L*fact (L+K+two)*pw N (L+two)*pw R (L+K+three)) ?_
  ipra_lc [tailScale] (𝔞(L)+𝔞(K)+3)*𝔞(N)*natEq (eq_add_of_le ih) +
    (𝔞(L)+𝔞(K)+3)*𝔞(denominator N L)*𝔞(fact (L+K+two))* 𝔞(pw N (L+two))*𝔞(pw R (L+K+three))*natEq (eq_add_of_le hRN) +
    𝔞(pw R (L+three))*𝔞(denominator N L)*d -
    (𝔞(L)+3)*𝔞(pw N (L+two))*𝔞(monus N R)*natEq (ComplexLogarithmCauchy.positive_succ (Γ := Γ) L R N K) -
    𝔞(denominator N L)*𝔞(pw N (L+two))*𝔞(pw R (L+succ K+three))*natEq ((congrAp2 factF e₂ (.eqRefl zero)).eqTrans (fact_succ (L+K+two) zero)) -
    𝔞(denominator N L)*𝔞(pw N (L+two))*𝔞(fact (L+K+two))* (𝔞(L)+𝔞(K)+3)*natEq ((congrAp2 powF e₃ (.eqRefl R)).eqTrans (pw_succ R (L+K+three)))

theorem finite_positive_strong (L R N K : PTm n) (hRN : Γ ⊢[PRAAx] le R N) :
    Γ ⊢[PRAAx] strong L R N K := by
  have all : Γ ⊢[PRAAx] .all (strong (Syn.shift L) (Syn.shift R) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_strong, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
        using strong_zero (Γ := Γ) L R N
    · simp only [subst_strong, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have shifted : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift R) (Syn.shift N) := by
        simpa [Fm.shift, Syn.shift] using hRN.shift
      exact strong_step shifted.wk Prf.hyp0
  simpa only [subst_strong, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    using Prf.allE K all

theorem finite_positive_bound (L R N K : PTm n) (hRN : Γ ⊢[PRAAx] le R N) :
    Γ ⊢[PRAAx] le (tailScale L R N*ComplexLogarithmCauchy.positive L R N K)
      (pw R (L+three)*denominator N L*denominator N (L+K)) :=
  le_trans (le_add_right _ _) (finite_positive_strong L R N K hRN)

/-- Exact finite C3 for the original cubic-and-higher Taylor recursor. -/
theorem finite_series_remainder (z N L R K : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hRN : Γ ⊢[PRAAx] le R N) :
    Γ ⊢[PRAAx] bounded (scale (tailScale L R N) (ComplexLogarithmCauchy.difference z N L K))
      (pw R (L+three)*denominator N L*denominator N (L+K)) :=
  bounded_mono (bounded_scale _ (ComplexLogarithmCauchy.difference_domination z N L R K hz))
    (finite_positive_bound L R N K hRN)

/-- The common quadratic term cancels: this is C3 for the actual canonical
factor, uniform in the later cutoff.  No analytic tail is supplied. -/
theorem finite_factor_remainder (z N L R K : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hRN : Γ ⊢[PRAAx] le R N) :
    Γ ⊢[PRAAx] bounded (scale (tailScale L R N) (GammaCanonicalFactors.factorDifference z N L K))
      (pw R (L+three)*GammaCanonicalFactors.factorDenominator N L*GammaCanonicalFactors.factorDenominator N (L+K)) := by
  have h := bounded_scale ((two*N*N)*(two*N*N)) (finite_series_remainder z N L R K hz hRN)
  have eq : Γ ⊢[PRAAx] normSq (scale (tailScale L R N) (GammaCanonicalFactors.factorDifference z N L K)) ≐
      normSq (scale ((two*N*N)*(two*N*N)) (scale (tailScale L R N) (ComplexLogarithmCauchy.difference z N L K))) := by
    apply deriveNat
    have E := natEq (GammaCanonicalFactors.difference_norm (Γ := Γ) z N L K (tailScale L R N))
    rw [E]
    rw [normSq_eval, normSq_eval]
    simp only [scale, eval_re_code, eval_im_code, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
    ring
  exact le_congr eq.eqSymm (by unfold GammaCanonicalFactors.factorDenominator; ipra_ring) h

/-- Strictly inside the geometric disk, the displayed remainder divisor is
positive, including radius zero. -/
theorem gap_positive (R N : PTm n) (h : Γ ⊢[PRAAx] lt R N) :
    Γ ⊢[PRAAx] le one (monus N R) := by
  have e : Γ ⊢[PRAAx] N ≐ R+succ (monus N (succ R)) :=
    (eq_add_of_le h).eqTrans (by ipra_ring)
  have g := (congrMonus e (.eqRefl R)).eqTrans (add_monus' (succ (monus N (succ R))) R)
  exact le_congr (.eqRefl _) g.eqSymm (zero_lt_succ _)

theorem scale_positive (L R N : PTm n) (h : Γ ⊢[PRAAx] lt R N) :
    Γ ⊢[PRAAx] le one (tailScale L R N) := by
  have hp : Γ ⊢[PRAAx] le one N := le_trans (zero_lt_succ R) h
  have hs : Γ ⊢[PRAAx] le one (L+three) := le_of_eq_add (d := L+two) (by ipra_ring)
  exact le_congr (by ipra_ring) (.eqRefl _)
    (le_mul_mono (le_mul_mono hs (ComplexLogarithmCauchy.power_positive N (L+two) hp))
      (gap_positive R N h))

/-- Source assumptions only: all three denominator components and the
actual finite-factor remainder bound are derived. -/
def certificate (z N L R K : PTm n) : Fm PTm n :=
  le one (tailScale L R N) ⋏
    (le one (GammaCanonicalFactors.factorDenominator N L) ⋏
      (le one (GammaCanonicalFactors.factorDenominator N (L+K)) ⋏
        bounded (scale (tailScale L R N) (GammaCanonicalFactors.factorDifference z N L K))
          (pw R (L+three)*GammaCanonicalFactors.factorDenominator N L*
            GammaCanonicalFactors.factorDenominator N (L+K))))

@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (z N L R K : PTm n) :
    (certificate z N L R K).subst σ = certificate
      (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [certificate]

theorem factor_certificate (z N L R K : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (h : Γ ⊢[PRAAx] lt R N) : Γ ⊢[PRAAx] certificate z N L R K := by
  have hp : Γ ⊢[PRAAx] le one N := le_trans (zero_lt_succ R) h
  exact .andI (scale_positive L R N h) (.andI
    (GammaCanonicalFactors.factorDenominator_positive N L hp) (.andI
      (GammaCanonicalFactors.factorDenominator_positive N (L+K) hp)
      (finite_factor_remainder z N L R K hz (le_of_lt h))))

/-- Actual error numerator, scale, two original denominators, and radius
power.  The payload contains the existing evaluator's literal outputs. -/
def output (z N L R K : PTm n) : PTm n :=
  pairT (GammaCanonicalFactors.factorDifference z N L K) (pairT (tailScale L R N)
    (pairT (GammaCanonicalFactors.factorDenominator N L)
      (pairT (GammaCanonicalFactors.factorDenominator N (L+K)) (pw R (L+three)))))

def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (z N L R K : PTm n) : PTm n := PTm.app outputF ![z,N,L,R,K]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (z N L R K : PTm n) :
    Syn.subst σ (output z N L R K) = output
      (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [output]

@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (z N L R K : PTm n) :
    Syn.subst σ (run z N L R K) = run
      (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ R) (Syn.subst σ K) := by
  simp only [run, ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (z N L R K : PTm n) : Γ ⊢[PRAAx] run z N L R K ≐ output z N L R K := by
  simpa [run, outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![z,N,L,R,K]

theorem returned_difference (z N L R K : PTm n) : Γ ⊢[PRAAx]
    fstT (run z N L R K) ≐ GammaCanonicalFactors.factorDifference z N L K :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)

theorem returned_scale (z N L R K : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run z N L R K)) ≐ tailScale L R N :=
  (congrFst ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)

theorem returned_lower_denominator (z N L R K : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run z N L R K))) ≐ GammaCanonicalFactors.factorDenominator N L :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (fst_pair _ _)

theorem returned_upper_denominator (z N L R K : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run z N L R K)))) ≐ GammaCanonicalFactors.factorDenominator N (L+K) :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)

theorem returned_radius_power (z N L R K : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run z N L R K)))) ≐ pw R (L+three) :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_remainder (z N L R K : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hRN : Γ ⊢[PRAAx] le R N) : Γ ⊢[PRAAx]
    bounded (scale (fstT (sndT (run z N L R K))) (fstT (run z N L R K)))
      (sndT (sndT (sndT (sndT (run z N L R K))))*
        fstT (sndT (sndT (run z N L R K)))*fstT (sndT (sndT (sndT (run z N L R K))))) := by
  have e : Γ ⊢[PRAAx]
      scale (fstT (sndT (run z N L R K))) (fstT (run z N L R K)) ≐
        scale (tailScale L R N) (GammaCanonicalFactors.factorDifference z N L K) := by
    simpa only [ComplexLogarithmRemainder.subst_scale, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using
      (Prf.eqCongr (Γ := Γ) (scale (var 0) (var 1) : PTm 2)
        (σ := ![fstT (sndT (run z N L R K)),fstT (run z N L R K)])
        (σ' := ![tailScale L R N,GammaCanonicalFactors.factorDifference z N L K])
        (fun i => by fin_cases i; exact returned_scale _ _ _ _ _; exact returned_difference _ _ _ _ _))
  have b := congrMul (congrMul (returned_radius_power (Γ := Γ) z N L R K)
    (returned_lower_denominator z N L R K)) (returned_upper_denominator z N L R K)
  exact le_congr (ComplexLogarithmRemainder.congr_normSq e).eqSymm
    (congrMul b b).eqSymm (finite_factor_remainder z N L R K hz hRN)

/-- Both cutoffs and the exact geometric slack remain numerical inputs. -/
theorem exact_positive_geometric_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 1) (var 2) ⟶ strong (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (finite_positive_strong _ _ _ _ Prf.hyp0))

theorem exact_finite_series_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (bounded (var 0) (var 3) ⟶ le (var 3) (var 1) ⟶
      bounded (scale (tailScale (var 2) (var 3) (var 1))
        (ComplexLogarithmCauchy.difference (var 0) (var 1) (var 2) (var 4)))
        (pw (var 3) (var 2+three)*denominator (var 1) (var 2)*
          denominator (var 1) (var 2+var 4))) :=
  closeUniv 5 (.impI (.impI (finite_series_remainder _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- Finite C3 with all actual positive denominator components. -/
theorem exact_finite_gamma_c3_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (bounded (var 0) (var 3) ⟶ lt (var 3) (var 1) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (factor_certificate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem geometric_gap_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 0) (var 1) ⟶ le one (monus (var 1) (var 0))) :=
  closeUniv 2 (.impI (gap_positive _ _ Prf.hyp0))

theorem exact_finite_gamma_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

theorem exact_finite_gamma_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
        GammaCanonicalFactors.factorDifference (var 0) (var 1) (var 2) (var 4) ⋏
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ tailScale (var 2) (var 3) (var 1) ⋏
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐
            GammaCanonicalFactors.factorDenominator (var 1) (var 2) ⋏
          (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐
              GammaCanonicalFactors.factorDenominator (var 1) (var 2+var 4) ⋏
            sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐
              pw (var 3) (var 2+three))))) :=
  closeUniv 5 (.andI (returned_difference _ _ _ _ _) (.andI (returned_scale _ _ _ _ _)
    (.andI (returned_lower_denominator _ _ _ _ _) (.andI (returned_upper_denominator _ _ _ _ _)
      (returned_radius_power _ _ _ _ _)))))

theorem exact_returned_gamma_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (bounded (var 0) (var 3) ⟶ le (var 3) (var 1) ⟶
      bounded (scale (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
        (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
        (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))*
          fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))*
          fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))) :=
  closeUniv 5 (.impI (.impI (returned_remainder _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GammaCanonicalRemainder
