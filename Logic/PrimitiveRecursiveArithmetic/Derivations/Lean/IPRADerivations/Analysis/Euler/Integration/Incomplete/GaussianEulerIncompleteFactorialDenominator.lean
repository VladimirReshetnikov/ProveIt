import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteFactorialPolynomial
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.CertificateTactics

/-!
# Integer numerator and exact factorial quotients of the incomplete polynomial

An actual natural recurrence computes the numerator over the ideal
denominator b^N. A genuine QF induction identifies that returned fraction
with N! times the original Gaussian finite exponential sum. Exact native
factorial quotients are also derived from the existing proved binomial
division theorem; no divisibility or output identity is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteFactorialDenominator

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteFactorialPolynomial (polynomial polynomial_zero polynomial_succ)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents radius_congr radius_multiply radius_power)
open GaussianRationalHorner (qadd canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalNaturalScale (natScale)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def stepBody : PTm 3 := succ (var 0)*sndT (var 2)*var 1+pw (fstT (var 2)) (succ (var 0))
def numeratorF : PR 2 := rec2 (one : PTm 1) stepBody
def numerator (N a b : PTm n) : PTm n := ap2 numeratorF N (pairT a b)
def denominator (N b : PTm n) : PTm n := pw b N
def quotient (N j : PTm n) : PTm n := quo (fact N) (fact j)
def normalForm (N a b : PTm n) : Fm PTm n := polynomial N a b ≐ radiusPoint (numerator N a b) (denominator N b)

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (N a b : PTm n) :
    Syn.subst σ (numerator N a b) = numerator (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (N b : PTm n) :
    Syn.subst σ (denominator N b) = denominator (Syn.subst σ N) (Syn.subst σ b) := by simp [denominator]
@[simp] theorem subst_quotient {m : ℕ} (σ : Fin n → PTm m) (N j : PTm n) :
    Syn.subst σ (quotient N j) = quotient (Syn.subst σ N) (Syn.subst σ j) := by simp [quotient,fact]
@[simp] theorem subst_normalForm {m : ℕ} (σ : Fin n → PTm m) (N a b : PTm n) :
    (normalForm N a b).subst σ = normalForm (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [normalForm]

theorem numerator_zero (a b : PTm n) : Γ ⊢[PRAAx] numerator zero a b ≐ one := by
  simpa [numerator,numeratorF] using rec2_zero (Γ := Γ) (one : PTm 1) stepBody (pairT a b)

theorem numerator_succ (N a b : PTm n) : Γ ⊢[PRAAx]
    numerator (succ N) a b ≐ succ N*b*numerator N a b+pw a (succ N) := by
  have h := rec2_succ (Γ := Γ) (one : PTm 1) stepBody N (pairT a b)
  have first : Γ ⊢[PRAAx] numerator (succ N) a b ≐ succ N*sndT (pairT a b)*numerator N a b+pw (fstT (pairT a b)) (succ N) := by
    simpa [numerator,numeratorF,stepBody] using h
  exact first.eqTrans (congrAdd (congrMul (congrMul (.eqRefl _) (snd_pair _ _)) (.eqRefl _))
    (congrAp2 powF (.eqRefl _) (fst_pair _ _)))

theorem denominator_positive (N b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] le one (denominator N b) :=
  GaussianPolynomialPerturbation.power_positive b N hb

theorem scaled_radius (m A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    natScale m (radiusPoint A B) ≐ radiusPoint (m*A) B := by
  have rep := GaussianRationalNaturalScale.natScale_represents m (radiusPoint A B) (radiusNumerator A) B hB (radius_represents A B hB)
  apply canonical_unique _ _ _ _ (GaussianRationalNaturalScale.natScale_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hB
    (hrv := radius_represents (m*A) B hB)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) rep
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [radiusNumerator,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
  all_goals ipra_simps
  all_goals ring

theorem radius_add_same (A C B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (radiusPoint A B) (radiusPoint C B) ≐ radiusPoint (A+C) B := by
  have rep := GaussianRationalHorner.qadd_represents _ _ _ _ _ hB (radius_represents A B hB) (radius_represents C B hB)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hB
    (hrv := radius_represents (A+C) B hB)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) rep
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [radiusNumerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
  all_goals ipra_simps
  all_goals ring

theorem radius_rescale (A B c : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le one c) : Γ ⊢[PRAAx]
    radiusPoint (A*c) (B*c) ≐ radiusPoint A B := by
  have hD := positive_product (Γ := Γ) B c hB hc
  have right := GaussianRationalHorner.represents_rescale (radiusPoint A B) (radiusNumerator A) B c (radius_represents A B hB)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hD)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hD (radius_represents (A*c) (B*c) hD)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) right
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [radiusNumerator,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
  all_goals ipra_simps
  all_goals ring

theorem normal_form_zero (a b : PTm n) : Γ ⊢[PRAAx] normalForm zero a b :=
  (polynomial_zero a b).eqTrans ((radius_congr (numerator_zero a b) (pw_zero b)).eqTrans GaussianDominantPairAlgebra.radius_one).eqSymm

theorem normal_form_step (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] normalForm N a b) : Γ ⊢[PRAAx] normalForm (succ N) a b := by
  let U := numerator N a b
  let V := denominator N b
  let W := denominator (succ N) b
  have hV := denominator_positive (Γ := Γ) N b hb
  have hW := denominator_positive (Γ := Γ) (succ N) b hb
  have scaled : Γ ⊢[PRAAx] natScale (succ N) (polynomial N a b) ≐ radiusPoint (succ N*b*U) W :=
    (GaussianRationalNaturalScale.natScale_congr (.eqRefl _) h).eqTrans
      ((scaled_radius (succ N) U V hV).eqTrans
        ((radius_rescale (succ N*U) V b hV hb).eqSymm.eqTrans
          (radius_congr (by ipra_ring) (pw_succ b N).eqSymm)))
  have power : Γ ⊢[PRAAx] GaussianRationalReciprocal.power (GaussianPositiveRationalLogarithm.fraction a b) (succ N) ≐ radiusPoint (pw a (succ N)) W :=
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb)).eqTrans
      (radius_power a b (succ N) hb)
  exact (polynomial_succ N a b).eqTrans ((qadd_congr scaled power).eqTrans
    ((radius_add_same _ _ W hW).eqTrans (radius_congr (numerator_succ N a b).eqSymm (.eqRefl _))))

/-- The returned denominator is exactly b^N, including N=0 and a=0. -/
theorem ideal_common_denominator (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    polynomial N a b ≐ radiusPoint (numerator N a b) (denominator N b) := by
  change Γ ⊢[PRAAx] normalForm N a b
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hb.shift
  have all : Γ ⊢[PRAAx] .all (normalForm (var 0) (Syn.shift a) (Syn.shift b)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_normalForm,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using normal_form_zero (Γ := Γ) a b
    · simp only [subst_normalForm,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact normal_form_step _ _ _ bs.wk Prf.hyp0
  simpa only [subst_normalForm,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem quotient_integer_form (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    quotient N j ≐ fact (monus N j)*Combinatorics.Binomial.binom N j :=
  Combinatorics.Binomial.quo_of_eq (AnalyticNumberTheory.Primes.fact_pos j)
    ((Combinatorics.BinomialIdentities.binom_eq hj).eqTrans (by unfold Combinatorics.Binomial.bden; ipra_ring))

theorem quotient_exact (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    fact j*quotient N j ≐ fact N := by
  ipra_lc (Groth.ι (Q.mk Γ (fact j)))*natEq (quotient_integer_form (Γ := Γ) N j hj)-
    natEq (Combinatorics.BinomialIdentities.binom_eq hj)

theorem quotient_diagonal (N : PTm n) : Γ ⊢[PRAAx] quotient N N ≐ one :=
  Combinatorics.Binomial.quo_of_eq (AnalyticNumberTheory.Primes.fact_pos N) (by ipra_ring)

theorem quotient_succ (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    quotient (succ N) j ≐ succ N*quotient N j := by
  apply Combinatorics.BinomialIdentities.mul_cancel (AnalyticNumberTheory.Primes.fact_pos j)
  ipra_lc natEq (quotient_exact (Γ := Γ) (succ N) j (le_trans hj (le_succ_self N)))-
    (𝔞 N+1)*natEq (quotient_exact (Γ := Γ) N j hj)+natEq (fact_succ (Γ := Γ) N zero)

def output (N a b : PTm n) : PTm n := pairT (polynomial N a b) (pairT (numerator N a b) (denominator N b))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (N a b : PTm n) : PTm n := ap3 outputF N a b
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (N a b : PTm n) :
    Syn.subst σ (output N a b) = output (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [output]
theorem program_at (N a b : PTm n) : Γ ⊢[PRAAx] run N a b ≐ output N a b := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![N,a,b]
theorem returned_value (N a b : PTm n) : Γ ⊢[PRAAx] fstT (run N a b) ≐ polynomial N a b :=
  (congrFst (program_at N a b)).eqTrans (fst_pair _ _)
theorem returned_tail (N a b : PTm n) : Γ ⊢[PRAAx] sndT (run N a b) ≐ pairT (numerator N a b) (denominator N b) :=
  (congrSnd (program_at N a b)).eqTrans (snd_pair _ _)
theorem returned_numerator (N a b : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run N a b)) ≐ numerator N a b :=
  (congrFst (returned_tail N a b)).eqTrans (fst_pair _ _)
theorem returned_denominator (N a b : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run N a b)) ≐ denominator N b :=
  (congrSnd (returned_tail N a b)).eqTrans (snd_pair _ _)

theorem actual_incomplete_factorial_polynomial_ideal_denominator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ polynomial (var 0) (var 1) (var 2) ≐ radiusPoint (numerator (var 0) (var 1) (var 2)) (pw (var 2) (var 0))) :=
  closeUniv 3 (.impI (ideal_common_denominator _ _ _ Prf.hyp0))
theorem actual_incomplete_factorial_polynomial_numerator_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (numerator (succ (var 0)) (var 1) (var 2) ≐ succ (var 0)*var 2*numerator (var 0) (var 1) (var 2)+pw (var 1) (succ (var 0))) :=
  closeUniv 3 (numerator_succ _ _ _)
theorem actual_exact_factorial_quotients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (var 0) ⟶ fact (var 1)*quotient (var 0) (var 1) ≐ fact (var 0)) :=
  closeUniv 2 (.impI (quotient_exact _ _ Prf.hyp0))
theorem actual_incomplete_factorial_polynomial_returned_fraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ fstT (run (var 0) (var 1) (var 2)) ≐
      radiusPoint (fstT (sndT (run (var 0) (var 1) (var 2)))) (sndT (sndT (run (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI ((returned_value _ _ _).eqTrans ((ideal_common_denominator _ _ _ Prf.hyp0).eqTrans
    (radius_congr (returned_numerator _ _ _).eqSymm (returned_denominator _ _ _).eqSymm))))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteFactorialDenominator
