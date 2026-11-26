import IPRADerivations.AnalyticNumberTheory.PerfectDivisorBounds
import IPRADerivations.AnalyticNumberTheory.MersenneExponent
import IPRADerivations.AnalyticNumberTheory.ValuationAdd
import IPRADerivations.AnalyticNumberTheory.FactorVector
import IPRADerivations.Core.Header

/-!
# The Euclid–Euler characterization of even perfect numbers

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`,
`chapters/elementary.tex`, `el:perfect`. For a positive even number
`N`, write `a = v₂(N)` and `m = N / 2^a` using the verified valuation
and cofactor programs. With `q = 2^{a+1} − 1`, perfection gives
`q σ(m) = (q+1)m`. Hence `q ∣ m` and, for `t = m/q`,
`σ(m) = m+t`. If `t > 1`, the actual divisor sum contains the three
distinct terms `1,t,m`, a contradiction. Thus `m=q`, and its divisor
sum proves its primality.

The closed characterization is stated with witness `a = e − 1`, so
`a ≥ 1`. The forward derivation supplies the primitive-recursive
witness `v₂(N)`. Primality of `e = a+1` uses the independent
Mersenne exponent theorem.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.EvenPerfectConverse

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (val_le)
open LeanProofs.IPRA.AnalyticNumberTheory.MersenneExponent
  (mersenne succ_mersenne two_le_mersenne prime_exponent)
open LeanProofs.IPRA.AnalyticNumberTheory.PerfectDivisorBounds (sigma_three sigma_gap prime_of_sigma)
open LeanProofs.IPRA.AnalyticNumberTheory.PerfectNumbers (euclid_perfect sig_two_pow mul_one_r)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaMult (sig sigma_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower (sig_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (coprime_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val cof_eq cof_not_dvd pw_val_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationAdd (le_val_of_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
  (dvd_of_eq' eq_of_dvd' dvd_sub' gcd_comm_one one_le_of_pos pos_of_eq_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem lt_quotient {q m t : PTm n} (hq : Γ ⊢[PRAAx] le two q)
    (ht : Γ ⊢[PRAAx] t ≐ succ (pred t)) (h : Γ ⊢[PRAAx] m ≐ q * t) :
    Γ ⊢[PRAAx] lt t m := by
  refine le_of_eq_add (d := monus q two * t + pred t) ?_
  ipra_lc natEq h + 𝔞 t * natEq (eq_add_of_le hq) + natEq ht

private theorem cofactor_eq_prime {q m : PTm n} (hq : Γ ⊢[PRAAx] le two q)
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] q * sig m ≐ succ q * m) :
    Γ ⊢[PRAAx] (m ≐ q) ⋏ prime q := by
  have qpos := p_pos hq
  have dsum : Γ ⊢[PRAAx] dvd q (m + q * m) :=
    dvd_of_eq' qpos (w := sig m) (h.eqTrans (by ipra_ring)).eqSymm
  have dividesM := dvd_sub' qpos dsum (dvd_of_eq' qpos (.eqRefl (q * m)))
  let t := quo m q
  have factored : Γ ⊢[PRAAx] m ≐ q * t := eq_of_dvd' qpos dividesM
  have tpos := pos_of_eq_mul hm factored
  have sigEq : Γ ⊢[PRAAx] sig m ≐ m + t := by
    refine mul_cancel qpos ?_
    ipra_lc natEq h + natEq factored
  have tOne : Γ ⊢[PRAAx] t ≐ one := by
    refine .orE (lt_or_le one t) ?_ ?_
    · have ht : (lt one t :: Γ) ⊢[PRAAx] lt one t := Prf.hyp0
      have bound := sigma_three ht (lt_quotient hq.wk tpos.wk factored.wk)
        (dvd_of_eq' tpos.wk (factored.wk.eqTrans (mul_comm _ _)))
      exact le_lt_absurd _ (le_congr (.eqRefl _) sigEq.wk bound) (sigma_gap t m)
    · exact le_antisymm Prf.hyp0 (one_le_of_pos tpos.wk)
  have mq := factored.eqTrans ((congrMul (.eqRefl _) tOne).eqTrans (mul_one_r q))
  refine .andI mq (prime_of_sigma hq ?_)
  exact (sig_congr mq.eqSymm).eqTrans (sigEq.eqTrans (congrAdd mq tOne))

/-- The exponent is written as `a + 1` in the standard even perfect form. -/
def perfectForm (N a : PTm n) : Fm PTm n :=
  le one a ⋏ (prime (mersenne (succ a)) ⋏ (N ≐ pw two a * mersenne (succ a)))

/-- Euler's direction with the explicit least-valuation witness. -/
theorem euler_witness {N : PTm n} (hN : Γ ⊢[PRAAx] le one N)
    (hEven : Γ ⊢[PRAAx] dvd two N) (hPerf : Γ ⊢[PRAAx] sig N ≐ two * N) :
    Γ ⊢[PRAAx] perfectForm N (val two N) := by
  let a := val two N
  let P := pw two a
  let m := quo N P
  let q := mersenne (succ a)
  have posN := pos_of_eq_succ ((eq_add_of_le hN).eqTrans (by ipra_ring))
  have he : Γ ⊢[PRAAx] le one a :=
    le_val_of_dvd (le_refl two) posN (dvd_congr_left (pw_one two).eqSymm hEven)
  have hFact : Γ ⊢[PRAAx] N ≐ P * m := cof_eq (le_refl two)
  have posP : Γ ⊢[PRAAx] P ≐ succ (pred P) := pw_val_pos (le_refl two)
  have posM := pos_of_eq_mul posN hFact
  have g2 := gcd_comm_one posM (gcd_prime (prime_two (Γ := Γ)) (cof_not_dvd (le_refl two) posN))
  have gP := gcd_comm_one posP (coprime_pow posM g2 a)
  have sigFact := (sig_congr hFact).eqTrans (sigma_mul posP posM gP)
  have sigP : Γ ⊢[PRAAx] sig P ≐ q :=
    add_right_cancel ((sig_two_pow a).eqTrans
      ((succ_mersenne (succ a)).eqSymm.eqTrans (succ_eq_add_one q)))
  have powers : Γ ⊢[PRAAx] succ q ≐ P * two :=
    (succ_mersenne (succ a)).eqTrans (pw_succ two a)
  have sigOdd : Γ ⊢[PRAAx] q * sig m ≐ succ q * m := by
    refine ((congrMul sigP.eqSymm (.eqRefl _)).eqTrans sigFact.eqSymm).eqTrans (hPerf.eqTrans ?_)
    ipra_lc 2 * natEq hFact - 𝔞 m * natEq powers
  have q2 : Γ ⊢[PRAAx] le two q :=
    two_le_mersenne ((succ_monus_succ one a).eqTrans he)
  have result := cofactor_eq_prime q2 posM sigOdd
  exact .andI he (.andI (Prf.andE₂ result) (hFact.eqTrans (congrMul (.eqRefl _) (Prf.andE₁ result))))

theorem euclid_from_witness {N a : PTm n} (h : Γ ⊢[PRAAx] perfectForm N a) :
    Γ ⊢[PRAAx] sig N ≐ two * N := by
  have form := Prf.andE₂ (Prf.andE₂ h)
  exact (sig_congr form).eqTrans ((euclid_perfect (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h))
    (succ_mersenne (succ a))).eqTrans (congrMul (.eqRefl _) form.eqSymm))

theorem prime_exponent_of_perfect_form {N a : PTm n} (h : Γ ⊢[PRAAx] perfectForm N a) :
    Γ ⊢[PRAAx] prime (succ a) :=
  prime_exponent ((succ_monus_succ one a).eqTrans (Prf.andE₁ h)) (Prf.andE₁ (Prf.andE₂ h))

def hasForm (N : PTm n) : Fm PTm n := Fm.ex (perfectForm (Syn.shift N) (var 0))

private theorem euler_exists {N : PTm n} (hN : Γ ⊢[PRAAx] le one N)
    (hEven : Γ ⊢[PRAAx] dvd two N) (hPerf : Γ ⊢[PRAAx] sig N ≐ two * N) :
    Γ ⊢[PRAAx] hasForm N := by
  unfold hasForm
  refine .exI (val two N) ?_
  simp only [perfectForm, Fm.subst_and, Fm.subst_eq, subst_le, Fermat.subst_prime, subst_ap2,
    PTm.subst_mul, PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  exact euler_witness hN hEven hPerf

private theorem euclid_exists {N : PTm n} (h : Γ ⊢[PRAAx] hasForm N) :
    Γ ⊢[PRAAx] sig N ≐ two * N := by
  unfold hasForm at h
  refine .exE h ?_
  simp only [Fm.shift, Fm.subst_eq, subst_ap2, PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  exact euclid_from_witness Prf.hyp0

def characterizationFormula : Fm PTm 1 :=
  le one (var 0) ⟶ dvd two (var 0) ⟶
    (((sig (var 0) ≐ two * var 0) ⟶ hasForm (var 0)) ⋏
      (hasForm (var 0) ⟶ (sig (var 0) ≐ two * var 0)))

/-- The two directions of Euclid–Euler for every positive even input. -/
theorem euclid_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 characterizationFormula :=
  closeUniv 1 (.impI (.impI (.andI (.impI (euler_exists hyp2 Prf.hyp1 Prf.hyp0))
    (.impI (euclid_exists Prf.hyp0)))))

/-- The actual exponent minus one is bounded by the input and certifies the full representation. -/
def certifiedWitnessFormula (N : PTm n) : Fm PTm n :=
  le (val two N) N ⋏ (perfectForm N (val two N) ⋏ prime (succ (val two N)))

theorem certified_witness {N : PTm n} (hN : Γ ⊢[PRAAx] le one N)
    (hEven : Γ ⊢[PRAAx] dvd two N) (hPerf : Γ ⊢[PRAAx] sig N ≐ two * N) :
    Γ ⊢[PRAAx] certifiedWitnessFormula N := by
  have form := euler_witness hN hEven hPerf
  have posN := pos_of_eq_succ ((eq_add_of_le hN).eqTrans (by ipra_ring))
  exact .andI (val_le (le_refl two) posN) (.andI form (prime_exponent_of_perfect_form form))

def witnessSentence : Fm PTm 1 :=
  le one (var 0) ⟶ dvd two (var 0) ⟶ (sig (var 0) ≐ two * var 0) ⟶ certifiedWitnessFormula (var 0)

theorem certified_even_perfect_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 witnessSentence :=
  closeUniv 1 (.impI (.impI (.impI (certified_witness hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.AnalyticNumberTheory.EvenPerfectConverse
