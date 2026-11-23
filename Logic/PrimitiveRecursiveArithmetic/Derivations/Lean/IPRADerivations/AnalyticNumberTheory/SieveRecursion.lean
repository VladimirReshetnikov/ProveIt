import IPRADerivations.AnalyticNumberTheory.SieveSurvivors
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.AnalyticNumberTheory.SievePairSum
import IPRADerivations.DiophantineNumberTheory.QuarticStep

/-!
# The recursion of Legendre's sieve

Packet: `analytic-number-theory/prime-counting-ipra`, `sections/sieve.tex`, Proposition "Legendre's identity and
sieve recursion", second identity: `Φ(N, a) + Φ(⌊N/p_a⌋, a − 1) = Φ(N, a − 1)`.

Here `Φ(x; P) = #{1 ≤ m ≤ x : gcd(m, P) = 1}` (`Phi`, the sum of `LegendreSieve.coB`), and the list of the first
primes is replaced by a modulus: for a prime `p` and `P ≥ 1` with `gcd(p, P) = 1`,

    Φ(x; P) = Φ(x; P p) + Φ(⌊x/p⌋; P)                                             (**`recursion`**).

The packet's proof: "the integers lost at step `a` are exactly `p_a u` with `1 ≤ u ≤ N/p_a` surviving step
`a − 1`."

* `pt`: at each `m`, `[gcd(m, P) = 1] = [gcd(m, P p) = 1] + [p ∣ m][gcd(m/p, P) = 1]` (with the factors
  `[m ≥ 1]`, `[m/p ≥ 1]`), by the cases `m = 0`, `p ∣ m`, `p ∤ m`;
* `cM_succ`: there are `⌊x/p⌋ + 1` multiples of `p` in `[0, x]`;
* `recursion`: the sum over `m ≤ x`, the multiples reindexed by `SumReindex.reindex_eq`;
* **`phi_step_prime`**, `phi_step_comp`, **`phi_step`**: for the primorials `P(r)`:
  `Φ(x; P(r)) = Φ(x; P(r + 1)) + [r + 1 prime] Φ(⌊x/(r + 1)⌋; P(r))`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveRecursion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP isP_01 prime_of_isP)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (subst_isP f_one f_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt' zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (count_multiples quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq cM)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairSum (subst_gcd')
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialUpper (pri pri_pos pri_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.LegendreSieve (coB inst2_coB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveSurvivors (not_coprime le_of_dvd_pri)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (quo_small)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' gcd_comm_one pos_of_eq_mul
  coprime_dvd_left coprime_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb one_ne_zero)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The term at `m` -/

theorem z_alg {s b3 b1 e su b2 : PTm n} (hs : Γ ⊢[PRAAx] s ≐ zero) (hsu : Γ ⊢[PRAAx] su ≐ zero) :
    Γ ⊢[PRAAx] s * b3 ≐ s * b1 + e * (su * b2) := by
  have a := natEq hs; have b := natEq hsu
  apply deriveNat; ipra_simps; linear_combination (𝔞 b3 - 𝔞 b1) * a - 𝔞 e * 𝔞 b2 * b

theorem a_alg {s b3 b1 e su b2 : PTm n} (hs : Γ ⊢[PRAAx] s ≐ one) (hb1 : Γ ⊢[PRAAx] b1 ≐ zero)
    (he : Γ ⊢[PRAAx] e ≐ one) (hsu : Γ ⊢[PRAAx] su ≐ one) (h : Γ ⊢[PRAAx] b2 ≐ b3) :
    Γ ⊢[PRAAx] s * b3 ≐ s * b1 + e * (su * b2) := by
  have a := natEq hs; have b := natEq hb1; have c := natEq he; have d := natEq hsu; have f := natEq h
  apply deriveNat; ipra_simps
  linear_combination 𝔞 b3 * a - 𝔞 s * b - 𝔞 su * 𝔞 b2 * c - 𝔞 b2 * d - f

theorem b_alg {s b3 b1 e X : PTm n} (he : Γ ⊢[PRAAx] e ≐ zero) (h : Γ ⊢[PRAAx] b1 ≐ b3) :
    Γ ⊢[PRAAx] s * b3 ≐ s * b1 + e * X := by
  have a := natEq he; have b := natEq h
  apply deriveNat; ipra_simps; linear_combination -𝔞 s * b - 𝔞 X * a

/-- `[gcd(m, P) = 1] = [gcd(m, P p) = 1] + [p ∣ m][gcd(m/p, P) = 1]` for a prime `p` coprime to `P ≥ 1`. -/
theorem pt {m p P : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hP : Γ ⊢[PRAAx] P ≐ succ (pred P))
    (hc : Γ ⊢[PRAAx] gcd p P ≐ one) :
    Γ ⊢[PRAAx] inst2 coB m P ≐ inst2 coB m (P * p) + inst2 (riB coB) m (pairT p P) := by
  have hp1 := p_pos (prime_two hp)
  have r : Γ ⊢[PRAAx] inst2 (riB coB) m (pairT p P) ≐ eqb (rem m p) zero * inst2 coB (quo m p) P := by
    rw [inst2_riB]
    exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
      (congrInst2 coB (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))
  refine .eqTrans ?_ (congrAdd (.eqRefl _) r.eqSymm)
  rw [inst2_coB, inst2_coB, inst2_coB]
  refine .orE (zero_or_succ m) ?_ ?_
  · -- `m = 0`
    have h0 : ((m ≐ zero) :: Γ) ⊢[PRAAx] m ≐ zero := Prf.hyp0
    have q0 : ((m ≐ zero) :: Γ) ⊢[PRAAx] quo m p ≐ zero :=
      (congrAp2 quoF h0 (.eqRefl _)).eqTrans (quo_small hp1.wk (zero_lt' hp1.wk))
    exact z_alg ((congrSg h0).eqTrans sg_zero) ((congrSg q0).eqTrans sg_zero)
  · let C : List (Fm PTm n) := (m ≐ succ (pred m)) :: Γ
    have hm : C ⊢[PRAAx] m ≐ succ (pred m) := Prf.hyp0
    have s1 : C ⊢[PRAAx] sg m ≐ one := (congrSg hm).eqTrans (sg_succ _)
    refine .orE (eq_or_ne (rem m p) zero) ?_ ?_
    · -- `p ∣ m`
      let D : List (Fm PTm n) := (rem m p ≐ zero) :: C
      have hd : D ⊢[PRAAx] dvd p m := Prf.hyp0
      have e := eq_of_dvd' hp1.wk.wk hd
      have hu := pos_of_eq_mul hm.wk e
      have su1 : D ⊢[PRAAx] sg (quo m p) ≐ one := (congrSg hu).eqTrans (sg_succ _)
      have b1 : D ⊢[PRAAx] eqb (gcd m (P * p)) one ≐ zero :=
        not_coprime hp.wk.wk hd (dvd_of_eq' hp1.wk.wk (mul_comm P p))
      have e1 : D ⊢[PRAAx] eqb (rem m p) zero ≐ one := eqb_of_eq hd
      have hPp : D ⊢[PRAAx] gcd P p ≐ one := gcd_comm_one hP.wk.wk hc.wk.wk
      have b23 : D ⊢[PRAAx] eqb (gcd (quo m p) P) one ≐ eqb (gcd m P) one := by
        refine .orE (eqb_cases (gcd (quo m p) P) one) ?_ ?_
        · let E : List (Fm PTm n) := (eqb (gcd (quo m p) P) one ≐ zero) :: D
          have z : E ⊢[PRAAx] eqb (gcd (quo m p) P) one ≐ zero := Prf.hyp0
          have nn : E ⊢[PRAAx] neg (gcd m P ≐ one) := by
            refine .impI ?_
            have g : ((gcd m P ≐ one) :: E) ⊢[PRAAx] gcd m P ≐ one := Prf.hyp0
            have du : ((gcd m P ≐ one) :: E) ⊢[PRAAx] dvd (quo m p) m :=
              dvd_of_eq' hu.wk.wk (e.wk.wk.eqTrans (mul_comm _ _))
            have gu := coprime_dvd_left hu.wk.wk du g
            exact one_ne_zero _ ((eqb_of_eq gu).eqSymm.eqTrans z.wk)
          exact z.eqTrans (eqb_of_ne nn).eqSymm
        · let E : List (Fm PTm n) := (eqb (gcd (quo m p) P) one ≐ one) :: D
          have o : E ⊢[PRAAx] eqb (gcd (quo m p) P) one ≐ one := Prf.hyp0
          have gPu : E ⊢[PRAAx] gcd P (quo m p) ≐ one := gcd_comm_one hP.wk.wk.wk (eq_of_eqb o)
          have gPm : E ⊢[PRAAx] gcd P (p * quo m p) ≐ one := coprime_mul hP.wk.wk.wk hPp.wk gPu
          have gPm' : E ⊢[PRAAx] gcd P m ≐ one := (congrGcd (.eqRefl _) e.wk).eqTrans gPm
          have gm : E ⊢[PRAAx] gcd m P ≐ one := gcd_comm_one hm.wk.wk gPm'
          exact o.eqTrans (eqb_of_eq gm).eqSymm
      exact a_alg s1.wk b1 e1 su1 b23
    · -- `p ∤ m`
      let D : List (Fm PTm n) := neg (rem m p ≐ zero) :: C
      have hn : D ⊢[PRAAx] neg (dvd p m) := Prf.hyp0
      have e0 : D ⊢[PRAAx] eqb (rem m p) zero ≐ zero := eqb_of_ne hn
      have gmp : D ⊢[PRAAx] gcd m p ≐ one := gcd_comm_one hm.wk (gcd_prime hp.wk.wk hn)
      have hPp1 : D ⊢[PRAAx] P * p ≐ succ (pred (P * p)) := pos_mul hP.wk.wk hp1.wk.wk
      have b13 : D ⊢[PRAAx] eqb (gcd m (P * p)) one ≐ eqb (gcd m P) one := by
        refine .orE (eqb_cases (gcd m P) one) ?_ ?_
        · let E : List (Fm PTm n) := (eqb (gcd m P) one ≐ zero) :: D
          have z : E ⊢[PRAAx] eqb (gcd m P) one ≐ zero := Prf.hyp0
          have nn : E ⊢[PRAAx] neg (gcd m (P * p) ≐ one) := by
            refine .impI ?_
            have g : ((gcd m (P * p) ≐ one) :: E) ⊢[PRAAx] gcd m (P * p) ≐ one := Prf.hyp0
            have g1 := gcd_comm_one hPp1.wk.wk g
            have dP : ((gcd m (P * p) ≐ one) :: E) ⊢[PRAAx] dvd P (P * p) :=
              dvd_of_eq' hP.wk.wk.wk.wk (.eqRefl _)
            have g2 := coprime_dvd_left hP.wk.wk.wk.wk dP g1
            have g3 := gcd_comm_one hm.wk.wk.wk g2
            exact one_ne_zero _ ((eqb_of_eq g3).eqSymm.eqTrans z.wk)
          exact (eqb_of_ne nn).eqTrans z.eqSymm
        · let E : List (Fm PTm n) := (eqb (gcd m P) one ≐ one) :: D
          have o : E ⊢[PRAAx] eqb (gcd m P) one ≐ one := Prf.hyp0
          have g : E ⊢[PRAAx] gcd m (P * p) ≐ one := coprime_mul hm.wk.wk (eq_of_eqb o) gmp.wk
          exact (eqb_of_eq g).eqTrans o.eqSymm
      exact b_alg e0 b13

/-! ## The sum -/

theorem cm_alg {x p Q R : PTm n} (d : Γ ⊢[PRAAx] x ≐ p * Q + R) (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] succ x + pred p ≐ p * succ Q + R := by
  have a := natEq d; have b := natEq hp1
  apply deriveNat; ipra_simps; linear_combination a - b

/-- There are `⌊x/p⌋ + 1` multiples of `p` in `[0, x]`. -/
theorem cM_succ {x p : PTm n} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] cM (succ x) p ≐ succ (quo x p) :=
  (count_multiples (j := succ x) hp1).eqTrans (quo_eq hp1 (cm_alg (div_eq (j := x) hp1) hp1) (rem_lt' hp1 x))

theorem shift_isP_eq {p : PTm n} (h : Γ ⊢[PRAAx] isP p ≐ one) :
    Γ.map Fm.shift ⊢[PRAAx] isP (Syn.shift p) ≐ one := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  rw [subst_isP] at e
  exact e

theorem shift_cop {p P : PTm n} (h : Γ ⊢[PRAAx] gcd p P ≐ one) :
    Γ.map Fm.shift ⊢[PRAAx] gcd (Syn.shift p) (Syn.shift P) ≐ one := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  rw [subst_gcd'] at e
  exact e

theorem shift_mul' (a b : PTm n) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by
  simp only [Syn.shift, PTm.subst_mul]

/-- `Φ(x; P) = #{1 ≤ m ≤ x : gcd(m, P) = 1}`. -/
abbrev Phi (x P : PTm n) : PTm n := ap2 (sumF coB) (succ x) P

/-- **The sieve recursion**: `Φ(x; P) = Φ(x; P p) + Φ(⌊x/p⌋; P)` for a prime `p` coprime to `P ≥ 1`. -/
theorem recursion {p P : PTm n} (hI : Γ ⊢[PRAAx] isP p ≐ one) (hP : Γ ⊢[PRAAx] P ≐ succ (pred P))
    (hc : Γ ⊢[PRAAx] gcd p P ≐ one) (x : PTm n) :
    Γ ⊢[PRAAx] Phi x P ≐ Phi x (P * p) + Phi (quo x p) P := by
  have hp1 := p_pos (prime_two (prime_of_isP hI))
  have hI' := shift_isP_eq hI
  have hP' := shift_pos hP
  have hc' := shift_cop hc
  have s : Γ ⊢[PRAAx] ap2 (sumF coB) (succ x) P ≐
      ap2 (sumF coB) (succ x) (P * p) + ap2 (sumF (riB coB)) (succ x) (pairT p P) := by
    refine sum_add2 coB (riB coB) coB (.allI (.impI ?_))
    rw [shift_pairT, shift_mul']
    exact pt (prime_of_isP hI'.wk) hP'.wk hc'.wk
  exact s.eqTrans (congrAdd (.eqRefl _)
    ((reindex_eq coB (succ x) hp1).eqTrans (congrAp2 (sumF coB) (cM_succ hp1) (.eqRefl _))))

/-! ## Primorials -/

theorem mul_one_r (X : PTm n) : Γ ⊢[PRAAx] X * one ≐ X := by apply deriveNat; ipra_simps; ring

/-- At a prime `r + 1`: `Φ(x; P(r)) = Φ(x; P(r + 1)) + Φ(⌊x/(r + 1)⌋; P(r))`. -/
theorem phi_step_prime {r : PTm n} (hI : Γ ⊢[PRAAx] isP (succ r) ≐ one) (x : PTm n) :
    Γ ⊢[PRAAx] Phi x (pri r) ≐ Phi x (pri (succ r)) + Phi (quo x (succ r)) (pri r) := by
  have hp := prime_of_isP hI
  have nd : Γ ⊢[PRAAx] neg (dvd (succ r) (pri r)) :=
    .impI (lt_irrefl r _ (le_of_dvd_pri hp.wk Prf.hyp0))
  have e : Γ ⊢[PRAAx] pri (succ r) ≐ pri r * succ r :=
    (pri_succ r).eqTrans (congrMul (.eqRefl _) ((f_one hI).eqTrans (pw_one _)))
  exact (recursion hI (pri_pos r) (gcd_prime hp nd) x).eqTrans
    (congrAdd (congrAp2 (sumF coB) (.eqRefl _) e.eqSymm) (.eqRefl _))

/-- At a composite `r + 1` the count does not change. -/
theorem phi_step_comp {r : PTm n} (hI : Γ ⊢[PRAAx] isP (succ r) ≐ zero) (x : PTm n) :
    Γ ⊢[PRAAx] Phi x (pri (succ r)) ≐ Phi x (pri r) :=
  congrAp2 (sumF coB) (.eqRefl _)
    ((pri_succ r).eqTrans ((congrMul (.eqRefl _) (f_zero hI)).eqTrans (mul_one_r _)))

theorem step_alg0 {A B I X : PTm n} (h : Γ ⊢[PRAAx] B ≐ A) (hI : Γ ⊢[PRAAx] I ≐ zero) :
    Γ ⊢[PRAAx] A ≐ B + I * X := by
  have a := natEq h; have b := natEq hI
  apply deriveNat; ipra_simps; linear_combination -a - 𝔞 X * b

theorem step_alg1 {A B I X : PTm n} (h : Γ ⊢[PRAAx] A ≐ B + X) (hI : Γ ⊢[PRAAx] I ≐ one) :
    Γ ⊢[PRAAx] A ≐ B + I * X := by
  have a := natEq h; have b := natEq hI
  apply deriveNat; ipra_simps; linear_combination a - 𝔞 X * b

/-- **The sieve recursion over the primorials**:
`Φ(x; P(r)) = Φ(x; P(r + 1)) + [r + 1 prime] Φ(⌊x/(r + 1)⌋; P(r))`. -/
theorem phi_step (r x : PTm n) :
    Γ ⊢[PRAAx] Phi x (pri r) ≐ Phi x (pri (succ r)) + isP (succ r) * Phi (quo x (succ r)) (pri r) := by
  refine .orE (isP_01 (succ r)) ?_ ?_
  · exact step_alg0 (phi_step_comp Prf.hyp0 x) Prf.hyp0
  · exact step_alg1 (phi_step_prime Prf.hyp0 x) Prf.hyp0

end LeanProofs.IPRA.AnalyticNumberTheory.SieveRecursion
