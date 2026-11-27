import IPRADerivations.AnalyticNumberTheory.SigmaPrimePower

/-!
# Robin's inequality with at most three prime factors: the arithmetic core (`robin_ipra_research_2026-11-19`, `thm:three`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `report.tex`, Theorem `thm:three`: "If `n ≥ 5041` has at
most three distinct prime factors, then `σ(n) < e^γ n log log n`. … `A(n) = Π (1 − p_i^{−a_i−1})/(1 − p_i^{−1}) <
Π p_i/(p_i − 1)`. Since `p_1 ≥ 2`, `p_2 ≥ 3`, `p_3 ≥ 5` and `p/(p − 1)` decreases, for `r ≤ 3` the right side is at most
`2 · 3/2 · 5/4 = 15/4`. The certificate above proves `B(5041) > 15/4` …"

The integer half is derived here: for primes `p < q < r` and exponents `a, b, c ≥ 0` (an exponent `0` drops that prime, so
this covers every `n` with at most three distinct prime factors),

  `4 σ(p^a q^b r^c) < 15 p^a q^b r^c`                                                     (`three_core`)

i.e. `A(n) = σ(n)/n < 15/4`. The proof: the prime powers are pairwise coprime (`cop_pows`), so
`σ(n) = σ(p^a)σ(q^b)σ(r^c)` (`SigmaMult.sigma_mul`); `(p−1)σ(p^a) + 1 = p^{a+1}` (`SigmaPrimePower.sigma_pow`); with
`D = (p−1)(q−1)(r−1)`, `4Dσ(n) + 4 ≤ 4 p^{a+1} q^{b+1} r^{c+1} ≤ 15 D n` since `4pqr ≤ 15D` for `p ≥ 2`, `q ≥ 3`,
`r ≥ 5` (`r ≠ 4` as `2 ∣ 4`, `r_ge_five`). The remaining half, `B(5041) > 15/4` with `B(n) = e^γ log log n`
monotone, is the packet's real-number certificate and is not derived.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinThree

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul rem_zero_of_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem two_le_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] le two p := by
  have h := hp; unfold prime at h; exact Prf.andE₁ h

/-- Powers of distinct primes are coprime. -/
theorem cop_pows {p q : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q) (hne : Γ ⊢[PRAAx] lt p q)
    (a b : PTm n) : Γ ⊢[PRAAx] gcd (pw p a) (pw q b) ≐ one := by
  have hp1 := prime_eq_succ_pred hp
  have hq1 := prime_eq_succ_pred hq
  have g : Γ ⊢[PRAAx] gcd p q ≐ one :=
    gcd_distinct_primes hp hq (.impI (lt_irrefl q _ (lt_congr Prf.hyp0 (.eqRefl _) hne.wk)))
  have g1 : Γ ⊢[PRAAx] gcd p (pw q b) ≐ one := cop_pow hp1 g b
  have g2 : Γ ⊢[PRAAx] gcd (pw q b) p ≐ one := gcd_comm_one (pos_pw hq1 b) g1
  have g3 : Γ ⊢[PRAAx] gcd (pw q b) (pw p a) ≐ one := cop_pow (pos_pw hq1 b) g2 a
  exact gcd_comm_one (pos_pw hp1 a) g3

/-- A prime `r > q ≥ 3` is at least `5`: `4 = 2 · 2` is not prime. -/
theorem r_ge_five {q r : PTm n} (hr : Γ ⊢[PRAAx] prime r) (hq3 : Γ ⊢[PRAAx] le (succ two) q)
    (hqr : Γ ⊢[PRAAx] lt q r) : Γ ⊢[PRAAx] le (succ (succ (succ (succ one)))) r := by
  have h4 : Γ ⊢[PRAAx] le (succ (succ two)) r := by ipra_le sl hq3 + sl hqr
  refine .orE (lt_or_le (succ (succ two)) r) Prf.hyp0 ?_
  let C : List (Fm PTm n) := le r (succ (succ two)) :: Γ
  have e4 : C ⊢[PRAAx] r ≐ succ (succ two) := le_antisymm Prf.hyp0 h4.wk
  have hr' := hr.wk (ψ := le r (succ (succ two)))
  unfold prime at hr'
  have hall := Prf.allE two (Prf.andE₂ hr')
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_inst_shift,
    Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hall
  have l2 : C ⊢[PRAAx] lt two r := le_congr (.eqRefl _) e4.eqSymm (by ipra_le 1)
  have nd := Prf.impE (Prf.impE hall (le_refl _)) l2
  have h2 : C ⊢[PRAAx] two ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm
  have dv : C ⊢[PRAAx] dvd two r := rem_zero_of_eq h2 (w := two) (e4.eqTrans (by ipra_ring))
  exact .botE _ (Prf.impE nd dv)

/-- `4pqr ≤ 15(p−1)(q−1)(r−1)` for `p ≥ 2`, `q ≥ 3`, `r ≥ 5`. -/
theorem euler_factor {p q r : PTm n} (hp : Γ ⊢[PRAAx] le two p) (hq : Γ ⊢[PRAAx] le (succ two) q)
    (hr : Γ ⊢[PRAAx] le (succ (succ (succ (succ one)))) r) :
    Γ ⊢[PRAAx] le (two * two * (p * q * r)) (succ two * succ (succ (succ (succ one))) * (pred p * pred q * pred r)) := by
  have ep : Γ ⊢[PRAAx] p ≐ succ (pred p) := pos_of_one_le (by ipra_le sl hp + 1)
  have eq' : Γ ⊢[PRAAx] q ≐ succ (pred q) := pos_of_one_le (by ipra_le sl hq + 1 + 1)
  have er : Γ ⊢[PRAAx] r ≐ succ (pred r) := pos_of_one_le (by ipra_le sl hr + 1 + 1 + 1 + 1)
  have fp := natEq ep
  have fq := natEq eq'
  have fr := natEq er
  -- `p ≤ 2(p−1)`, `2q ≤ 3(q−1)`, `4r ≤ 5(r−1)`
  have a1 : Γ ⊢[PRAAx] le p (two * pred p) := by ipra_le sl hp with -2 * fp
  have a2 : Γ ⊢[PRAAx] le (two * q) (succ two * pred q) := by ipra_le sl hq with -3 * fq
  have a3 : Γ ⊢[PRAAx] le (two * two * r) (succ (succ (succ (succ one))) * pred r) := by ipra_le sl hr with -5 * fr
  have m := le_mul_mono (le_mul_mono a1 a2) a3
  have c : Γ ⊢[PRAAx] le (two * (two * two * (p * q * r)))
      (two * (succ two * succ (succ (succ (succ one))) * (pred p * pred q * pred r))) := by
    ipra_le sl m
  exact mul_le_cancel (le_congr (.eqRefl _) (.eqRefl _) c)

/-- `thm:three`, integer core: `4 σ(p^a q^b r^c) < 15 p^a q^b r^c` for primes `p < q < r`. -/
theorem three_core {p q r : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q) (hr : Γ ⊢[PRAAx] prime r)
    (hpq : Γ ⊢[PRAAx] lt p q) (hqr : Γ ⊢[PRAAx] lt q r) (a b c : PTm n) :
    Γ ⊢[PRAAx] lt (two * two * sig (pw p a * pw q b * pw r c))
      (succ two * succ (succ (succ (succ one))) * (pw p a * pw q b * pw r c)) := by
  have hp1 := prime_eq_succ_pred hp
  have hq1 := prime_eq_succ_pred hq
  have hr1 := prime_eq_succ_pred hr
  have hA := pos_pw hp1 a
  have hB := pos_pw hq1 b
  have hC := pos_pw hr1 c
  have hp2 := two_le_prime hp
  have hq3 : Γ ⊢[PRAAx] le (succ two) q := by ipra_le sl hp2 + sl hpq
  have hr5 := r_ge_five hr hq3 hqr
  -- multiplicativity
  have gAB := cop_pows hp hq hpq a b
  have gAC := cop_pows hp hr (by ipra_le sl hpq + sl hqr + 1) a c
  have gBC := cop_pows hq hr hqr b c
  have gCA : Γ ⊢[PRAAx] gcd (pw r c) (pw p a) ≐ one := gcd_comm_one hC gAC
  have gCB : Γ ⊢[PRAAx] gcd (pw r c) (pw q b) ≐ one := gcd_comm_one hC gBC
  have gC_AB : Γ ⊢[PRAAx] gcd (pw r c) (pw p a * pw q b) ≐ one := coprime_mul hC gCA gCB
  have gAB_C : Γ ⊢[PRAAx] gcd (pw p a * pw q b) (pw r c) ≐ one := gcd_comm_one (pos_mul hA hB) gC_AB
  have s1 := sigma_mul (pos_mul hA hB) hC gAB_C
  have s2 := sigma_mul hA hB gAB
  have sN : Γ ⊢[PRAAx] sig (pw p a * pw q b * pw r c) ≐ sig (pw p a) * sig (pw q b) * sig (pw r c) :=
    s1.eqTrans (congrMul s2 (.eqRefl _))
  -- the prime-power formulas, multiplied out
  have E1 : Γ ⊢[PRAAx] (pw p a * p) * (pw q b * q) * (pw r c * r) ≐
      (pred p * sig (pw p a) + one) * (pred q * sig (pw q b) + one) * (pred r * sig (pw r c) + one) :=
    (congrMul (congrMul ((sigma_pow hp a).eqTrans (pw_succ p a)) ((sigma_pow hq b).eqTrans (pw_succ q b)))
      ((sigma_pow hr c).eqTrans (pw_succ r c))).eqSymm
  have E2 : Γ ⊢[PRAAx] pred p * pred q * pred r * (two * two * sig (pw p a * pw q b * pw r c)) ≐
      pred p * pred q * pred r * (two * two * (sig (pw p a) * sig (pw q b) * sig (pw r c))) :=
    congrMul (.eqRefl _) (congrMul (.eqRefl _) sN)
  have e1 := natEq E1
  have e2 := natEq E2
  have ef := euler_factor hp2 hq3 hr5
  have ef' := le_mul_mono ef (le_refl (pw p a * pw q b * pw r c))
  -- `4Dσ(n) + 4 ≤ 15 D n`, with `X₁ = (p−1)σ(p^a)` etc.
  have key : Γ ⊢[PRAAx] le (pred p * pred q * pred r * (two * two * sig (pw p a * pw q b * pw r c)) + two * two)
      (succ two * succ (succ (succ (succ one))) * (pred p * pred q * pred r) * (pw p a * pw q b * pw r c)) := by
    ipra_le sl ef' + 𝔞 (two * two * (pred p * sig (pw p a) * (pred q * sig (pw q b)) +
        pred p * sig (pw p a) * (pred r * sig (pw r c)) + pred q * sig (pw q b) * (pred r * sig (pw r c)) +
        pred p * sig (pw p a) + pred q * sig (pw q b) + pred r * sig (pw r c))) with 4 * e1 - e2
  -- cancel `D` by contradiction
  refine .orE (lt_or_le (two * two * sig (pw p a * pw q b * pw r c))
    (succ two * succ (succ (succ (succ one))) * (pw p a * pw q b * pw r c))) Prf.hyp0 ?_
  let C : List (Fm PTm n) := le (succ two * succ (succ (succ (succ one))) * (pw p a * pw q b * pw r c))
    (two * two * sig (pw p a * pw q b * pw r c)) :: Γ
  have h1 := le_mul_mono (le_refl (pred p * pred q * pred r)) (Prf.hyp0 : C ⊢[PRAAx] _)
  exact lt_irrefl zero _ (by ipra_le sl h1 + sl key.wk + 3)

end LeanProofs.IPRA.AnalyticNumberTheory.RobinThree
