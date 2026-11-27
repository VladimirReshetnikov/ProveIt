import IPRADerivations.AnalyticNumberTheory.PhiLowerSharp

/-!
# The composite upper bound `φ(n) ≤ n − ⌈√n⌉`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem
`thm:phi-upper-composite`: if `n > 1` is composite and `r` is the least integer with `n ≤ r²`, then
`φ(n) ≤ n − r`.

With `p = lpf(n)` and `q = n / p`:
* `lpf_min`: `lpf(n) ≤ d` for every divisor `2 ≤ d` of `n`;
* `tot_mul_le`: `[gcd(k, n) = 1] + [p ∣ k] ≤ 1`, so `φ(n) + q ≤ n`, the multiples of `p` below `n`
  numbering `q` (`Totient.count_multiples`);
* `p ≤ q` (as `lpf(q) ∣ n`), so `n = pq ≤ q²`, and the least `r` with `n ≤ r²` (a bounded search,
  `sqrtUp`) satisfies `r ≤ q`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiUpper

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot mulBody inst2_mul count_multiples)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (lpf μz lpfBody inst2_lpf lpf_dvd lpf_prime prime eq_succ_pred)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lpf_congr prime_congr two_le_lpf)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (quo_exact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Minimality of the least prime factor -/

theorem le_succ_succ {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (succ (succ a)) (succ (succ b)) :=
  (succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans h)

/-- `lpf(n) ≤ d` for every divisor `d ≥ 2` of `n ≥ 1`. -/
theorem lpf_min {N d : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hd : Γ ⊢[PRAAx] le two d)
    (hdN : Γ ⊢[PRAAx] dvd d N) : Γ ⊢[PRAAx] le (lpf N) d := by
  have hdd : Γ ⊢[PRAAx] d ≐ succ (succ (monus d two)) :=
    (eq_add_of_le hd).eqTrans (by ipra_ring)
  have hdp : Γ ⊢[PRAAx] d ≐ succ (pred d) := eq_succ_pred hdd
  have hf : Γ ⊢[PRAAx] inst2 lpfBody (monus d two) N ≐ zero := by
    rw [inst2_lpf]; exact (congrAp2 remF (.eqRefl _) hdd.eqSymm).eqTrans hdN
  have hle := dvd_le' hdp hdN hN
  have hlt : Γ ⊢[PRAAx] lt (monus d two) N := by
    refine le_of_eq_add (d := succ (monus N d)) ?_
    ipra_lc natEq (eq_add_of_le hle) + natEq hdd
  have s := Search.search_found (f := lpfBody) hf hlt
  exact le_congr (.eqRefl _) hdd.eqSymm (le_succ_succ (Prf.andE₂ (Prf.andE₂ s)))

/-! ## Totatives versus multiples of `p` -/

/-- `[p ∣ k]`, with `p = lpf(n)`, over `0 = k`, `1 = n`. -/
abbrev lmB : PTm 2 := eqb (rem (var 0) (lpf (var 1))) zero

theorem inst2_lm (k N : PTm n) : inst2 lmB k N = eqb (rem k (lpf N)) zero := by simp [inst2]

/-- `[gcd(k, n) = 1] + [p ∣ k] ≤ 1` for a divisor `p ≥ 2` of `n`. -/
theorem tot_mul_le {N p k : PTm n} (hp2 : Γ ⊢[PRAAx] le two p) (hpN : Γ ⊢[PRAAx] dvd p N) :
    Γ ⊢[PRAAx] le (eqb (gcd k N) one + eqb (rem k p) zero) one := by
  have hp1 := AnalyticNumberTheory.Euler.N_pos hp2
  refine .orE (eq_or_ne (rem k p) zero) ?_ ?_
  · have hne : ((rem k p ≐ zero) :: Γ) ⊢[PRAAx] neg (gcd k N ≐ one) := by
      refine .impI ?_
      have d : ((gcd k N ≐ one) :: (rem k p ≐ zero) :: Γ) ⊢[PRAAx] dvd p one :=
        dvd_congr Prf.hyp0 (gcd_greatest' hp1.wk.wk Prf.hyp1 hpN.wk.wk)
      have e1 := eq_one_of_dvd_one hp1.wk.wk d
      exact not_succ_le_self one _ (le_congr (.eqRefl _) e1 hp2.wk.wk)
    exact le_congr ((zero_add _).eqSymm.eqTrans (congrAdd (eqb_of_ne hne).eqSymm (eqb_of_eq Prf.hyp0).eqSymm))
      (.eqRefl _) (le_refl _)
  · exact le_congr ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) (eqb_of_ne Prf.hyp0).eqSymm)) (.eqRefl _)
      (eqb_le_one _ _)

section Main

variable {N d : PTm n} (hN : Γ ⊢[PRAAx] le two N) (hd : Γ ⊢[PRAAx] le two d) (hdN : Γ ⊢[PRAAx] lt d N)
  (hdv : Γ ⊢[PRAAx] dvd d N)
include hN hd hdN hdv

theorem lpf_facts : Γ ⊢[PRAAx] prime (lpf N) ⋏ dvd (lpf N) N := by
  have hNe : Γ ⊢[PRAAx] N ≐ succ (succ (monus N two)) := (eq_add_of_le hN).eqTrans (by ipra_ring)
  have hL := lpf_congr hNe
  refine .andI (prime_congr hL.eqSymm (lpf_prime _)) ?_
  exact dvd_congr hNe.eqSymm (dvd_congr_left hL.eqSymm (Prf.andE₁ (lpf_dvd _)))

/-- `φ(n) + n/p ≤ n`. -/
theorem phi_add_quo : Γ ⊢[PRAAx] le (phi N + quo N (lpf N)) N := by
  have lf := lpf_facts hN hd hdN hdv
  have hp2 : Γ ⊢[PRAAx] le two (lpf N) := two_le_lpf N
  have hp1 := AnalyticNumberTheory.Euler.N_pos hp2
  have hpt : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 (addBody totBody lmB) (var 0) (Syn.shift N)) (inst2 (one : PTm 2) (var 0) (Syn.shift N))) := by
    refine .allI (.impI ?_)
    rw [inst2_addBody, inst2_tot, inst2_lm]
    have e : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift N) = one := by simp [inst2]
    rw [e]
    have hp2' : Γ.map Fm.shift ⊢[PRAAx] le two (lpf (Syn.shift N)) := two_le_lpf _
    have hpN' : Γ.map Fm.shift ⊢[PRAAx] dvd (lpf (Syn.shift N)) (Syn.shift N) := by
      have h := SumPhi.shift_eq' (Prf.andE₂ lf)
      simp [Syn.shift] at h
      exact h
    exact tot_mul_le hp2'.wk hpN'.wk
  have hle := Analysis.PowerSums.sum_le (addBody totBody lmB) one N N hpt
  have hadd := sum_add (Γ := Γ) totBody lmB N N
  have hcnt : Γ ⊢[PRAAx] ap2 (sumF lmB) N N ≐ quo N (lpf N) := by
    refine (sum_congr_bounded lmB mulBody N (lpf N) N (.allI (.impI ?_))).eqTrans
      ((count_multiples hp1).eqTrans (quo_exact hp1 (Prf.andE₂ lf)))
    have e : Syn.shift (lpf N) = lpf (Syn.shift N) := by simp [Syn.shift]
    rw [inst2_lm, inst2_mul, e]
    exact Prf.eqRefl _
  exact le_congr (hadd.eqTrans (congrAdd (.eqRefl _) hcnt)) (SumPhi.sum_ones _ _) hle

/-- `p ≤ n/p`, so `n ≤ (n/p)²`. -/
theorem quo_sq : Γ ⊢[PRAAx] le N (quo N (lpf N) * quo N (lpf N)) := by
  have lf := lpf_facts hN hd hdN hdv
  have hp2 : Γ ⊢[PRAAx] le two (lpf N) := two_le_lpf N
  have hp1 := AnalyticNumberTheory.Euler.N_pos hp2
  have hNp := AnalyticNumberTheory.Euler.N_pos hN
  have hNe := eq_of_dvd' hp1 (Prf.andE₂ lf)
  have hq : Γ ⊢[PRAAx] quo N (lpf N) ≐ succ (pred (quo N (lpf N))) := by
    refine .orE (zero_or_succ (quo N (lpf N))) ?_ Prf.hyp0
    exact succ_ne_zero' _ (hNp.wk.eqSymm.eqTrans (hNe.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))))
  have lmin := lpf_min hNp hd hdv
  -- `q ≥ 2`: `q = 1` would make `n = p ≤ d < n`.
  have hq2 : Γ ⊢[PRAAx] le two (quo N (lpf N)) := by
    refine .orE (lt_or_le one (quo N (lpf N))) Prf.hyp0 ?_
    refine .botE _ ?_
    have q1 : (le (quo N (lpf N)) one :: Γ) ⊢[PRAAx] quo N (lpf N) ≐ one :=
      le_antisymm Prf.hyp0 (one_le_of_pos hq.wk)
    have eN : (le (quo N (lpf N)) one :: Γ) ⊢[PRAAx] N ≐ lpf N :=
      hNe.wk.eqTrans ((congrMul (.eqRefl _) q1).eqTrans (EulerProduct.mul_one' _))
    exact not_succ_le_self d _ (le_trans hdN.wk (le_congr eN.eqSymm (.eqRefl _) lmin.wk))
  -- `p ≤ q`: `lpf(q)` divides `n`.
  have hqq : Γ ⊢[PRAAx] quo N (lpf N) ≐ succ (succ (monus (quo N (lpf N)) two)) :=
    (eq_add_of_le hq2).eqTrans (by ipra_ring)
  have hLq := lpf_congr hqq
  have dq := Prf.andE₁ (lpf_dvd (Γ := Γ) (monus (quo N (lpf N)) two))
  have lq := Prf.andE₂ (lpf_dvd (Γ := Γ) (monus (quo N (lpf N)) two))
  have dN : Γ ⊢[PRAAx] dvd (lpf (quo N (lpf N))) N := by
    have hLp := AnalyticNumberTheory.Euler.N_pos (two_le_lpf (Γ := Γ) (quo N (lpf N)))
    refine dvd_trans' hLp hq (dvd_congr hqq.eqSymm (dvd_congr_left hLq.eqSymm dq)) ?_
    exact dvd_of_eq' hq (w := lpf N) (hNe.eqTrans (mul_comm _ _))
  have hpq : Γ ⊢[PRAAx] le (lpf N) (quo N (lpf N)) :=
    le_trans (lpf_min hNp (two_le_lpf _) dN) (le_congr hLq.eqSymm hqq.eqSymm lq)
  exact le_congr hNe.eqSymm (.eqRefl _) (le_mul_mono hpq (le_refl _))

end Main

/-! ## `⌈√n⌉` -/

/-- `n ∸ i²`, over `0 = i`, `1 = n`. -/
abbrev sqB : PTm 2 := monus (var 1) (var 0 * var 0)

/-- `⌈√n⌉`: the least `r ≤ n` with `n ≤ r²`. -/
abbrev sqrtUp (N : PTm n) : PTm n := Search.mu sqB (succ N) N

theorem inst2_sq (i N : PTm n) : inst2 sqB i N = monus N (i * i) := by simp [inst2]

/-- `thm:phi-upper-composite` at arbitrary terms: for `2 ≤ d < n` with `d ∣ n`,
`φ(n) + ⌈√n⌉ ≤ n`. -/
theorem phi_upper_at {N d : PTm n} (hN : Γ ⊢[PRAAx] le two N) (hd : Γ ⊢[PRAAx] le two d)
    (hdN : Γ ⊢[PRAAx] lt d N) (hdv : Γ ⊢[PRAAx] dvd d N) :
    Γ ⊢[PRAAx] le (phi N + sqrtUp N) N := by
  have lf := lpf_facts hN hd hdN hdv
  have hp1 := AnalyticNumberTheory.Euler.N_pos (two_le_lpf (Γ := Γ) N)
  have hqN : Γ ⊢[PRAAx] lt (quo N (lpf N)) (succ N) := by
    have hNe := eq_of_dvd' hp1 (Prf.andE₂ lf)
    refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred (lpf N) * quo N (lpf N)) ?_)
    ipra_lc natEq hNe + Groth.ι (Q.mk _ (quo N (lpf N))) * natEq hp1
  have hf : Γ ⊢[PRAAx] inst2 sqB (quo N (lpf N)) N ≐ zero := by
    rw [inst2_sq]; exact quo_sq hN hd hdN hdv
  have hr := Prf.andE₂ (Prf.andE₂ (Search.search_found (f := sqB) hf hqN))
  have hb := phi_add_quo hN hd hdN hdv
  refine le_trans ?_ hb
  refine le_of_eq_add (d := monus (quo N (lpf N)) (sqrtUp N)) ?_
  ipra_lc natEq (eq_add_of_le hr)

/-- `thm:phi-upper-composite`: variables `0 = n`, `1 = d`. -/
abbrev phiUpperFormula : Fm PTm 2 :=
  le two (var 0) ⟶ le two (var 1) ⟶ lt (var 1) (var 0) ⟶ dvd (var 1) (var 0) ⟶
    le (phi (var 0) + sqrtUp (var 0)) (var 0)

theorem phi_upper : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 phiUpperFormula :=
  closeUniv 2 (.impI (.impI (.impI (.impI (phi_upper_at Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiUpper

export_ipra AnalyticNumberTheory.PhiUpper (lpf_min)
