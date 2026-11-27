import IPRADerivations.AnalyticNumberTheory.GeneralMul

/-!
# Corollaries: gcd–lcm identity, odd nontotients, `φ(n) < n`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`:

* `cor:phi-gcd-lcm`: `φ(gcd(m, n)) φ(lcm(m, n)) = φ(m) φ(n)` for `m, n ≥ 1`, with
  `lcm(m, n) = mn / gcd(m, n)`: since `gcd ∣ lcm` and `mn = lcm · gcd`,
  `φ(mn) = gcd · φ(lcm)` (`PhiPower.phi_mul_pow_at`), and `thm:phi-general-mul` cancels;
* `thm:odd-nontotient`: no `φ(n)` equals an odd number `≥ 3` (`φ(n)` is even for `n ≥ 3`, and
  `φ(0) = 0`, `φ(1) = φ(2) = 1`);
* `thm:phi-upper-composite` (first consequence): `φ(n) < n` for `n ≥ 2`, since the summand at `0`
  vanishes.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot quo_eq pred_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (phi_two two_pos')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The gcd–lcm identity -/

abbrev lcm (m N : PTm n) : PTm n := quo (m * N) (gcd m N)

section GL

variable {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
include hm hN

/-- `lcm(m, n) = d (m/d)(n/d)` with `d = gcd(m, n)`. -/
theorem lcm_eq : Γ ⊢[PRAAx] lcm m N ≐ gcd m N * (quo m (gcd m N) * quo N (gcd m N)) := by
  have hd := gcd_pos (B := N) hm
  have hgd := gcd_dvd' (b := N) hm
  refine quo_eq hd (r := zero) ?_ (zero_lt' hd)
  ipra_lc Groth.ι (Q.mk _ N) * natEq (eq_of_dvd' hd (Prf.andE₁ hgd)) +
    Groth.ι (Q.mk _ (gcd m N)) * Groth.ι (Q.mk _ (quo m (gcd m N))) * natEq (eq_of_dvd' hd (Prf.andE₂ hgd))

/-- `φ(gcd) φ(lcm) = φ(m) φ(n)`. -/
theorem gcd_lcm_at : Γ ⊢[PRAAx] phi (gcd m N) * phi (lcm m N) ≐ phi m * phi N := by
  have hd := gcd_pos (B := N) hm
  have hgd := gcd_dvd' (b := N) hm
  have hL := lcm_eq hm hN
  have em := natEq (eq_of_dvd' hd (Prf.andE₁ hgd))
  have en := natEq (eq_of_dvd' hd (Prf.andE₂ hgd))
  -- `mn = lcm · d`, `lcm ≥ 1`, `d ∣ lcm`.
  have hmn : Γ ⊢[PRAAx] m * N ≐ lcm m N * gcd m N := by
    have h₁ := natEq hL
    apply deriveNat; ipra_simps
    linear_combination Groth.ι (Q.mk _ N) * em +
      Groth.ι (Q.mk _ (gcd m N)) * Groth.ι (Q.mk _ (quo m (gcd m N))) * en -
      Groth.ι (Q.mk _ (gcd m N)) * h₁
  have hLp : Γ ⊢[PRAAx] lcm m N ≐ succ (pred (lcm m N)) := by
    refine .orE (zero_or_succ (lcm m N)) ?_ Prf.hyp0
    exact succ_ne_zero' _ ((pos_mul hm hN).wk.eqSymm.eqTrans (hmn.wk.eqTrans
      ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))))
  have hdL : Γ ⊢[PRAAx] dvd (gcd m N) (pw (lcm m N) one) :=
    dvd_congr (pw_one _).eqSymm (dvd_of_eq' hd (w := quo m (gcd m N) * quo N (gcd m N)) hL)
  have hφ := (congrAp2 (sumF totBody) hmn hmn).eqTrans (PhiPower.phi_mul_pow_at hLp hd hdL)
  have hg := GeneralMul.general_mul_at hm hN
  refine mul_cancel hd ?_
  ipra_lc -Groth.ι (Q.mk _ (phi (gcd m N))) * natEq hφ + natEq hg

end GL

/-- `cor:phi-gcd-lcm`: `φ(gcd(m, n)) φ(lcm(m, n)) = φ(m) φ(n)`; variables `0 = m − 1`, `1 = n − 1`. -/
abbrev gcdLcmFormula : Fm PTm 2 :=
  phi (gcd (succ (var 0)) (succ (var 1))) * phi (lcm (succ (var 0)) (succ (var 1))) ≐
    phi (succ (var 0)) * phi (succ (var 1))

theorem gcd_lcm : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 gcdLcmFormula :=
  closeUniv 2 (gcd_lcm_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm))

/-! ## Odd nontotients -/

theorem phi_zero : Γ ⊢[PRAAx] phi (zero : PTm n) ≐ zero := sum_zero _ _

/-- `2 T ≠ 2k + 3`. -/
theorem even_ne_odd {T k : PTm n} (h : Γ ⊢[PRAAx] two * T ≐ succ (succ (succ (two * k)))) : Γ ⊢[PRAAx] Fm.bot := by
  have r₀ := rem_eq' (two_pos' (Γ := Γ)) (z := two * T) (q := T) (r := zero) (add_zero _).eqSymm (zero_lt' two_pos')
  have r₁ := rem_eq' (two_pos' (Γ := Γ)) (z := succ (succ (succ (two * k)))) (q := succ k) (r := one)
    (by ipra_ring) (le_refl _)
  exact succ_ne_zero (a := zero) (r₁.eqSymm.eqTrans ((congrAp2 remF h.eqSymm (.eqRefl _)).eqTrans r₀))

theorem one_ne_odd {k : PTm n} (h : Γ ⊢[PRAAx] one ≐ succ (succ (succ (two * k)))) : Γ ⊢[PRAAx] Fm.bot :=
  succ_ne_zero ((pred_succ _).eqSymm.eqTrans ((congrPred h).eqSymm.eqTrans (pred_succ _)))

theorem lt3_cases {N : PTm n} (h : Γ ⊢[PRAAx] lt N (succ two)) :
    Γ ⊢[PRAAx] (N ≐ zero) ⋎ ((N ≐ one) ⋎ (N ≐ two)) := by
  refine .orE (zero_or_succ N) (.orI₁ Prf.hyp0) ?_
  refine .orE (zero_or_succ (pred N)) (.orI₂ (.orI₁ (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)))) ?_
  refine .orE (zero_or_succ (pred (pred N))) ?_ ?_
  · exact .orI₂ (.orI₂ (Prf.hyp1.wk.eqTrans (congrSucc (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)))))
  · have e : ((pred (pred N) ≐ succ (pred (pred (pred N)))) :: (pred N ≐ succ (pred (pred N))) ::
        (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ succ (succ (succ (pred (pred (pred N))))) :=
      Prf.hyp1.wk.eqTrans (congrSucc (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)))
    have h' := le_congr (congrSucc e) (.eqRefl _) h.wk.wk.wk
    have h₃ := (succ_monus_succ _ _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans
      ((succ_monus_succ _ _).eqSymm.eqTrans h'))
    exact .botE _ (succ_ne_zero ((monus_zero _).eqSymm.eqTrans h₃))

/-- `thm:odd-nontotient` at arbitrary terms: `φ(n) ≠ 2k + 3`. -/
theorem odd_nontotient_at (N k : PTm n) : Γ ⊢[PRAAx] neg (phi N ≐ succ (succ (succ (two * k)))) := by
  refine .impI (.orE (lt_or_le N (succ two)) ?_ ?_)
  · refine .orE (lt3_cases Prf.hyp0) ?_ (.orE Prf.hyp0 ?_ ?_)
    · exact succ_ne_zero (Prf.hyp1.wk.eqSymm.eqTrans ((congrAp2 (sumF totBody) Prf.hyp0 Prf.hyp0).eqTrans phi_zero))
    · exact one_ne_odd (((congrAp2 (sumF totBody) Prf.hyp0 Prf.hyp0).eqTrans phi_one).eqSymm.eqTrans Prf.hyp1.wk.wk)
    · exact one_ne_odd (((congrAp2 (sumF totBody) Prf.hyp0 Prf.hyp0).eqTrans phi_two).eqSymm.eqTrans Prf.hyp1.wk.wk)
  · exact even_ne_odd ((Totatives.phi_even_at Prf.hyp0).eqSymm.eqTrans Prf.hyp1)

/-- `thm:odd-nontotient`: no `φ(n)` equals `2k + 3`; variables `0 = n`, `1 = k`. -/
abbrev oddNontotientFormula : Fm PTm 2 := neg (phi (var 0) ≐ succ (succ (succ (two * var 1))))

theorem odd_nontotient : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 oddNontotientFormula :=
  closeUniv 2 (odd_nontotient_at (var 0) (var 1))

/-! ## `φ(n) < n` -/

alias eqb_le_one := Common.eqb_le_one

/-- `φ(n) ≤ n − 1` for `n ≥ 2`. -/
theorem phi_lt {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] lt (phi N) N := by
  have hp := AnalyticNumberTheory.Euler.N_pos hN
  have s := sum_shift (Γ := Γ) totBody (pred N) N
  rw [inst2_tot] at s
  have hs := (congrAp2 (sumF totBody) hp (.eqRefl N)).eqTrans (s.eqTrans
    ((congrAdd (Totatives.e_zero hN) (.eqRefl _)).eqTrans (zero_add _)))
  have hle := Analysis.PowerSums.sum_le (Γ := Γ) (shiftBody totBody) one N (pred N) (.allI (.impI ?_))
  · have hb := le_congr hs.eqSymm (SumPhi.sum_ones (Γ := Γ) (pred N) N) hle
    exact le_congr (.eqRefl _) hp.eqSymm ((succ_monus_succ _ _).eqTrans hb)
  · rw [inst2_shiftBody, inst2_tot]
    have e : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift N) = one := by simp [inst2]
    rw [e]; exact eqb_le_one _ _

/-- `φ(n) < n` for `n ≥ 2`; variable `0 = n − 2`. -/
abbrev phiLtFormula : Fm PTm 1 := lt (phi (succ (succ (var 0)))) (succ (succ (var 0)))

theorem phi_lt_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiLtFormula :=
  closeUniv 1 (phi_lt (le_of_eq_add (d := var 0) (by ipra_ring)))

end LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries

export_ipra AnalyticNumberTheory.TotientCorollaries (eqb_le_one lcm lcm_eq)
