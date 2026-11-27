import IPRADerivations.AnalyticNumberTheory.PerfectNumbers

/-!
# Three distinct divisors bound the divisor sum

The converse of `el:perfect` in the number-theory packet needs the
contributions of `1`, a proper divisor, and the whole number. Their
separation makes each contribution a different term in the actual
`SigmaMult.sig` sum. This also proves that a number at least two with
divisor sum `N + 1` is prime.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PerfectDivisorBounds

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaMult (sB sig inst2_sB)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private abbrev prefixSum (i N : PTm n) : PTm n := ap2 (sumF sB) i N

private theorem prefix_mono {i j : PTm n} (N : PTm n) (h : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] le (prefixSum i N) (prefixSum j N) :=
  le_of_eq_add ((congrAp2 (sumF sB) (eq_add_of_le h) (.eqRefl _)).eqTrans
    (sum_split sB i (monus j i) N))

private theorem divisor_term {d N : PTm n} (h : Γ ⊢[PRAAx] dvd d N) :
    Γ ⊢[PRAAx] inst2 sB d N ≐ d := by
  rw [inst2_sB]
  exact (congrMul (eqb_of_eq h) (.eqRefl _)).eqTrans (one_mul _)

private theorem prefix_divisor {d N : PTm n} (hd : Γ ⊢[PRAAx] dvd d N) :
    Γ ⊢[PRAAx] prefixSum (succ d) N ≐ prefixSum d N + d :=
  (sum_succ' sB d N).eqTrans (congrAdd (.eqRefl _) (divisor_term hd))

/-- Distinct divisors `1 < d < N` give `1 + d + N ≤ σ(N)`. -/
theorem sigma_three {d N : PTm n} (hd : Γ ⊢[PRAAx] lt one d) (hN : Γ ⊢[PRAAx] lt d N)
    (h : Γ ⊢[PRAAx] dvd d N) : Γ ⊢[PRAAx] le (one + d + N) (sig N) := by
  have oneDvd : Γ ⊢[PRAAx] dvd one N :=
    dvd_of_eq' (pos_of_eq_succ (c := zero) (.eqRefl one)) (w := N) (one_mul N).eqSymm
  have atOne : Γ ⊢[PRAAx] le one (prefixSum two N) :=
    le_congr (divisor_term oneDvd) (.eqRefl _) (term_le_sum sB (le_refl two))
  have prefixD := le_trans atOne (prefix_mono N hd)
  have includeD := le_congr (.eqRefl _) (prefix_divisor h).eqSymm (add_le_add_right d prefixD)
  have prefixN := le_trans includeD (prefix_mono N hN)
  have posN := p_pos (le_trans hd (le_of_lt hN))
  exact le_congr (.eqRefl _) (prefix_divisor (dvd_self' posN)).eqSymm
    (add_le_add_right N prefixN)

theorem sigma_gap (d N : PTm n) :
    Γ ⊢[PRAAx] lt (N + d) (one + d + N) := by
  unfold lt
  exact le_congr (by ipra_ring) (.eqRefl _) (le_refl (one + d + N))

/-- If `N ≥ 2` and `σ(N) = N + 1`, no proper nontrivial divisor exists. -/
theorem prime_of_sigma {N : PTm n} (hN : Γ ⊢[PRAAx] le two N)
    (h : Γ ⊢[PRAAx] sig N ≐ N + one) : Γ ⊢[PRAAx] prime N := by
  unfold prime
  refine .andI hN (.allI (.impI (.impI (.impI ?_))))
  let d : PTm (n + 1) := var 0
  let N' := Syn.shift N
  let Δ := dvd d N' :: lt d N' :: le two d :: Γ.map Fm.shift
  have hd : Δ ⊢[PRAAx] lt one d := hyp2
  have hNd : Δ ⊢[PRAAx] lt d N' := Prf.hyp1
  have hDiv : Δ ⊢[PRAAx] dvd d N' := Prf.hyp0
  have sumEq : Δ ⊢[PRAAx] sig N' ≐ N' + one := by
    have h' := h.shift
    simp only [Fm.shift, Fm.subst_eq, PTm.subst_add, subst_ap2,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h'
    exact h'.wk.wk.wk
  have bound := le_congr (.eqRefl _) sumEq (sigma_three hd hNd hDiv)
  have canceled : Δ ⊢[PRAAx] le d zero :=
    le_of_add_le_add_right (c := N' + one)
      (le_congr (by ipra_ring) (zero_add _).eqSymm bound)
  exact lt_zero_absurd _ (le_trans (le_trans (le_succ_self _) hd) canceled)

end LeanProofs.IPRA.AnalyticNumberTheory.PerfectDivisorBounds
