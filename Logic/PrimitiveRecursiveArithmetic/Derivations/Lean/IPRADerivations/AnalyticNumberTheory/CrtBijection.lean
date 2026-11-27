import IPRADerivations.AnalyticNumberTheory.Multiplicative

/-!
# The constructive Chinese remainder bijection

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:crt`.

For `m, n ≥ 1` with `gcd(m, n) = 1`, the map `x ↦ (x mod m, x mod n)` is a bijection from
`[0, mn)` onto `[0, m) × [0, n)`, and it restricts to a bijection of reduced residue systems:

* `crt_into`: it lands in `[0, m) × [0, n)`;
* `crt_inj`: two numbers below `mn` with the same residues are equal
  (`Foundations.ChineseRemainder.crt_unique_at` with `gcd = 1`);
* `crt_surj`: every `(a, b)` with `a < m`, `b < n` is hit by some `x < mn` (the Bézout witness of
  `Foundations.ChineseRemainder.crt_exists_at`, reduced mod `mn`);
* `crt_reduced`, `crt_reduced_inv`: `gcd(x, mn) = 1` iff `gcd(x mod m, m) = gcd(x mod n, n) = 1`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.CrtBijection

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt' rem_eq' zero_lt' rem_rem_mul cop_left cop_right
  cop_both gcd_rem shift_lt)
export RSA (quo_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem rem_small {a M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M) :
    Γ ⊢[PRAAx] rem a M ≐ a :=
  rem_eq' hM (q := zero) (by ipra_ring) ha

section CRT

variable {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
include hm hN

/-- The residue pair lies in `[0, m) × [0, n)`. -/
theorem crt_into (x : PTm n) : Γ ⊢[PRAAx] lt (rem x m) m ⋏ lt (rem x N) N :=
  .andI (rem_lt' hm x) (rem_lt' hN x)

/-- Injectivity on `[0, mn)`. -/
theorem crt_inj (hc : Γ ⊢[PRAAx] gcd m N ≐ one) {x y : PTm n} (hx : Γ ⊢[PRAAx] lt x (m * N))
    (hy : Γ ⊢[PRAAx] lt y (m * N)) (h₁ : Γ ⊢[PRAAx] rem x m ≐ rem y m) (h₂ : Γ ⊢[PRAAx] rem x N ≐ rem y N) :
    Γ ⊢[PRAAx] x ≐ y := by
  have u := crt_unique_at hm hN h₁ h₂
  have q : Γ ⊢[PRAAx] m * quo N (gcd m N) ≐ m * N :=
    congrMul (.eqRefl _) ((congrAp2 quoF (.eqRefl _) hc).eqTrans (quo_one N))
  have P := pos_mul hm hN
  exact (rem_small P hx).eqSymm.eqTrans ((congrAp2 remF (.eqRefl _) q.eqSymm).eqTrans
    (u.eqTrans ((congrAp2 remF (.eqRefl _) q).eqTrans (rem_small P hy))))

/-- Surjectivity onto `[0, m) × [0, n)`. -/
theorem crt_surj (hc : Γ ⊢[PRAAx] gcd m N ≐ one) {a b : PTm n} (ha : Γ ⊢[PRAAx] lt a m) (hb : Γ ⊢[PRAAx] lt b N) :
    Γ ⊢[PRAAx] Fm.ex (lt (var 0) (Syn.shift (m * N)) ⋏
      (rem (var 0) (Syn.shift m) ≐ Syn.shift a ⋏ rem (var 0) (Syn.shift N) ≐ Syn.shift b)) := by
  have hc' : Γ ⊢[PRAAx] rem a (gcd m N) ≐ rem b (gcd m N) :=
    (congrAp2 remF (.eqRefl _) hc).eqTrans ((Euler.rem_one _).eqTrans
      ((Euler.rem_one _).eqSymm.eqTrans (congrAp2 remF (.eqRefl _) hc.eqSymm)))
  refine Prf.exE (crt_exists_at hm hN hc') ?_
  have hm' := shift_pos hm
  have hN' := shift_pos hN
  have ha' := shift_lt ha
  have hb' := shift_lt hb
  let C := (rem (var 0) (Syn.shift m) ≐ rem (Syn.shift a) (Syn.shift m) ⋏
    rem (var 0) (Syn.shift N) ≐ rem (Syn.shift b) (Syn.shift N)) :: Γ.map Fm.shift
  have h : C ⊢[PRAAx] _ := Prf.hyp0
  have rr := rem_rem_mul (Γ := C) hm'.wk hN'.wk (var 0)
  have e₁ := (Prf.andE₁ rr).eqTrans ((Prf.andE₁ h).eqTrans (rem_small hm'.wk ha'.wk))
  have e₂ := (Prf.andE₂ rr).eqTrans ((Prf.andE₂ h).eqTrans (rem_small hN'.wk hb'.wk))
  have hl := rem_lt' (Γ := C) (pos_mul hm'.wk hN'.wk) (var 0)
  refine .exI (rem (var 0) (Syn.shift m * Syn.shift N)) ?_
  simp only [Fm.subst, Fm.subst_and, subst_lt, subst_ap2, Syn.subst_var]
  have g := Prf.andI hl (Prf.andI e₁ e₂)
  simp [Syn.shift, Syn.subst_subst]
  exact g

/-- Reduced residues go to reduced residue pairs. -/
theorem crt_reduced {x : PTm n} (h : Γ ⊢[PRAAx] gcd x (m * N) ≐ one) :
    Γ ⊢[PRAAx] gcd (rem x m) m ≐ one ⋏ gcd (rem x N) N ≐ one :=
  .andI ((gcd_rem hm x).eqTrans (cop_left hm h)) ((gcd_rem hN x).eqTrans (cop_right hN h))

/-- Reduced residue pairs come only from reduced residues. -/
theorem crt_reduced_inv {x : PTm n} (h₁ : Γ ⊢[PRAAx] gcd (rem x m) m ≐ one) (h₂ : Γ ⊢[PRAAx] gcd (rem x N) N ≐ one) :
    Γ ⊢[PRAAx] gcd x (m * N) ≐ one :=
  cop_both hm hN ((gcd_rem hm x).eqSymm.eqTrans h₁) ((gcd_rem hN x).eqSymm.eqTrans h₂)

end CRT

end LeanProofs.IPRA.AnalyticNumberTheory.CrtBijection
