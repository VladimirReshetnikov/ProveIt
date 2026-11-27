import IPRADerivations.AnalyticNumberTheory.BertrandSearch
import IPRADerivations.AnalyticNumberTheory.BertrandMiddle
import IPRADerivations.AnalyticNumberTheory.PrimorialUpper

/-!
# Bertrand's postulate: the bound on the central coefficient after a failed search

Packet: `analytic-number-theory/bertrand_ipra`, `bertrand.tex`, §"Where the prime factors can occur", the table
of prime ranges and the estimate (8): if the scan finds no prime in `(n, 2n − 2)`, then
`C(2n, n) ≤ (2n)^{s+1} 4^{⌊2n/3⌋}` with `s = ⌊√(2n)⌋`.

Write `P = 2x`, `s = isqrt P`, `m = ⌊P/3⌋`. The paper splits the factorization (7) of `C(2x, x)` by ranges of
primes. Here the factorization is never written: the single divisibility

    C(2x, x) ∣ ∏_{i ≤ s} i^{[i prime] v_i(lcm(1..P))} · ∏_{p ≤ m} p · (P − 1)        (`cb_dvd`)

is derived by comparing the valuations at every prime `q` (`BinomialLcm.dvd_of_val_le`), and the table of the
paper becomes the case analysis of `val_bound`:

* `q ≤ s`: `v_q(C(2x, x)) ≤ v_q(lcm(1..P))` (`BinomialLcm.binom_val_le`), the exponent of the first factor;
* `s < q ≤ m`: `q² > P`, so `v_q ≤ 1` (`BertrandSearch.exponent_le_one`), covered by the second factor;
* `m < q ≤ x` (and `q > s`): `v_q = 0` (`BertrandMiddle.val_middle`, `case_third`);
* `x < q` (`case_top`): `q > P` gives `v_q = 0`; `q = P` and `q = P − 2` are even and not prime
  (`even_not_prime`); `x < q < P − 2` is excluded by the failed search; `q = P − 1` is covered by the third
  factor with `v_q(q) = 1` (`val_self`).

Then `gap` (the estimate (8)): the first factor is at most `P^s` (`PrimorialLower.small_le`), the second at most
`4^m` (`PrimorialUpper.pri_le`), the third at most `P`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.BertrandFactor

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP prime_of_isP isP_of_prime lpf_of_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (dvd_of_val_le PE XE val_PE inst2_XE PE_pos binom_val_le)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialLower (Sm vB inst2_vB small_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialUpper (pri pri_pos pri_le val_pri mul_one1 lt_succ_add_l
  lt_succ_add_r)
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandSearch (found limit exclude_interval_prime exponent_le_one
  exponent_zero_above)
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandMiddle (val_middle)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrVal)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos val_mul val_unique not_dvd_one)
open LeanProofs.IPRA.Combinatorics.Catalan (cb)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.CentralBinomial (central_pos)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu)
open LeanProofs.IPRA.Signum (sg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Small facts -/

theorem sum1 {V A B C : PTm n} (h : Γ ⊢[PRAAx] le V A) : Γ ⊢[PRAAx] le V ((A + B) + C) := by
  ipra_le sl h + 𝔞 B + 𝔞 C

theorem sum2 {V A B C : PTm n} (h : Γ ⊢[PRAAx] le V B) : Γ ⊢[PRAAx] le V ((A + B) + C) := by
  ipra_le sl h + 𝔞 A + 𝔞 C

theorem sum3 {V A B C : PTm n} (h : Γ ⊢[PRAAx] le V C) : Γ ⊢[PRAAx] le V ((A + B) + C) := by
  ipra_le sl h + 𝔞 A + 𝔞 B

/-- An even number `2y` with `y ≥ 2` is not prime. -/
theorem even_not_prime {q y : PTm n} (hq : Γ ⊢[PRAAx] prime q) (e : Γ ⊢[PRAAx] q ≐ two * y)
    (hy : Γ ⊢[PRAAx] le two y) : Γ ⊢[PRAAx] Fm.bot := by
  have hq2 := prime_two hq
  have hz : Γ ⊢[PRAAx] q ≐ two * y + zero := e.eqTrans (add_zero _).eqSymm
  have hr : Γ ⊢[PRAAx] lt (zero : PTm n) two := le_of_eq_add (d := one) (by ipra_ring)
  have d2 : Γ ⊢[PRAAx] dvd two q := Prf.andE₂ (dmu two_pos' hz hr)
  have l := le_congr (lpf_of_prime hq) (.eqRefl _) (lpf_min (p_pos hq2) (le_refl two) d2)
  have en := natEq e
  have bad : Γ ⊢[PRAAx] le two zero := by ipra_le sl l + 2 * sl hy with en
  exact lt_zero_absurd _ bad

/-- `v_q(q) = 1` for a prime `q`. -/
theorem val_self {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) : Γ ⊢[PRAAx] val q q ≐ one := by
  have hq2 := prime_two hq
  exact val_unique hq2 (p_pos hq2) (c := one)
    ((mul_one1 q).eqSymm.eqTrans (congrMul (pw_one q).eqSymm (.eqRefl one))) (not_dvd_one hq2)

/-! ## The three factors -/

/-- `s = ⌊√(2x)⌋`. -/
abbrev sq (x : PTm n) : PTm n := isqrt (two * x)

/-- `m = ⌊2x/3⌋`. -/
abbrev md (x : PTm n) : PTm n := quo (two * x) (succ two)

/-- `∏_{i ≤ s} i^{[i prime] v_i(lcm(1..2x))} · ∏_{p ≤ m} p · (2x − 1)`. -/
abbrev Bd (x : PTm n) : PTm n := (Sm (sq x) (two * x) * pri (md x)) * pred (two * x)

theorem two_x_ge {x : PTm n} (h4 : Γ ⊢[PRAAx] le (two + two) x) : Γ ⊢[PRAAx] le two (two * x) := by
  ipra_le 2 * sl h4 + 6

theorem pred_pos {x : PTm n} (h4 : Γ ⊢[PRAAx] le (two + two) x) :
    Γ ⊢[PRAAx] pred (two * x) ≐ succ (pred (pred (two * x))) := by
  have hxn := natEq (p_pos (two_x_ge h4))
  exact pos_of_one_le (by ipra_le 2 * sl h4 + 6 with hxn)

/-- `2x < q²` for `q > ⌊√(2x)⌋`. -/
theorem sq_lt {q x : PTm n} (hsq : Γ ⊢[PRAAx] lt (sq x) q) : Γ ⊢[PRAAx] lt (two * x) (q * q) := by
  have hs2 := lt_isqrt_succ_sq (Γ := Γ) (two * x)
  ipra_le sl hs2 + sl hsq * sl hsq + 2 * (𝔞 (sq x) + 1) * sl hsq

/-! ## The ranges of primes -/

/-- The middle third: `⌊2x/3⌋ < q ≤ x` and `2x < q²` give `v_q(C(2x, x)) = 0`. -/
theorem case_third {q x : PTm n} (hq : Γ ⊢[PRAAx] prime q) (h3 : Γ ⊢[PRAAx] lt (two * x) (q * q))
    (hmq : Γ ⊢[PRAAx] lt (md x) q) (hqx : Γ ⊢[PRAAx] le q x) : Γ ⊢[PRAAx] val q (cb x) ≐ zero := by
  have tp : Γ ⊢[PRAAx] (succ two : PTm n) ≐ succ (pred (succ two)) := congrSucc (pred_succ _).eqSymm
  have d := dm tp (two * x)
  have dn := natEq (Prf.andE₁ d)
  have hr := Prf.andE₂ d
  have h2 : Γ ⊢[PRAAx] lt (two * x) (succ two * q) := by ipra_le 3 * sl hmq + sl hr with dn
  exact val_middle hq hqx h2 h3

/-- No prime `q` has `x < q < 2x − 1` after a failed search, for `x ≥ 4`. -/
theorem top_absurd {q x : PTm n} (hq : Γ ⊢[PRAAx] prime q) (fail : Γ ⊢[PRAAx] found x ≐ zero)
    (h4 : Γ ⊢[PRAAx] le (two + two) x) (hxq : Γ ⊢[PRAAx] lt x q)
    (hqT : Γ ⊢[PRAAx] lt q (pred (two * x))) : Γ ⊢[PRAAx] Fm.bot := by
  refine .orE (lt_or_le q (limit x)) ?_ ?_
  · exact exclude_interval_prime fail.wk hxq.wk Prf.hyp0 hq.wk
  · have hl : (le (limit x) q :: Γ) ⊢[PRAAx] le (limit x) q := Prf.hyp0
    have h4' : (le (limit x) q :: Γ) ⊢[PRAAx] le (two + two) x := h4.wk
    have hqT' : (le (limit x) q :: Γ) ⊢[PRAAx] lt q (pred (two * x)) := hqT.wk
    have x2 : (le (limit x) q :: Γ) ⊢[PRAAx] le two x := by ipra_le sl h4' + 2
    have hxn := natEq (p_pos (two_x_ge h4'))
    have limn := natEq (eq_add_of_le (two_x_ge h4'))
    have xpn := natEq (p_pos x2)
    have a : (le (limit x) q :: Γ) ⊢[PRAAx] le q (two * pred x) := by ipra_le sl hqT' with hxn - 2 * xpn
    have b : (le (limit x) q :: Γ) ⊢[PRAAx] le (two * pred x) q := by ipra_le sl hl with 2 * xpn - limn
    have px2 : (le (limit x) q :: Γ) ⊢[PRAAx] le two (pred x) := by ipra_le sl h4' + 1 with xpn
    exact even_not_prime hq.wk (le_antisymm a b) px2

/-- A prime `q > x` with `2x < q²` occurs in `C(2x, x)` at most as often as in `2x − 1`, after a failed search. -/
theorem case_top {q x : PTm n} (hq : Γ ⊢[PRAAx] prime q) (fail : Γ ⊢[PRAAx] found x ≐ zero)
    (h4 : Γ ⊢[PRAAx] le (two + two) x) (h3 : Γ ⊢[PRAAx] lt (two * x) (q * q)) (hxq : Γ ⊢[PRAAx] lt x q) :
    Γ ⊢[PRAAx] le (val q (cb x)) (val q (pred (two * x))) := by
  have hx := p_pos (two_x_ge h4)
  have v1 := exponent_le_one hq hx h3
  have x2 : Γ ⊢[PRAAx] le two x := by ipra_le sl h4 + 2
  refine .orE (lt_or_le (two * x) q) ?_ ?_
  · exact le_congr (exponent_zero_above hq.wk hx.wk Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · refine .orE (lt_or_eq_of_le (Prf.hyp0 (Γ := Γ) (φ := le q (two * x)))) ?_ ?_
    · have hqP : (lt q (two * x) :: le q (two * x) :: Γ) ⊢[PRAAx] lt q (two * x) := Prf.hyp0
      have hxn := natEq (hx.wk.wk : (lt q (two * x) :: le q (two * x) :: Γ) ⊢[PRAAx] _)
      have hqT : (lt q (two * x) :: le q (two * x) :: Γ) ⊢[PRAAx] le q (pred (two * x)) := by
        ipra_le sl hqP with hxn
      refine .orE (lt_or_eq_of_le hqT) ?_ ?_
      · exact .botE _ (top_absurd hq.wk.wk.wk fail.wk.wk.wk h4.wk.wk.wk hxq.wk.wk.wk Prf.hyp0)
      · have vs := (congrVal (.eqRefl q) (Prf.hyp0 (Γ := lt q (two * x) :: le q (two * x) :: Γ)
          (φ := q ≐ pred (two * x))).eqSymm).eqTrans (val_self hq.wk.wk.wk)
        exact le_congr (.eqRefl _) vs.eqSymm v1.wk.wk.wk
    · exact .botE _ (even_not_prime hq.wk.wk Prf.hyp0 x2.wk.wk)

/-- The comparison of valuations at a prime `q`. -/
theorem val_bound {q x : PTm n} (hq : Γ ⊢[PRAAx] prime q) (fail : Γ ⊢[PRAAx] found x ≐ zero)
    (h4 : Γ ⊢[PRAAx] le (two + two) x) : Γ ⊢[PRAAx] le (val q (cb x)) (val q (Bd x)) := by
  have hx := p_pos (two_x_ge h4)
  have Tpos := pred_pos h4
  have Spos := PE_pos (Γ := Γ) vB (succ (sq x)) (two * x)
  have Rpos := pri_pos (Γ := Γ) (md x)
  have vS := val_PE hq vB (succ (sq x)) (two * x)
  rw [inst2_XE, inst2_vB] at vS
  have vR := val_pri hq (md x)
  have vT := (val_mul hq (pos_mul Spos Rpos) Tpos).eqTrans
    (congrAdd ((val_mul hq Spos Rpos).eqTrans (congrAdd vS vR)) (.eqRefl _))
  refine le_congr (.eqRefl _) vT.eqSymm ?_
  refine .orE (lt_or_le (sq x) q) ?_ ?_
  · have h3 := sq_lt (Γ := lt (sq x) q :: Γ) (x := x) (q := q) Prf.hyp0
    have v1 := exponent_le_one hq.wk hx.wk h3
    refine .orE (lt_or_le (md x) q) ?_ ?_
    · refine .orE (lt_or_le x q) ?_ ?_
      · exact sum3 (case_top hq.wk.wk.wk fail.wk.wk.wk h4.wk.wk.wk h3.wk.wk Prf.hyp0)
      · exact le_congr (case_third hq.wk.wk.wk h3.wk.wk Prf.hyp1 Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
    · have sgm := sg_lt (a := q) (b := succ (md x))
        ((succ_monus_succ _ _).eqTrans (Prf.hyp0 (Γ := lt (sq x) q :: Γ) (φ := le q (md x))))
      exact sum2 (le_congr (.eqRefl _) sgm.eqSymm v1.wk)
  · have sgs := sg_lt (a := q) (b := succ (sq x))
      ((succ_monus_succ _ _).eqTrans (Prf.hyp0 (Γ := Γ) (φ := le q (sq x))))
    have Aeq : (le q (sq x) :: Γ) ⊢[PRAAx]
        (isP q * val q (lcmu (two * x))) * sg (monus (succ (sq x)) q) ≐ val q (lcmu (two * x)) :=
      (congrMul ((congrMul (isP_of_prime hq.wk) (.eqRefl _)).eqTrans (one_mul _)) sgs).eqTrans (mul_one1 _)
    exact sum1 (le_congr (.eqRefl _) Aeq.eqSymm (binom_val_le hq.wk x))

/-! ## The divisibility and the estimate (8) -/

theorem Bd_pos {x : PTm n} (h4 : Γ ⊢[PRAAx] le (two + two) x) : Γ ⊢[PRAAx] Bd x ≐ succ (pred (Bd x)) :=
  pos_mul (pos_mul (PE_pos vB (succ (sq x)) (two * x)) (pri_pos (md x))) (pred_pos h4)

/-- After a failed search: `C(2x, x) ∣ ∏_{i ≤ s} i^{[i prime] v_i(lcm(1..2x))} · ∏_{p ≤ m} p · (2x − 1)`. -/
theorem cb_dvd {x : PTm n} (fail : Γ ⊢[PRAAx] found x ≐ zero) (h4 : Γ ⊢[PRAAx] le (two + two) x) :
    Γ ⊢[PRAAx] dvd (cb x) (Bd x) := by
  have cpos := pos_of_one_le (central_pos (Γ := Γ) x)
  refine dvd_of_val_le (N := succ (cb x + Bd x)) cpos (Bd_pos h4) (lt_succ_add_l _ _) (lt_succ_add_r _ _)
    (.allI (.impI (.impI ?_)))
  have sa : Syn.shift (cb x) = cb (Syn.shift x) := by simp [Syn.shift]
  have sb : Syn.shift (Bd x) = Bd (Syn.shift x) := by simp [Syn.shift]
  have fail' : Γ.map Fm.shift ⊢[PRAAx] found (Syn.shift x) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using fail.shift
  have h4' : Γ.map Fm.shift ⊢[PRAAx] le (two + two) (Syn.shift x) := by
    simpa [Fm.shift, Syn.shift] using h4.shift
  rw [sa, sb]
  exact val_bound (prime_of_isP Prf.hyp0) fail'.wk.wk h4'.wk.wk

/-- The estimate (8): after a failed search, `C(2x, x) ≤ (2x)^s · 4^m · 2x`. -/
theorem gap {x : PTm n} (fail : Γ ⊢[PRAAx] found x ≐ zero) (h4 : Γ ⊢[PRAAx] le (two + two) x) :
    Γ ⊢[PRAAx] le (cb x) ((pw (two * x) (sq x) * pw two (two * md x)) * (two * x)) := by
  have hx := p_pos (two_x_ge h4)
  have hxn := natEq hx
  have cpos := pos_of_one_le (central_pos (Γ := Γ) x)
  have l1 := dvd_le' cpos (cb_dvd fail h4) (Bd_pos h4)
  have pl : Γ ⊢[PRAAx] le (pred (two * x)) (two * x) := by ipra_le 1 with hxn
  exact le_trans l1 (le_mul_mono (le_mul_mono (small_le hx (sq x)) (pri_le (md x))) pl)

end LeanProofs.IPRA.AnalyticNumberTheory.BertrandFactor
