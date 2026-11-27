import IPRADerivations.AnalyticNumberTheory.ChebyshevBounds
import IPRADerivations.DiophantineNumberTheory.AperyMultibound
import IPRADerivations.DiophantineNumberTheory.ResidueFacts
import IPRADerivations.Foundations.NumeralPrimes

/-!
# Bertrand's postulate: the integer inequality

Packet: `analytic-number-theory/bertrand_ipra`, `bertrand.tex`, §"The integer inequality and the finite
certificate", the estimates (9), (10), (11).

With `u = 2x + 1`, `s = ⌊√(2x)⌋ ≥ 38` and `3m ≤ 2x`, the inequality `4^x ≤ u^{s+2} 4^m` is contradictory:

* `ten` (the estimate (10)): `(d + 39)^6 ≤ 2^{d+36}` for every `d` (that is `(s + 1)^6 ≤ 2^{s−2}` for
  `s = d + 38`), by induction on `d`. The base is `39^6 ≤ 64^6 = 2^{36}`. The step is the polynomial inequality
  `(d + 40)^6 ≤ 2 (d + 39)^6`, whose difference has the nonnegative coefficients
  `1, 228, 21630, 1092760, 31003230, 468290388, 2941487522` (the paper raises `9 (s + 2) ≤ 10 (s + 1)` to the
  sixth power instead);
* `cube` (the estimate (9)): cubing and cancelling `4^{2x}` gives `4^x ≤ u^{3(s+2)}`;
* `power_chain` (the estimate (11)): `u^{3(s+2)} ≤ ((s + 1)^6)^{s+2} ≤ 2^{(s−2)(s+2)}`;
* `growth_absurd`: `(s − 2)(s + 2) + 4 = s² ≤ 2x`, so `16 · 4^x ≤ 4^x`, which is absurd.

Powers of four are written `2^{2x}`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.BertrandGrowth

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts (pw_two)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.NumeralPrimes (subst_num num_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Sixth powers -/

/-- `A^6 = ((A A)(A A))(A A)`. -/
theorem pw_six (A : PTm n) : Γ ⊢[PRAAx] pw A (num 6) ≐ ((A * A) * (A * A)) * (A * A) := by
  have e6 : Γ ⊢[PRAAx] (num 6 : PTm n) ≐ (two + two) + two := by
    ipra_lc
  exact (congrPw (.eqRefl _) e6).eqTrans ((pw_add A (two + two) two).eqTrans
    (congrMul ((pw_add A two two).eqTrans (congrMul (pw_two A) (pw_two A))) (pw_two A)))

/-- `(B + 1)^6 ≤ 2 B^6` for `B = d + 39`. -/
theorem six_step (d : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ d + num 39) (num 6)) (two * pw (d + num 39) (num 6)) := by
  have s6 := natEq (pw_six (Γ := Γ) (d + num 39))
  have s6' := natEq (pw_six (Γ := Γ) (succ d + num 39))
  ipra_le 𝔞 d ^ 6 + 228 * 𝔞 d ^ 5 + 21630 * 𝔞 d ^ 4 + 1092760 * 𝔞 d ^ 3 + 31003230 * 𝔞 d ^ 2 +
    468290388 * 𝔞 d + 2941487522 using (push_cast at s6 s6' ⊢; linear_combination 2 * s6 - s6')

/-- `2^{(d+1)+36} = 2 · 2^{d+36}`. -/
theorem two_step (d : PTm n) : Γ ⊢[PRAAx] pw two (succ d + num 36) ≐ two * pw two (d + num 36) := by
  have e : Γ ⊢[PRAAx] succ d + num 36 ≐ succ (d + num 36) := by ipra_ring
  exact (congrPw (.eqRefl _) e).eqTrans ((pw_succ two (d + num 36)).eqTrans (mul_comm _ _))

/-- `39^6 ≤ 2^{36}`, as `39^6 ≤ 64^6 = (2^6)^6`. -/
theorem base_six : Γ ⊢[PRAAx] le (pw ((zero : PTm n) + num 39) (num 6)) (pw two (zero + num 36)) := by
  have h : Γ ⊢[PRAAx] le ((zero : PTm n) + num 39) (num 64) := by ipra_le 25 using (push_cast; ring)
  have b2 : Γ ⊢[PRAAx] (num 64 : PTm n) ≐ pw two (num 6) := by
    ipra_lc -natEq (pw_six two)
  have ex : Γ ⊢[PRAAx] (num 6 : PTm n) * num 6 ≐ zero + num 36 := by
    ipra_lc
  have b3 : Γ ⊢[PRAAx] pw (num 64 : PTm n) (num 6) ≐ pw two (zero + num 36) :=
    (congrPw b2 (.eqRefl _)).eqTrans ((pw_mul two (num 6) (num 6)).eqTrans (congrPw (.eqRefl _) ex))
  exact le_congr (.eqRefl _) b3 (pw_le_pw (num 6) h)

/-- Variable: `0 = d` (induction). -/
private abbrev tenF : Fm PTm 1 := le (pw (var 0 + num 39) (num 6)) (pw two (var 0 + num 36))

private theorem ten₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] tenF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2, subst_num]
  · exact base_six
  · have ih : [tenF] ⊢[PRAAx] le (pw (var 0 + num 39) (num 6)) (pw two (var 0 + num 36)) := Prf.hyp0
    exact le_trans (six_step (var 0))
      (le_congr (.eqRefl _) (two_step (var 0)).eqSymm (le_mul_mono (le_refl two) ih))

/-- The estimate (10): `(d + 39)^6 ≤ 2^{d+36}`. -/
theorem ten (d : PTm n) : Γ ⊢[PRAAx] le (pw (d + num 39) (num 6)) (pw two (d + num 36)) := by
  simpa [subst_num] using inst (Γ := Γ) ten₀ (![d] : Fin 1 → PTm n)

/-! ## Cubing -/

theorem cancel_r {c a b : PTm n} (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (h : Γ ⊢[PRAAx] le (a * c) (b * c)) :
    Γ ⊢[PRAAx] le a b :=
  mul_le_cancel_at hc (le_congr (mul_comm a c) (mul_comm b c) h)

/-- The estimate (9): from `4^x ≤ u^e 4^m` and `3m ≤ 2x`: `4^x ≤ u^{3e}`. -/
theorem cube {x u e m : PTm n} (G0 : Γ ⊢[PRAAx] le (pw two (two * x)) (pw u e * pw two (two * m)))
    (hm : Γ ⊢[PRAAx] le (succ two * m) (two * x)) :
    Γ ⊢[PRAAx] le (pw two (two * x)) (pw u (e * succ two)) := by
  have c1 := pw_le_pw (succ two) G0
  have ex : Γ ⊢[PRAAx] (two * x) * succ two ≐ two * x + two * (two * x) := by
    ipra_ring
  have L1 : Γ ⊢[PRAAx] pw (pw two (two * x)) (succ two) ≐ pw two (two * x) * pw two (two * (two * x)) :=
    (pw_mul two (two * x) (succ two)).eqTrans ((congrPw (.eqRefl _) ex).eqTrans (pw_add two _ _))
  have R1 : Γ ⊢[PRAAx] pw (pw u e * pw two (two * m)) (succ two) ≐
      pw u (e * succ two) * pw two ((two * m) * succ two) :=
    (mul_pw _ _ _).eqTrans (congrMul (pw_mul u e (succ two)) (pw_mul two (two * m) (succ two)))
  have hexp : Γ ⊢[PRAAx] le ((two * m) * succ two) (two * (two * x)) := by ipra_le 2 * sl hm
  have r2 := pw_le_exp two_pos' hexp
  have c2 := le_trans (le_congr L1 R1 c1) (le_mul_mono (le_refl (pw u (e * succ two))) r2)
  exact cancel_r (pw_pos' two_pos' _) c2

/-! ## The chain of powers -/

/-- The estimate (11): `u ≤ (s + 1)²` and `s = d + 38` give `u^{3(s+2)} ≤ 2^{(d+36)(s+2)}`. -/
theorem power_chain {u s d : PTm n} (hu : Γ ⊢[PRAAx] le u ((s + one) * (s + one)))
    (es : Γ ⊢[PRAAx] s ≐ d + num 38) :
    Γ ⊢[PRAAx] le (pw u ((s + two) * succ two)) (pw two ((d + num 36) * (s + two))) := by
  have k1 := pw_le_pw ((s + two) * succ two) hu
  have ex : Γ ⊢[PRAAx] two * ((s + two) * succ two) ≐ num 6 * (s + two) := by
    ipra_lc
  have t1 : Γ ⊢[PRAAx] pw ((s + one) * (s + one)) ((s + two) * succ two) ≐ pw (pw (s + one) (num 6)) (s + two) :=
    (congrPw (pw_two (s + one)).eqSymm (.eqRefl _)).eqTrans ((pw_mul (s + one) two _).eqTrans
      ((congrPw (.eqRefl _) ex).eqTrans (pw_mul (s + one) (num 6) (s + two)).eqSymm))
  have e39 : Γ ⊢[PRAAx] d + num 39 ≐ s + one := by
    ipra_lc -natEq es
  have t2 := pw_le_pw (s + two) (ten (Γ := Γ) d)
  have t3 := le_congr (congrPw (congrPw e39 (.eqRefl _)) (.eqRefl _)) (pw_mul two (d + num 36) (s + two)) t2
  exact le_trans (le_congr (.eqRefl _) t1 k1) t3

/-- `x P ≤ x` is absurd for `x ≥ 1`, `P ≥ 2`. -/
theorem mul_absurd {X P : PTm n} (h : Γ ⊢[PRAAx] le (X * P) X) (hX : Γ ⊢[PRAAx] le one X)
    (hP : Γ ⊢[PRAAx] le two P) : Γ ⊢[PRAAx] Fm.bot := by
  have bad : Γ ⊢[PRAAx] le one zero := by ipra_le sl h + 𝔞 X * sl hP + sl hX
  exact lt_zero_absurd _ bad

/-- `4^x ≤ u^{s+2} 4^m` with `u = 2x + 1`, `3m ≤ 2x`, `s² ≤ 2x < (s + 1)²` and `s = d + 38` is absurd. -/
theorem growth_absurd {x s m d : PTm n}
    (G0 : Γ ⊢[PRAAx] le (pw two (two * x)) (pw (succ (two * x)) (s + two) * pw two (two * m)))
    (hm : Γ ⊢[PRAAx] le (succ two * m) (two * x))
    (hs1 : Γ ⊢[PRAAx] le (s * s) (two * x)) (hs2 : Γ ⊢[PRAAx] lt (two * x) ((s + one) * (s + one)))
    (es : Γ ⊢[PRAAx] s ≐ d + num 38) : Γ ⊢[PRAAx] Fm.bot := by
  have K1 := cube G0 hm
  have K2 := power_chain (u := succ (two * x)) hs2 es
  have ex2 : Γ ⊢[PRAAx] (d + num 36) * (s + two) + two * two ≐ s * s := by
    ipra_lc (-(𝔞 s + 2)) * natEq es
  have k4 := pw_le_exp two_pos' (le_congr ex2.eqSymm (.eqRefl _) hs1)
  have K3 := le_congr (pw_add two ((d + num 36) * (s + two)) (two * two)) (.eqRefl _) k4
  have fin := le_trans (le_mul_mono (le_trans K1 K2) (le_refl (pw two (two * two)))) K3
  have h14 : Γ ⊢[PRAAx] le (one : PTm n) (two * two) :=
    le_of_eq_add (d := succ two) (by ipra_ring)
  have hP : Γ ⊢[PRAAx] le two (pw two (two * two)) :=
    le_congr (pw_one two) (.eqRefl _) (pw_le_exp two_pos' h14)
  exact mul_absurd fin (one_le_pos (pw_pos' two_pos' _)) hP

end LeanProofs.IPRA.AnalyticNumberTheory.BertrandGrowth
