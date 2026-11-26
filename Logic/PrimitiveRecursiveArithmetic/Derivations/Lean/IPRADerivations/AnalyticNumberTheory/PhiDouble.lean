import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The doubling formula `φ(2n)`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-double`:
`φ(2n) = φ(n)` for odd `n`, and `φ(2n) = 2 φ(n)` for even `n ≥ 2`.

* odd `n`: `gcd(2, n) = 1` (`odd_cop`), so `φ(2n) = φ(2) φ(n)` (`Multiplicative.phi_mul_at`) with
  `φ(2) = 1` (`phi_two`);
* even `n`: `[gcd(k, 2n) = 1] = [gcd(k, n) = 1]` (`even_point`), and `[gcd(k, n) = 1]` has period
  `n` (`gcd_period`), so splitting `∑_{k<n+n}` (`sum_split`) gives `2 φ(n)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos rem_eq_of_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_pos_right)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (eqb_iff shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_eq' shift_mul' shift_rem')
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Splitting a sum at its parameter -/

/-- `f(x + i, x)`, over `0 = i`, `1 = x`. -/
def shiftBy (f : PTm 2) : PTm 2 := Syn.subst ![var 1 + var 0, var 1] f

theorem inst2_shiftBy (f : PTm 2) (i x : PTm n) : inst2 (shiftBy f) i x = inst2 f (x + i) x := by
  simp only [inst2, shiftBy, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

/-- Variables: `0 = B`, `1 = x`. -/
private abbrev splitF (f : PTm 2) : Fm PTm 2 :=
  ap2 (sumF f) (var 1 + var 0) (var 1) ≐ ap2 (sumF f) (var 1) (var 1) + ap2 (sumF (shiftBy f)) (var 0) (var 1)

private theorem sum_split₀ (f : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] splitF f := by
  ipra_ind [subst_ap2]
  · exact (congrAp2 (sumF f) (add_zero _) (.eqRefl _)).eqTrans
      ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) (sum_zero _ _).eqSymm))
  · refine (congrAp2 (sumF f) (add_succ _ _) (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans ?_)
    refine .eqTrans ?_ (congrAdd (.eqRefl _) (sum_succ' _ _ _)).eqSymm
    rw [inst2_shiftBy]
    refine withEq Prf.hyp0 fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring

/-- `∑_{k<x+B} f(k, x) = ∑_{k<x} f(k, x) + ∑_{i<B} f(x + i, x)`. -/
theorem sum_split (f : PTm 2) (B x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF f) (x + B) x ≐ ap2 (sumF f) x x + ap2 (sumF (shiftBy f)) B x := by
  have h := inst (Γ := Γ) (sum_split₀ f) (![B, x] : Fin 2 → PTm n)
  simpa using h

/-! ## Small facts -/

theorem two_pos' : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

/-- `φ(2) = 1`. -/
theorem phi_two : Γ ⊢[PRAAx] phi (two : PTm n) ≐ one := by
  have s₂ := sum_succ' (Γ := Γ) totBody one two
  have s₁ := sum_succ' (Γ := Γ) totBody zero two
  rw [inst2_tot] at s₁ s₂
  have e₀ := AnalyticNumberTheory.Totatives.e_zero (Γ := Γ) (N := two) (le_refl _)
  have g := gcd_pos (B := two) (Γ := Γ) (congrSucc (pred_succ zero).eqSymm)
  have e₁ : Γ ⊢[PRAAx] eqb (gcd one two) one ≐ one :=
    eqb_of_eq (eq_one_of_dvd_one g (Prf.andE₁ (gcd_dvd' (b := two) (congrSucc (pred_succ zero).eqSymm))))
  refine s₂.eqTrans ((congrAdd (s₁.eqTrans ((congrAdd (sum_zero _ _) e₀))) e₁).eqTrans ?_)
  ipra_ring

/-- `gcd(n + i, n) = gcd(i, n)`. -/
theorem gcd_period {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (i : PTm n) :
    Γ ⊢[PRAAx] gcd (N + i) N ≐ gcd i N := by
  have r : Γ ⊢[PRAAx] rem (N + i) N ≐ rem i N :=
    rem_eq_of_eq hN (k₁ := zero) (k₂ := one) (by ipra_ring)
  exact (gcd_rem hN (N + i)).eqSymm.eqTrans ((congrGcd r (.eqRefl _)).eqTrans (gcd_rem hN i))

/-! ## Odd `n` -/

/-- `gcd(2, 2t + 1) = 1`. -/
theorem odd_cop (t : PTm n) : Γ ⊢[PRAAx] gcd two (two * t + one) ≐ one := by
  have hg := gcd_pos (B := two * t + one) (two_pos' (Γ := Γ))
  have d := gcd_dvd' (b := two * t + one) (two_pos' (Γ := Γ))
  have hle := dvd_le' hg (Prf.andE₁ d) two_pos'
  refine .orE (lt_or_eq_of_le hle) ?_ ?_
  · have l : (lt (gcd two (two * t + one)) two :: Γ) ⊢[PRAAx] le (gcd two (two * t + one)) one :=
      (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    exact le_antisymm l (one_le_of_pos hg.wk)
  · have d2 : ((gcd two (two * t + one) ≐ two) :: Γ) ⊢[PRAAx] rem (two * t + one) two ≐ zero :=
      dvd_congr_left Prf.hyp0 (Prf.andE₂ d).wk
    have r1 : ((gcd two (two * t + one) ≐ two) :: Γ) ⊢[PRAAx] rem (two * t + one) two ≐ one :=
      rem_eq' two_pos' (q := t) (.eqRefl _) (le_refl _)
    exact succ_ne_zero' _ (r1.eqSymm.eqTrans d2)

/-- `φ(2n) = φ(n)` for `n = 2t + 1`. -/
theorem phi_double_odd_at (t : PTm n) : Γ ⊢[PRAAx] phi (two * (two * t + one)) ≐ phi (two * t + one) := by
  have hn : Γ ⊢[PRAAx] two * t + one ≐ succ (pred (two * t + one)) :=
    AnalyticNumberTheory.Primes.eq_succ_pred (y := two * t) (by ipra_ring)
  refine (phi_mul_at two_pos' hn (odd_cop t)).eqTrans ((congrMul phi_two (.eqRefl _)).eqTrans (one_mul _))

/-! ## Even `n` -/

/-- `[gcd(k, 2n) = 1] = [gcd(k, n) = 1]` when `2 ∣ n`. -/
theorem even_point {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (h2 : Γ ⊢[PRAAx] dvd two N) (k : PTm n) :
    Γ ⊢[PRAAx] eqb (gcd k (two * N)) one ≐ eqb (gcd k N) one := by
  refine eqb_iff (.impI (cop_right hN.wk Prf.hyp0)) (.impI ?_)
  have hk : ((gcd k N ≐ one) :: Γ) ⊢[PRAAx] gcd k N ≐ one := Prf.hyp0
  have g := gcd_pos_right (a := k) (two_pos' (Γ := (gcd k N ≐ one) :: Γ))
  have d := gcd_dvd_at g
  have dn := dvd_trans' g two_pos' (Prf.andE₂ d) h2.wk
  have c2 := eq_one_of_dvd_one g (dvd_congr hk (gcd_greatest' g (Prf.andE₁ d) dn))
  exact cop_both two_pos' hN.wk c2 hk

/-- `φ(2n) = 2 φ(n)` for even `n ≥ 1`. -/
theorem phi_double_even_at {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (h2 : Γ ⊢[PRAAx] dvd two N) :
    Γ ⊢[PRAAx] phi (two * N) ≐ two * phi N := by
  have h2' : Γ.map Fm.shift ⊢[PRAAx] dvd two (Syn.shift N) := by
    have e := shift_eq' h2
    rw [shift_rem'] at e
    simpa [Syn.shift] using e
  have s₁ : Γ ⊢[PRAAx] phi (two * N) ≐ ap2 (sumF totBody) (two * N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_tot, inst2_tot, shift_mul']
    have e : Syn.shift (two : PTm n) = two := by simp [Syn.shift]
    rw [e]
    exact even_point (shift_pos hN).wk h2'.wk _
  have s₂ : Γ ⊢[PRAAx] ap2 (sumF totBody) (two * N) N ≐ ap2 (sumF totBody) (N + N) N :=
    congrAp2 (sumF totBody) (by ipra_ring) (.eqRefl _)
  have s₃ := sum_split (Γ := Γ) totBody N N
  have s₄ : Γ ⊢[PRAAx] ap2 (sumF (shiftBy totBody)) N N ≐ phi N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_shiftBy, inst2_tot, inst2_tot]
    exact congrEqb (gcd_period (shift_pos hN).wk _) (.eqRefl _)
  refine s₁.eqTrans (s₂.eqTrans (s₃.eqTrans ((congrAdd (.eqRefl _) s₄).eqTrans ?_)))
  ipra_ring

/-! ## Closed statements -/

/-- `thm:phi-double`, odd case: `φ(2(2t + 1)) = φ(2t + 1)`. -/
abbrev phiDoubleOddFormula : Fm PTm 1 := phi (two * (two * var 0 + one)) ≐ phi (two * var 0 + one)

theorem phi_double_odd : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiDoubleOddFormula :=
  closeUniv 1 (phi_double_odd_at (var 0))

/-- `thm:phi-double`, even case: `φ(2 · 2(t + 1)) = 2 φ(2(t + 1))`. -/
abbrev phiDoubleEvenFormula : Fm PTm 1 :=
  phi (two * (two * succ (var 0))) ≐ two * phi (two * succ (var 0))

theorem phi_double_even : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiDoubleEvenFormula :=
  closeUniv 1 (phi_double_even_at (pos_mul two_pos' (congrSucc (pred_succ _).eqSymm))
    (dvd_of_eq' two_pos' (w := succ (var 0)) (.eqRefl _)))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble
