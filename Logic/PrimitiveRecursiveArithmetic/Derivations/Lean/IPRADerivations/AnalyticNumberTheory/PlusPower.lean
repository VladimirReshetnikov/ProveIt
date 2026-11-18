import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.AnalyticNumberTheory.PhiDivides
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.AnalyticNumberTheory.CrtBijection

/-!
# The `aⁿ + bⁿ` totient congruence

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:plus-power`:
for distinct positive `a, b` and `n ≥ 1`, `n ∣ φ(aⁿ + bⁿ)`.

The packet's proof builds the unit `u = −A B⁻¹` and computes its order. Here the order is replaced by
the set of exponents `E = {k : Aᵏ ≡ Bᵏ (mod C)}`, `C = Aⁿ + Bⁿ`, for coprime distinct `A, B ≥ 1`:

* `cancel`: a unit factor cancels from a congruence (Euler: `w^{φ(C)} ≡ 1`);
* `cop_pow`, `cop_sum`: `A` and `B` are units mod `C`;
* `sub_closed`: `E` is closed under differences; `phi_mem`: `φ(C) ∈ E` (Euler); `two_n_mem`: `2n ∈ E`
  (`A^{2n} + Bⁿ C = B^{2n} + Aⁿ C`);
* `small_not_mem`: no `1 ≤ k ≤ n` lies in `E`, since then `Aᵏ, Bᵏ < C` and `Aᵏ ≠ Bᵏ`;
* `two_n_dvd`: hence `φ(C) mod 2n ∈ E` is `0` (otherwise it or `2n` minus it is a small member), so
  `2n ∣ φ(C)`;
* `plus_power`: for general distinct `a, b ≥ 1`, divide by `g = gcd(a, b)`: `aⁿ + bⁿ = gⁿ C`, so
  `φ(C) ∣ φ(aⁿ + bⁿ)` (`PhiDivides`) and `n ∣ φ(aⁿ + bⁿ)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PlusPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos rem_eq_of_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (rem_mul_congr pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (euler_at)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_rem_congr pw_one_base phi_pos gcd_pos_right gcd_eq_one_of_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDivides (phi_divides_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_lt_pw pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.CrtBijection (rem_small)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem pos_shift {x : PTm n} (h : Γ ⊢[PRAAx] x ≐ succ (pred x)) :
    Γ.map Fm.shift ⊢[PRAAx] Syn.shift x ≐ succ (pred (Syn.shift x)) := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, PTm.subst_pred, ConciseIPRA.PTm.subst_succ] at e
  exact e

theorem one_pos : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := (congrSucc (pred_succ _)).eqSymm

/-- A unit factor cancels: `x w ≡ y w (mod C)`, `gcd(w, C) = 1` give `x ≡ y`. -/
theorem cancel {C w x y : PTm n} (hC : Γ ⊢[PRAAx] C ≐ succ (pred C)) (hw : Γ ⊢[PRAAx] gcd w C ≐ one)
    (h : Γ ⊢[PRAAx] rem (x * w) C ≐ rem (y * w) C) : Γ ⊢[PRAAx] rem x C ≐ rem y C := by
  have e := euler_at hw hC
  have hp := phi_pos hC
  have pw' : Γ ⊢[PRAAx] pw w (phi C) ≐ w * pw w (pred (phi C)) :=
    (congrPw (.eqRefl _) hp).eqTrans ((pw_succ _ _).eqTrans (mul_comm _ _))
  have side : ∀ z : PTm n, Γ ⊢[PRAAx] rem z C ≐ rem (z * w * pw w (pred (phi C))) C := fun z =>
    (congrAp2 remF (one_mul z).eqSymm (.eqRefl _)).eqTrans ((rem_mul_congr z hC e).eqSymm.eqTrans
      (congrAp2 remF ((congrMul pw' (.eqRefl _)).eqTrans (by apply deriveNat; ipra_simps; ring)) (.eqRefl _)))
  exact (side x).eqTrans ((rem_mul_congr _ hC h).eqTrans (side y).eqSymm)

/-- `gcd(C, B) = 1 → gcd(C, Bᵏ) = 1`. -/
theorem cop_pow {B C : PTm n} (hC : Γ ⊢[PRAAx] C ≐ succ (pred C)) (h : Γ ⊢[PRAAx] gcd C B ≐ one) (k : PTm n) :
    Γ ⊢[PRAAx] gcd C (pw B k) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (gcd (Syn.shift C) (pw (Syn.shift B) (var 0)) ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ex2, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact (congrGcd (.eqRefl _) (pw_zero _)).eqTrans
        (gcd_eq_one_of_dvd (gcd_pos_right one_pos) (.orI₂ (.eqRefl _)))
    · simp only [Fm.subst_eq, subst_ex2, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have h' := Euler.shift_cop h
      exact (congrGcd (.eqRefl _) (pw_succ _ _)).eqTrans (coprime_mul (pos_shift hC).wk Prf.hyp0 h'.wk)
  have h2 := Prf.allE k hall
  simp only [Fm.subst_eq, subst_ex2, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h2
  exact h2

/-- `gcd(B, A) = 1`, `n ≥ 1`, `B ≥ 1` give `gcd(B, Aⁿ + Bⁿ) = 1`. -/
theorem cop_sum {A B N : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (h : Γ ⊢[PRAAx] gcd B A ≐ one) : Γ ⊢[PRAAx] gcd B (pw A N + pw B N) ≐ one := by
  have hd := gcd_pos (B := pw A N + pw B N) hB
  have dd := gcd_dvd' (b := pw A N + pw B N) hB
  have dBn : Γ ⊢[PRAAx] dvd (gcd B (pw A N + pw B N)) (pw B N) :=
    dvd_congr ((pw_succ _ _).eqSymm.eqTrans (congrPw (.eqRefl _) hN.eqSymm))
      (dvd_congr (mul_comm _ _) (dvd_mul' hd (pw B (pred N)) (Prf.andE₁ dd))).eqSymm.eqSymm
  have dAn := dvd_sub' hd (Prf.andE₂ dd) dBn
  have g := cop_pow hB h N
  exact eq_one_of_dvd_one hd (dvd_congr g (gcd_greatest' hd (Prf.andE₁ dd) dAn))

/-! ## The exponent set `E = {k : Aᵏ ≡ Bᵏ (mod C)}` -/

abbrev mem (A B C k : PTm n) : Fm PTm n := rem (pw A k) C ≐ rem (pw B k) C

section Exponents

variable {A B C : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hC : Γ ⊢[PRAAx] C ≐ succ (pred C))
  (hBC : Γ ⊢[PRAAx] gcd B C ≐ one)
include hB hC hBC

/-- `E` is closed under differences. -/
theorem sub_closed {k d : PTm n} (hk : Γ ⊢[PRAAx] mem A B C k) (hj : Γ ⊢[PRAAx] mem A B C (k + d)) :
    Γ ⊢[PRAAx] mem A B C d := by
  have hBk : Γ ⊢[PRAAx] gcd (pw B k) C ≐ one :=
    gcd_comm_one (pw_pos' hB k) (cop_pow hC (gcd_comm_one hC hBC) k)
  have s₁ : Γ ⊢[PRAAx] rem (pw A k * pw A d) C ≐ rem (pw B k * pw A d) C := rem_mul_congr _ hC hk
  have s₂ : Γ ⊢[PRAAx] rem (pw A k * pw A d) C ≐ rem (pw B k * pw B d) C :=
    (congrAp2 remF (pw_add _ _ _).eqSymm (.eqRefl _)).eqTrans (hj.eqTrans (congrAp2 remF (pw_add _ _ _) (.eqRefl _)))
  refine cancel hC hBk ?_
  exact (congrAp2 remF (mul_comm _ _) (.eqRefl _)).eqTrans (s₁.eqSymm.eqTrans
    (s₂.eqTrans (congrAp2 remF (mul_comm _ _) (.eqRefl _))))

end Exponents

/-- `2n ∈ E`: `A^{2n} + Bⁿ C = B^{2n} + Aⁿ C` for `C = Aⁿ + Bⁿ`. -/
theorem two_n_mem {A B N : PTm n} (hC : Γ ⊢[PRAAx] pw A N + pw B N ≐ succ (pred (pw A N + pw B N))) :
    Γ ⊢[PRAAx] mem A B (pw A N + pw B N) (two * N) := by
  have ea : Γ ⊢[PRAAx] pw A (two * N) ≐ pw A N * pw A N :=
    (congrPw (.eqRefl _) (by apply deriveNat; ipra_simps; ring)).eqTrans (pw_add _ _ _)
  have eb : Γ ⊢[PRAAx] pw B (two * N) ≐ pw B N * pw B N :=
    (congrPw (.eqRefl _) (by apply deriveNat; ipra_simps; ring)).eqTrans (pw_add _ _ _)
  have x := natEq ea; have y := natEq eb
  refine rem_eq_of_eq hC (k₁ := pw B N) (k₂ := pw A N) ?_
  apply deriveNat; ipra_simps
  linear_combination x - y

/-- No `1 ≤ k ≤ n` lies in `E` when `A ≠ B`. -/
theorem small_not_mem {A B N k : PTm n} (φ : Fm PTm n) (hA : Γ ⊢[PRAAx] A ≐ succ (pred A))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hne : Γ ⊢[PRAAx] neg (A ≐ B)) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k))
    (hkn : Γ ⊢[PRAAx] le k N) (h : Γ ⊢[PRAAx] mem A B (pw A N + pw B N) k) : Γ ⊢[PRAAx] φ := by
  have pA := natEq (pw_pos' hA N); have pB := natEq (pw_pos' hB N)
  have hC : Γ ⊢[PRAAx] pw A N + pw B N ≐ succ (pred (pw A N + pw B N)) :=
    AnalyticNumberTheory.Primes.eq_succ_pred (y := pw A N + pred (pw B N)) (by apply deriveNat; ipra_simps; linear_combination pB)
  have la : Γ ⊢[PRAAx] lt (pw A k) (pw A N + pw B N) := by
    have m := natEq (eq_add_of_le (pw_le_exp hA hkn))
    refine le_of_eq_add (d := monus (pw A N) (pw A k) + pred (pw B N)) ?_
    apply deriveNat; ipra_simps; linear_combination m + pB
  have lb : Γ ⊢[PRAAx] lt (pw B k) (pw A N + pw B N) := by
    have m := natEq (eq_add_of_le (pw_le_exp hB hkn))
    refine le_of_eq_add (d := monus (pw B N) (pw B k) + pred (pw A N)) ?_
    apply deriveNat; ipra_simps; linear_combination m + pA
  have e : Γ ⊢[PRAAx] pw A k ≐ pw B k := (rem_small hC la).eqSymm.eqTrans (h.eqTrans (rem_small hC lb))
  have e' : Γ ⊢[PRAAx] pw A (succ (pred k)) ≐ pw B (succ (pred k)) :=
    (congrPw (.eqRefl _) hk.eqSymm).eqTrans (e.eqTrans (congrPw (.eqRefl _) hk))
  refine .orE (lt_or_le A B) ?_ ?_
  · exact lt_irrefl _ _ (lt_congr e'.wk (.eqRefl _) (pw_lt_pw (a := B) (b := A) (pred k) Prf.hyp0))
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact lt_irrefl _ _ (lt_congr e'.wk.wk.eqSymm (.eqRefl _) (pw_lt_pw (a := A) (b := B) (pred k) Prf.hyp0))
    · exact .botE _ (.impE hne.wk.wk Prf.hyp0.eqSymm)

/-- `2n ∣ φ(Aⁿ + Bⁿ)` for coprime distinct `A, B ≥ 1` and `n ≥ 1`. -/
theorem two_n_dvd {A B N : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hAB : Γ ⊢[PRAAx] gcd A B ≐ one) (hne : Γ ⊢[PRAAx] neg (A ≐ B)) :
    Γ ⊢[PRAAx] dvd (two * N) (phi (pw A N + pw B N)) := by
  have pB := natEq (pw_pos' hB N)
  have hC : Γ ⊢[PRAAx] pw A N + pw B N ≐ succ (pred (pw A N + pw B N)) :=
    AnalyticNumberTheory.Primes.eq_succ_pred (y := pw A N + pred (pw B N)) (by apply deriveNat; ipra_simps; linear_combination pB)
  have hBC : Γ ⊢[PRAAx] gcd B (pw A N + pw B N) ≐ one := cop_sum hB hN (gcd_comm_one hB hAB)
  have hAC : Γ ⊢[PRAAx] gcd A (pw A N + pw B N) ≐ one :=
    (congrGcd (.eqRefl _) (add_comm _ _)).eqTrans (cop_sum hA hN hAB)
  have h2N : Γ ⊢[PRAAx] two * N ≐ succ (pred (two * N)) :=
    AnalyticNumberTheory.Primes.eq_succ_pred (y := succ (two * pred N))
      (by have e := natEq hN; apply deriveNat; ipra_simps; linear_combination 2 * e)
  -- `φ(C) = 2n q + s`.
  have dv := div_eq (j := phi (pw A N + pw B N)) h2N
  have sl := rem_lt' h2N (phi (pw A N + pw B N))
  have m2 := two_n_mem (A := A) (B := B) hC
  have mq : Γ ⊢[PRAAx] mem A B (pw A N + pw B N) (two * N * quo (phi (pw A N + pw B N)) (two * N)) :=
    (congrAp2 remF (pw_mul _ _ _).eqSymm (.eqRefl _)).eqTrans ((pw_rem_congr hC m2 _).eqTrans
      (congrAp2 remF (pw_mul _ _ _) (.eqRefl _)))
  have mφ : Γ ⊢[PRAAx] mem A B (pw A N + pw B N) (phi (pw A N + pw B N)) :=
    (euler_at hAC hC).eqTrans (euler_at hBC hC).eqSymm
  have mφ' : Γ ⊢[PRAAx] mem A B (pw A N + pw B N)
      (two * N * quo (phi (pw A N + pw B N)) (two * N) + rem (phi (pw A N + pw B N)) (two * N)) :=
    (congrAp2 remF (congrPw (.eqRefl _) dv.eqSymm) (.eqRefl _)).eqTrans (mφ.eqTrans
      (congrAp2 remF (congrPw (.eqRefl _) dv) (.eqRefl _)))
  have ms := sub_closed hB hC hBC mq mφ'
  -- `s = 0`.
  refine dvd_of_eq' h2N (w := quo (phi (pw A N + pw B N)) (two * N)) ?_
  refine .orE (zero_or_succ (rem (phi (pw A N + pw B N)) (two * N))) ?_ ?_
  · exact dv.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))
  · have hs : (((rem (phi (pw A N + pw B N)) (two * N)) ≐ succ (pred (rem (phi (pw A N + pw B N)) (two * N)))) :: Γ) ⊢[PRAAx] (rem (phi (pw A N + pw B N)) (two * N)) ≐ succ (pred (rem (phi (pw A N + pw B N)) (two * N))) := Prf.hyp0
    refine .orE (lt_or_le (rem (phi (pw A N + pw B N)) (two * N)) (succ N)) ?_ ?_
    · exact small_not_mem _ hA.wk.wk hB.wk.wk hne.wk.wk hs.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
        ms.wk.wk
    · -- `n < (rem (phi (pw A N + pw B N)) (two * N)) < 2n`: `t = 2n − (rem (phi (pw A N + pw B N)) (two * N)) ∈ E` with `1 ≤ t < n`.
      let C' := le (succ N) (rem (phi (pw A N + pw B N)) (two * N)) :: ((rem (phi (pw A N + pw B N)) (two * N)) ≐ succ (pred (rem (phi (pw A N + pw B N)) (two * N)))) :: Γ
      have f1 := natEq (eq_add_of_le (Prf.hyp0 : C' ⊢[PRAAx] le (succ N) (rem (phi (pw A N + pw B N)) (two * N))))
      have f2 := natEq (eq_add_of_le (sl.wk.wk : C' ⊢[PRAAx] lt (rem (phi (pw A N + pw B N)) (two * N)) (two * N)))
      have e2 : C' ⊢[PRAAx] two * N ≐ (rem (phi (pw A N + pw B N)) (two * N)) + monus (two * N) (rem (phi (pw A N + pw B N)) (two * N)) :=
        eq_add_of_le (le_of_lt sl.wk.wk)
      have f3 := natEq e2
      have mt : C' ⊢[PRAAx] mem A B (pw A N + pw B N) (monus (two * N) (rem (phi (pw A N + pw B N)) (two * N))) :=
        sub_closed hB.wk.wk hC.wk.wk hBC.wk.wk ms.wk.wk
          ((congrAp2 remF (congrPw (.eqRefl _) e2.eqSymm) (.eqRefl _)).eqTrans (m2.wk.wk.eqTrans
            (congrAp2 remF (congrPw (.eqRefl _) e2) (.eqRefl _))))
      have ht : C' ⊢[PRAAx] monus (two * N) (rem (phi (pw A N + pw B N)) (two * N)) ≐ succ (pred (monus (two * N) (rem (phi (pw A N + pw B N)) (two * N)))) :=
        AnalyticNumberTheory.Primes.eq_succ_pred (y := monus (two * N) (succ (rem (phi (pw A N + pw B N)) (two * N))))
          (by apply deriveNat; ipra_simps; linear_combination f2 - f3)
      have htn : C' ⊢[PRAAx] le (monus (two * N) (rem (phi (pw A N + pw B N)) (two * N))) N :=
        le_of_eq_add (d := succ (monus (rem (phi (pw A N + pw B N)) (two * N)) (succ N))) (by apply deriveNat; ipra_simps; linear_combination f1 + f3)
      exact small_not_mem _ hA.wk.wk hB.wk.wk hne.wk.wk ht htn mt

/-- `thm:plus-power`: for distinct `a, b ≥ 1` and `n ≥ 1`, `n ∣ φ(aⁿ + bⁿ)`. -/
theorem plus_power {a b N : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hne : Γ ⊢[PRAAx] neg (a ≐ b)) :
    Γ ⊢[PRAAx] dvd N (phi (pw a N + pw b N)) := by
  have hg := gcd_pos (B := b) ha
  have dg := gcd_dvd' (b := b) ha
  have eA := eq_of_dvd' hg (Prf.andE₁ dg)
  have eB := eq_of_dvd' hg (Prf.andE₂ dg)
  have hA := pos_of_eq_mul ha eA
  have hB := pos_of_eq_mul hb eB
  have hAB := coprime_quotients (c := b) ha
  have hne' : Γ ⊢[PRAAx] neg (quo a (gcd a b) ≐ quo b (gcd a b)) :=
    .impI (.impE hne.wk (eA.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans eB.wk.eqSymm)))
  have t := two_n_dvd hA hB hN hAB hne'
  have pB := natEq (pw_pos' hB N)
  have hC : Γ ⊢[PRAAx] (pw (quo a (gcd a b)) N + pw (quo b (gcd a b)) N) ≐ succ (pred (pw (quo a (gcd a b)) N + pw (quo b (gcd a b)) N)) :=
    AnalyticNumberTheory.Primes.eq_succ_pred (y := pw (quo a (gcd a b)) N + pred (pw (quo b (gcd a b)) N))
      (by apply deriveNat; ipra_simps; linear_combination pB)
  have hφ := phi_pos hC
  have nφ : Γ ⊢[PRAAx] dvd N (phi (pw (quo a (gcd a b)) N + pw (quo b (gcd a b)) N)) := by
    have e := natEq (eq_of_dvd' (AnalyticNumberTheory.Primes.eq_succ_pred (y := succ (two * pred N))
      (by have e := natEq hN; apply deriveNat; ipra_simps; linear_combination 2 * e)) t)
    exact dvd_of_eq' hN (w := two * quo (phi (pw (quo a (gcd a b)) N + pw (quo b (gcd a b)) N)) (two * N)) (by apply deriveNat; ipra_simps; linear_combination e)
  have sum : Γ ⊢[PRAAx] pw a N + pw b N ≐ (pw (quo a (gcd a b)) N + pw (quo b (gcd a b)) N) * pw (gcd a b) N := by
    have x := natEq ((congrPw eA (.eqRefl N)).eqTrans (pw_mul_base _ _ _))
    have y := natEq ((congrPw eB (.eqRefl N)).eqTrans (pw_mul_base _ _ _))
    apply deriveNat; ipra_simps; linear_combination x + y
  have dC := phi_divides_at hC (dvd_of_eq' hC sum)
  exact dvd_trans' hN hφ nφ dC

end LeanProofs.IPRA.AnalyticNumberTheory.PlusPower
