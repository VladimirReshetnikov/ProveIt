import IPRADerivations.Combinatorics.LegendreDigits
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.AnalyticNumberTheory.ValuationMul
import IPRADerivations.Core.CertificateTactics

/-!
# The alternating digit rule modulo `b + 1`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem `el:digits`,
second congruence: `n ≡ ∑_i (−1)^i d_i (mod b + 1)` (the rule for `11` at `b = 10`).

With `Q_j = ⌊n/b^j⌋` and `d_j = Q_j mod b` (`LegendreDigits.qB'`, `dB`), the digit step `Q_j = b Q_{j+1} + d_j`
reads `Q_j + Q_{j+1} = (b + 1) Q_{j+1} + d_j`, and its alternating sum telescopes. The signs are separated by the
parity of the index, so every statement is an equation of natural numbers:

* `evD`, `odD`, `evQ`, `odQ`: the digits `d_j` and the quotients `Q_{j+1}` at even and at odd `j`;
* `compl_par`: `1 ∸ par(K + 1) = par(K)`;
* `step_alg`, `alt_step`, `alt_base`, `alt_telescope`: for every `K`,
  `n + (b + 1) ∑_{j<K, odd} Q_{j+1} + ∑_{j<K, odd} d_j + [K odd] Q_K
     = (b + 1) ∑_{j<K, even} Q_{j+1} + ∑_{j<K, even} d_j + [K even] Q_K`;
* **`alternating_rule`**: for a base `b ≥ 2`,
  `(n + ∑_{j<n, odd} d_j) mod (b + 1) = (∑_{j<n, even} d_j) mod (b + 1)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.DigitAlternating

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB' dB_at qB'_at digit_step quo_small)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The four bodies -/

/-- The digit `d_j` at even `j`; variables `0 = j`, `1 = ⟨b, n⟩`. -/
abbrev evD : PTm 2 := monus one (par (var 0)) * Combinatorics.LegendreDigits.dB
/-- The digit `d_j` at odd `j`. -/
abbrev odD : PTm 2 := par (var 0) * Combinatorics.LegendreDigits.dB
/-- The quotient `Q_{j+1}` at even `j`. -/
abbrev evQ : PTm 2 := monus one (par (var 0)) * qB'
/-- The quotient `Q_{j+1}` at odd `j`. -/
abbrev odQ : PTm 2 := par (var 0) * qB'

theorem evD_at (j p m : PTm n) :
    Γ ⊢[PRAAx] inst2 evD j (pairT p m) ≐ monus one (par j) * rem (quo m (pw p j)) p := by
  have e : inst2 evD j (pairT p m) = monus one (par j) * inst2 Combinatorics.LegendreDigits.dB j (pairT p m) := by simp [inst2]
  rw [e]; exact congrMul (.eqRefl _) (dB_at j p m)

theorem odD_at (j p m : PTm n) :
    Γ ⊢[PRAAx] inst2 odD j (pairT p m) ≐ par j * rem (quo m (pw p j)) p := by
  have e : inst2 odD j (pairT p m) = par j * inst2 Combinatorics.LegendreDigits.dB j (pairT p m) := by simp [inst2]
  rw [e]; exact congrMul (.eqRefl _) (dB_at j p m)

theorem evQ_at (j p m : PTm n) :
    Γ ⊢[PRAAx] inst2 evQ j (pairT p m) ≐ monus one (par j) * quo m (pw p (succ j)) := by
  have e : inst2 evQ j (pairT p m) = monus one (par j) * inst2 qB' j (pairT p m) := by simp [inst2]
  rw [e]; exact congrMul (.eqRefl _) (qB'_at j p m)

theorem odQ_at (j p m : PTm n) :
    Γ ⊢[PRAAx] inst2 odQ j (pairT p m) ≐ par j * quo m (pw p (succ j)) := by
  have e : inst2 odQ j (pairT p m) = par j * inst2 qB' j (pairT p m) := by simp [inst2]
  rw [e]; exact congrMul (.eqRefl _) (qB'_at j p m)

/-! ## Parity -/

/-- `1 ∸ par(K + 1) = par(K)`. -/
theorem compl_par (K : PTm n) : Γ ⊢[PRAAx] monus one (par (succ K)) ≐ par K := by
  refine .orE (par_cases K) ?_ ?_
  · have h0 : ((par K ≐ zero) :: Γ) ⊢[PRAAx] par K ≐ zero := Prf.hyp0
    have s : ((par K ≐ zero) :: Γ) ⊢[PRAAx] par (succ K) ≐ one :=
      (par_succ K).eqTrans ((congrMonus (.eqRefl _) h0).eqTrans monus_one_zero)
    exact ((congrMonus (.eqRefl _) s).eqTrans monus_one_one).eqTrans h0.eqSymm
  · have h1 : ((par K ≐ one) :: Γ) ⊢[PRAAx] par K ≐ one := Prf.hyp0
    have s : ((par K ≐ one) :: Γ) ⊢[PRAAx] par (succ K) ≐ zero :=
      (par_succ K).eqTrans ((congrMonus (.eqRefl _) h1).eqTrans monus_one_one)
    exact ((congrMonus (.eqRefl _) s).eqTrans monus_one_zero).eqTrans h1.eqSymm

/-! ## The invariant -/

/-- The step of the invariant, with all quantities abstract. -/
theorem step_alg {m p Oq Od Eq Ed Q Q' d π c π' c' Oq' Od' Eq' Ed' : PTm n}
    (ih : Γ ⊢[PRAAx] m + succ p * Oq + Od + π * Q ≐ succ p * Eq + Ed + c * Q)
    (ds : Γ ⊢[PRAAx] Q ≐ p * Q' + d)
    (so : Γ ⊢[PRAAx] Oq' ≐ Oq + π * Q') (sd : Γ ⊢[PRAAx] Od' ≐ Od + π * d)
    (se : Γ ⊢[PRAAx] Eq' ≐ Eq + c * Q') (sed : Γ ⊢[PRAAx] Ed' ≐ Ed + c * d)
    (pc : Γ ⊢[PRAAx] π' ≐ c) (cp : Γ ⊢[PRAAx] c' ≐ π) :
    Γ ⊢[PRAAx] m + succ p * Oq' + Od' + π' * Q' ≐ succ p * Eq' + Ed' + c' * Q' := by
  ipra_lc natEq ih + (𝔞 p + 1) * natEq so + natEq sd - (𝔞 p + 1) * natEq se - natEq sed + 𝔞 Q' * natEq pc -
    𝔞 Q' * natEq cp - (𝔞 π - 𝔞 c) * natEq ds

/-- The invariant at `K + 1` from the invariant at `K`. -/
theorem alt_step {p m K : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (ih : Γ ⊢[PRAAx] m + succ p * ap2 (sumF odQ) K (pairT p m) + ap2 (sumF odD) K (pairT p m) +
        par K * quo m (pw p K) ≐
      succ p * ap2 (sumF evQ) K (pairT p m) + ap2 (sumF evD) K (pairT p m) +
        monus one (par K) * quo m (pw p K)) :
    Γ ⊢[PRAAx] m + succ p * ap2 (sumF odQ) (succ K) (pairT p m) + ap2 (sumF odD) (succ K) (pairT p m) +
        par (succ K) * quo m (pw p (succ K)) ≐
      succ p * ap2 (sumF evQ) (succ K) (pairT p m) + ap2 (sumF evD) (succ K) (pairT p m) +
        monus one (par (succ K)) * quo m (pw p (succ K)) :=
  step_alg ih (digit_step hp m K)
    ((sum_succ' odQ K (pairT p m)).eqTrans (congrAdd (.eqRefl _) (odQ_at K p m)))
    ((sum_succ' odD K (pairT p m)).eqTrans (congrAdd (.eqRefl _) (odD_at K p m)))
    ((sum_succ' evQ K (pairT p m)).eqTrans (congrAdd (.eqRefl _) (evQ_at K p m)))
    ((sum_succ' evD K (pairT p m)).eqTrans (congrAdd (.eqRefl _) (evD_at K p m)))
    (par_succ K) (compl_par K)

theorem base_alg {m p Oq Od Eq Ed π c Q : PTm n} (z1 : Γ ⊢[PRAAx] Oq ≐ zero) (z2 : Γ ⊢[PRAAx] Od ≐ zero)
    (z3 : Γ ⊢[PRAAx] Eq ≐ zero) (z4 : Γ ⊢[PRAAx] Ed ≐ zero) (pz : Γ ⊢[PRAAx] π ≐ zero)
    (c1 : Γ ⊢[PRAAx] c ≐ one) (q0 : Γ ⊢[PRAAx] Q ≐ m) :
    Γ ⊢[PRAAx] m + succ p * Oq + Od + π * Q ≐ succ p * Eq + Ed + c * Q := by
  ipra_lc (𝔞 p + 1) * natEq z1 + natEq z2 + 𝔞 Q * natEq pz - (𝔞 p + 1) * natEq z3 - natEq z4 - 𝔞 Q * natEq c1 -
    natEq q0

/-- The invariant at `K = 0`. -/
theorem alt_base (p m : PTm n) :
    Γ ⊢[PRAAx] m + succ p * ap2 (sumF odQ) zero (pairT p m) + ap2 (sumF odD) zero (pairT p m) +
        par zero * quo m (pw p zero) ≐
      succ p * ap2 (sumF evQ) zero (pairT p m) + ap2 (sumF evD) zero (pairT p m) +
        monus one (par zero) * quo m (pw p zero) :=
  base_alg (sum_zero _ _) (sum_zero _ _) (sum_zero _ _) (sum_zero _ _) par_zero
    ((congrMonus (.eqRefl _) par_zero).eqTrans monus_one_zero)
    ((congrAp2 quoF (.eqRefl m) (pw_zero p)).eqTrans (AnalyticNumberTheory.RSA.quo_one m))

/-- Variables: `0 = K`, `1 = b`, `2 = n`. -/
abbrev altF : Fm PTm 3 :=
  (var 1 ≐ succ (pred (var 1))) ⟶
    (var 2 + succ (var 1) * ap2 (sumF odQ) (var 0) (pairT (var 1) (var 2)) +
        ap2 (sumF odD) (var 0) (pairT (var 1) (var 2)) + par (var 0) * quo (var 2) (pw (var 1) (var 0)) ≐
      succ (var 1) * ap2 (sumF evQ) (var 0) (pairT (var 1) (var 2)) +
        ap2 (sumF evD) (var 0) (pairT (var 1) (var 2)) +
        monus one (par (var 0)) * quo (var 2) (pw (var 1) (var 0)))

theorem alt_open : ([] : List (Fm PTm 3)) ⊢[PRAAx] altF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_ap1, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_monus, PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (alt_base (var 0) (var 1))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_ap1, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_monus, PTm.subst_pred, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (alt_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- The alternating telescope at every `K`. -/
theorem alt_telescope {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (K m : PTm n) :
    Γ ⊢[PRAAx] m + succ p * ap2 (sumF odQ) K (pairT p m) + ap2 (sumF odD) K (pairT p m) +
        par K * quo m (pw p K) ≐
      succ p * ap2 (sumF evQ) K (pairT p m) + ap2 (sumF evD) K (pairT p m) +
        monus one (par K) * quo m (pw p K) := by
  have h := inst (Γ := Γ) alt_open (![K, p, m] : Fin 3 → PTm n)
  simp at h
  exact .impE h hp

/-! ## The rule -/

theorem fin_alg {m S Oq Od Eq Ed π c Q : PTm n}
    (t : Γ ⊢[PRAAx] m + S * Oq + Od + π * Q ≐ S * Eq + Ed + c * Q) (z : Γ ⊢[PRAAx] Q ≐ zero) :
    Γ ⊢[PRAAx] S * Oq + (m + Od) ≐ S * Eq + Ed := by
  ipra_lc natEq t - (𝔞 π - 𝔞 c) * natEq z

/-- **The alternating rule**: for a base `b ≥ 2`,
`(n + ∑_{j odd} d_j) mod (b + 1) = (∑_{j even} d_j) mod (b + 1)`. -/
theorem alternating_rule {b : PTm n} (hb : Γ ⊢[PRAAx] le two b) (m : PTm n) :
    Γ ⊢[PRAAx] rem (m + ap2 (sumF odD) m (pairT b m)) (succ b) ≐ rem (ap2 (sumF evD) m (pairT b m)) (succ b) := by
  have pos := p_pos hb
  have t := alt_telescope pos m m
  have z := quo_small (pw_pos' pos m) (lt_pw hb m)
  have e := fin_alg t z
  have hS : Γ ⊢[PRAAx] succ b ≐ succ (pred (succ b)) := congrSucc (pred_succ _).eqSymm
  exact (rem_add_mul hS _ _).eqSymm.eqTrans ((congrAp2 remF e (.eqRefl _)).eqTrans (rem_add_mul hS _ _))

end LeanProofs.IPRA.DiophantineNumberTheory.DigitAlternating
