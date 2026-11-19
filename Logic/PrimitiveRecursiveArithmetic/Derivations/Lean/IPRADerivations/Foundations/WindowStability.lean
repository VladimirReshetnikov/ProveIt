import IPRADerivations.Core.Division
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Probability.FiniteLaws
import IPRADerivations.Foundations.FrontierSoundness

/-!
# Finite-window stability: the two selection arguments

Packet: `foundations/ipra_framework`, `paper/sections/05_metastability.tex`, Theorem `thm:rational-window`
("Rational finite-window stability") and Theorem `thm:real-window` ("Represented finite-window
stability"). Values are numerators over a common denominator.

`thm:rational-window`: the integers `r_i = ⌊s_{n_i}/ε⌋` are nondecreasing and bounded, so two adjacent
ones coincide (`Foundations/RiseAlternative`), and then every value of the window lies in one half-open
interval of length `ε`:

* `window_of_nonrise`: if `⌊s_hi/ε⌋ ≤ ⌊s_lo/ε⌋` (a nonrise of the floors at the two endpoints) and
  `s_lo ≤ s_u`, `s_v ≤ s_hi` (monotonicity at the two indices of the window), then `s_v < s_u + ε`.

`thm:real-window`: the start is the index minimizing the rational differences `a_{i+1} − a_i` of the
endpoint observations, and "minimality and finite telescoping give `K Δ ≤ ∑_{i<K} (a_{i+1} − a_i) =
a_K − a_0`". Observations of a monotone sequence need not be monotone, so the differences are shifted by
a slack `c`: `d_i = a_{i+1} + c − a_i`.

* `sum_lower`: `m ≤ f_i` for `i < N` gives `N m ≤ ∑_{i<N} f_i`;
* `telescope_incr`: `d_i + a_i = a_{i+1} + c` for `i < N` gives `∑_{i<N} d_i + a_0 = a_N + N c`;
* `min_gap`: with `Δ = min_{i ≤ K′} d_i` (`K = K′ + 1` differences), `K Δ + a_0 ≤ a_K + K c`.

The candidate starts `n_i`, the choice of `K` and the final margin are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.WindowStability

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.FiniteLaws (Mn mn_le)
open LeanProofs.IPRA.Foundations.FrontierSoundness (shift_succ' le_of_lt_succ')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The rational window -/

/-- `thm:rational-window`: equal floors at the endpoints put the window in one interval of length `ε`. -/
theorem window_of_nonrise {e' slo shi su sv : PTm n}
    (hnr : Γ ⊢[PRAAx] le (quo shi (succ e')) (quo slo (succ e')))
    (h₁ : Γ ⊢[PRAAx] le slo su) (h₂ : Γ ⊢[PRAAx] le sv shi) :
    Γ ⊢[PRAAx] lt sv (su + succ e') := by
  have d₁ := div_mod (Γ := Γ) slo e'
  have d₂ := div_mod (Γ := Γ) shi e'
  have k₁ := natEq (Prf.andE₁ d₁)
  have k₂ := natEq (Prf.andE₁ d₂)
  have hr : Γ ⊢[PRAAx] le (succ (rem shi (succ e'))) (succ e') := Prf.andE₂ d₂
  have g : Γ ⊢[PRAAx] le (succ sv) (su + succ e') := by
    ipra_le sl h₁ + sl h₂ + (𝔟 e' + 1) * sl hnr + 𝔟 (rem slo (succ e')) + sl hr using
      linear_combination k₁ - k₂
  exact g

/-! ## A lower bound for a sum -/

theorem lower_step {f : PTm 2} {k x m : PTm n} (hk : Γ ⊢[PRAAx] le m (inst2 f k x))
    (ih : Γ ⊢[PRAAx] le (k * m) (ap2 (sumF f) k x)) :
    Γ ⊢[PRAAx] le (succ k * m) (ap2 (sumF f) (succ k) x) := by
  have es := natEq (sum_succ' (Γ := Γ) f k x)
  ipra_le sl ih + sl hk using rw [es]; ring

theorem lower_guard {f : PTm 2} {k x m N : PTm n} (hkN : Γ ⊢[PRAAx] le (succ k) N)
    (hk : Γ ⊢[PRAAx] le m (inst2 f k x))
    (ih : Γ ⊢[PRAAx] le k N ⟶ le (k * m) (ap2 (sumF f) k x)) :
    Γ ⊢[PRAAx] le (succ k * m) (ap2 (sumF f) (succ k) x) :=
  lower_step hk (Prf.impE ih (le_trans (le_succ_self k) hkN))

/-- `m ≤ f_i` for `i < N` gives `N m ≤ ∑_{i<N} f_i`. -/
theorem sum_lower {f : PTm 2} {N x m : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (Syn.shift m) (inst2 f (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (N * m) (ap2 (sumF f) N x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (var 0 * Syn.shift m) (ap2 (sumF f) (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have z := natEq (sum_zero (Γ := le zero N :: Γ) f x)
      ipra_le 0 using rw [z]; ring
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (lower_guard Prf.hyp0 (Prf.impE h.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  have a := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact .impE a (le_refl N)

/-! ## Telescoping shifted increments -/

theorem incr_step {a d : PTm 2} {k x c : PTm n}
    (hd : Γ ⊢[PRAAx] inst2 d k x + inst2 a k x ≐ inst2 a (succ k) x + c)
    (ih : Γ ⊢[PRAAx] ap2 (sumF d) k x + inst2 a zero x ≐ inst2 a k x + k * c) :
    Γ ⊢[PRAAx] ap2 (sumF d) (succ k) x + inst2 a zero x ≐ inst2 a (succ k) x + succ k * c := by
  have e₁ := natEq (sum_succ' (Γ := Γ) d k x)
  have e₂ := natEq hd
  have e₃ := natEq ih
  apply deriveNat; ipra_simps
  linear_combination e₁ + e₂ + e₃

theorem incr_guard {a d : PTm 2} {k x c N : PTm n} (hkN : Γ ⊢[PRAAx] le (succ k) N)
    (hd : Γ ⊢[PRAAx] inst2 d k x + inst2 a k x ≐ inst2 a (succ k) x + c)
    (ih : Γ ⊢[PRAAx] le k N ⟶ (ap2 (sumF d) k x + inst2 a zero x ≐ inst2 a k x + k * c)) :
    Γ ⊢[PRAAx] ap2 (sumF d) (succ k) x + inst2 a zero x ≐ inst2 a (succ k) x + succ k * c :=
  incr_step hd (Prf.impE ih (le_trans (le_succ_self k) hkN))

/-- `d_i + a_i = a_{i+1} + c` for `i < N` gives `∑_{i<N} d_i + a_0 = a_N + N c`. -/
theorem telescope_incr {a d : PTm 2} {N x c : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 d (var 0) (Syn.shift x) + inst2 a (var 0) (Syn.shift x) ≐
        inst2 a (succ (var 0)) (Syn.shift x) + Syn.shift c))) :
    Γ ⊢[PRAAx] ap2 (sumF d) N x + inst2 a zero x ≐ inst2 a N x + N * c := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (ap2 (sumF d) (var 0) (Syn.shift x) + inst2 a zero (Syn.shift x) ≐
        inst2 a (var 0) (Syn.shift x) + var 0 * Syn.shift c)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have z := natEq (sum_zero (Γ := le zero N :: Γ) d x)
      apply deriveNat; ipra_simps
      linear_combination z
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      exact .impI (incr_guard Prf.hyp0 (Prf.impE hd.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  have b := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at b
  exact .impE b (le_refl N)

/-! ## The minimal gap -/

/-- `thm:real-window`: for the minimum `Δ` of `K = K′ + 1` shifted differences,
`K Δ + a_0 ≤ a_K + K c`. -/
theorem min_gap {a d : PTm 2} {K' x c : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ K')) ⟶
      (inst2 d (var 0) (Syn.shift x) + inst2 a (var 0) (Syn.shift x) ≐
        inst2 a (succ (var 0)) (Syn.shift x) + Syn.shift c))) :
    Γ ⊢[PRAAx] le (succ K' * Mn d K' x + inst2 a zero x) (inst2 a (succ K') x + succ K' * c) := by
  have hlow : Γ ⊢[PRAAx] le (succ K' * Mn d K' x) (ap2 (sumF d) (succ K') x) := by
    refine sum_lower (.allI (.impI ?_))
    have e : Syn.shift (Mn d K' x) = Mn d (Syn.shift K') (Syn.shift x) := by simp [Syn.shift]
    rw [e, shift_succ']
    exact mn_le d (le_of_lt_succ' Prf.hyp0)
  have e := natEq (telescope_incr hd)
  ipra_le sl hlow using linear_combination -e

end LeanProofs.IPRA.Foundations.WindowStability
