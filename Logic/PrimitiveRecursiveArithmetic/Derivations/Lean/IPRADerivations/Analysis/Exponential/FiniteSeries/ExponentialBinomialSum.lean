import IPRADerivations.Analysis.Exponential.FiniteSeries.BinomialExponentialGap
import IPRADerivations.Analysis.Exponential.ExponentialSeries
import IPRADerivations.Analysis.Gamma.BohrMollerup.BohrMollerupUniqueness
import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Combinatorics.BellTriangle
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination

/-!
# The exponential sums against `(1 + 1/m)^m`, summed

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section "A finite proof that `log e = 1`", `eq:EB`:

`0 ≤ E_m − B_m ≤ (1/(2m)) ∑_{j=2}^m 1/(j − 2)! ≤ 3/(2m)`, `2 ≤ B_m ≤ E_m ≤ 3`,

for `E_m = ∑_{j≤m} 1/j!` and `B_m = (1 + 1/m)^m`. Everything is cleared by `m! m^m`: `m! E_m = en m`
(`Analysis/ExponentialSeries`) and `m^m B_m = (m + 1)^m`. The term-by-term comparison is
`Analysis/BinomialExponentialGap`; this file sums it:

* `en_sum`: `∑_{k≤m} (m)_k = en m`, i.e. `∑_{j≤m} m!/j! = m! E_m` (falling factorials `(m)_k = m!/(m − k)!`);
* `binom_ff`: `m! C(m, k) = (m)_k (m)_{m−k}` for `k ≤ m`;
* `term_gap`: for `k ≤ m`, `2m (m)_k m^m ≤ 2m m! C(m, k) m^k + m^m (m)_{k+2}`, the cleared difference of the
  `(m − k)`-th terms of `E_m` and `B_m` against `(1/(2m)) · 1/(m − k − 2)!`;
* `shifted_ff_sum`: `∑_{k≤m} (m)_{k+2} + 1 + m = en m`, so the summed right side is at most `en m`;
* `eb_lower`: `m! (m + 1)^m ≤ m^m en m`, i.e. `B_m ≤ E_m`;
* `eb_upper`: `2m m^m en m ≤ 2m m! (m + 1)^m + m^m en m`, i.e. `E_m − B_m ≤ E_m/(2m)`, and with
  `en_le` (`E_m ≤ 3`) `E_m − B_m ≤ 3/(2m)` (`eb_upper3`);
* `b_lower`: `2 m^m ≤ (m + 1)^m`, i.e. `B_m ≥ 2` (Bernoulli).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ExponentialBinomialSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.StirlingPowers (ffB ff ff_zero ff_succ ff_zero_above congrFF)
open LeanProofs.IPRA.Combinatorics.FallingFactorial (ff_add ff_fact ff_binom)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (tBody binomial_at)
open LeanProofs.IPRA.Combinatorics.BellTriangle (binom_symm)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.ExponentialSeries (en en_zero en_succ en_upper UpInv)
open LeanProofs.IPRA.Analysis.BinomialExponentialGap (GapInv binomial_exponential_gap)
open LeanProofs.IPRA.Analysis.BohrMollerupUniqueness (bernoulli)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Falling factorial facts -/

theorem ff_one (X : PTm n) : Γ ⊢[PRAAx] ff X (succ zero) ≐ X := by
  have a := natEq (ff_succ (Γ := Γ) X zero)
  have b := natEq (ff_zero (Γ := Γ) X)
  have c := natEq (monus_zero (Γ := Γ) X)
  apply deriveNat; ipra_simps; rw [a, b, c]; ring

theorem succ_monus_one (a : PTm n) : Γ ⊢[PRAAx] monus (succ a) (succ zero) ≐ a :=
  (monus_succ _ _).eqTrans ((congrPred (monus_zero _)).eqTrans (pred_succ a))

/-- `j (j ∸ 1) + j = j²`. -/
theorem mul_pred_add (j : PTm n) : Γ ⊢[PRAAx] j * pred j + j ≐ j * j := by
  refine .orE (lt_or_le zero j) ?_ ?_
  · have e := natEq (eq_add_of_le (Prf.hyp0 : (lt zero j :: Γ) ⊢[PRAAx] lt zero j))
    have p : (lt zero j :: Γ) ⊢[PRAAx] j ≐ succ (pred j) :=
      LeanProofs.IPRA.Foundations.MixedRadix.pos_of_lt Prf.hyp0
    have q := natEq p
    apply deriveNat; ipra_simps
    linear_combination (-𝔟 j) * q
  · have h : (le j zero :: Γ) ⊢[PRAAx] j ≐ zero := (monus_zero j).eqSymm.eqTrans Prf.hyp0
    have q := natEq h
    apply deriveNat; ipra_simps; rw [q]; ring

/-- `m! C(m, k) = (m)_k (m)_{m−k}` for `k ≤ m`. -/
theorem binom_ff {m k : PTm n} (h : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] fact m * binom m k ≐ ff m k * ff m (monus m k) := by
  have hj : Γ ⊢[PRAAx] le (monus m k) m := by
    have e := natEq (eq_add_of_le h)
    ipra_le 𝔟 k using linear_combination e
  have f₁ := natEq (ff_fact h)
  have f₂ := natEq (ff_binom hj)
  have s := natEq (binom_symm h)
  apply deriveNat; ipra_simps
  rw [f₂, s]
  linear_combination (-𝔟 (binom m k)) * f₁

/-! ## `∑_{k≤m} (m)_k = en m` -/

/-- `(m)_k` over `(k, m)`. -/
abbrev fB : PTm 2 := ff (var 1) (var 0)

theorem inst2_fB (k m : PTm n) : inst2 fB k m = ff m k := by simp [inst2]

theorem en_base : Γ ⊢[PRAAx] ap2 (sumF fB) (succ zero) (zero : PTm n) ≐ en zero := by
  have s := sum_succ' (Γ := Γ) fB zero zero
  rw [inst2_fB] at s
  have s' := natEq s
  have z := natEq (sum_zero (Γ := Γ) fB (zero : PTm n))
  have f := natEq (ff_zero (Γ := Γ) (zero : PTm n))
  have e := natEq (en_zero (Γ := Γ) (n := n))
  apply deriveNat; ipra_simps; rw [s', z, f, e]; ring

theorem en_step {m : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF fB) (succ m) m ≐ en m) :
    Γ ⊢[PRAAx] ap2 (sumF fB) (succ (succ m)) (succ m) ≐ en (succ m) := by
  have b : Γ ⊢[PRAAx] succ (succ m) ≐ succ zero + succ m := by ipra_ring
  have s := (congrAp2 (sumF fB) b (.eqRefl (succ m))).eqTrans (sum_split fB (succ zero) (succ m) (succ m))
  have s₁' := sum_succ' (Γ := Γ) fB zero (succ m)
  rw [inst2_fB] at s₁'
  have s₂ := sum_scale (Γ := Γ) (offB fB) fB (succ m) (succ m) m (pairT (succ zero) (succ m)) (.allI (.impI (by
    have e₁ : Syn.shift (pairT (succ zero) (succ m)) = pairT (succ zero) (succ (Syn.shift m)) := by simp [Syn.shift]
    have e₂ : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
    rw [e₁, e₂, inst2_offB, inst2_fB, inst2_fB]
    refine (congrFF (snd_pair _ _) (congrAdd (fst_pair _ _) (.eqRefl _))).eqTrans ((ff_add _ _ _).eqTrans ?_)
    exact congrMul (ff_one _) (congrFF (succ_monus_one _) (.eqRefl _)))))
  have e := natEq s
  have e₁ := natEq s₁'
  have z := natEq (sum_zero (Γ := Γ) fB (succ m))
  have f := natEq (ff_zero (Γ := Γ) (succ m))
  have e₂ := natEq s₂
  have i := natEq ih
  have es := natEq (en_succ (Γ := Γ) m)
  apply deriveNat; ipra_simps
  rw [e, e₁, z, f, e₂, i, es]; ring

private abbrev enSumF : Fm PTm 1 := ap2 (sumF fB) (succ (var 0)) (var 0) ≐ en (var 0)

private theorem en_sum₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] enSumF := by
  refine ind _ trivial ?_ ?_
  · simp only [enSumF, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact en_base
  · simp only [enSumF, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact en_step Prf.hyp0

/-- `∑_{k≤m} (m)_k = en m = m! E_m`. -/
theorem en_sum (m : PTm n) : Γ ⊢[PRAAx] ap2 (sumF fB) (succ m) m ≐ en m := by
  have h := inst (Γ := Γ) en_sum₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-! ## The term-by-term gap -/

/-- `2m (m)_k m^m ≤ 2m m! C(m, k) m^k + m^m (m)_{k+2}` for `k ≤ m`. -/
theorem term_gap {m k : PTm n} (h : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] le (two * m * (ff m k * pw m m))
      (two * m * (fact m * (binom m k * pw m k)) + pw m m * ff m (succ (succ k))) := by
  have em := eq_add_of_le h
  have e₁ := natEq ((Combinatorics.BinomialTheorem.congrPw (.eqRefl m) em).eqTrans (pw_add (Γ := Γ) m k (monus m k)))
  have e₂ := natEq (binom_ff h)
  have f₁ := natEq (ff_succ (Γ := Γ) m (succ k))
  have f₀ := natEq (ff_succ (Γ := Γ) m k)
  have e₄ := natEq (monus_succ (Γ := Γ) m k)
  have e₅ := natEq (mul_pred_add (Γ := Γ) (monus m k))
  have g := binomial_exponential_gap (Γ := Γ) m (monus m k)
  ipra_le 𝔟 (ff m k) * 𝔟 (pw m k) * sl g using
    linear_combination (𝔟 (ff m (succ (succ k))) - 2 * 𝔟 m * 𝔟 (ff m k)) * e₁ +
      2 * 𝔟 m * 𝔟 (pw m k) * e₂ + 𝔟 (pw m k) * 𝔟 (pw m (monus m k)) * f₁ +
      𝔟 (pw m k) * 𝔟 (pw m (monus m k)) * 𝔟 (monus m (succ k)) * f₀ +
      𝔟 (pw m k) * 𝔟 (pw m (monus m k)) * 𝔟 (ff m k) * 𝔟 (monus m k) * e₄ +
      𝔟 (ff m k) * 𝔟 (pw m k) * 𝔟 (pw m (monus m k)) * e₅

/-! ## The shifted falling factorials -/

/-- `(m)_{k+2}` over `(k, m)`. -/
abbrev f2B : PTm 2 := ff (var 1) (succ (succ (var 0)))

theorem inst2_f2B (k m : PTm n) : inst2 f2B k m = ff m (succ (succ k)) := by simp [inst2]

/-- `∑_{k≤m} (m)_{k+2} + 1 + m = en m`. -/
theorem shifted_ff_sum (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF f2B) (succ m) m + succ zero + m ≐ en m := by
  have cv := natEq (sum_congr_bounded (Γ := Γ) (offB fB) f2B (pairT (succ (succ zero)) m) m (succ m)
    (.allI (.impI (by
      have e₁ : Syn.shift (pairT (succ (succ zero)) m) = pairT (succ (succ zero)) (Syn.shift m) := by
        simp [Syn.shift]
      rw [e₁, inst2_offB, inst2_fB, inst2_f2B]
      exact congrFF (snd_pair _ _) ((congrAdd (fst_pair _ _) (.eqRefl _)).eqTrans
        (by ipra_ring))))))
  have t₁' := sum_succ' (Γ := Γ) fB (succ zero) m
  rw [inst2_fB] at t₁'
  have t₀' := sum_succ' (Γ := Γ) fB zero m
  rw [inst2_fB] at t₀'
  have t₁ := natEq t₁'
  have t₀ := natEq t₀'
  have b : Γ ⊢[PRAAx] succ (succ zero) + succ m ≐ succ (succ (succ m)) := by ipra_ring
  have u₂' := sum_succ' (Γ := Γ) fB (succ (succ m)) m
  rw [inst2_fB] at u₂'
  have u₁' := sum_succ' (Γ := Γ) fB (succ m) m
  rw [inst2_fB] at u₁'
  have u₂ := natEq u₂'
  have u₁ := natEq u₁'
  have h₁ : Γ ⊢[PRAAx] lt m (succ m) := by ipra_le 0
  have h₂ : Γ ⊢[PRAAx] lt m (succ (succ m)) := by ipra_le 1
  ipra_lc natEq (en_sum (Γ := Γ) m) + natEq (ff_zero_above h₁) + u₁ + natEq (ff_zero_above h₂) + u₂ +
    natEq (congrAp2 (Γ := Γ) (sumF fB) b (.eqRefl m)) - natEq (ff_one (Γ := Γ) m) - natEq (ff_zero (Γ := Γ) m) -
    natEq (sum_zero (Γ := Γ) fB m) - t₀ - t₁ - natEq (sum_split (Γ := Γ) fB (succ (succ zero)) (succ m) m) - cv

/-! ## Summing -/

/-- `∑_{k≤m} m! C(m, k) m^k = m! (m + 1)^m`. -/
theorem sum_B (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0)))) (succ m) m ≐
      fact m * pw (succ m) m := by
  refine (sum_scale _ tBody (succ m) (fact m) (pairT m m) m (.allI (.impI ?_))).eqTrans
    (congrMul (.eqRefl _) (binomial_at m m))
  have e₁ : Syn.shift (pairT m m) = pairT (Syn.shift m) (Syn.shift m) := by simp [Syn.shift]
  have e₂ : Syn.shift (fact m) = fact (Syn.shift m) := by simp [Syn.shift]
  rw [e₁, e₂]
  have c : inst2 tBody (var 0) (pairT (Syn.shift m) (Syn.shift m)) =
      binom (fstT (pairT (Syn.shift m) (Syn.shift m))) (var 0) *
        pw (sndT (pairT (Syn.shift m) (Syn.shift m))) (var 0) := by
    simp [inst2]
  have d : inst2 (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))) (var 0) (Syn.shift m) =
      fact (Syn.shift m) * (binom (Syn.shift m) (var 0) * pw (Syn.shift m) (var 0)) := by simp [inst2]
  rw [c, d]
  exact congrMul (.eqRefl _) (congrMul (Combinatorics.BinomialTheorem.congrBinom (fst_pair _ _) (.eqRefl _)).eqSymm
    (Combinatorics.BinomialTheorem.congrPw (snd_pair _ _) (.eqRefl _)).eqSymm)

/-- `∑_{k≤m} (m)_k m^m = m^m en m`. -/
theorem sum_E (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (ff (var 1) (var 0) * pw (var 1) (var 1))) (succ m) m ≐ pw m m * en m := by
  refine (sum_scale _ fB (succ m) (pw m m) m m (.allI (.impI ?_))).eqTrans
    (congrMul (.eqRefl _) (en_sum m))
  have e₂ : Syn.shift (pw m m) = pw (Syn.shift m) (Syn.shift m) := by simp [Syn.shift]
  rw [e₂, inst2_fB]
  have d : inst2 (ff (var 1) (var 0) * pw (var 1) (var 1)) (var 0) (Syn.shift m) =
      ff (Syn.shift m) (var 0) * pw (Syn.shift m) (Syn.shift m) := by simp [inst2]
  rw [d]
  exact mul_comm _ _

/-- `∑_{k≤m} m^m (m)_{k+2} = m^m ∑_{k≤m} (m)_{k+2}`. -/
theorem sum_F (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (pw (var 1) (var 1) * ff (var 1) (succ (succ (var 0))))) (succ m) m ≐
      pw m m * ap2 (sumF f2B) (succ m) m := by
  refine sum_scale _ f2B (succ m) (pw m m) m m (.allI (.impI ?_))
  have e₂ : Syn.shift (pw m m) = pw (Syn.shift m) (Syn.shift m) := by simp [Syn.shift]
  rw [e₂, inst2_f2B]
  have d : inst2 (pw (var 1) (var 1) * ff (var 1) (succ (succ (var 0)))) (var 0) (Syn.shift m) =
      pw (Syn.shift m) (Syn.shift m) * ff (Syn.shift m) (succ (succ (var 0))) := by simp [inst2]
  rw [d]
  exact .eqRefl _

theorem le_of_lt_succ_shift {m : PTm n} :
    (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift m) := by
  have h₀ : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (succ (Syn.shift m)) := by
    have e : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
    rw [← e]; exact Prf.hyp0
  ipra_le sl h₀

/-- `B_m ≤ E_m`: `m! (m + 1)^m ≤ m^m en m`. -/
theorem eb_lower (m : PTm n) : Γ ⊢[PRAAx] le (fact m * pw (succ m) m) (pw m m * en m) := by
  have s := sum_le (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0)))
    (ff (var 1) (var 0) * pw (var 1) (var 1)) m (succ m) (.allI (.impI (by
      have hk := le_of_lt_succ_shift (Γ := Γ) (m := m)
      have d₁ : inst2 (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))) (var 0) (Syn.shift m) =
          fact (Syn.shift m) * (binom (Syn.shift m) (var 0) * pw (Syn.shift m) (var 0)) := by simp [inst2]
      have d₂ : inst2 (ff (var 1) (var 0) * pw (var 1) (var 1)) (var 0) (Syn.shift m) =
          ff (Syn.shift m) (var 0) * pw (Syn.shift m) (Syn.shift m) := by simp [inst2]
      rw [d₁, d₂]
      have em := eq_add_of_le hk
      have e₁ := natEq ((Combinatorics.BinomialTheorem.congrPw (.eqRefl _) em).eqTrans
        (pw_add (Syn.shift m) (var 0) (monus (Syn.shift m) (var 0))))
      have e₂ := natEq (binom_ff hk)
      have g := LeanProofs.IPRA.Analysis.BinomialExponentialGap.ff_le_pw
        (Γ := lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) (Syn.shift m) (monus (Syn.shift m) (var 0))
      ipra_le 𝔟 (ff (Syn.shift m) (var 0)) * 𝔟 (pw (Syn.shift m) (var 0)) * sl g using
        linear_combination 𝔟 (ff (Syn.shift m) (var 0)) * e₁ - 𝔟 (pw (Syn.shift m) (var 0)) * e₂)))
  exact le_congr (sum_B m) (sum_E m) s

/-- `E_m − B_m ≤ E_m/(2m)`: `2m m^m en m ≤ 2m m! (m + 1)^m + m^m en m`. -/
theorem eb_upper (m : PTm n) :
    Γ ⊢[PRAAx] le (two * m * (pw m m * en m)) (two * m * (fact m * pw (succ m) m) + pw m m * en m) := by
  have s := sum_le (two * var 1 * (ff (var 1) (var 0) * pw (var 1) (var 1)))
    (two * var 1 * (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))) +
      pw (var 1) (var 1) * ff (var 1) (succ (succ (var 0)))) m (succ m) (.allI (.impI (by
      have hk := le_of_lt_succ_shift (Γ := Γ) (m := m)
      have d₁ : inst2 (two * var 1 * (ff (var 1) (var 0) * pw (var 1) (var 1))) (var 0) (Syn.shift m) =
          two * Syn.shift m * (ff (Syn.shift m) (var 0) * pw (Syn.shift m) (Syn.shift m)) := by simp [inst2]
      have d₂ : inst2 (two * var 1 * (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))) +
          pw (var 1) (var 1) * ff (var 1) (succ (succ (var 0)))) (var 0) (Syn.shift m) =
          two * Syn.shift m * (fact (Syn.shift m) * (binom (Syn.shift m) (var 0) * pw (Syn.shift m) (var 0))) +
            pw (Syn.shift m) (Syn.shift m) * ff (Syn.shift m) (succ (succ (var 0))) := by simp [inst2]
      rw [d₁, d₂]
      exact term_gap hk)))
  have sl₁ := natEq (sum_scale (Γ := Γ) (two * var 1 * (ff (var 1) (var 0) * pw (var 1) (var 1)))
    (ff (var 1) (var 0) * pw (var 1) (var 1)) (succ m) (two * m) m m (.allI (.impI (by
      have e : Syn.shift (two * m) = two * Syn.shift m := by simp [Syn.shift]
      rw [e]
      have d₁ : inst2 (two * var 1 * (ff (var 1) (var 0) * pw (var 1) (var 1))) (var 0) (Syn.shift m) =
          two * Syn.shift m * (ff (Syn.shift m) (var 0) * pw (Syn.shift m) (Syn.shift m)) := by simp [inst2]
      have d₂ : inst2 (ff (var 1) (var 0) * pw (var 1) (var 1)) (var 0) (Syn.shift m) =
          ff (Syn.shift m) (var 0) * pw (Syn.shift m) (Syn.shift m) := by simp [inst2]
      rw [d₁, d₂]; exact .eqRefl _))))
  have sa : Γ ⊢[PRAAx] ap2 (sumF (two * var 1 * (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))) +
      pw (var 1) (var 1) * ff (var 1) (succ (succ (var 0))))) (succ m) m ≐
      ap2 (sumF (two * var 1 * (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))))) (succ m) m +
        ap2 (sumF (pw (var 1) (var 1) * ff (var 1) (succ (succ (var 0))))) (succ m) m := sum_add _ _ _ _
  have sl₂ := natEq (sum_scale (Γ := Γ) (two * var 1 * (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))))
    (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))) (succ m) (two * m) m m (.allI (.impI (by
      have e : Syn.shift (two * m) = two * Syn.shift m := by simp [Syn.shift]
      rw [e]
      have d₁ : inst2 (two * var 1 * (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0)))) (var 0)
          (Syn.shift m) =
          two * Syn.shift m * (fact (Syn.shift m) * (binom (Syn.shift m) (var 0) * pw (Syn.shift m) (var 0))) := by
        simp [inst2]
      have d₂ : inst2 (fact (var 1) * (binom (var 1) (var 0) * pw (var 1) (var 0))) (var 0) (Syn.shift m) =
          fact (Syn.shift m) * (binom (Syn.shift m) (var 0) * pw (Syn.shift m) (var 0)) := by simp [inst2]
      rw [d₁, d₂]; exact .eqRefl _))))
  have sE := natEq (sum_E (Γ := Γ) m)
  have sB := natEq (sum_B (Γ := Γ) m)
  have sF := natEq (sum_F (Γ := Γ) m)
  have sh := natEq (shifted_ff_sum (Γ := Γ) m)
  have sa' := natEq sa
  ipra_le sl s + 𝔟 (pw m m) * (1 + 𝔟 m) using
    linear_combination sl₁ - sa' - sl₂ - sF + 2 * 𝔟 m * sE - 2 * 𝔟 m * sB - 𝔟 (pw m m) * sh

/-- `E_m ≤ 3`: `en m ≤ 3 m!` for `m ≥ 1`. -/
theorem en_le (m₀ : PTm n) : Γ ⊢[PRAAx] le (en (succ m₀)) (num 3 * fact (succ m₀)) := by
  have u := en_upper (Γ := Γ) m₀
  refine mul_le_cancel (d' := m₀) ?_
  have u' : Γ ⊢[PRAAx] le (succ m₀ * en (succ m₀) + succ zero) (num 3 * (succ m₀ * fact (succ m₀))) := u
  ipra_le sl u' + 1

/-- `eq:EB`: `E_m − B_m ≤ 3/(2m)`: `2m m^m en m ≤ 2m m! (m + 1)^m + 3 m! m^m` for `m ≥ 1`. -/
theorem eb_upper3 (m₀ : PTm n) :
    Γ ⊢[PRAAx] le (two * succ m₀ * (pw (succ m₀) (succ m₀) * en (succ m₀)))
      (two * succ m₀ * (fact (succ m₀) * pw (succ (succ m₀)) (succ m₀)) +
        num 3 * (fact (succ m₀) * pw (succ m₀) (succ m₀))) := by
  have a := eb_upper (Γ := Γ) (succ m₀)
  have b := en_le (Γ := Γ) m₀
  ipra_le sl a + 𝔟 (pw (succ m₀) (succ m₀)) * sl b

/-- `B_m ≥ 2`: `2 m^m ≤ (m + 1)^m` for `m ≥ 1`. -/
theorem b_lower (m₀ : PTm n) :
    Γ ⊢[PRAAx] le (two * pw (succ m₀) (succ m₀)) (pw (succ (succ m₀)) (succ m₀)) := by
  have b := bernoulli (Γ := Γ) (succ m₀) one m₀
  have c := le_congr (.eqRefl _) (Combinatorics.BinomialTheorem.congrPw
    (by ipra_ring : Γ ⊢[PRAAx] succ m₀ + one ≐ succ (succ m₀)) (.eqRefl _)) b
  have p := natEq (pw_succ (Γ := Γ) (succ m₀) m₀)
  ipra_le sl c using rw [p]; ring

end LeanProofs.IPRA.Analysis.ExponentialBinomialSum
