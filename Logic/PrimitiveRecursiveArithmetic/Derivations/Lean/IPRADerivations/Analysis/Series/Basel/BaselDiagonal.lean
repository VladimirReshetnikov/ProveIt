import IPRADerivations.AnalyticNumberTheory.Primes
import IPRADerivations.AnalyticNumberTheory.GcdFiber
import IPRADerivations.AnalyticNumberTheory.PhiDouble
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.SumReflect
import IPRADerivations.Combinatorics.Bell
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination

/-!
# The finite convolution identity of the Basel packet

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Lemma `lem:diagonal`, identity `(eq:diagonal)`:
for `d ≥ 1`, `∑_{i<d} 1/((2i+1)(2d−2i−1)) = H_d/d` with `H_d = ∑_{i<d} 1/(2i+1)`.

Denominators are cleared by `F = (2d)!`, which every odd `2i + 1 < 2d` divides exactly. With
`d = m + 1` and `G_i = F/(2i+1)`, so that `F²/((2i+1)(2d−2i−1)) = G_i G_{m−i}` and `F/(2i+1) = G_i`,
the identity reads `d ∑_{i ≤ m} G_i G_{m−i} = F ∑_{i ≤ m} G_i` (`diagonal`).

* `pair_pt`: `a G b G' = F G' + F G`-style pointwise law: if `a ∣ F`, `b ∣ F` and `a + b = k`, then
  `k (F/a)(F/b) = F (F/a + F/b)` (the packet's partial fraction
  `1/(ab) = (1/(a+b)) (1/a + 1/b)`);
* `refl_pt`: reflecting `G_i` gives `G_{m−i}`;
* `diagonal`: sum the pointwise law over `i ≤ m` (`sum_scale`), use the reflection (`sum_reflect`) to see
  that both halves are `∑ G_i`, and cancel the factor `2`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BaselDiagonal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.Bell (monus_le')
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (dvd_fact)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The partial-fraction law with denominators cleared: `a, b ∣ F`, `a + b = k` give
`k (F/a)(F/b) = F (F/a + F/b)`. -/
theorem pair_pt {F a b k : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (da : Γ ⊢[PRAAx] dvd a F) (db : Γ ⊢[PRAAx] dvd b F) (hk : Γ ⊢[PRAAx] a + b ≐ k) :
    Γ ⊢[PRAAx] k * (quo F a * quo F b) ≐ F * (quo F a + quo F b) := by
  ipra_lc -𝔞 (quo F b) * natEq (div_eq (j := F) ha) - 𝔞 (quo F a) * natEq (div_eq (j := F) hb) -
    𝔞 (quo F b) * natEq da - 𝔞 (quo F a) * natEq db - 𝔞 (quo F a) * 𝔞 (quo F b) * natEq hk

/-! ## Bodies; variables `0 = i`, `1 = m`, and `F = (2(m+1))!` -/

/-- `F = (2(m + 1))!`. -/
abbrev FT (m : PTm n) : PTm n := fact (two * succ m)

/-- `G_i = F/(2i + 1)`. -/
abbrev gB : PTm 2 := quo (FT (var 1)) (succ (two * var 0))
/-- `G_{m−i}`. -/
abbrev rB : PTm 2 := quo (FT (var 1)) (succ (two * monus (var 1) (var 0)))
/-- `G_i G_{m−i}`. -/
abbrev convB : PTm 2 := gB * rB
/-- `2(m + 1) G_i G_{m−i}`. -/
abbrev dcB : PTm 2 := (two * succ (var 1)) * convB

theorem inst2_g (i m : PTm n) : inst2 gB i m = quo (FT m) (succ (two * i)) := by simp [inst2]
theorem inst2_r (i m : PTm n) : inst2 rB i m = quo (FT m) (succ (two * monus m i)) := by simp [inst2]
theorem inst2_conv (i m : PTm n) : inst2 convB i m = inst2 gB i m * inst2 rB i m := by simp [inst2]
theorem inst2_dc (i m : PTm n) : inst2 dcB i m = (two * succ m) * inst2 convB i m := by simp [inst2]

theorem shift_FT (m : PTm n) : Syn.shift (FT m) = FT (Syn.shift m) := by simp [Syn.shift]

/-- `2i + 1 ∣ (2(m+1))!` for `i ≤ m`. -/
theorem odd_dvd {i m : PTm n} (h : Γ ⊢[PRAAx] le i m) : Γ ⊢[PRAAx] dvd (succ (two * i)) (FT m) := by
  refine dvd_fact (le_of_eq_add (d := succ (two * monus m i)) ?_)
  ipra_lc 2 * natEq (eq_add_of_le h)

/-- The pointwise law: `2(m+1) G_i G_{m−i} = F (G_i + G_{m−i})` for `i ≤ m`. -/
theorem dc_pt {i m : PTm n} (h : Γ ⊢[PRAAx] le i m) :
    Γ ⊢[PRAAx] inst2 dcB i m ≐ FT m * inst2 (addBody gB rB) i m := by
  rw [inst2_dc, inst2_conv, inst2_addBody, inst2_g, inst2_r]
  refine pair_pt (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm) (odd_dvd h)
    (odd_dvd (monus_le' h)) ?_
  ipra_lc -2 * natEq (eq_add_of_le h)

/-- Reflecting `G_i` gives `G_{m−i}`. -/
theorem refl_pt {i m : PTm n} :
    Γ ⊢[PRAAx] inst2 (rflBody gB) i (pairT (succ m) m) ≐ inst2 rB i m := by
  rw [inst2_rflBody, inst2_r]
  have hk : Γ ⊢[PRAAx] monus (fstT (pairT (succ m) m)) (succ i) ≐ monus m i :=
    (congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans (succ_monus_succ _ _)
  refine (congrInst2 gB hk (snd_pair _ _)).eqTrans ?_
  rw [inst2_g]
  exact .eqRefl _

/-- `lem:diagonal`: `(m + 1) ∑_{i ≤ m} G_i G_{m−i} = F ∑_{i ≤ m} G_i`, where `F = (2(m+1))!` and
`G_i = F/(2i+1)`; that is, `∑_{i<d} 1/((2i+1)(2d−2i−1)) = H_d/d` for `d = m + 1`. -/
theorem diagonal (m : PTm n) :
    Γ ⊢[PRAAx] succ m * ap2 (sumF convB) (succ m) m ≐ FT m * ap2 (sumF gB) (succ m) m := by
  have c : Γ ⊢[PRAAx] ap2 (sumF (rflBody gB)) (succ m) (pairT (succ m) m) ≐ ap2 (sumF rB) (succ m) m := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_succ]
    exact refl_pt
  have s₁ : Γ ⊢[PRAAx] ap2 (sumF dcB) (succ m) m ≐ FT m * ap2 (sumF (addBody gB rB)) (succ m) m := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_FT]
    simp only [Syn.shift, ConciseIPRA.PTm.subst_succ]
    exact dc_pt ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  have s₂ : Γ ⊢[PRAAx] ap2 (sumF dcB) (succ m) m ≐ (two * succ m) * ap2 (sumF convB) (succ m) m := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_dc]
    simp only [Syn.shift, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    exact .eqRefl _
  have c' := natEq c; have e₁ := natEq s₁; have e₂ := natEq s₂
  refine mul_cancel two_pos' ?_
  ipra_lc e₁ - e₂ +
    𝔞 (FT m) * (natEq (sum_add (Γ := Γ) gB rB (succ m) m) - natEq (sum_reflect (Γ := Γ) gB (succ m) m) - c')

end LeanProofs.IPRA.Analysis.BaselDiagonal
