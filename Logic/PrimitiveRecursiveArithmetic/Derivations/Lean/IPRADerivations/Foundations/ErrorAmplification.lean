import IPRADerivations.DiophantineNumberTheory.AperyMultibound
import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Core.OrderCertificates

/-!
# Integer error amplification for randomized algorithms

Packet: `foundations/ipra_complexity_foundations_2026-11-20`, `tex/extensions.tex`, Theorem `thm:amplification`:
"Suppose a randomized Boolean algorithm has at most `F` failing seeds out of `M`, where `3F ≤ M`. The majority of
`r = 16(k+1)+1` independent runs has at most a `2^{−k}` fraction of failing combined seeds. The construction and
the integer inequality are provable in iPRA." The proof: with `r = 2m + 1`, the weighted count of seed tuples
gives `2^{m+1} B ≤ (M + F)^{2m+1}` for the number `B` of tuples with a failing majority; "since
`3(M + F) ≤ 4M`, `3 · 9^m B ≤ 2 · 8^m M^{2m+1}`", and "`2 · 8^8 = 33554432 < 43046721 = 9^8` gives, for
`m = 8(k + 1)`, `2^{k+1} 8^m < 9^m`. Combining the inequalities yields `2^k B ≤ M^r`."

The integer part, with all quantities object terms (`M, F, B, k, m` arbitrary; powers `pw`):

* `nine_eight`: `3 · 9^m B ≤ 2 · 8^m M^{2m+1}` from `3F ≤ M` and `2^{m+1} B ≤ (M + F)^{2m+1}`, written with
  `9^m = (3^m)²`, `8^m = (2^m)³` (multiplying by `3^{2m+1}`, `(3(M+F))^r ≤ (4M)^r`, cancelling `2^{m+1}`);
* `window`: `2^{k+1} (2^m)³ ≤ (3^m)²` for `m = 8(k + 1)`, from `2 · 256³ ≤ 6561²` raised to the power `k + 1`;
* `amplification`: `3 · 2^k B ≤ M^{2m+1}`, the asserted `B ≤ 2^{−k} M^r` with a spare factor `3`; and
  `amplification_window` at `m = 8(k + 1)`, `r = 16(k + 1) + 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ErrorAmplification

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw pw_num)
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (cancel_pos one_le_pw_of)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `pw a (2m + 1) = (pw a m)² a`. -/
theorem pw_odd (a m : PTm n) : Γ ⊢[PRAAx] pw a (succ (m + m)) ≐ pw a m * pw a m * a :=
  (pw_succ _ _).eqTrans (congrMul (pw_add _ _ _) (.eqRefl _))

/-- `3 · 9^m B ≤ 2 · 8^m M^{2m+1}`. -/
theorem nine_eight {M F B m : PTm n} (hF : Γ ⊢[PRAAx] le (num 3 * F) M)
    (hB : Γ ⊢[PRAAx] le (pw (num 2) (succ m) * B) (pw (M + F) (succ (m + m)))) :
    Γ ⊢[PRAAx] le (num 3 * (pw (num 3) m * pw (num 3) m) * B)
      (num 2 * (pw (num 2) m * pw (num 2) m * pw (num 2) m) * (pw M m * pw M m * M)) := by
  have h34 : Γ ⊢[PRAAx] le (num 3 * (M + F)) (num 4 * M) := by ipra_le sl hF
  have Y := pw_le_pw (succ (m + m)) h34
  have a := natEq (mul_pw (Γ := Γ) (num 3) (M + F) (succ (m + m)))
  have b := natEq (mul_pw (Γ := Γ) (num 4) M (succ (m + m)))
  have c := natEq ((congrAp2 (Γ := Γ) powF (.eqRefl (succ (m + m))) (show Γ ⊢[PRAAx] num 4 ≐ num 2 * num 2 by
    apply deriveNat; ipra_simps; norm_num)).eqTrans (mul_pw _ _ _))
  have d := natEq (pw_odd (Γ := Γ) (num 2) m)
  have f := natEq (pw_odd (Γ := Γ) (num 3) m)
  have g := natEq (pw_odd (Γ := Γ) M m)
  have h := natEq (pw_succ (Γ := Γ) (num 2) m)
  have hP := one_le_pw_of (Γ := Γ) m (show Γ ⊢[PRAAx] le one (num 2) by ipra_le 1)
  refine cancel_pos (X := num 2 * pw (num 2) m) (by ipra_le 2 * sl hP + 1) ?_
  ipra_le sl Y + 𝔟 (pw (num 3) (succ (m + m))) * sl hB with
    a - b - 𝔟 (pw M (succ (m + m))) * c -
      𝔟 (pw M (succ (m + m))) * (𝔟 (pw (num 2) (succ (m + m))) + 2 * 𝔟 (pw (num 2) m) ^ 2) * d +
      𝔟 B * 𝔟 (pw (num 2) (succ m)) * f - 4 * 𝔟 (pw (num 2) m) ^ 4 * g +
      3 * 𝔟 B * 𝔟 (pw (num 3) m) ^ 2 * h

/-- `2^{k+1} (2^m)³ ≤ (3^m)²` at `m = 8(k + 1)`. -/
theorem window (k : PTm n) :
    Γ ⊢[PRAAx] le (pw (num 2) (succ k) *
        (pw (num 2) (num 8 * succ k) * pw (num 2) (num 8 * succ k) * pw (num 2) (num 8 * succ k)))
      (pw (num 3) (num 8 * succ k) * pw (num 3) (num 8 * succ k)) := by
  have F2 : Γ ⊢[PRAAx] pw (num 256) (succ k) ≐ pw (num 2) (num 8 * succ k) :=
    (congrAp2 powF (.eqRefl (succ k)) (pw_num (Γ := Γ) 2 8).eqSymm).eqTrans (pw_mul _ _ _)
  have F3 : Γ ⊢[PRAAx] pw (num 6561) (succ k) ≐ pw (num 3) (num 8 * succ k) :=
    (congrAp2 powF (.eqRefl (succ k)) (pw_num (Γ := Γ) 3 8).eqSymm).eqTrans (pw_mul _ _ _)
  have h0 : Γ ⊢[PRAAx] le (num 2 * (num 256 * num 256 * num 256)) (num 6561 * num 6561) := by
    ipra_le 9492289
  have H := pw_le_pw (succ k) h0
  have lhsEq : Γ ⊢[PRAAx] pw (num 2 * (num 256 * num 256 * num 256)) (succ k) ≐
      pw (num 2) (succ k) *
        (pw (num 2) (num 8 * succ k) * pw (num 2) (num 8 * succ k) * pw (num 2) (num 8 * succ k)) :=
    (mul_pw _ _ _).eqTrans (congrMul (.eqRefl _)
      ((mul_pw _ _ _).eqTrans (congrMul ((mul_pw _ _ _).eqTrans (congrMul F2 F2)) F2)))
  have rhsEq : Γ ⊢[PRAAx] pw (num 6561 * num 6561) (succ k) ≐
      pw (num 3) (num 8 * succ k) * pw (num 3) (num 8 * succ k) :=
    (mul_pw _ _ _).eqTrans (congrMul F3 F3)
  exact le_congr lhsEq rhsEq H

/-- `3 · 2^k B ≤ M^{2m+1}` from the window inequality `2^{k+1} (2^m)³ ≤ (3^m)²`. -/
theorem amplification {M F B k m : PTm n} (hF : Γ ⊢[PRAAx] le (num 3 * F) M)
    (hB : Γ ⊢[PRAAx] le (pw (num 2) (succ m) * B) (pw (M + F) (succ (m + m))))
    (hm : Γ ⊢[PRAAx] le (pw (num 2) (succ k) * (pw (num 2) m * pw (num 2) m * pw (num 2) m))
      (pw (num 3) m * pw (num 3) m)) :
    Γ ⊢[PRAAx] le (num 3 * pw (num 2) k * B) (pw M (succ (m + m))) := by
  have A := nine_eight hF hB
  have g := natEq (pw_odd (Γ := Γ) M m)
  have e5 := natEq (pw_succ (Γ := Γ) (num 2) k)
  have hP := one_le_pw_of (Γ := Γ) m (show Γ ⊢[PRAAx] le one (num 3) by ipra_le 2)
  refine cancel_pos (X := pw (num 3) m * pw (num 3) m) (by ipra_le sl hP * (𝔟 (pw (num 3) m) + 1)) ?_
  ipra_le 𝔟 (pw (num 2) k) * sl A + 𝔟 (pw M m) ^ 2 * 𝔟 M * sl hm with
    𝔟 (pw (num 3) m) ^ 2 * g + 𝔟 (pw M m) ^ 2 * 𝔟 M * 𝔟 (pw (num 2) m) ^ 3 * e5

/-- `thm:amplification`: with `r = 16(k + 1) + 1` runs, `3 · 2^k B ≤ M^r`. -/
theorem amplification_window {M F B k : PTm n} (hF : Γ ⊢[PRAAx] le (num 3 * F) M)
    (hB : Γ ⊢[PRAAx] le (pw (num 2) (succ (num 8 * succ k)) * B)
      (pw (M + F) (succ (num 8 * succ k + num 8 * succ k)))) :
    Γ ⊢[PRAAx] le (num 3 * pw (num 2) k * B) (pw M (succ (num 8 * succ k + num 8 * succ k))) :=
  amplification hF hB (window k)

end LeanProofs.IPRA.Foundations.ErrorAmplification
