import IPRADerivations.AnalyticNumberTheory.RobinLipName
import IPRADerivations.AnalyticNumberTheory.RobinLogInterval
import IPRADerivations.Core.LinearCombination

/-!
# Lipschitz bounds for the reduced logarithm names (`robin_ipra_research_2026-11-19`, §"Explicit interval arithmetic")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`. In `LogI` (`RobinLogInterval`) the
reduced argument `y = a/B ∈ [1, 2]` enters through `z = (y − 1)/(y + 1) = d/s`, `a = B + d`, `s = a + B`. This module
translates the `z`-Lipschitz bounds of `RobinLipName` into `y`:

* `arg_up`: for `1 ≤ y = a/B ≤ y' = a'/B'` (`a'B = aB' + Δ`), `S_K(z(y')) ≤ S_K(z(y)) + (y' − y)/y`;
* `arg_low`: if moreover `y ≤ 2`, `S_K(z(y)) + (y' − y)/y' ≤ S_K(z(y')) + (y' − y)/(y · 9^K)`;
* `Nz_p0`: `S_K(0) = 0`.

The first is `2(z' − z)/(1 − z'²) = (y' − y)(y' + 1)/(y'(y + 1)) ≤ (y' − y)/y`; the second uses
`2(z' − z)/(1 − z²) ≥ (y' − y)/y'` and the truncation error `z^{2K} ≤ 9^{−K}` from `z ≤ 1/3`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLipArg

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv L_zero L_succ Pv P_succ P_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Nz_zero Nz_succ Dz Lz)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (Rv lip_up lip_low)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (c3)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `S_K(0) = 0` -/

theorem Nz_p0 (K s : PTm n) : Γ ⊢[PRAAx] Nz K zero s ≐ zero := by
  have hall : Γ ⊢[PRAAx] Fm.all (Nz (var 0) zero (Syn.shift s) ≐ zero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift]
      exact Nz_zero _ _
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := (Nz (var 0) zero (Syn.shift s) ≐ zero) :: Γ.map Fm.shift
      ipra_lc natEq (Nz_succ (Γ := Δ) (var 0) zero (Syn.shift s)) +
        (2 * 𝔞 (var 0 : PTm (n + 1)) + 1) * (𝔞 (Syn.shift s)) ^ 2 * natEq (Prf.hyp0 : Δ ⊢[PRAAx] Nz (var 0) zero (Syn.shift s) ≐ zero) +
        2 * 𝔞 (Lv (var 0 : PTm (n + 1)) zero) * (𝔞 (Syn.shift s)) ^ 2 * natEq (pw_succ (Γ := Δ) (zero : PTm (n + 1)) (two * var 0))
  have r := Prf.allE K hall
  simpa [Syn.subst_inst_shift] using r

/-! ## Reduced-argument bookkeeping -/

theorem one_le_sum {B a : PTm n} (hB : Γ ⊢[PRAAx] le one B) (x : PTm n) (h : Γ ⊢[PRAAx] a ≐ x + B) :
    Γ ⊢[PRAAx] le one a := by
  have e := natEq h
  ipra_le sl hB + 𝔞 x with e

/-- `(y' − y)/y` as a reduced name difference: `S_K(z(y')) ≤ S_K(z(y)) + Δ/(aB')`. -/
theorem arg_up {a B d s a' B' d' s' Dy : PTm n} (hB : Γ ⊢[PRAAx] le one B) (hB' : Γ ⊢[PRAAx] le one B')
    (ha : Γ ⊢[PRAAx] a ≐ B + d) (hs : Γ ⊢[PRAAx] s ≐ a + B) (ha' : Γ ⊢[PRAAx] a' ≐ B' + d')
    (hs' : Γ ⊢[PRAAx] s' ≐ a' + B') (hD : Γ ⊢[PRAAx] a' * B ≐ a * B' + Dy) (K : PTm n) :
    Γ ⊢[PRAAx] le (Nz K d' s' * Dz K d s * (a * B'))
      (Nz K d s * Dz K d' s' * (a * B') + Dy * Dz K d s * Dz K d' s') := by
  have ea := natEq ha
  have es := natEq hs
  have ea' := natEq ha'
  have es' := natEq hs'
  have eD := natEq hD
  have hW' : Γ ⊢[PRAAx] s' * s' ≐ two * two * B' * a' + d' * d' := by
    ipra_lc (-2 * 𝔞 B' + 𝔞 d' + 𝔞 s') * ea' + (2 * 𝔞 B' + 𝔞 d' + 𝔞 s') * es'
  have hd : Γ ⊢[PRAAx] d' * s ≐ d * s' + two * Dy := by
    ipra_lc (2 * 𝔞 B' + 𝔞 d') * ea + 𝔞 d' * es + (-2 * 𝔞 B - 𝔞 d) * ea' - 𝔞 d * es' + 2 * eD
  have LU := lip_up hW' hd K
  have hsa : Γ ⊢[PRAAx] le (s' * a) (s * a') := by
    ipra_le 𝔞 Dy with (𝔞 B' + 𝔞 a' - 𝔞 s') * ea + 𝔞 a' * es + (-𝔞 B - 𝔞 d) * es' + eD
  have sc : Γ ⊢[PRAAx] le (two * (two * Dy) * s' * (a * B')) (Dy * s * (two * two * B' * a')) := by
    ipra_le 4 * 𝔞 Dy * 𝔞 B' * sl hsa
  have c : Γ ⊢[PRAAx] le (s * (two * two * B' * a') * (Nz K d' s' * Dz K d s * (a * B')))
      (s * (two * two * B' * a') * (Nz K d s * Dz K d' s' * (a * B') + Dy * Dz K d s * Dz K d' s')) := by
    ipra_le 𝔞 (Lz K d s * a * B') * sl LU + 𝔞 (Lz K d s * Lz K d s * Pv K s * Pv K s') * sl sc
  have hs1 := one_le_sum hB a hs
  have ha1 := one_le_sum hB' d' (ha'.eqTrans (add_comm _ _))
  have hp : Γ ⊢[PRAAx] s * (two * two * B' * a') ≐ succ (pred (s * (two * two * B' * a'))) := by
    have m := le_mul_mono hs1 (le_mul_mono hB' ha1)
    exact pos_of_one_le (by ipra_le sl m + 3 * 𝔞 (s * B' * a'))
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

/-- `S_K(z(y)) + Δ/(a'B) ≤ S_K(z(y')) + Δ/(aB' 9^K)` for `y ≤ 2`. -/
theorem arg_low {a B d s a' B' d' s' Dy : PTm n} (hB : Γ ⊢[PRAAx] le one B) (hB' : Γ ⊢[PRAAx] le one B')
    (ha : Γ ⊢[PRAAx] a ≐ B + d) (hs : Γ ⊢[PRAAx] s ≐ a + B) (ha' : Γ ⊢[PRAAx] a' ≐ B' + d')
    (hs' : Γ ⊢[PRAAx] s' ≐ a' + B') (hD : Γ ⊢[PRAAx] a' * B ≐ a * B' + Dy) (h2 : Γ ⊢[PRAAx] le a (two * B))
    (K : PTm n) :
    Γ ⊢[PRAAx] le (Nz K d s * Dz K d' s' * ((a' * B) * (a * B' * Rv K c3)) +
        Dy * Dz K d s * Dz K d' s' * (a * B' * Rv K c3))
      (Nz K d' s' * Dz K d s * ((a' * B) * (a * B' * Rv K c3)) + Dy * Dz K d s * Dz K d' s' * (a' * B)) := by
  have ea := natEq ha
  have es := natEq hs
  have ea' := natEq ha'
  have es' := natEq hs'
  have eD := natEq hD
  have hW : Γ ⊢[PRAAx] s * s ≐ two * two * B * a + d * d := by
    ipra_lc (-2 * 𝔞 B + 𝔞 d + 𝔞 s) * ea + (2 * 𝔞 B + 𝔞 d + 𝔞 s) * es
  have hd : Γ ⊢[PRAAx] d' * s ≐ d * s' + two * Dy := by
    ipra_lc (2 * 𝔞 B' + 𝔞 d') * ea + 𝔞 d' * es + (-2 * 𝔞 B - 𝔞 d) * ea' - 𝔞 d * es' + 2 * eD
  have LL := lip_low hW hd K
  have hsa : Γ ⊢[PRAAx] le (s' * a) (s * a') := by
    ipra_le 𝔞 Dy with (𝔞 B' + 𝔞 a' - 𝔞 s') * ea + 𝔞 a' * es + (-𝔞 B - 𝔞 d) * es' + eD
  have hsB : Γ ⊢[PRAAx] le (s * B') (s' * B) := by
    ipra_le 𝔞 Dy with -(𝔞 B') * es + 𝔞 B * es' + eD
  have sc2 : Γ ⊢[PRAAx] le (Dy * s' * (two * two * B * a)) (two * (two * Dy) * s * (a' * B)) := by
    ipra_le 4 * 𝔞 Dy * 𝔞 B * sl hsa
  have h3d : Γ ⊢[PRAAx] le (c3 * d) s := by
    ipra_le 2 * sl h2 with 3 * ea + es
  have pr0 := pw_le_pw (Γ := Γ) (two * K) h3d
  have pr : Γ ⊢[PRAAx] le (Rv K c3 * Rv K d) (Rv K s) := le_congr (LocalFactor.pw_mul_base _ _ _) (.eqRefl _) pr0
  have m := le_mul_mono hsB pr
  have eQ0 := natEq (pw_succ (Γ := Γ) s (two * K))
  have sc3 : Γ ⊢[PRAAx] le (two * (two * Dy) * (s * s) * Rv K d * (a * B' * Rv K c3))
      (Dy * Pv K s * s' * (two * two * B * a)) := by
    ipra_le 4 * 𝔞 Dy * 𝔞 a * 𝔞 s * sl m with (4 * 𝔞 B * 𝔞 Dy * 𝔞 a * 𝔞 s') * eQ0
  have c : Γ ⊢[PRAAx] le (s' * (two * two * B * a) * (Nz K d s * Dz K d' s' * ((a' * B) * (a * B' * Rv K c3)) +
        Dy * Dz K d s * Dz K d' s' * (a * B' * Rv K c3)))
      (s' * (two * two * B * a) * (Nz K d' s' * Dz K d s * ((a' * B) * (a * B' * Rv K c3)) +
        Dy * Dz K d s * Dz K d' s' * (a' * B))) := by
    ipra_le 𝔞 (Lz K d s * (a' * B) * (a * B' * Rv K c3)) * sl LL +
      𝔞 (Lz K d s * Lz K d s * Pv K s * Pv K s' * (a * B' * Rv K c3)) * sl sc2 +
      𝔞 (Lz K d s * Lz K d s * Pv K s' * (a' * B)) * sl sc3
  have hs1 := one_le_sum hB' a' hs'
  have ha1 := one_le_sum hB d (ha.eqTrans (add_comm _ _))
  have hp : Γ ⊢[PRAAx] s' * (two * two * B * a) ≐ succ (pred (s' * (two * two * B * a))) := by
    have m' := le_mul_mono hs1 (le_mul_mono hB ha1)
    exact pos_of_one_le (by ipra_le sl m' + 3 * 𝔞 (s' * B * a))
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) c)

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLipArg
