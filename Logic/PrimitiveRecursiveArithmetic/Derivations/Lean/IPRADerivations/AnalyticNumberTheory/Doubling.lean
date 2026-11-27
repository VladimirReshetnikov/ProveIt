import IPRADerivations.AnalyticNumberTheory.BlockCases

/-!
# Harmonic lengths of dyadic blocks (`pnt_ipra_constructive_2026-11-14`, `con:block-length`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, (con:block-length): the blocks of
the contraction have logarithmic length `H ≥ 512q`. Discretely a block of divisors `D < d ≤ 2^m D` has harmonic length
`S(2^m D) − S(D) ≥ m F/2 − 2^m D` (`F = L!`), the lower companion of `HarmonicLogPow2.S_pow2`
(`S(2^m D) ≤ S(D) + mF`):

* `S_double_lower`: `2S(K) + F + 1 ≤ 2S(2K) + 2K` (`BlockCases.S_gap` and `F = 2K⌊F/2K⌋ + r`, `r < 2K`);
* `S_pow2_lower`: `2S(M) + mF ≤ 2S(M 2^m) + 2M 2^m`, by quantifier-free induction on `m`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Doubling

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB pw2_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockCases (S_gap)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `2S(K) + F + 1 ≤ 2S(2K) + 2K` for `K ≥ 1`: a doubling adds at least `F/2 − K` to the harmonic length. -/
theorem S_double_lower {K : PTm n} (F : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le (two * S K F + F + one) (two * S (K + K) F + two * K) := by
  have sg := S_gap (Γ := Γ) F (le_add_right K K)
  have em := natEq (add_monus (Γ := Γ) K K)
  have hKK : Γ ⊢[PRAAx] le one (K + K) := le_trans hK (le_add_right K K)
  have dm := div_mod_at (Γ := Γ) (x := F) (pos_of_one_le hKK)
  have e1 := natEq (Prf.andE₁ dm)
  have hr := Prf.andE₂ dm
  ipra_le 2 * sl sg + sl hr with 2 * 𝔞 (quo F (K + K)) * em - e1

/-- `2S(M) + mF ≤ 2S(M 2^m) + 2M 2^m` for `M ≥ 1`. -/
theorem S_pow2_lower {M : PTm n} (F m : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le (two * S M F + m * F) (two * S (M * pw two m) F + two * (M * pw two m)) := by
  have hM' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hall : Γ ⊢[PRAAx] Fm.all (le (two * S (Syn.shift M) (Syn.shift F) + var 0 * Syn.shift F)
      (two * S (Syn.shift M * pw two (var 0)) (Syn.shift F) + two * (Syn.shift M * pw two (var 0)))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2]
    · have e0 : Γ ⊢[PRAAx] M * pw two zero ≐ M := by
        ipra_lc 𝔞 M * natEq (pw_zero (two : PTm n))
      have e := natEq (congrAp2 (Γ := Γ) (sumF hB) e0 (.eqRefl F))
      have e0' := natEq e0
      ipra_le 2 * 𝔞 M with -2 * e - 2 * e0'
    · let Δ : List (Fm PTm (n + 1)) := le (two * S (Syn.shift M) (Syn.shift F) + var 0 * Syn.shift F)
          (two * S (Syn.shift M * pw two (var 0)) (Syn.shift F) + two * (Syn.shift M * pw two (var 0))) ::
          Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (two * S (Syn.shift M) (Syn.shift F) + var 0 * Syn.shift F)
          (two * S (Syn.shift M * pw two (var 0)) (Syn.shift F) + two * (Syn.shift M * pw two (var 0))) := Prf.hyp0
      have hp : Δ ⊢[PRAAx] le one (Syn.shift M * pw two (var 0)) := by
        have a := natEq (eq_add_of_le (Γ := Δ) hM'.wk)
        have b := natEq (pw2_pos (Γ := Δ) (var 0))
        ipra_le 𝔞 (monus (Syn.shift M) one) * 𝔞 (pw two (var 0)) + 𝔞 (pred (pw two (var 0))) with
          𝔞 (pw two (var 0)) * a + b
      have sd := S_double_lower (Γ := Δ) (Syn.shift F) hp
      have ek : Δ ⊢[PRAAx] Syn.shift M * pw two (succ (var 0)) ≐
          Syn.shift M * pw two (var 0) + Syn.shift M * pw two (var 0) := by
        ipra_lc 𝔞 (Syn.shift M) * natEq (pw_succ (Γ := Δ) two (var 0))
      have e := natEq (congrAp2 (Γ := Δ) (sumF hB) ek (.eqRefl (Syn.shift F)))
      have ek' := natEq ek
      ipra_le sl ih + sl sd + 1 with 2 * e + 2 * ek'
  have h := Prf.allE m hall
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

end LeanProofs.IPRA.AnalyticNumberTheory.Doubling

export_ipra AnalyticNumberTheory.Doubling (S_pow2_lower)
