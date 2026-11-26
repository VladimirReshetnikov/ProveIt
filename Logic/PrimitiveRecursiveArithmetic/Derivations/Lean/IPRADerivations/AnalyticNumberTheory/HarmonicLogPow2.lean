import IPRADerivations.AnalyticNumberTheory.LogElementary
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Header

/-!
# `log 2 ≤ 1` for the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`, towards `con:global`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`. The global bound `con:global` (`|r(t)| ≤ 4`)
rests on Chebyshev's `ψ(x) ≤ 4x log 2 ≤ 4x`; `ChebyshevBounds.lcmu_upper` gives the integer form
`lcm(1, …, x) ≤ 2^{4x}`, and "the passage to real logarithms … is not formalized". For the packet's rational
logarithm `λ_M(a/b) = H_{Ma} − H_{Mb}` (with `H_m = S(m, F)/F`) the passage needs `log 2 ≤ 1`:

* `S_double`: `S(2K) ≤ S(K) + F`, i.e. `λ_K(2) = H_{2K} − H_K ≤ 1` at every mesh — from
  `LogElementary.log_upper` (`H_{2K} − H_K ≤ K/(K+1)`);
* `S_pow2`: `S(M 2^m) ≤ S(M) + m F`, i.e. `λ_M(2^m) ≤ m` — one QF induction on `m`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogPow2

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.LogElementary (log_upper)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `λ_K(2) ≤ 1`: `S(2K) ≤ S(K) + F`. -/
theorem S_double (K F : PTm n) : Γ ⊢[PRAAx] le (S (K + K) F) (S K F + F) := by
  have lu := log_upper (Γ := Γ) K K F
  refine mul_le_cancel (d' := K) ?_
  ipra_le sl lu + 𝔞 F

/-- `λ_M(2^m) ≤ m`: `S(M 2^m) ≤ S(M) + m F`. -/
theorem S_pow2 (M F m : PTm n) : Γ ⊢[PRAAx] le (S (M * pw two m) F) (S M F + m * F) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (S (Syn.shift M * pw two (var 0)) (Syn.shift F))
      (S (Syn.shift M) (Syn.shift F) + var 0 * Syn.shift F)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have e0 : Γ ⊢[PRAAx] M * pw two zero ≐ M := by
        have a := natEq (pw_zero (Γ := Γ) (two : PTm n))
        apply deriveNat; ipra_simps; linear_combination 𝔞 M * a
      have e := natEq (congrAp2 (Γ := Γ) (sumF hB) e0 (.eqRefl F))
      ipra_le 0 with e
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      let Δ : List (Fm PTm (n + 1)) := le (S (Syn.shift M * pw two (var 0)) (Syn.shift F))
          (S (Syn.shift M) (Syn.shift F) + var 0 * Syn.shift F) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (S (Syn.shift M * pw two (var 0)) (Syn.shift F))
          (S (Syn.shift M) (Syn.shift F) + var 0 * Syn.shift F) := Prf.hyp0
      have sd := S_double (Γ := Δ) (Syn.shift M * pw two (var 0)) (Syn.shift F)
      have ek : Δ ⊢[PRAAx] Syn.shift M * pw two (succ (var 0)) ≐
          Syn.shift M * pw two (var 0) + Syn.shift M * pw two (var 0) := by
        have a := natEq (pw_succ (Γ := Δ) two (var 0))
        apply deriveNat; ipra_simps; linear_combination 𝔞 (Syn.shift M) * a
      have e := natEq (congrAp2 (Γ := Δ) (sumF hB) ek (.eqRefl (Syn.shift F)))
      ipra_le sl ih + sl sd with e
  have h := Prf.allE m hall
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogPow2
