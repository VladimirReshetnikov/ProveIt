import IPRADerivations.DiophantineNumberTheory.KhinchinAmplify
import IPRADerivations.Core.Gcd

/-!
# The rounds of the (K2) amplification (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Amplification by the finitely many
residual gaps": "If `R_j = |[0,1] ∖ U_j|`, (K11) gives `R_{j+1} ≤ (1 − 1/b₀) R_j`. … After `T = b₀(m+1)` stages
we therefore have `R_T ≤ 2^{−(m+1)}`."

`KhinchinAmplify` proves the constant: `half_bound` (`2 c^{c+1} < (c+1)^{c+1}`) and `pow_amp`
(`2x ≤ y ⇒ 2^j x^j ≤ y^j`). This module runs the rounds, for a residual sequence given as a term `R` in the
round variable `0` and `b = c + 1` (the packet's `c = 16383`), cleared of denominators:

* `contract`: `b R_{j+1} ≤ c R_j` for every round `j < T` gives `b^T R_T ≤ c^T R_0` (one QF induction);
* `amplify`: for `T = (c+1)(m+1)`, `2^{m+1} R_T ≤ R_0` — `contract`, then `half_bound` raised to the power
  `m + 1` (`pow_amp`, `RSA.pw_mul`), then cancellation of the positive factor `(c+1)^T` (`mul_le_cancel`);
* `amplify_b0`: the packet's `b₀ = 16384`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinAmplify (half_bound pow_amp)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A residual sequence `R_j` (the term `R` in the round variable `0`) with `b R_{j+1} ≤ c R_j` for every round
`j < T` satisfies `b^T R_T ≤ c^T R_0`. -/
theorem contract (b c T : PTm n) (R : PTm (n + 1))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift T) ⟶
      le (Syn.shift b * Syn.subst (repl (succ (var 0))) R) (Syn.shift c * R))) :
    Γ ⊢[PRAAx] le (pw b T * Syn.subst (Syn.inst T) R) (pw c T * Syn.subst (Syn.inst zero) R) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift T) ⟶
      le (pw (Syn.shift b) (var 0) * R) (pw (Syn.shift c) (var 0) * Syn.shift (Syn.subst (Syn.inst zero) R))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift]
      refine .impI ?_
      have eb := natEq (pw_zero (Γ := le zero T :: Γ) b)
      have ec := natEq (pw_zero (Γ := le zero T :: Γ) c)
      ipra_le 0 with 𝔞 (Syn.subst (Syn.inst zero) R) * (ec - eb)
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift]
      refine .impI ?_
      let Θ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift T) ::
        (le (var 0) (Syn.shift T) ⟶
          le (pw (Syn.shift b) (var 0) * R) (pw (Syn.shift c) (var 0) * Syn.shift (Syn.subst (Syn.inst zero) R))) ::
        Γ.map Fm.shift
      have hle : Θ ⊢[PRAAx] le (var 0) (Syn.shift T) := le_trans (le_succ_self _) Prf.hyp0
      have ih : Θ ⊢[PRAAx] le (pw (Syn.shift b) (var 0) * R)
          (pw (Syn.shift c) (var 0) * Syn.shift (Syn.subst (Syn.inst zero) R)) := Prf.impE Prf.hyp1 hle
      have pt : Θ ⊢[PRAAx] le (Syn.shift b * Syn.subst (repl (succ (var 0))) R) (Syn.shift c * R) :=
        Prf.impE h.allOpen.wk.wk Prf.hyp0
      have eb := natEq (pw_succ (Γ := Θ) (Syn.shift b) (var 0))
      have ec := natEq (pw_succ (Γ := Θ) (Syn.shift c) (var 0))
      ipra_le 𝔞 (pw (Syn.shift b) (var 0)) * sl pt + 𝔞 (Syn.shift c) * sl ih with
        𝔞 (Syn.shift (Syn.subst (Syn.inst zero) R)) * ec - 𝔞 (Syn.subst (repl (succ (var 0))) R) * eb
  have h2 := Prf.allE T hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at h2
  exact .impE h2 (le_refl T)

/-- (K2) amplification count: if every round `j < T = (c+1)(m+1)` shrinks the residual by the factor
`1 − 1/(c+1)`, then `R_T ≤ 2^{−(m+1)} R_0`. -/
theorem amplify (c m : PTm n) (R : PTm (n + 1))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ c * succ m)) ⟶
      le (Syn.shift (succ c) * Syn.subst (repl (succ (var 0))) R) (Syn.shift c * R))) :
    Γ ⊢[PRAAx] le (pw two (succ m) * Syn.subst (Syn.inst (succ c * succ m)) R) (Syn.subst (Syn.inst zero) R) := by
  have hc := contract (succ c) c (succ c * succ m) R h
  have pd0 := pow_amp (le_of_lt (half_bound (Γ := Γ) c)) (succ m)
  have pd : Γ ⊢[PRAAx] le (pw two (succ m) * pw c (succ c * succ m)) (pw (succ c) (succ c * succ m)) :=
    le_congr (congrMul (.eqRefl _) (AnalyticNumberTheory.RSA.pw_mul c (succ c) (succ m)))
      (AnalyticNumberTheory.RSA.pw_mul (succ c) (succ c) (succ m)) pd0
  have hB : Γ ⊢[PRAAx] le (pw (succ c) (succ c * succ m) * (pw two (succ m) * Syn.subst (Syn.inst (succ c * succ m)) R))
      (pw (succ c) (succ c * succ m) * Syn.subst (Syn.inst zero) R) := by
    ipra_le 𝔞 (pw two (succ m)) * sl hc + 𝔞 (Syn.subst (Syn.inst zero) R) * sl pd
  have pos := DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) c (succ c * succ m)
  exact mul_le_cancel (le_congr (congrMul pos (.eqRefl _)) (congrMul pos (.eqRefl _)) hB)

/-- The packet's constants: `b₀ = 16384` and `T = b₀(m+1)` rounds give `R_T ≤ 2^{−(m+1)} R_0`. -/
theorem amplify_b0 (m : PTm n) (R : PTm (n + 1))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ (num 16383) * succ m)) ⟶
      le (Syn.shift (succ (num 16383)) * Syn.subst (repl (succ (var 0))) R) (Syn.shift (num 16383) * R))) :
    Γ ⊢[PRAAx] le (pw two (succ m) * Syn.subst (Syn.inst (succ (num 16383) * succ m)) R) (Syn.subst (Syn.inst zero) R) :=
  amplify (num 16383) m R h

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRounds
