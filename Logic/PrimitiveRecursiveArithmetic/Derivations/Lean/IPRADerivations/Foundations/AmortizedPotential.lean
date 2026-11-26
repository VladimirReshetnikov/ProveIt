import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# The potential method of amortized analysis

Packet: `foundations/ipra_complexity_foundations_2026-11-20`, `tex/extensions.tex`, "Worst case, finite averages,
and amortized costs": "If states `s_0, …, s_m`, nonnegative costs `c_i`, and a numerical potential `Φ` obey
`c_i + Φ(s_{i+1}) ≤ a_i + Φ(s_i)`, summing and canceling gives
`∑_{i<m} c_i + Φ(s_m) ≤ ∑_{i<m} a_i + Φ(s_0)`. The induction is an inequality between finite sums."

For bodies `c(i, x)` (actual costs), `a(i, x)` (amortized costs) and `P(i, x)` (the potential of the `i`-th
state), with the step inequalities as one object-level premise over `i < N`:

* `amortized`: `∑_{i<N} c_i + P_N ≤ ∑_{i<N} a_i + P_0`, by quantifier-free induction on the prefix length with
  the premise outside the induction matrix.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.AmortizedPotential

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The amortized bound: `∑_{i<N} c_i + P_N ≤ ∑_{i<N} a_i + P_0`. -/
theorem amortized (c a P : PTm 2) (x N : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 c (var 0) (Syn.shift x) + inst2 P (succ (var 0)) (Syn.shift x))
        (inst2 a (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF c) N x + inst2 P N x) (ap2 (sumF a) N x + inst2 P zero x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (ap2 (sumF c) (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x))
        (ap2 (sumF a) (var 0) (Syn.shift x) + inst2 P zero (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, subst_inst2, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have L0 : (le zero N :: Γ) ⊢[PRAAx] ap2 (sumF c) zero x + inst2 P zero x ≐ inst2 P zero x :=
        (congrAdd (sum_zero c x) (.eqRefl _)).eqTrans (zero_add _)
      have R0 : (le zero N :: Γ) ⊢[PRAAx] ap2 (sumF a) zero x + inst2 P zero x ≐ inst2 P zero x :=
        (congrAdd (sum_zero a x) (.eqRefl _)).eqTrans (zero_add _)
      exact .impI (le_congr L0.eqSymm R0.eqSymm (le_refl _))
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, subst_inst2, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have hf := hp.allOpen
      refine .impI ?_
      let IH : Fm PTm (n + 1) := le (var 0) (Syn.shift N) ⟶
        le (ap2 (sumF c) (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x))
          (ap2 (sumF a) (var 0) (Syn.shift x) + inst2 P zero (Syn.shift x))
      let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      have hle : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
      have h₁ : Δ ⊢[PRAAx] le (ap2 (sumF c) (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x))
          (ap2 (sumF a) (var 0) (Syn.shift x) + inst2 P zero (Syn.shift x)) := Prf.impE Prf.hyp1 hle
      have h₂ : Δ ⊢[PRAAx] le (inst2 c (var 0) (Syn.shift x) + inst2 P (succ (var 0)) (Syn.shift x))
          (inst2 a (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x)) := Prf.impE hf.wk.wk Prf.hyp0
      have ec := natEq (sum_succ' (Γ := Δ) c (var 0) (Syn.shift x))
      have ea := natEq (sum_succ' (Γ := Δ) a (var 0) (Syn.shift x))
      ipra_le sl h₁ + sl h₂ with ea - ec
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact Prf.impE h2 (le_refl N)

end LeanProofs.IPRA.Foundations.AmortizedPotential
