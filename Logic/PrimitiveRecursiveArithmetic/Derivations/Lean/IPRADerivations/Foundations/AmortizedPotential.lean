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

namespace LeanProofs.IPRA.Foundations.AmortizedPotential

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The amortized bound: `∑_{i<N} c_i + P_N ≤ ∑_{i<N} a_i + P_0`. -/
theorem amortized (c a P : PTm 2) (x N : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 c (var 0) (Syn.shift x) + inst2 P (succ (var 0)) (Syn.shift x))
        (inst2 a (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF c) N x + inst2 P N x) (ap2 (sumF a) N x + inst2 P zero x) := by
  let invariant := le (ap2 (sumF c) (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x))
    (ap2 (sumF a) (var 0) (Syn.shift x) + inst2 P zero (Syn.shift x))
  have atBound : Γ ⊢[PRAAx] invariant.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simp only [invariant, subst_le, subst_ap2, PTm.subst_add, subst_inst2, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have L0 := (congrAdd (sum_zero (Γ := Γ) c x) (.eqRefl (inst2 P zero x))).eqTrans (zero_add _)
      have R0 := (congrAdd (sum_zero (Γ := Γ) a x) (.eqRefl (inst2 P zero x))).eqTrans (zero_add _)
      exact le_congr L0.eqSymm R0.eqSymm (le_refl _)
    · simp only [invariant, subst_le, subst_ap2, PTm.subst_add, subst_inst2, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      let Δ := lt (var 0) (Syn.shift N) :: invariant :: Γ.map Fm.shift
      have previous : Δ ⊢[PRAAx] invariant := Prf.hyp1
      have next : Δ ⊢[PRAAx] le (inst2 c (var 0) (Syn.shift x) + inst2 P (succ (var 0)) (Syn.shift x))
          (inst2 a (var 0) (Syn.shift x) + inst2 P (var 0) (Syn.shift x)) :=
        .impE hp.allOpen.wk.wk Prf.hyp0
      have ec := natEq (sum_succ' (Γ := Δ) c (var 0) (Syn.shift x))
      have ea := natEq (sum_succ' (Γ := Δ) a (var 0) (Syn.shift x))
      ipra_le sl previous + sl next with ea - ec
  simpa [invariant] using atBound

end LeanProofs.IPRA.Foundations.AmortizedPotential
