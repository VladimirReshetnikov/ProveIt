import IPRADerivations.Foundations.DiscreteGronwall

/-!
# The integer geometric bound at every node

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Lemma `lem:ode-growth`
("For positive `n`, natural `K`, and `0 ≤ j ≤ n`, `(1 + K/n)^j ≤ 3^K`"). The case `j = n` is
`Foundations/DiscreteGronwall.growth` (`(k + A)^k ≤ 3^A k^k`, for the packet `ipra_local_global`); here every
node `j ≤ n` is covered, as the paper's last step "Finally `1 + K/n ≥ 1` and `j ≤ n`":

* `growth_le`: for `k = k₀ + 1` and `j + d = k`, `(k + A)^j ≤ 3^A k^j`, cleared of `k^j`.

The proof writes `k = j + d`, bounds `(k + A)^j k^d ≤ (k + A)^j (k + A)^d = (k + A)^k ≤ 3^A k^k = 3^A k^j k^d`
and cancels the positive factor `k^d`.
-/

namespace LeanProofs.IPRA.Analysis.OdeGrowth

open_ipra
open LeanProofs.IPRA.Foundations.DiscreteGronwall (growth)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- `lem:ode-growth` at every node: `(k + A)^j ≤ 3^A k^j` for `j + d = k = k₀ + 1`. -/
theorem growth_le {k₀ A j d : PTm n} (hk : Γ ⊢[PRAAx] j + d ≐ succ k₀) :
    Γ ⊢[PRAAx] le (pw (succ k₀ + A) j) (pw (num 3) A * pw (succ k₀) j) := by
  have g := growth (Γ := Γ) k₀ A
  have hm := pw_le_pw (Γ := Γ) d (show Γ ⊢[PRAAx] le (succ k₀) (succ k₀ + A) by ipra_le 𝔞 A)
  have E1 : Γ ⊢[PRAAx] pw (succ k₀ + A) (succ k₀) ≐ pw (succ k₀ + A) j * pw (succ k₀ + A) d :=
    (congrAp2 powF hk.eqSymm (.eqRefl _)).eqTrans (pw_add _ _ _)
  have E2 : Γ ⊢[PRAAx] pw (succ k₀) (succ k₀) ≐ pw (succ k₀) j * pw (succ k₀) d :=
    (congrAp2 powF hk.eqSymm (.eqRefl _)).eqTrans (pw_add _ _ _)
  have e1 := natEq E1; have e2 := natEq E2
  have hZ := pw_pos' (Γ := Γ) (p := succ k₀) (congrSucc (pred_succ k₀).eqSymm) d
  refine mul_le_cancel (d' := pred (pw (succ k₀) d))
    (le_congr (congrMul hZ (.eqRefl _)) (congrMul hZ (.eqRefl _)) ?_)
  ipra_le 𝔞 (pw (succ k₀ + A) j) * sl hm + sl g using rw [e1, e2]; ring

end LeanProofs.IPRA.Analysis.OdeGrowth
