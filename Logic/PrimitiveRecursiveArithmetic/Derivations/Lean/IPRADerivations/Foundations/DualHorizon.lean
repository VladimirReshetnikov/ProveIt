import IPRADerivations.Probability.UnionUtility
import IPRADerivations.Core.OrderCertificates

/-!
# Dual-horizon composition

Packet: `foundations/ipra_frnf_framework_bundle`, `paper/sections/07_dual_horizons.tex`, Definition "Dual
horizon" and Theorem `thm:dual-compose` ("Dual-horizon composition"). A finite-use interface carries a
computation horizon `r_F(d)` and a justification horizon `j_F(d)` with `r_F ≤ j_F`. For a composite `G ∘ F`,

  `r_{G∘F}(d) = max_{q ≤ r_G(d)} r_F(q)`,   `j_{G∘F}(d) = max_{q ≤ j_G(d)} j_F(q)`,

and the theorem states that these are horizons of the composite and `r_{G∘F}(d) ≤ j_{G∘F}(d)`. The use of the
inner horizons inside the composite derivation is the simultaneous cut of the paper's proof; the arithmetic
of the two horizons is derived here.

Horizons are bodies `r_F(q, x)`, `j_F(q, x)`, `r_G(d, x)`, `j_G(d, x)`; the prefix maximum is
`UnionUtility.Mx` over `q < r_G(d) + 1`.

* `rComp`, `jComp`: the composite horizons;
* `query_le`: every query `q ≤ r_G(d)` of the outer computation reads inputs only below `r_{G∘F}(d)`,
  i.e. `r_F(q) ≤ r_{G∘F}(d)`;
* `proof_le`: every inner contract instance `q ≤ j_G(d)` needs inputs only below `j_{G∘F}(d)`;
* `comp_le` (`thm:dual-compose`, the inequality): if `r_G(d) ≤ j_G(d)` and `r_F(q) ≤ j_F(q)` for all `q`,
  then `r_{G∘F}(d) ≤ j_{G∘F}(d)` (the maximum `r_{G∘F}(d)` is attained at some `q ≤ r_G(d)`,
  `UnionUtility.ag_attains`).
-/

namespace LeanProofs.IPRA.Foundations.DualHorizon

open_ipra exports
open LeanProofs.IPRA.Probability.UnionUtility (Mx Ag mx_upper ag_attains)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (rF jF rG jG : PTm 2)

/-- `r_{G∘F}(d) = max_{q ≤ r_G(d)} r_F(q)`. -/
abbrev rComp (d x : PTm n) : PTm n := Mx rF (succ (inst2 rG d x)) x

/-- `j_{G∘F}(d) = max_{q ≤ j_G(d)} j_F(q)`. -/
abbrev jComp (d x : PTm n) : PTm n := Mx jF (succ (inst2 jG d x)) x

variable {rF jF rG jG}

/-- Every query `q ≤ r_G(d)` of the outer computation reads inputs only below `r_{G∘F}(d)`. -/
theorem query_le {q d x : PTm n} (hq : Γ ⊢[PRAAx] le q (inst2 rG d x)) :
    Γ ⊢[PRAAx] le (inst2 rF q x) (rComp rF rG d x) :=
  mx_upper rF (b := q) (K := succ (inst2 rG d x)) (x := x) (by show Γ ⊢[PRAAx] le (succ q) (succ (inst2 rG d x)); ipra_le sl hq)

/-- Every inner contract instance `q ≤ j_G(d)` needs inputs only below `j_{G∘F}(d)`. -/
theorem proof_le {q d x : PTm n} (hq : Γ ⊢[PRAAx] le q (inst2 jG d x)) :
    Γ ⊢[PRAAx] le (inst2 jF q x) (jComp jF jG d x) :=
  mx_upper jF (b := q) (K := succ (inst2 jG d x)) (x := x) (by show Γ ⊢[PRAAx] le (succ q) (succ (inst2 jG d x)); ipra_le sl hq)

/-- `thm:dual-compose`: the composite computation horizon is below the composite justification horizon. -/
theorem comp_le {d x : PTm n} (hG : Γ ⊢[PRAAx] le (inst2 rG d x) (inst2 jG d x))
    (hF : ∀ q : PTm n, Γ ⊢[PRAAx] le (inst2 rF q x) (inst2 jF q x)) :
    Γ ⊢[PRAAx] le (rComp rF rG d x) (jComp jF jG d x) := by
  have a := ag_attains rF (Γ := Γ) (inst2 rG d x) x
  have hA : Γ ⊢[PRAAx] le (succ (Ag rF (succ (inst2 rG d x)) x)) (succ (inst2 rG d x)) := Prf.andE₁ a
  have hq : Γ ⊢[PRAAx] le (Ag rF (succ (inst2 rG d x)) x) (inst2 jG d x) := by
    ipra_le sl hA + sl hG
  have p := proof_le (jF := jF) (jG := jG) hq
  exact le_congr (Prf.andE₂ a) (.eqRefl _) (le_trans (hF _) p)

end LeanProofs.IPRA.Foundations.DualHorizon
