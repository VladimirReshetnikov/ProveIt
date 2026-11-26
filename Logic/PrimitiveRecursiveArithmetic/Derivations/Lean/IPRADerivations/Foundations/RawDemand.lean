import IPRADerivations.Foundations.FiniteStabilization
import IPRADerivations.Foundations.ReverseDemand
import IPRADerivations.Probability.Ninther
import IPRADerivations.Core.Header

/-!
# Raw demand adequacy of the capped closure

Packets: `foundations/ipra_kifcs_framework_2026-11-16` and `foundations/ipra_kifcr_framework_2026-11-16`,
`paper/sections/07b_cyclic_demand.tex`, Corollary `cor:raw-demand-adequacy` ("Raw demand adequacy"): if
`ov(r*) = 0`, then `r*` satisfies every uncapped edge inequality `d_e(r*_j) ≤ r*_i` and is least among all
raw closed vectors in the capped box. "No overflow means every edge demand is at most the receiving cap. At
a fixed point, the capped maximum equals the current coordinate. Any raw closed vector is a pre-fixed point
of `T`, so leastness follows from `thm:capped-closure`."

One coordinate with seed `s`, cap `C` (`s ≤ C`) and one incoming edge demand `e = d(r)`: the capped
update is `T(r) = min(C, max(max(s, r), d(r)))`, and no overflow is `d(r) ≤ C`.

* `raw_adequate`: at a fixed point `T(r*) = r*` without overflow, `d(r*) ≤ r*`: the uncapped edge
  inequality;
* `raw_prefixed`: a raw closed `u` in the box (`s ≤ u ≤ C`, `d(u) ≤ u`) is a pre-fixed point,
  `T(u) ≤ u`;
* `raw_least`: hence the capped closure `r* = T^C(x)` (`FiniteStabilization.capped_closure`) lies below
  every raw closed vector of the box.

Several coordinates (the packed vector with its join and rank) are not treated here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RawDemand

open_ipra
open LeanProofs.IPRA.Foundations.IterationFusion (app1 iter)
open LeanProofs.IPRA.Foundations.FiniteStabilization (capped_closure_least)
open LeanProofs.IPRA.Foundations.ReverseDemand (le_mx_left le_mx_right mx_lub)
open LeanProofs.IPRA.Probability.Ninther (mx mn mn_le mn_ge)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- The capped update `min(C, max(max(s, r), e))`. -/
abbrev capT (C s r e : PTm k) : PTm k := mn C (mx (mx s r) e)

/-- `min(C, M) ≤ M`. -/
theorem mn_le_right (C M : PTm k) : Γ ⊢[PRAAx] le (mn C M) M :=
  .orE (le_total C M) (le_congr (mn_le Prf.hyp0).eqSymm (.eqRefl _) Prf.hyp0)
    (le_congr (mn_ge Prf.hyp0).eqSymm (.eqRefl _) (le_refl _))

/-- `min(C, M) ≤ C`. -/
theorem mn_le_left (C M : PTm k) : Γ ⊢[PRAAx] le (mn C M) C :=
  .orE (le_total C M) (le_congr (mn_le Prf.hyp0).eqSymm (.eqRefl _) (le_refl _))
    (le_congr (mn_ge Prf.hyp0).eqSymm (.eqRefl _) Prf.hyp0)

/-- `cor:raw-demand-adequacy`, the edge inequality: a fixed point without overflow satisfies `e ≤ r`. -/
theorem raw_adequate {C s r e : PTm k} (hfix : Γ ⊢[PRAAx] capT C s r e ≐ r) (hs : Γ ⊢[PRAAx] le s C)
    (he : Γ ⊢[PRAAx] le e C) : Γ ⊢[PRAAx] le e r := by
  have hrC : Γ ⊢[PRAAx] le r C := le_congr hfix (.eqRefl _) (mn_le_left C _)
  have hM : Γ ⊢[PRAAx] le (mx (mx s r) e) C := mx_lub (mx_lub hs hrC) he
  have eM := (mn_ge hM).eqSymm.eqTrans hfix
  exact le_congr (.eqRefl _) eM (le_mx_right _ _)

/-- A raw closed vector of the box is a pre-fixed point of the capped update. -/
theorem raw_prefixed {C s u e : PTm k} (hsu : Γ ⊢[PRAAx] le s u) (heu : Γ ⊢[PRAAx] le e u) :
    Γ ⊢[PRAAx] le (capT C s u e) u :=
  le_trans (mn_le_right C _) (mx_lub (mx_lub hsu (le_refl u)) heu)

/-- `cor:raw-demand-adequacy`, leastness: the capped closure lies below every raw closed vector. -/
theorem raw_least {f d : PTm 1}
    (hmono : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s s' : PTm k},
      (Γ ⊢[PRAAx] le s s') → (Γ ⊢[PRAAx] le (app1 f s) (app1 f s')))
    {x C s u N : PTm k} (hT : Γ ⊢[PRAAx] app1 f u ≐ capT C s u (app1 d u))
    (hxu : Γ ⊢[PRAAx] le x u) (hsu : Γ ⊢[PRAAx] le s u) (hdu : Γ ⊢[PRAAx] le (app1 d u) u) :
    Γ ⊢[PRAAx] le (iter f N x) u :=
  capped_closure_least hmono hxu (le_congr hT.eqSymm (.eqRefl _) (raw_prefixed hsu hdu))

end LeanProofs.IPRA.Foundations.RawDemand
