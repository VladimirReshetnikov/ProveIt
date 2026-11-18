import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.BoundedSums

/-!
# Transfer of a bound from a certified finite net

Packets (`docs/proofs/foundations`): `ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`,
`ipra_kifcr_framework_2026-11-16`, `ipra_kifcs_framework_2026-11-16`, Theorem "Certified finite-net transfer":
if `f` has a modulus on `K`, a finite net of the corresponding mesh has been certified, and a bound
`f(z) ≤ M − slack` is verified at every net point with enough evaluation precision, then `f(x) ≤ M` for
every admissible `x`; the constants are chosen so that evaluation and transport errors fit the slack.

Values are natural numerators over a common denominator. The net points are indexed by `i < K`; `fv(i, p)`
is the value of `f` at the `i`-th net point, `av(i, p)` its evaluated approximation, `fx` the value at the
query point, `ω` the transport error given by the modulus at the mesh of the net and `e` the evaluation
error.

* `net_transfer`: from
  - coverage with the modulus applied: `∃ i < K. fx ≤ fv(i) + ω`,
  - the evaluation certificates: `∀ i < K. fv(i) ≤ av(i) + e`,
  - the verified bound with slack `e + ω`: `∀ i < K. av(i) + e + ω ≤ M`,

  derive `fx ≤ M`. The covering index is eliminated in the object theory; no net point is selected.

The finite approximate-witness theorem of the same packets (the selected net point is nearly optimal) is
`Foundations/ApproximateWitness`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.NetTransfer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The arithmetic chain at one net point. -/
theorem chain {fx fz az ω e M : PTm n} (hc : Γ ⊢[PRAAx] le fx (fz + ω)) (he : Γ ⊢[PRAAx] le fz (az + e))
    (hb : Γ ⊢[PRAAx] le (az + e + ω) M) : Γ ⊢[PRAAx] le fx M := by
  ipra_le sl hc + sl he + sl hb

/-- "Certified finite-net transfer". -/
theorem net_transfer {fv av : PTm 2} {K p fx ω e M : PTm n}
    (hcov : Γ ⊢[PRAAx] Fm.ex (lt (var 0) (Syn.shift K) ⋏
      le (Syn.shift fx) (inst2 fv (var 0) (Syn.shift p) + Syn.shift ω)))
    (hev : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶
      le (inst2 fv (var 0) (Syn.shift p)) (inst2 av (var 0) (Syn.shift p) + Syn.shift e)))
    (hbd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶
      le (inst2 av (var 0) (Syn.shift p) + Syn.shift e + Syn.shift ω) (Syn.shift M))) :
    Γ ⊢[PRAAx] le fx M := by
  refine .exE hcov ?_
  have w : ((lt (var 0) (Syn.shift K) ⋏ le (Syn.shift fx) (inst2 fv (var 0) (Syn.shift p) + Syn.shift ω)) ::
      Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (Syn.shift K) ⋏ le (Syn.shift fx) (inst2 fv (var 0) (Syn.shift p) + Syn.shift ω) := Prf.hyp0
  have r := chain (Prf.andE₂ w) (Prf.impE hev.allOpen.wk (Prf.andE₁ w))
    (Prf.impE hbd.allOpen.wk (Prf.andE₁ w))
  simp only [Fm.shift, subst_le]
  exact r

end LeanProofs.IPRA.Foundations.NetTransfer
