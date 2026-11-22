import IPRADerivations.Core.Search

/-!
Packet: `geometry/hyperbox_surface_ipra_2026-11-20`. Imported from the packet's `lean/IPRASquareRoot.lean`:
`ceilRoot_majorizes`, `ceilRoot_minimal` (the integer ceiling square root used for a facet chord, by bounded search).

 Object-level proofs for the integer ceiling square root used for a facet chord.
    Run in the ProveIt Lake workspace indicated in README.md. -/
namespace LeanProofs.IPRA.Geometry.Hyperbox
open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rootBody : PTm 2 := monus (var 1) (var 0 * var 0)
def ceilRoot (s : PTm n) : PTm n := Search.mu rootBody (succ (succ s)) s

private theorem body_zero_iff (i s : PTm n) :
    (inst2 rootBody i s ≐ zero) = le s (i*i) := by
  simp [rootBody, inst2, le]

private theorem upper_witness (s : PTm n) :
    Γ ⊢[PRAAx] le s (succ s * succ s) := by
  exact le_trans (le_succ_self s) (le_congr (.eqRefl _) (mul_succ (succ s) s).eqSymm
    (le_add_left (succ s) (succ s*s)))

/-- The selected integer's square majorizes the integer squared chord. -/
theorem ceilRoot_majorizes (s : PTm n) :
    Γ ⊢[PRAAx] le s (ceilRoot s * ceilRoot s) := by
  have hf : Γ ⊢[PRAAx] inst2 rootBody (succ s) s ≐ zero := by
    rw [body_zero_iff]; exact upper_witness s
  have h := Search.search_found hf (le_refl (succ (succ s)))
  have e := Prf.andE₁ (Prf.andE₂ h)
  rw [body_zero_iff] at e
  exact e

/-- Every strictly smaller integer has square strictly below the input. -/
theorem ceilRoot_minimal (s i : PTm n) (h : Γ ⊢[PRAAx] lt i (ceilRoot s)) :
    Γ ⊢[PRAAx] lt (i*i) s := by
  have hn := Search.search_minimal (f := rootBody) h
  rw [body_zero_iff] at hn
  exact .orE (lt_or_le (i*i) s) Prf.hyp0 (.botE _ (.impE hn.wk Prf.hyp0))

end LeanProofs.IPRA.Geometry.Hyperbox
