import IPRADerivations.Topology.BrouwerInterval
import IPRADerivations.Core.IntCertificates

/-!
# The uniform simplex approximation theorem in dimension one

Packet: `topology/approximate_brouwer_ipra`, `brouwer.tex`, Theorem `thm:main` ("Uniform simplex
approximation") for `d = 1`: "Then `x` is a barycentric grid point of denominator `N`, and for every `s ≥ m`,
`‖x − A(x, s)‖ ≤ (2d/(d+1))(N^{-1} + 2^{-m}) ≤ (d/(d+1)) 2^{-k} < 2^{-k}` … The scan has finished before `s`
is chosen, so the same `x` proves the entire tail estimate."

With `m = k + 2`, the samples `g(i, x) = N · A(i/N, m)` on the grid, the witness `W` of
`Topology/BrouwerInterval` (found at stage `m` only) and a later-stage sample `gs = N · A(W/N, s)`:

* `main_interval`: if the cell oscillation `E` of the samples and the stage difference `E'`
  (`|gs − g(W)| ≤ E'`) are both at most `N · 2^{-m}` (the contract `eq:contract` at inputs within
  `1/N ≤ 2^{-μ(m)}`), then `|W − gs| ≤ N · 2^{-k-1}`: the grid point `W/N` has residual at most `2^{-k-1}` at
  every later stage.
-/

namespace LeanProofs.IPRA.Topology.BrouwerIntervalMain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.BrouwerInterval (W approx_fixed_point)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `thm:main` for `d = 1`: the residual of the witness at any later stage is at most `2^{-k-1}`. -/
theorem main_interval (g : PTm 2) (k : ℕ) (N x E E' gs : PTm n) (hN : Γ ⊢[PRAAx] le (inst2 g N x) N)
    (hosc : ∀ i : PTm n, Γ ⊢[PRAAx] lt i N ⟶ le (inst2 g i x) (inst2 g (succ i) x + E))
    (hs₁ : Γ ⊢[PRAAx] le gs (inst2 g (W g N x) x + E'))
    (hs₂ : Γ ⊢[PRAAx] le (inst2 g (W g N x) x) (gs + E'))
    (hE : Γ ⊢[PRAAx] le (num (2 ^ (k + 2)) * E) N) (hE' : Γ ⊢[PRAAx] le (num (2 ^ (k + 2)) * E') N) :
    (Γ ⊢[PRAAx] le (num (2 ^ (k + 1)) * gs) (num (2 ^ (k + 1)) * W g N x + N)) ∧
      (Γ ⊢[PRAAx] le (num (2 ^ (k + 1)) * W g N x) (num (2 ^ (k + 1)) * gs + N)) := by
  have w := approx_fixed_point g N x E hN hosc
  have hle : Γ ⊢[PRAAx] le (inst2 g (W g N x) x) (W g N x) := Prf.andE₂ (Prf.andE₁ w)
  have hup : Γ ⊢[PRAAx] le (W g N x) (inst2 g (W g N x) x + E) := Prf.andE₂ w
  refine ⟨?_, ?_⟩
  · ipra_le 2 ^ (k + 1) * sl hs₁ + 2 ^ (k + 1) * sl hle + sl hE' + 2 ^ (k + 1) * Groth.ι (Q.mk Γ E')
      using push_cast; ring
  · apply le_of_two_mul
    ipra_le 2 ^ (k + 2) * sl hup + 2 ^ (k + 2) * sl hs₂ + sl hE + sl hE' using push_cast; ring

end LeanProofs.IPRA.Topology.BrouwerIntervalMain
