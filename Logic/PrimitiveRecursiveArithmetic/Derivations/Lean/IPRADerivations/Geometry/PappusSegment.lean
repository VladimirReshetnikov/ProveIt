import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.LinearCombination

/-!
# The midpoint moment of a segment

Packet: `geometry/pappus_centroid_ipra_2026-11-15` (`lem:segment-moment`). A meridional segment
from radius `r₀` to `r₁` is cut into `N` equal pieces, each with its mass at its midpoint; the
midpoint of piece `j` has radius `r₀ + (2j + 1)(r₁ − r₀)/(2N)`. The first moment is independent
of `N`: `M_N = ℓ (r₀ + r₁)/2`. Cleared of the factor `ℓ/(2N²)` and with `r₁ = r₀ + δ`:

* `affine_sum`: `∑_{j<N} (c + (2j + 1) δ) = N c + N² δ`;
* `sum_odd`: `∑_{j<N} (2j + 1) = N²`, the odd-number identity of the packet;
* `midpoint_moment`: `∑_{j<N} (2N r₀ + (2j + 1) δ) = N² (r₀ + r₁)`.

The limits and the surface and volume theorems of the packet are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PappusSegment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `c + (2j + 1) δ`, with the parameter `⟨c, δ⟩`. -/
abbrev afB : PTm 2 := fstT (var 1) + succ (two * var 0) * sndT (var 1)
/-- `2j + 1`. -/
abbrev oddB : PTm 2 := succ (two * var 0)

theorem inst2_af (j y : PTm n) : inst2 afB j y = fstT y + succ (two * j) * sndT y := by simp [inst2]
theorem inst2_odd (j x : PTm n) : inst2 oddB j x = succ (two * j) := by simp [inst2]

theorem af_base (c δ : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF afB) zero (pairT c δ) ≐ zero * c + zero * zero * δ := by
  ipra_lc natEq (sum_zero (Γ := Γ) afB (pairT c δ))

theorem af_step {N c δ : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF afB) N (pairT c δ) ≐ N * c + N * N * δ) :
    Γ ⊢[PRAAx] ap2 (sumF afB) (succ N) (pairT c δ) ≐ succ N * c + succ N * succ N * δ := by
  have e := sum_succ' (Γ := Γ) afB N (pairT c δ)
  rw [inst2_af] at e
  have t : Γ ⊢[PRAAx] fstT (pairT c δ) + succ (two * N) * sndT (pairT c δ) ≐ c + succ (two * N) * δ :=
    congrAdd (fst_pair _ _) (congrMul (.eqRefl _) (snd_pair _ _))
  ipra_lc natEq (e.eqTrans (congrAdd (.eqRefl _) t)) + natEq ih

/-- Variables: `0 = N`, `1 = c`, `2 = δ`. -/
private abbrev afF : Fm PTm 3 :=
  ap2 (sumF afB) (var 0) (pairT (var 1) (var 2)) ≐ var 0 * var 1 + var 0 * var 0 * var 2

private theorem af₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] afF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact af_base _ _
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero,
      repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact af_step Prf.hyp0

/-- `∑_{j<N} (c + (2j + 1) δ) = N c + N² δ`. -/
theorem affine_sum (N c δ : PTm n) : Γ ⊢[PRAAx] ap2 (sumF afB) N (pairT c δ) ≐ N * c + N * N * δ := by
  have h := inst (Γ := Γ) af₀ (![N, c, δ] : Fin 3 → PTm n)
  simpa using h

theorem odd_pt (j x : PTm n) : Γ ⊢[PRAAx] inst2 oddB j x ≐ inst2 afB j (pairT zero one) := by
  rw [inst2_odd, inst2_af]
  exact ((congrAdd (fst_pair _ _) (congrMul (.eqRefl _) (snd_pair _ _))).eqTrans
    (by ipra_ring)).eqSymm

/-- `∑_{j<N} (2j + 1) = N²`. -/
theorem sum_odd (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF oddB) N x ≐ N * N := by
  refine (sum_congr_bounded oddB afB x (pairT zero one) N (.allI (.impI ?_))).eqTrans
    ((affine_sum N zero one).eqTrans (by ipra_ring))
  simp only [Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
  exact odd_pt _ _

/-- `lem:segment-moment`, cleared: `∑_{j<N} (2N r₀ + (2j + 1) δ) = N² (r₀ + r₁)` with
`r₁ = r₀ + δ`. Dividing by `2N²` and multiplying by the length gives `M_N = ℓ (r₀ + r₁)/2`. -/
theorem midpoint_moment (N r₀ δ : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF afB) N (pairT (two * N * r₀) δ) ≐ N * N * (r₀ + (r₀ + δ)) :=
  (affine_sum N (two * N * r₀) δ).eqTrans (by ipra_ring)

end LeanProofs.IPRA.Geometry.PappusSegment
