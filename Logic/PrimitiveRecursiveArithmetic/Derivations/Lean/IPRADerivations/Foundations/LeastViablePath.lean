import IPRADerivations.Foundations.ViableChain
import IPRADerivations.Core.Search

/-!
# Finite dependent choice by least viability

Packets (`docs/proofs/foundations`): `ipra_kifc_framework_2026-11-15` and its later editions
(`ipra_kifc_framework_2026-11-16`, `ipra_kifcr_framework_2026-11-16`, `ipra_kifcs_framework_2026-11-16`),
Theorem `thm:finite-choice` ("Finite dependent choice by least viability"): "If
`Any_{a < B_0} W_0(a) = 1`, a compatible accepted path can be constructed primitive recursively. Choose
the least viable `a_0`. Given `a_i`, choose the least `a_{i+1}` satisfying
`V_{i+1}(a_{i+1}) ∧ E_i(a_i, a_{i+1}) ∧ W_{i+1}(a_{i+1}) = 1`. The resulting path is valid, compatible,
and terminally accepted." The same statement is the "least viable path" corollary of the related packets.

For a finite compatibility instance `I` of `Foundations/BackwardViability` (local tests `G`, edge tests
`T`, bounds `B`, horizon `h`, viability bits `V`), `Foundations/ViableChain` builds the path from a given
viable start by taking the least passing successor at every level. Here the start itself is chosen by
least search:

* `nvB I`: the body `(1 ∸ V(h, a)) + (V(h, a) ∸ 1)`, zero exactly when the candidate `a` of level `0` is
  viable for the whole horizon; `viable_of_zero`, `zero_of_viable`;
* `sLeast I`: the least such candidate below `B(0)`, a term in the parameter;
* `start_spec`: if some candidate `a < B(0)` is viable, the selected start is below `B(0)`, is viable, and
  is at most `a`;
* `path_inv`, `path_local`, `path_edge`: then the path `c(0) = sLeast`, `c(t + 1) = nxt(c(t))` satisfies
  `c(t) < B(t)` and `V(h ∸ t, c(t)) = 1` and `G(t, c(t)) ≠ 0` for `t ≤ h`, and `T(t, c(t), c(t + 1)) ≠ 0`
  for `t < h`.

The path is a term in `t`; no coded sequence and no choice principle are used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.LeastViablePath

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Search (mu search_found)
open LeanProofs.IPRA.Foundations.BackwardViability
open LeanProofs.IPRA.Foundations.BackwardViability.Instance
open LeanProofs.IPRA.Foundations.ViableChain (start chain chain_inv chain_edge chain_local subst_V)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)} (I : Instance)

/-- `(1 ∸ V(h, a)) + (V(h, a) ∸ 1)` over `0 = a`, `1 = p`: zero exactly when `V(h, a) = 1`. -/
def nvB : PTm 2 :=
  monus one (I.V (I.h (var 1)) (var 0) (var 1)) + monus (I.V (I.h (var 1)) (var 0) (var 1)) one

theorem inst2_nvB (a p : PTm k) :
    inst2 (nvB I) a p = monus one (I.V (I.h p) a p) + monus (I.V (I.h p) a p) one := by
  simp [inst2, nvB]

theorem viable_of_zero {a p : PTm k} (h : Γ ⊢[PRAAx] inst2 (nvB I) a p ≐ zero) :
    Γ ⊢[PRAAx] I.V (I.h p) a p ≐ one := by
  rw [inst2_nvB] at h
  exact le_antisymm (add_eq_zero_right h) (add_eq_zero_left h)

theorem zero_of_viable {a p : PTm k} (hv : Γ ⊢[PRAAx] I.V (I.h p) a p ≐ one) :
    Γ ⊢[PRAAx] inst2 (nvB I) a p ≐ zero := by
  rw [inst2_nvB]
  exact (congrAdd (congrMonus (.eqRefl one) hv) (congrMonus hv (.eqRefl one))).eqTrans
    ((congrAdd (monus_self one) (monus_self one)).eqTrans (add_zero zero))

/-- The least viable start candidate, a term in the parameter `p`. -/
def sLeast : PTm 1 := mu (nvB I) (I.bd zero (var 0)) (var 0)

theorem start_sLeast (p : PTm k) : start (sLeast I) p = mu (nvB I) (I.bd zero p) p := by
  simp [start, sLeast]

/-- The first choice: the selected start is in range, viable, and at most any viable candidate. -/
theorem start_spec {a p : PTm k} (ha : Γ ⊢[PRAAx] lt a (I.bd zero p))
    (hv : Γ ⊢[PRAAx] I.V (I.h p) a p ≐ one) :
    Γ ⊢[PRAAx] lt (start (sLeast I) p) (I.bd zero p) ⋏
      ((I.V (I.h p) (start (sLeast I) p) p ≐ one) ⋏ le (start (sLeast I) p) a) := by
  rw [start_sLeast]
  have sf := search_found (zero_of_viable I hv) ha
  exact .andI (Prf.andE₁ sf)
    (.andI (viable_of_zero I (Prf.andE₁ (Prf.andE₂ sf))) (Prf.andE₂ (Prf.andE₂ sf)))

/-- `thm:finite-choice`: along the selected path, `c(t) < B(t)` and `V(h ∸ t, c(t)) = 1` for `t ≤ h`. -/
theorem path_inv {a t p : PTm k} (ha : Γ ⊢[PRAAx] lt a (I.bd zero p))
    (hv : Γ ⊢[PRAAx] I.V (I.h p) a p ≐ one) (ht : Γ ⊢[PRAAx] le t (I.h p)) :
    Γ ⊢[PRAAx] lt (chain I (sLeast I) t p) (I.bd t p) ⋏
      (I.V (monus (I.h p) t) (chain I (sLeast I) t p) p ≐ one) :=
  chain_inv (Prf.andE₁ (start_spec I ha hv)) (Prf.andE₁ (Prf.andE₂ (start_spec I ha hv))) ht

/-- The local tests hold along the selected path: `G(t, c(t)) ≠ 0` for `t ≤ h`. -/
theorem path_local {a t p : PTm k} (ha : Γ ⊢[PRAAx] lt a (I.bd zero p))
    (hv : Γ ⊢[PRAAx] I.V (I.h p) a p ≐ one) (ht : Γ ⊢[PRAAx] le t (I.h p)) :
    Γ ⊢[PRAAx] neg (I.g t (chain I (sLeast I) t p) p ≐ zero) :=
  chain_local (Prf.andE₁ (start_spec I ha hv)) (Prf.andE₁ (Prf.andE₂ (start_spec I ha hv))) ht

/-- The edge tests hold along the selected path: `T(t, c(t), c(t + 1)) ≠ 0` for `t < h`. -/
theorem path_edge {a t p : PTm k} (ha : Γ ⊢[PRAAx] lt a (I.bd zero p))
    (hv : Γ ⊢[PRAAx] I.V (I.h p) a p ≐ one) (ht : Γ ⊢[PRAAx] lt t (I.h p)) :
    Γ ⊢[PRAAx] neg (I.t t (chain I (sLeast I) t p) (chain I (sLeast I) (succ t) p) p ≐ zero) :=
  chain_edge (Prf.andE₁ (start_spec I ha hv)) (Prf.andE₁ (Prf.andE₂ (start_spec I ha hv))) ht

end LeanProofs.IPRA.Foundations.LeastViablePath
