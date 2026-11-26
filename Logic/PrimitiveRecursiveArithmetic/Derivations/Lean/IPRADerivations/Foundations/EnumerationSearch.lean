import IPRADerivations.Foundations.BoundedEnumeration
import IPRADerivations.Core.Header

/-!
# Complete search through an enumeration

Packet: `foundations/ipra_uniformity_framework_2026-11-15`, `report.tex`, Theorem `thm:search`
("Uniform search completeness"): "If iPRA proves `∀ x [W(p, x) = 1 ⇒ h(p, x) ≤ B(p)]` and proves the
bounded enumeration-cover equation, then it proves that `W(p, x) = 1` exactly when `x` occurs on the
computed finite list … The list and its length are PR in `p`."

The candidates are produced by an enumeration `E(j, x)`, `j < N` (a body in the index `j` and the
parameter `x`), and the verifier is a zero test `g(y, x) = 0`. The list is obtained by scanning `j < N`
and retaining the indices with `g(E(j, x), x) = 0`: with the composed body `hL g E` of
`Foundations/BoundedEnumeration`, its length is `rank (vb (hL g E)) N x` and its `r`-th entry is
`E(sel (vb (hL g E)) r N x, x)`.

* `search_sound`: for `r` below the length, the selected index is below `N` and the entry passes the
  verifier;
* `search_complete`: if `y = E(j, x)` for some `j < N` (the instance of the cover that the height bound
  provides for a solution `y`) and `g(y, x) = 0`, then `y` is the entry of index `rank j`, which is below
  the length.

The existential form of the cover is eliminated by the user; the height bound enters only through the
cover. Deduplication of equal values `E(j) = E(j′)` is not performed: the list is duplicate-free in the
indices (`sel_strict`), not in the values.
-/

namespace LeanProofs.IPRA.Foundations.EnumerationSearch

open_ipra
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel)
open LeanProofs.IPRA.Foundations.BoundedEnumeration (vb hL inst2_hL listed entry)

variable {n : ℕ} {Γ : List (Fm PTm n)} {g E : PTm 2} {N x : PTm n}

/-- Soundness: every entry of the list passes the verifier. -/
theorem search_sound {r : PTm n} (hr : Γ ⊢[PRAAx] lt r (rank (vb (hL g E)) N x)) :
    Γ ⊢[PRAAx] lt (sel (vb (hL g E)) r N x) N ⋏
      (inst2 g (inst2 E (sel (vb (hL g E)) r N x) x) x ≐ zero) := by
  have e := entry (f := hL g E) hr
  have e₂ := Prf.andE₁ (Prf.andE₂ e)
  rw [inst2_hL] at e₂
  exact .andI (Prf.andE₁ e) e₂

/-- Completeness: a solution covered by the enumeration occurs on the list. -/
theorem search_complete {j y : PTm n} (hj : Γ ⊢[PRAAx] lt j N) (hE : Γ ⊢[PRAAx] inst2 E j x ≐ y)
    (hy : Γ ⊢[PRAAx] inst2 g y x ≐ zero) :
    Γ ⊢[PRAAx] (inst2 E (sel (vb (hL g E)) (rank (vb (hL g E)) j x) N x) x ≐ y) ⋏
      lt (rank (vb (hL g E)) j x) (rank (vb (hL g E)) N x) := by
  have hf : Γ ⊢[PRAAx] inst2 (hL g E) j x ≐ zero := by
    rw [inst2_hL]
    exact (congrInst2 g hE (.eqRefl x)).eqTrans hy
  have l := listed (f := hL g E) hj hf
  exact .andI ((congrInst2 E (Prf.andE₁ l) (.eqRefl x)).eqTrans hE) (Prf.andE₂ l)

end LeanProofs.IPRA.Foundations.EnumerationSearch
