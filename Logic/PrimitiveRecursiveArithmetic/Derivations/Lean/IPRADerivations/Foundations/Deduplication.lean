import IPRADerivations.Foundations.FiniteCoverSkeleton
import IPRADerivations.Core.Header

/-!
# Removing duplicates from a finite list (`ipra_presentations_to_witnesses`, `prop:reconstruction`)

Packet: `foundations/ipra_presentations_to_witnesses`, proposition `prop:reconstruction`: "Then
filter `⋃_{q ∈ G} B(q)` by `V` and remove duplicates. ... A finite deduplication pass preserves
membership. Its invariant equates membership in the output prefix with membership in the
processed input prefix; bounded folds make that invariant quantifier-free."

For a list `L_i = l(i)`, `i < N`, the deduplicated list keeps the first occurrence of each
value: the index `r` is kept when the first-match scan of `L_r` returns `r`. This is the
skeleton of `Foundations/FiniteCoverSkeleton` for the equality relation (`eqE`, `eq_laws`), so no
separate prefix invariant is needed.

* `first N x`: the least `i < N` with `L_i = x`;
* `dedup_mem`: if `x = L_j` for some `j < N`, then `first N x < N`, that index is kept, and
  `L_{first N x} = x`: every member of the list is a member of the deduplicated list;
* `dedup_nodup`: two kept indices with equal entries are equal: the deduplicated list has no
  repetitions;
* `dedup_first`: a kept index is the first occurrence of its entry: `L_i ≠ L_r` for `i < r`;
* `dedup_mem_closed`, `dedup_nodup_closed`: closed sentences.

Membership in the deduplicated list implies membership in the list by construction (a kept
index is an index). The compaction of the kept indices to an initial segment is `rank`/`sel` of
`Foundations/FilteredEnumeration`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.Deduplication

open_ipra
open LeanProofs.IPRA.Foundations.FiniteCoverSkeleton

variable {k : ℕ} {Γ : List (Fm PTm k)}

variable (l : PTm 1)

/-- The first occurrence of `x` in the list: the least `i < N` with `L_i = x`. -/
abbrev first (N x : PTm k) : PTm k := rep eqE l N x

/-- The index `r` is kept by the deduplication pass. -/
abbrev keptIdx (N r : PTm k) : Fm PTm k := kept eqE l N r

/-- Every member of the list is a member of the deduplicated list. -/
theorem dedup_mem {N j x : PTm k} (hj : Γ ⊢[PRAAx] lt j N)
    (hx : Γ ⊢[PRAAx] inst1 l j ≐ x) :
    Γ ⊢[PRAAx] lt (first l N x) N ⋏
      (keptIdx l N (first l N x) ⋏ (inst1 l (first l N x) ≐ x)) := by
  have f := rep_found (e := eqE) (l := l) hj (eqE_of_eq hx)
  have hr := Prf.andE₁ f
  exact .andI hr (.andI (rep_idem eq_laws hr) (eq_of_eqE (Prf.andE₁ (Prf.andE₂ f))))

/-- The deduplicated list has no repetitions. -/
theorem dedup_nodup {N r s : PTm k} (hr : Γ ⊢[PRAAx] keptIdx l N r)
    (hs : Γ ⊢[PRAAx] keptIdx l N s) (h : Γ ⊢[PRAAx] inst1 l r ≐ inst1 l s) :
    Γ ⊢[PRAAx] r ≐ s :=
  kept_inj eq_laws hr hs (eqE_of_eq h)

/-- A kept index is the first occurrence of its entry. -/
theorem dedup_first {N r i : PTm k} (hr : Γ ⊢[PRAAx] keptIdx l N r)
    (hi : Γ ⊢[PRAAx] lt i r) : Γ ⊢[PRAAx] neg (inst1 l i ≐ inst1 l r) :=
  .impI (.impE (kept_scan (e := eqE) hr hi).wk (eqE_of_eq Prf.hyp0))

/-- Membership is preserved, as a closed sentence. Variables: `0 = N`, `1 = j`. -/
theorem dedup_mem_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶
      (lt (first l (var 0) (inst1 l (var 1))) (var 0) ⋏
        (keptIdx l (var 0) (first l (var 0) (inst1 l (var 1))) ⋏
          (inst1 l (first l (var 0) (inst1 l (var 1))) ≐ inst1 l (var 1))))) :=
  closeUniv 2 (.impI (dedup_mem l Prf.hyp0 (.eqRefl _)))

/-- No repetitions, as a closed sentence. Variables: `0 = N`, `1 = r`, `2 = s`. -/
theorem dedup_nodup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (keptIdx l (var 0) (var 1) ⟶ keptIdx l (var 0) (var 2) ⟶
      (inst1 l (var 1) ≐ inst1 l (var 2)) ⟶ (var 1 ≐ var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (dedup_nodup l hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Foundations.Deduplication
