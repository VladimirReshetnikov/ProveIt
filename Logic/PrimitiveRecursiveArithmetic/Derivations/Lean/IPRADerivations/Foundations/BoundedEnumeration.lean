import IPRADerivations.Foundations.FilteredEnumeration
import IPRADerivations.Core.Division
import IPRADerivations.Probability.UnionUtility

/-!
# The complete duplicate-free list of the solutions below a height bound

The conversion "height bound to complete list" of the framework packets:

* `ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`, `ipra_kifcr_framework_2026-11-16`,
  `ipra_kifcs_framework_2026-11-16`: `thm:height-list`, direction (i) ⇒ (ii);
* `ocipra_framework_2026-11-15`: `thm:height-list` ("Height-to-list conversion") and `cor:bounded-list`;
* `ipra_proof_carrying_observation_graphs_2026-11-15`: Theorem "Height-to-list";
* `ipra_pfig_framework_2026-11-15`: Theorem "Height bound implies complete list".

The candidates are the numbers `i < N` and the verifier is the zero test `f(i, x) = 0`. The retained set of
`Foundations/FilteredEnumeration` is the validity bit `v_i = 1 ∸ sg f(i, x)`, which is nonzero exactly for
solutions; the list is `FilteredEnumeration.sel` and its length is `cnt = rank N`, the number of solutions
below `N`. This module states the list in terms of the verifier and adds strict monotonicity and the
height-bound wrapper:

* `kept_of_valid`, `valid_of_kept`: `v_i ≠ 0 ↔ f(i, x) = 0`;
* `listed` (completeness): a solution `i < N` is the entry of index `rank i`, and `rank i < cnt`;
* `entry` (soundness): for `r < cnt`, the entry is below `N`, is a solution, and has rank `r`;
* `sel_strict` (no duplicates): `r < r' < cnt` gives `entry r < entry r'`;
* `complete_of_bound`: under a height bound `∀ y. f(y, x) = 0 → y < N`, every solution `y` is listed.

The converse conversion, direction (ii) ⇒ (i) of `thm:height-list` ("List-to-height" of the PCOG packet,
"Complete list implies height bound" of the PFIG packet): for a list `ℓ(k, x)`, `k < m`, and a height term
`h(y, x)`, the bound is the running maximum `H = max_{k<m} h(ℓ(k, x), x)` (`UnionUtility.Mx`), and

* `bound_of_list`: a point `y` that occurs in the list, `∃ k < m. y = ℓ(k, x)`, has `h(y, x) ≤ H`.

For a complete list the premise holds for every solution, so `H` dominates the height of every solution.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BoundedEnumeration

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec sel_rank rank_lt_size rank_mono)
open LeanProofs.IPRA.Foundations.BoundedFormulas (sg_of_pos sg_of_zero not_of_zero not_of_one)
open LeanProofs.IPRA.Probability.UnionUtility (Mx mx_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The validity bit `v_i = 1 ∸ sg f(i, x)`: the retained set of the solutions of `f(i, x) = 0`. -/
abbrev vb (f : PTm 2) : PTm 2 := monus (succ zero) (sg f)

theorem inst2_vb (f : PTm 2) (i x : PTm n) : inst2 (vb f) i x = monus (succ zero) (sg (inst2 f i x)) := by
  simp [inst2]

section Bits

variable {f : PTm 2} {i x : PTm n}

theorem vb_one (h : Γ ⊢[PRAAx] inst2 f i x ≐ zero) : Γ ⊢[PRAAx] inst2 (vb f) i x ≐ succ zero := by
  rw [inst2_vb]; exact not_of_zero (sg_of_zero h)

theorem vb_zero {c : PTm n} (h : Γ ⊢[PRAAx] inst2 f i x ≐ succ c) : Γ ⊢[PRAAx] inst2 (vb f) i x ≐ zero := by
  rw [inst2_vb]; exact not_of_one (sg_of_pos h)

/-- A solution is retained. -/
theorem kept_of_valid (h : Γ ⊢[PRAAx] inst2 f i x ≐ zero) : Γ ⊢[PRAAx] neg (inst2 (vb f) i x ≐ zero) :=
  .impI (succ_ne_zero' _ ((vb_one h.wk).eqSymm.eqTrans Prf.hyp0))

/-- A retained candidate is a solution. -/
theorem valid_of_kept (h : Γ ⊢[PRAAx] neg (inst2 (vb f) i x ≐ zero)) : Γ ⊢[PRAAx] inst2 f i x ≐ zero :=
  .orE (zero_or_succ (inst2 f i x)) Prf.hyp0 (.botE _ (Prf.impE h.wk (vb_zero Prf.hyp0)))

end Bits

section List

variable {f : PTm 2} {N x : PTm n}

/-- Completeness: a solution `i < N` is the entry of index `rank i`, which is below the count. -/
theorem listed {i : PTm n} (hi : Γ ⊢[PRAAx] lt i N) (hv : Γ ⊢[PRAAx] inst2 f i x ≐ zero) :
    Γ ⊢[PRAAx] (sel (vb f) (rank (vb f) i x) N x ≐ i) ⋏ lt (rank (vb f) i x) (rank (vb f) N x) :=
  .andI (sel_rank (vb f) hi (kept_of_valid hv)) (rank_lt_size (vb f) hi (kept_of_valid hv))

/-- Soundness: for `r` below the count, the entry is below `N`, is a solution, and has rank `r`. -/
theorem entry {r : PTm n} (hr : Γ ⊢[PRAAx] lt r (rank (vb f) N x)) :
    Γ ⊢[PRAAx] lt (sel (vb f) r N x) N ⋏
      ((inst2 f (sel (vb f) r N x) x ≐ zero) ⋏ (rank (vb f) (sel (vb f) r N x) x ≐ r)) := by
  have s := sel_spec (vb f) hr
  exact .andI (Prf.andE₁ s) (.andI (valid_of_kept (Prf.andE₁ (Prf.andE₂ s))) (Prf.andE₂ (Prf.andE₂ s)))

/-- No duplicates: the list is strictly increasing. -/
theorem sel_strict {r r' : PTm n} (hrr : Γ ⊢[PRAAx] lt r r') (hr' : Γ ⊢[PRAAx] lt r' (rank (vb f) N x)) :
    Γ ⊢[PRAAx] lt (sel (vb f) r N x) (sel (vb f) r' N x) := by
  have hr : Γ ⊢[PRAAx] lt r (rank (vb f) N x) := lt_of_lt_of_le hrr (le_of_lt hr')
  have e := Prf.andE₂ (Prf.andE₂ (sel_spec (vb f) hr))
  have e' := Prf.andE₂ (Prf.andE₂ (sel_spec (vb f) hr'))
  refine .orE (lt_or_le (sel (vb f) r N x) (sel (vb f) r' N x)) Prf.hyp0 ?_
  have hm : (le (sel (vb f) r' N x) (sel (vb f) r N x) :: Γ) ⊢[PRAAx]
      le (rank (vb f) (sel (vb f) r' N x) x) (rank (vb f) (sel (vb f) r N x) x) :=
    rank_mono (vb f) Prf.hyp0 x
  exact le_lt_absurd _ (le_congr e'.wk e.wk hm) hrr.wk

end List

/-- From a height bound to the complete list: if `∀ y. f(y, x) = 0 → y < N`, every solution `y` is the entry
of index `rank y`, and that index is below the count. -/
theorem complete_of_bound {f : PTm 2} {N x y : PTm n}
    (hb : Γ ⊢[PRAAx] Fm.all ((inst2 f (var 0) (Syn.shift x) ≐ zero) ⟶ lt (var 0) (Syn.shift N)))
    (hy : Γ ⊢[PRAAx] inst2 f y x ≐ zero) :
    Γ ⊢[PRAAx] (sel (vb f) (rank (vb f) y x) N x ≐ y) ⋏ lt (rank (vb f) y x) (rank (vb f) N x) := by
  have a := Prf.allE y hb
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at a
  exact listed (Prf.impE a hy) hy

/-! ## From a complete list to a height bound -/

/-- The heights of the list entries, over `0 = k`, `1 = x`: `h(ℓ(k, x), x)`. -/
def hL (h l : PTm 2) : PTm 2 := Syn.subst ![l, var 1] h

theorem inst2_hL (h l : PTm 2) (k x : PTm n) : inst2 (hL h l) k x = inst2 h (inst2 l k x) x := by
  simp only [hL, inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

/-- A point that occurs in the list has height at most the maximum height of the list. -/
theorem bound_of_list {h l : PTm 2} {m x y : PTm n}
    (hy : Γ ⊢[PRAAx] Fm.ex (lt (var 0) (Syn.shift m) ⋏ (Syn.shift y ≐ inst2 l (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (inst2 h y x) (Mx (hL h l) m x) := by
  refine .exE hy ?_
  have w : ((lt (var 0) (Syn.shift m) ⋏ (Syn.shift y ≐ inst2 l (var 0) (Syn.shift x))) :: Γ.map Fm.shift)
      ⊢[PRAAx] lt (var 0) (Syn.shift m) ⋏ (Syn.shift y ≐ inst2 l (var 0) (Syn.shift x)) := Prf.hyp0
  have u := mx_upper (hL h l) (x := Syn.shift x) (Prf.andE₁ w)
  rw [inst2_hL] at u
  have r := le_congr (congrInst2 h (Prf.andE₂ w).eqSymm (.eqRefl (Syn.shift x))) (.eqRefl _) u
  simp only [Fm.shift, subst_le, subst_inst2, subst_ap2]
  exact r

end LeanProofs.IPRA.Foundations.BoundedEnumeration
