import IPRADerivations.Foundations.FrontierSoundness
import IPRADerivations.Core.Search
import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.OrderCertificates

/-!
# The median index of a finite weighted law

Packet: `probability/median_ipra_constructive_proofs`, Theorem "Existence and median interval for a
finite law": "Let `r` be the least index with `2 ∑_{j ≤ r} w_j ≥ W` … Minimality of `r` gives strictly
less than half the weight below `a_r`, while the defining inequality gives at most half above it. Thus
`a_r` is a median."

For weights `w(j, p)`, `j ≤ N′`, of a law on a sorted support, with the total `W = ∑_{j ≤ N′} w_j` and the
prefix sums `C(k) = ∑_{j<k} w_j`:

* `hfB w`: the test `W ∸ 2 C(j + 1)`, zero exactly when the prefix through `j` has at least half of the
  weight (the total is carried in the parameter `⟨W, p⟩`);
* `mi w N′ p`: the least index `r ≤ N′` passing the test, by the bounded search of `Core/Search`;
* `median_index`: `r ≤ N′`, `W ≤ 2 C(r + 1)` and `2 C(r) ≤ W`. The weight strictly below the `r`-th
  point is `C(r)` and the weight strictly above it is `W − C(r + 1)`, so both are at most `W/2`: the
  `r`-th point is a weighted median, an explicit witness of existence. No positivity of `W` is needed.

The symmetric greatest index `s` and the description of the whole median interval `[a_r, a_s]` are not
derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianIndex

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Search (mu search_minimal search_found)
open LeanProofs.IPRA.Foundations.FrontierSoundness (rdB inst2_rdB)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Index

variable (w : PTm 2)

/-- `T ∸ 2 ∑_{i ≤ j} w_i`; variables `0 = j`, `1 = y = ⟨T, p⟩`. -/
def hfB : PTm 2 := monus (fstT (var 1)) (two * ap2 (sumF (rdB w)) (succ (var 0)) (var 1))

theorem inst2_hfB (j y : PTm n) :
    inst2 (hfB w) j y = monus (fstT y) (two * ap2 (sumF (rdB w)) (succ j) y) := by
  simp [inst2, hfB]

/-- The prefix sums with the tagged parameter. -/
theorem prefix_at (k T p : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rdB w)) k (pairT T p) ≐ ap2 (sumF w) k p := by
  refine sum_congr_bounded (rdB w) w (pairT T p) p k (.allI (.impI ?_))
  rw [inst2_rdB, shift_pairT]
  exact congrInst2 w (.eqRefl _) (snd_pair _ _)

theorem hf_zero_of {j T p : PTm n} (h : Γ ⊢[PRAAx] le T (two * ap2 (sumF w) (succ j) p)) :
    Γ ⊢[PRAAx] inst2 (hfB w) j (pairT T p) ≐ zero := by
  rw [inst2_hfB]
  exact le_congr (fst_pair T p).eqSymm
    (congrMul (.eqRefl two) (prefix_at w (succ j) T p)).eqSymm h

theorem of_hf_zero {j T p : PTm n} (h : Γ ⊢[PRAAx] inst2 (hfB w) j (pairT T p) ≐ zero) :
    Γ ⊢[PRAAx] le T (two * ap2 (sumF w) (succ j) p) := by
  rw [inst2_hfB] at h
  exact le_congr (fst_pair T p) (congrMul (.eqRefl two) (prefix_at w (succ j) T p)) h

/-- The least index whose prefix has at least half of the total weight. -/
abbrev mi (N' p : PTm n) : PTm n :=
  mu (hfB w) (succ N') (pairT (ap2 (sumF w) (succ N') p) p)

/-- The median index: `r ≤ N′`, `W ≤ 2 C(r + 1)` and `2 C(r) ≤ W`. -/
theorem median_index (N' p : PTm n) :
    Γ ⊢[PRAAx] lt (mi w N' p) (succ N') ⋏
      (le (ap2 (sumF w) (succ N') p) (two * ap2 (sumF w) (succ (mi w N' p)) p) ⋏
        le (two * ap2 (sumF w) (mi w N' p) p) (ap2 (sumF w) (succ N') p)) := by
  have hT : Γ ⊢[PRAAx] le (ap2 (sumF w) (succ N') p) (two * ap2 (sumF w) (succ N') p) := by
    ipra_le 𝔟(ap2 (sumF w) (succ N') p)
  have hlast : Γ ⊢[PRAAx] lt N' (succ N') := le_refl (succ N')
  have f := search_found (f := hfB w) (hf_zero_of w hT) hlast
  refine .andI (Prf.andE₁ f) (.andI (of_hf_zero w (Prf.andE₁ (Prf.andE₂ f))) ?_)
  refine .orE (zero_or_succ (mi w N' p)) ?_ ?_
  · have hz : ((mi w N' p ≐ zero) :: Γ) ⊢[PRAAx] mi w N' p ≐ zero := Prf.hyp0
    have e := natEq ((congrAp2 (sumF w) hz (.eqRefl p)).eqTrans (sum_zero w p))
    ipra_le 𝔟(ap2 (sumF w) (succ N') p) using linear_combination -2 * e
  · have hr : ((mi w N' p ≐ succ (pred (mi w N' p))) :: Γ) ⊢[PRAAx]
        mi w N' p ≐ succ (pred (mi w N' p)) := Prf.hyp0
    have hlt : ((mi w N' p ≐ succ (pred (mi w N' p))) :: Γ) ⊢[PRAAx]
        lt (pred (mi w N' p)) (mi w N' p) :=
      lt_congr (.eqRefl _) hr.eqSymm (le_refl (succ (pred (mi w N' p))))
    have nz := search_minimal (f := hfB w) hlt
    refine .orE (lt_or_le (two * ap2 (sumF w) (succ (pred (mi w N' p))) p)
      (ap2 (sumF w) (succ N') p)) ?_ ?_
    · exact le_congr
        (congrMul (.eqRefl two) (congrAp2 (sumF w) hr.wk.eqSymm (.eqRefl p)))
        (.eqRefl _) (le_of_lt Prf.hyp0)
    · exact .botE _ (Prf.impE nz.wk (hf_zero_of w Prf.hyp0))

end Index

end LeanProofs.IPRA.Probability.MedianIndex
