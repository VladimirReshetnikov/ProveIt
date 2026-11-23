import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Analysis.PowerSums

/-!
# Finite thinning, uniformly in the number of classes

Packet: `combinatorics/ramsey_ipra`, `ramsey.tex`, "Finite thinning": "If more than `qk` candidates receive
one of `q` labels, at least one label occurs more than `k` times. Compute all `q` counts and take the first
with count greater than `k`. Such a count exists because the sum of the counts is the number of candidates."

Here the number of classes is an object-level term `N` (not a numeral of the metatheory), the class counts are
a body `c(i, x)` and the thresholds a body `b(i, x)` (the constant `k` for finite thinning), and the selected
class is the primitive-recursive witness of the bounded search:

* `exc c b`: the excess `c(i, x) ∸ b(i, x)`;
* `exists_excess`: `∑_{i<N} b(i, x) < ∑_{i<N} c(i, x)` makes the bit of `∃ i < N, c(i, x) > b(i, x)` equal to
  one (if the bit were zero, every summand would be dominated and so would the sums);
* `thinning`: the first such class `w = wit (exc c b) N x` satisfies `w < N` and `b(w, x) < c(w, x)`;
* `thinning_least`: no earlier class exceeds its threshold.

For a fixed number of classes and an object-level disjunction instead of a witness, see
`Combinatorics/RamseyBounds.thinning`.
-/

namespace LeanProofs.IPRA.Combinatorics.UniformThinning

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim ex_none ex_least)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (c b : PTm 2)

/-- The excess `c(i, x) ∸ b(i, x)` of a class count over its threshold. -/
def exc : PTm 2 := monus c b

theorem inst2_exc (i x : PTm n) : inst2 (exc c b) i x = monus (inst2 c i x) (inst2 b i x) := by
  simp [inst2, exc]

/-- If the counts sum to more than the thresholds, some class exceeds its threshold: the bit of the bounded
existential is one. -/
theorem exists_excess (N x : PTm n) (h : Γ ⊢[PRAAx] lt (ap2 (sumF b) N x) (ap2 (sumF c) N x)) :
    Γ ⊢[PRAAx] exB (exc c b) N x ≐ one := by
  refine .orE (ex_cases (exc c b) N x) ?_ Prf.hyp0
  have h0 : ((exB (exc c b) N x ≐ zero) :: Γ) ⊢[PRAAx] exB (exc c b) N x ≐ zero := Prf.hyp0
  have hle : ((exB (exc c b) N x ≐ zero) :: Γ) ⊢[PRAAx] le (ap2 (sumF c) N x) (ap2 (sumF b) N x) := by
    refine sum_le c b x N (.allI (.impI ?_))
    have h0s := (h0.shift).wk (ψ := lt (var 0) (Syn.shift N))
    have e : Fm.shift (exB (exc c b) N x ≐ zero) = (exB (exc c b) (Syn.shift N) (Syn.shift x) ≐ zero) := by
      simp [Fm.shift, Syn.shift]
    rw [e] at h0s
    have z := ex_none (exc c b) h0s Prf.hyp0
    rw [inst2_exc] at z
    exact z
  exact not_succ_le_self _ _ (le_trans h.wk hle)

/-- Finite thinning with its witness: the first class whose count exceeds its threshold. -/
theorem thinning (N x : PTm n) (h : Γ ⊢[PRAAx] lt (ap2 (sumF b) N x) (ap2 (sumF c) N x)) :
    Γ ⊢[PRAAx] lt (wit (exc c b) N x) N ⋏
      lt (inst2 b (wit (exc c b) N x) x) (inst2 c (wit (exc c b) N x) x) := by
  have w := ex_elim (exc c b) (exists_excess c b N x h)
  have w₂ := Prf.andE₂ w
  rw [inst2_exc] at w₂
  refine .andI (Prf.andE₁ w) ?_
  refine .orE (lt_or_le (inst2 b (wit (exc c b) N x) x) (inst2 c (wit (exc c b) N x) x)) Prf.hyp0 ?_
  exact .botE _ (.impE w₂.wk Prf.hyp0)

/-- The witness is the first such class: an earlier class does not exceed its threshold. -/
theorem thinning_least {N j x : PTm n} (hj : Γ ⊢[PRAAx] lt j (wit (exc c b) N x)) :
    Γ ⊢[PRAAx] le (inst2 c j x) (inst2 b j x) := by
  have z := ex_least (exc c b) hj
  rw [inst2_exc] at z
  exact z

end LeanProofs.IPRA.Combinatorics.UniformThinning
