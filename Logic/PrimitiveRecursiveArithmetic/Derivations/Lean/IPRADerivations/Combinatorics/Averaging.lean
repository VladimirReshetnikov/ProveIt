import IPRADerivations.Combinatorics.UniformThinning
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.OrderCertificates

/-!
# Averaging arguments with primitive recursive witnesses

Packet: `combinatorics/Combinatorics-iPRA`, `graphs.tex`, results 19 and 33:

* "A graph with `e` edges has a partition into two classes with at least `⌈e/2⌉` crossing edges … The largest
  cut is at least the average and is returned by a mask scan";
* "If all colorings had a bad set, assigning the first one to each would give at least `2^M` pairs.
  Equivalently the row counts have a zero, found by the first-success scan" (the first-moment lower bound for
  `R(k, k)`).

Both are instances of two uniform statements about bounded sums of a body `c(i, x)` over `i < N` (`N` an
object-level term), with the witness found by bounded search (`Combinatorics/UniformThinning`):

* `average`: if `∑_{i<N} b(i, x) ≤ ∑_{i<N} c(i, x)` and `0 < N`, the first row with `b(i, x) ≤ c(i, x)` is a
  primitive recursive term below `N` (the largest value is at least the average: take `b` constant);
* `zero_row`: if `∑_{i<N} c(i, x) < N`, the first row with `c(i, x) = 0` is a primitive recursive term below
  `N` (fewer bad pairs than rows leave a row without a bad set).
-/

namespace LeanProofs.IPRA.Combinatorics.Averaging

open_ipra
open LeanProofs.IPRA.Foundations.BoundedReflection (wit)
open LeanProofs.IPRA.Combinatorics.UniformThinning (exc thinning)
open LeanProofs.IPRA.Probability.Variance (sum_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Some row is at least its threshold when the sums are: the first such row, as a term. -/
theorem average (c b : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] le (ap2 (sumF b) N x) (ap2 (sumF c) N x)) (hN : Γ ⊢[PRAAx] lt zero N) :
    Γ ⊢[PRAAx] lt (wit (exc (addBody c (one : PTm 2)) b) N x) N ⋏
      le (inst2 b (wit (exc (addBody c (one : PTm 2)) b) N x) x)
        (inst2 c (wit (exc (addBody c (one : PTm 2)) b) N x) x) := by
  have hN' : Γ ⊢[PRAAx] le (succ zero) N := hN
  have h' : Γ ⊢[PRAAx] lt (ap2 (sumF b) N x) (ap2 (sumF (addBody c (one : PTm 2))) N x) := by
    show Γ ⊢[PRAAx] le (succ (ap2 (sumF b) N x)) (ap2 (sumF (addBody c (one : PTm 2))) N x)
    ipra_le sl h + sl hN' with natEq (sum_add (Γ := Γ) c (one : PTm 2) N x) + natEq (sum_one (Γ := Γ) N x)
  have t := thinning (addBody c (one : PTm 2)) b N x h'
  have e2 : inst2 (addBody c (one : PTm 2)) (wit (exc (addBody c (one : PTm 2)) b) N x) x =
      inst2 c (wit (exc (addBody c (one : PTm 2)) b) N x) x + one := by
    rw [inst2_addBody]
    simp [inst2]
  have t₂ := Prf.andE₂ t
  rw [e2] at t₂
  have t₃ : Γ ⊢[PRAAx] le (succ (inst2 b (wit (exc (addBody c (one : PTm 2)) b) N x) x))
      (inst2 c (wit (exc (addBody c (one : PTm 2)) b) N x) x + succ zero) := t₂
  refine .andI (Prf.andE₁ t) ?_
  ipra_le sl t₃

/-- Fewer marks than rows leave an unmarked row: the first row with `c(i, x) = 0`, as a term. -/
theorem zero_row (c : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] lt (ap2 (sumF c) N x) N) :
    Γ ⊢[PRAAx] lt (wit (exc (one : PTm 2) c) N x) N ⋏
      (inst2 c (wit (exc (one : PTm 2) c) N x) x ≐ zero) := by
  have h' : Γ ⊢[PRAAx] lt (ap2 (sumF c) N x) (ap2 (sumF (one : PTm 2)) N x) :=
    le_congr (.eqRefl _) (sum_one N x).eqSymm h
  have t := thinning (one : PTm 2) c N x h'
  have e1 : inst2 (one : PTm 2) (wit (exc (one : PTm 2) c) N x) x = one := by simp [inst2]
  have t₂ := Prf.andE₂ t
  rw [e1] at t₂
  have t₃ : Γ ⊢[PRAAx] le (succ (inst2 c (wit (exc (one : PTm 2) c) N x) x)) (succ zero) := t₂
  have hz : Γ ⊢[PRAAx] le (inst2 c (wit (exc (one : PTm 2) c) N x) x) zero := by
    ipra_le sl t₃
  exact .andI (Prf.andE₁ t) (le_antisymm hz (zero_le _))

end LeanProofs.IPRA.Combinatorics.Averaging
