import IPRADerivations.Combinatorics.FisherInequality

/-!
# Hall's condition: necessity, and regular bipartite graphs

Packets: `combinatorics/graph-ipra`, `tex/flows.tex`, Theorem 12.1 (`fl:hall`) and Corollary 12.2
(`fl:edgecolour`), and `combinatorics/Combinatorics-iPRA`, `graphs.tex`, results 28 and 29. A bipartite
(multi)graph with sides `Fin a` and `Fin b` is a matrix of integer terms; a left subset `X` is a vector `x` and
a right subset `Y` a vector `y`. As iPRA derivations:

* `double_weighted`: rows of sum at least `w_i` and columns of sum at most `u_j` give `∑ w_i ≤ ∑ u_j`;
* `hall_necessary`: if a matching saturates `X` into `Y ⊇ N(X)`, then `|X| ≤ |Y|`. For the table `T i j` of the
  matching edges leaving `X` (row sums at least `x_i`, column sums at most `y_j`) this is `double_weighted`;
* `regular_sides`: "Counting edges from each side gives `d a = d b`, whence `a = b`", for `d ≥ 1`;
* `regular_hall`: "The `d |X|` incidences from a left subset `X` arrive in `N(X)`, whose total degree is
  `d |N(X)|`. Positive cancellation proves Hall's condition": for row sums `d` and
  `∑_i A_{ij} x_i ≤ d y_j`, `|X| ≤ |N(X)|`.

Not derived: the sufficiency of Hall's condition (the flow construction), the deficiency formula, and the
decomposition into perfect matchings.
-/

namespace LeanProofs.IPRA.Combinatorics.HallCondition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.DesignCounts (flag_count)
open LeanProofs.IPRA.Combinatorics.FisherInequality (znn_of_pos_mul)
open Syn
open scoped Fm

variable {n a b : ℕ} {Γ : List (Fm PTm n)}

/-- Rows of sum at least `w_i` and columns of sum at most `u_j`: `∑ w_i ≤ ∑ u_j`. -/
theorem double_weighted (T : Fin a → Fin b → ZT n) (w : Fin a → ZT n) (u : Fin b → ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle (w i) (ZT.sumFin fun j => T i j))
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => T i j) (u j)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin w) (ZT.sumFin u) := by
  have hsw : ∑ i, ∑ j, ZT.toZ Γ (T i j) = ∑ j, ∑ i, ZT.toZ Γ (T i j) := Finset.sum_comm
  refine zle_of_comb (∑ i, zsl (hr i) + ∑ j, zsl (hc j)) ?_
    (nn_add (nn_sum _ _ fun i _ => nn_zsl _) (nn_sum _ _ fun j _ => nn_zsl _))
  zsimp
  simp only [Finset.sum_sub_distrib]
  linear_combination (-1 : Groth (Q Γ)) * hsw

/-- Necessity of Hall's condition: a matching saturating `X` into `Y` gives `|X| ≤ |Y|`. -/
theorem hall_necessary (T : Fin a → Fin b → ZT n) (x : Fin a → ZT n) (y : Fin b → ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle (x i) (ZT.sumFin fun j => T i j))
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => T i j) (y j)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin x) (ZT.sumFin y) :=
  double_weighted T x y hr hc

/-- A `d`-regular bipartite graph with `d ≥ 1` has sides of equal size. -/
theorem regular_sides (A : Fin a → Fin b → ZT n) (d : ZT n) (hd1 : Γ ⊢[PRAAx] zle (ZT.natLit 1) d)
    (hrow : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => A i j) d)
    (hcol : ∀ j, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => A i j) d) :
    (Γ ⊢[PRAAx] zle (ZT.natLit a : ZT n) (ZT.natLit b)) ∧
      (Γ ⊢[PRAAx] zle (ZT.natLit b : ZT n) (ZT.natLit a)) := by
  have e := ZT.toZ_eq (flag_count A d d hrow hcol)
  simp only [ZT.toZ_mul, ZT.toZ_natLit] at e
  have h1 : Γ ⊢[PRAAx] zle (ZT.natLit 0) (d * (ZT.natLit b - ZT.natLit a)) := by
    refine zle_of_comb 0 ?_ nn_zero
    zsimp
    linear_combination (-1 : Groth (Q Γ)) * e
  have h2 : Γ ⊢[PRAAx] zle (ZT.natLit 0) (d * (ZT.natLit a - ZT.natLit b)) := by
    refine zle_of_comb 0 ?_ nn_zero
    zsimp
    linear_combination e
  have k1 := znn_of_pos_mul hd1 h1
  have k2 := znn_of_pos_mul hd1 h2
  constructor
  · refine zle_of_comb (zsl k1) ?_ (nn_zsl _)
    zsimp
    ring
  · refine zle_of_comb (zsl k2) ?_ (nn_zsl _)
    zsimp
    ring

/-- `∑_j ∑_i a_{ij} x_i = d ∑_i x_i` when every row sums to `d`. -/
theorem regular_sum {R : Type*} [CommRing R] (A : Fin a → Fin b → R) (x : Fin a → R) (d : R)
    (hrow : ∀ i, ∑ j, A i j = d) : ∑ j, ∑ i, A i j * x i = d * ∑ i, x i := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, hrow i]

/-- Hall's condition in a regular bipartite graph: `|X| ≤ |N(X)|`. -/
theorem regular_hall (A : Fin a → Fin b → ZT n) (x : Fin a → ZT n) (y : Fin b → ZT n) (d : ZT n)
    (hd1 : Γ ⊢[PRAAx] zle (ZT.natLit 1) d)
    (hrow : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => A i j) d)
    (hN : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => A i j * x i) (d * y j)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin x) (ZT.sumFin y) := by
  have hrow1 : ∀ i, ∑ j, ZT.toZ Γ (A i j) = ZT.toZ Γ d := fun i => by
    have h := ZT.toZ_eq (hrow i)
    simpa only [ZT.toZ_sumFin] using h
  have S := regular_sum (fun i j => ZT.toZ Γ (A i j)) (fun i => ZT.toZ Γ (x i)) (ZT.toZ Γ d) hrow1
  beta_reduce at S
  have hpos : Γ ⊢[PRAAx] zle (ZT.natLit 0) (d * (ZT.sumFin y - ZT.sumFin x)) := by
    refine zle_of_comb (∑ j, zsl (hN j)) ?_ (nn_sum _ _ fun j _ => nn_zsl _)
    zsimp
    rw [Finset.sum_sub_distrib, S, ← Finset.mul_sum]
    ring
  have k := znn_of_pos_mul hd1 hpos
  refine zle_of_comb (zsl k) ?_ (nn_zsl _)
  zsimp
  ring

end LeanProofs.IPRA.Combinatorics.HallCondition
