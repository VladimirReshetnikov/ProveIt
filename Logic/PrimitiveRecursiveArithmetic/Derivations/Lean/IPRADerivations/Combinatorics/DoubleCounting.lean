import IPRADerivations.Core.CertificateTactics

/-!
# Double counting of a finite table

Packet: `combinatorics/Combinatorics-iPRA`, `foundations.tex`, result 02 (`lem:fiber`, "Counting fibers and
cancelling signs"): "For explicitly bounded sets `X, Y` and a coded relation `R`, summing its row counts gives the
same total as summing its column counts. ... An injection gives the corresponding inequality." The table is a
family `M i j` of integer terms indexed by `Fin a × Fin b`. As iPRA derivations:

* `exchange`: the row sums and the column sums have the same total;
* `count_le`: if every row sum is at least `r` and every column sum is at most `c`, then `a r ≤ b c`;
* `injection_count`: rows summing to at least one and columns to at most one give `a ≤ b` ("Apply this to
  `[x ∈ X][F(x) = y][y ∈ Y]`, where each valid row sums to one and columns to one or at most one");
* `packing_bound`: the counting step of the Hamming bound of result 48 (`structure.tex`), "Radius-`t` balls about
  codewords are disjoint ... Counting all their points gives the first bound": `a V ≤ b` for a membership table
  of `a` balls of volume at least `V` among `b` words, each word in at most one ball;
* `covering_bound`: the counting step of the Gilbert bound of result 48, "balls of radius `d − 1` around the final
  code cover all `q^n` words. Counting them with multiplicity gives the opposite inequality": `b ≤ a V`;
* `colour_classes`: `n ≤ α χ` of Proposition 13.1 (`co:greedy`) of `combinatorics/graph-ipra`, `tex/color.tex`:
  "Each colour class is independent, so summing its size gives the second inequality".
* `weighted_count_le`: rows of sum at least `w_i` and columns of sum at most `c` give `∑_i w_i ≤ b c`: the counting
  step of the LYM inequality of result 40 (`structure.tex`), "A particular `j`-set appears in `j! (n − j)!`
  orders ... Count the pairs (order, selected prefix) by their two coordinates to obtain the inequality"
  `∑_j a_j j! (n − j)! ≤ r n!`, with the `n!` orders as columns, each meeting the family in at most `r` members;
  likewise the cyclic count `|F| n k! (n − k)! ≤ k n!` of result 41 (Erdős–Ko–Rado);
* `sumfree_columns`: the counting step of result 34 (`thm:graph-sumfree`, `graphs.tex`),
  "`3 ∑_{1 ≤ t < p} |B_t| = 3 |A| (q + 1) > |A| (p − 1)`" for `p = 3q + 2`: a table with `a + 1` rows of sum at
  least `q + 1` and `3q + 1` columns cannot have `3 · (column sum) ≤ a + 1` in every column.

Not derived: the sign-reversing involution of result 02, the ball volumes and the constructions of result 48,
the prime and the sum-free residues of result 34, and the extremal families of results 40 and 41.
-/

namespace LeanProofs.IPRA.Combinatorics.DoubleCounting

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n a b : ℕ} {Γ : List (Fm PTm n)}

/-- The row sums and the column sums of a finite table have the same total. -/
theorem exchange (M : Fin a → Fin b → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => ZT.sumFin fun j => M i j)
      (ZT.sumFin fun j => ZT.sumFin fun i => M i j) := by
  apply ZT.derive
  zsimp
  exact Finset.sum_comm

/-- Rows of sum at least `r` and columns of sum at most `c`: `a r ≤ b c`. -/
theorem count_le (M : Fin a → Fin b → ZT n) (r c : ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle r (ZT.sumFin fun j => M i j))
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => M i j) c) :
    Γ ⊢[PRAAx] zle (ZT.natLit a * r) (ZT.natLit b * c) := by
  have hsw : ∑ i, ∑ j, ZT.toZ Γ (M i j) = ∑ j, ∑ i, ZT.toZ Γ (M i j) := Finset.sum_comm
  refine zle_of_comb (∑ i, zsl (hr i) + ∑ j, zsl (hc j)) ?_
    (nn_add (nn_sum _ _ fun i _ => nn_zsl _) (nn_sum _ _ fun j _ => nn_zsl _))
  zsimp
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination (-1 : Groth (Q Γ)) * hsw

/-- Rows of sum at least `w_i` and columns of sum at most `c`: `∑_i w_i ≤ b c`. -/
theorem weighted_count_le (M : Fin a → Fin b → ZT n) (w : Fin a → ZT n) (c : ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle (w i) (ZT.sumFin fun j => M i j))
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => M i j) c) :
    Γ ⊢[PRAAx] zle (ZT.sumFin w) (ZT.natLit b * c) := by
  have hsw : ∑ i, ∑ j, ZT.toZ Γ (M i j) = ∑ j, ∑ i, ZT.toZ Γ (M i j) := Finset.sum_comm
  refine zle_of_comb (∑ i, zsl (hr i) + ∑ j, zsl (hc j)) ?_
    (nn_add (nn_sum _ _ fun i _ => nn_zsl _) (nn_sum _ _ fun j _ => nn_zsl _))
  zsimp
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination (-1 : Groth (Q Γ)) * hsw

/-- An injection of `a` rows into `b` columns: `a ≤ b`. -/
theorem injection_count (M : Fin a → Fin b → ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun j => M i j))
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => M i j) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (ZT.natLit a : ZT n) (ZT.natLit b) := by
  have h := count_le M _ _ hr hc
  ipra_zle (zsl h)

/-- Packing: `a` disjoint sets of at least `V` elements among `b` elements give `a V ≤ b`. -/
theorem packing_bound (M : Fin a → Fin b → ZT n) (V : ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle V (ZT.sumFin fun j => M i j))
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => M i j) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (ZT.natLit a * V) (ZT.natLit b) := by
  have h := count_le M _ _ hr hc
  ipra_zle (zsl h)

/-- Covering: `a` sets of at most `V` elements covering `b` elements give `b ≤ a V`. -/
theorem covering_bound (M : Fin a → Fin b → ZT n) (V : ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle (ZT.sumFin fun j => M i j) V)
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun i => M i j)) :
    Γ ⊢[PRAAx] zle (ZT.natLit b) (ZT.natLit a * V) := by
  have h := count_le (fun j i => M i j) _ _ hc hr
  ipra_zle (zsl h)

/-- `n ≤ α χ`: a colouring of `a` vertices with `b` colours whose classes have at most `α` vertices. -/
theorem colour_classes (C : Fin a → Fin b → ZT n) (alpha : ZT n)
    (hr : ∀ v, Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun c => C v c))
    (hc : ∀ c, Γ ⊢[PRAAx] zle (ZT.sumFin fun v => C v c) alpha) :
    Γ ⊢[PRAAx] zle (ZT.natLit a) (ZT.natLit b * alpha) := by
  have h := count_le C _ _ hr hc
  ipra_zle (zsl h)

/-- With `a + 1` rows of sum at least `q + 1` and `3q + 1` columns, some column has `3 · (sum) > a + 1`: the
contrary bounds are contradictory. -/
theorem sumfree_columns {q : ℕ} (M : Fin (a + 1) → Fin (3 * q + 1) → ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit (q + 1)) (ZT.sumFin fun t => M i t))
    (hc : ∀ t, Γ ⊢[PRAAx] zle (ZT.natLit 3 * ZT.sumFin fun i => M i t) (ZT.natLit (a + 1)))
    (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  have hsw : ∑ i, ∑ t, ZT.toZ Γ (M i t) = ∑ t, ∑ i, ZT.toZ Γ (M i t) := Finset.sum_comm
  refine false_of_comb (3 * ∑ i, zsl (hr i) + ∑ t, zsl (hc t) + ((2 * a + 1 : ℕ) : Groth (Q Γ))) ?_
    (nn_add (nn_add (nn_mul (nn_ofNat 3) (nn_sum _ _ fun i _ => nn_zsl _))
      (nn_sum _ _ fun t _ => nn_zsl _)) (nn_natCast _)) φ
  zsimp
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  push_cast
  linear_combination (3 : Groth (Q Γ)) * hsw

end LeanProofs.IPRA.Combinatorics.DoubleCounting
