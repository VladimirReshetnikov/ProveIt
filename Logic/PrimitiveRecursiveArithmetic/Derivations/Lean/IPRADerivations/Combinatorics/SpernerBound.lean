import IPRADerivations.Combinatorics.FisherInequality
import IPRADerivations.Combinatorics.DoubleCounting
import Mathlib.Data.Nat.Choose.Basic

/-!
# From the LYM inequality to Sperner's bound, and the Erdős–Ko–Rado cancellation

Packet: `combinatorics/Combinatorics-iPRA`, `structure.tex`, results 40 ("LYM, Sperner, and the general chain
bound") and 41 ("Erdős–Ko–Rado"). For every numeral `N`, by cancelling a positive factorial
(`Combinatorics/FisherInequality.znn_of_pos_mul`):

* `zle_natLit`: an inequality of numerals is derivable;
* `mid_weight`: `N! ≤ j! (N − j)! C(N, ⌊N/2⌋)` for `j ≤ N`, that is `C(N, j) ≤ C(N, ⌊N/2⌋)` (metatheory);
* `sperner_bound`: from the LYM inequality "`∑_j a_j j! (n − j)! ≤ r n!`" for level counts `a_j ≥ 0`
  (integer terms), `∑_j a_j ≤ r C(n, ⌊n/2⌋)`. For `r = 1`: "the maximum antichain size is `C(n, ⌊n/2⌋)`";
* `sperner_family`: the same from the incidence table itself. For a family of `a` sets of sizes `s_i` and the
  table of pairs (set, linear order displaying it as a prefix) over the `N!` orders: "A particular `j`-set
  appears in `j! (n − j)!` orders" (row sums at least `s_i! (N − s_i)!`) and every order displays at most `r`
  members (column sums at most `r`); then `a ≤ r C(N, ⌊N/2⌋)`. The count
  `Combinatorics/DoubleCounting.weighted_count_le` gives the LYM inequality, and the factorial is cancelled;
* `ekr_bound`: from "`|F| n k! (n − k)! ≤ k n!`", "the claimed bound after cancellation of positive factors":
  `|F| ≤ C(n − 1, k − 1)` (stated with `n = N + 1`, `k = K + 1`).

Not derived: the sharper bound by the `r` largest binomial coefficients for `r > 1`, the equality cases, the
enumeration of the orders displaying a set, and the arc lemma behind the Erdős–Ko–Rado count.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.SpernerBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.FisherInequality (znn_of_pos_mul)
open LeanProofs.IPRA.Combinatorics.DoubleCounting (weighted_count_le)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- An inequality between numerals. -/
theorem zle_natLit {m m' : ℕ} (h : m ≤ m') : Γ ⊢[PRAAx] zle (ZT.natLit m : ZT n) (ZT.natLit m') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine zle_of_comb (d : Groth (Q Γ)) ?_ (nn_natCast d)
  zsimp
  push_cast
  ring

/-- `N! ≤ j! (N − j)! C(N, ⌊N/2⌋)` for `j ≤ N`. -/
theorem mid_weight {N j : ℕ} (hj : j ≤ N) :
    N.factorial ≤ j.factorial * (N - j).factorial * N.choose (N / 2) := by
  have h := Nat.choose_mul_factorial_mul_factorial hj
  calc N.factorial = N.choose j * j.factorial * (N - j).factorial := h.symm
    _ ≤ N.choose (N / 2) * j.factorial * (N - j).factorial :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.choose_le_middle _ _))
    _ = j.factorial * (N - j).factorial * N.choose (N / 2) := by ring

/-- The cast of the slack `j! (N − j)! C(N, ⌊N/2⌋) − N!`. -/
theorem mid_weight_cast {R : Type*} [CommRing R] {N j : ℕ} (hj : j ≤ N) :
    ((j.factorial * (N - j).factorial * N.choose (N / 2) - N.factorial : ℕ) : R) =
      ((j.factorial * (N - j).factorial : ℕ) : R) * ((N.choose (N / 2) : ℕ) : R) - ((N.factorial : ℕ) : R) := by
  rw [Nat.cast_sub (mid_weight hj), Nat.cast_mul]

/-- `W (ρ c − ∑ a_j) = c (ρ W − ∑ a_j w_j) + ∑ a_j (w_j c − W)`. -/
theorem weight_identity {R : Type*} [CommRing R] {m : ℕ} (a w : Fin m → R) (c W ρ : R) :
    W * (ρ * c - ∑ j, a j) = c * (ρ * W - ∑ j, a j * w j) + ∑ j, a j * (w j * c - W) := by
  have e : ∑ j, a j * (w j * c - W) = c * ∑ j, a j * w j - W * ∑ j, a j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  ring

/-- `W (ρ c − a) = c (W ρ − ∑ w_i) + ∑ (w_i c − W)` over `a` summands. -/
theorem family_identity {R : Type*} [CommRing R] {a : ℕ} (w : Fin a → R) (c W ρ : R) :
    W * (ρ * c - (a : R)) = c * (W * ρ - ∑ i, w i) + ∑ i, (w i * c - W) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Sperner's bound from the LYM inequality: `∑ a_j ≤ ρ C(N, ⌊N/2⌋)`. -/
theorem sperner_bound (N ρ : ℕ) (a : Fin (N + 1) → ZT n) (ha : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 0) (a j))
    (hLYM : Γ ⊢[PRAAx] zle
      (ZT.sumFin fun j => a j * ZT.natLit (j.val.factorial * (N - j.val).factorial))
      (ZT.natLit ρ * ZT.natLit N.factorial)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin a) (ZT.natLit ρ * ZT.natLit (N.choose (N / 2))) := by
  have hc : ∀ j : Fin (N + 1),
      ((j.val.factorial * (N - j.val).factorial * N.choose (N / 2) - N.factorial : ℕ) : Groth (Q Γ)) =
        ((j.val.factorial * (N - j.val).factorial : ℕ) : Groth (Q Γ)) * ((N.choose (N / 2) : ℕ) : Groth (Q Γ)) -
          ((N.factorial : ℕ) : Groth (Q Γ)) := fun j => mid_weight_cast (Nat.le_of_lt_succ j.isLt)
  have hW1 : Γ ⊢[PRAAx] zle (ZT.natLit 1 : ZT n) (ZT.natLit N.factorial) :=
    zle_natLit (Nat.factorial_pos N)
  have hpos : Γ ⊢[PRAAx] zle (ZT.natLit 0)
      (ZT.natLit N.factorial * (ZT.natLit ρ * ZT.natLit (N.choose (N / 2)) - ZT.sumFin a)) := by
    have I := weight_identity (fun j => ZT.toZ Γ (a j))
      (fun j : Fin (N + 1) => ((j.val.factorial * (N - j.val).factorial : ℕ) : Groth (Q Γ)))
      ((N.choose (N / 2) : ℕ) : Groth (Q Γ)) ((N.factorial : ℕ) : Groth (Q Γ)) (ρ : Groth (Q Γ))
    beta_reduce at I
    refine zle_of_comb (((N.choose (N / 2) : ℕ) : Groth (Q Γ)) * zsl hLYM +
        ∑ j : Fin (N + 1), ZT.toZ Γ (a j) *
          ((j.val.factorial * (N - j.val).factorial * N.choose (N / 2) - N.factorial : ℕ) : Groth (Q Γ))) ?_
      (nn_add (nn_mul (nn_natCast _) (nn_zsl _))
        (nn_sum _ _ fun j _ => nn_mul (nn_zle0 (ha j)) (nn_natCast _)))
    zsimp
    simp only [hc]
    linear_combination I
  have hX := znn_of_pos_mul hW1 hpos
  refine zle_of_comb (zsl hX) ?_ (nn_zsl _)
  zsimp
  ring

/-- Sperner's bound from the incidence table of sets and linear orders: `a ≤ ρ C(N, ⌊N/2⌋)`. -/
theorem sperner_family (N ρ a : ℕ) (s : Fin a → Fin (N + 1)) (M : Fin a → Fin N.factorial → ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit ((s i).val.factorial * (N - (s i).val).factorial))
      (ZT.sumFin fun j => M i j))
    (hcol : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => M i j) (ZT.natLit ρ)) :
    Γ ⊢[PRAAx] zle (ZT.natLit a) (ZT.natLit ρ * ZT.natLit (N.choose (N / 2))) := by
  have h := weighted_count_le M
    (fun i => ZT.natLit ((s i).val.factorial * (N - (s i).val).factorial)) (ZT.natLit ρ) hr hcol
  have hc : ∀ i : Fin a,
      (((s i).val.factorial * (N - (s i).val).factorial * N.choose (N / 2) - N.factorial : ℕ) :
          Groth (Q Γ)) =
        (((s i).val.factorial * (N - (s i).val).factorial : ℕ) : Groth (Q Γ)) *
            ((N.choose (N / 2) : ℕ) : Groth (Q Γ)) - ((N.factorial : ℕ) : Groth (Q Γ)) :=
    fun i => mid_weight_cast (Nat.le_of_lt_succ (s i).isLt)
  have hW1 : Γ ⊢[PRAAx] zle (ZT.natLit 1 : ZT n) (ZT.natLit N.factorial) :=
    zle_natLit (Nat.factorial_pos N)
  have hpos : Γ ⊢[PRAAx] zle (ZT.natLit 0)
      (ZT.natLit N.factorial * (ZT.natLit ρ * ZT.natLit (N.choose (N / 2)) - ZT.natLit a)) := by
    have I := family_identity
      (fun i : Fin a => (((s i).val.factorial * (N - (s i).val).factorial : ℕ) : Groth (Q Γ)))
      ((N.choose (N / 2) : ℕ) : Groth (Q Γ)) ((N.factorial : ℕ) : Groth (Q Γ)) (ρ : Groth (Q Γ))
    beta_reduce at I
    refine zle_of_comb (((N.choose (N / 2) : ℕ) : Groth (Q Γ)) * zsl h +
        ∑ i : Fin a,
          (((s i).val.factorial * (N - (s i).val).factorial * N.choose (N / 2) - N.factorial : ℕ) :
            Groth (Q Γ))) ?_
      (nn_add (nn_mul (nn_natCast _) (nn_zsl _)) (nn_sum _ _ fun i _ => nn_natCast _))
    zsimp
    simp only [hc]
    linear_combination I
  have hX := znn_of_pos_mul hW1 hpos
  refine zle_of_comb (zsl hX) ?_ (nn_zsl _)
  zsimp
  ring

/-- The Erdős–Ko–Rado cancellation: `|F| n k! (n − k)! ≤ k n!` gives `|F| ≤ C(n − 1, k − 1)`, with
`n = N + 1` and `k = K + 1`. -/
theorem ekr_bound (N K : ℕ) (hK : K ≤ N) {f : ZT n}
    (h : Γ ⊢[PRAAx] zle (ZT.natLit ((N + 1) * (K + 1).factorial * (N - K).factorial) * f)
      (ZT.natLit ((K + 1) * (N + 1).factorial))) :
    Γ ⊢[PRAAx] zle f (ZT.natLit (N.choose K)) := by
  have e : (N + 1) * (K + 1).factorial * (N - K).factorial * N.choose K = (K + 1) * (N + 1).factorial := by
    have h0 := Nat.choose_mul_factorial_mul_factorial hK
    rw [Nat.factorial_succ, Nat.factorial_succ, ← h0]
    ring
  have ec : (((N + 1) * (K + 1).factorial * (N - K).factorial : ℕ) : Groth (Q Γ)) *
      ((N.choose K : ℕ) : Groth (Q Γ)) = (((K + 1) * (N + 1).factorial : ℕ) : Groth (Q Γ)) := by
    rw [← Nat.cast_mul, e]
  have hP : Γ ⊢[PRAAx] zle (ZT.natLit 1 : ZT n)
      (ZT.natLit ((N + 1) * (K + 1).factorial * (N - K).factorial)) :=
    zle_natLit (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos N) (Nat.factorial_pos _))
      (Nat.factorial_pos _)))
  have hpos : Γ ⊢[PRAAx] zle (ZT.natLit 0)
      (ZT.natLit ((N + 1) * (K + 1).factorial * (N - K).factorial) * (ZT.natLit (N.choose K) - f)) := by
    refine zle_of_comb (zsl h) ?_ (nn_zsl _)
    zsimp
    linear_combination ec
  have hX := znn_of_pos_mul hP hpos
  refine zle_of_comb (zsl hX) ?_ (nn_zsl _)
  zsimp
  ring

end LeanProofs.IPRA.Combinatorics.SpernerBound
