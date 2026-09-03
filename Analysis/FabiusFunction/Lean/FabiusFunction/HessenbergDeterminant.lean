import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators

/-!
# Lower-Hessenberg determinants and linear recurrences

For coefficients `β : ℕ → ℕ → R`, let `α_0 = 1` and `α_{n+1} = ∑_{k ≤ n} β_{n+1,k} α_k`
(`hessenbergSeq`), and let `H_{n+1}` be the `(n+1) × (n+1)` lower-Hessenberg matrix with rows
`1..n+1` and columns `0..n`, entries `β_{r,k}` for `k ≤ r`, `-1` for `k = r+1` and `0` above
(`hessenbergMatrix`).  Then `det H_{n+1} = α_{n+1}` (`det_hessenbergMatrix`,
thm:fabius-hessenberg for the recurrence-defined sequence).

The proof avoids minors: the recurrence says `H_{n+1} α = α_{n+1} e_{last}`; applying the
adjugate, `det H_{n+1} · α_0 = α_{n+1} · adj(H_{n+1})_{0,last}`, and the cofactor
`adj(H_{n+1})_{0,last}` is the determinant of a lower-triangular matrix with diagonal `-1`
of size `n` up to the sign `(-1)^n`, hence `1`.
-/

set_option autoImplicit false

open Finset Matrix

namespace Fabius

variable {R : Type*} [CommRing R]

/-- The sequence `α_0 = 1`, `α_{n+1} = ∑_{k ≤ n} β_{n+1,k} α_k`. -/
noncomputable def hessenbergSeq (β : ℕ → ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), β (n + 1) k * hessenbergSeq β k
termination_by n => n
decreasing_by exact k.isLt

/-- The Hessenberg sequence starts at `1`. -/
theorem hessenbergSeq_zero (β : ℕ → ℕ → R) : hessenbergSeq β 0 = 1 := by
  rw [hessenbergSeq]

/-- The defining expansion of the Hessenberg sequence: each term is the weighted sum of all
earlier ones. -/
theorem hessenbergSeq_succ (β : ℕ → ℕ → R) (n : ℕ) :
    hessenbergSeq β (n + 1) = ∑ k ∈ range (n + 1), β (n + 1) k * hessenbergSeq β k := by
  rw [hessenbergSeq, Fin.sum_univ_eq_sum_range (fun k => β (n + 1) k * hessenbergSeq β k)]

/-- The entry in row `r` (the `(r+1)`-st row of the text) and column `c`. -/
def hessenbergEntry (β : ℕ → ℕ → R) (r c : ℕ) : R :=
  if c ≤ r then β (r + 1) c else if c = r + 1 then -1 else 0

/-- The `(n+1) × (n+1)` lower-Hessenberg matrix `H_{n+1}`. -/
def hessenbergMatrix (β : ℕ → ℕ → R) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun r c => hessenbergEntry β r c

/-- The recurrence as a matrix identity: `H_{n+1} α = α_{n+1} e_{last}`. -/
theorem hessenbergMatrix_mulVec (β : ℕ → ℕ → R) (n : ℕ) :
    hessenbergMatrix β n *ᵥ (fun c : Fin (n + 1) => hessenbergSeq β c) =
      Pi.single (Fin.last n) (hessenbergSeq β (n + 1)) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, hessenbergMatrix]
  rw [Fin.sum_univ_eq_sum_range (fun c => hessenbergEntry β r c * hessenbergSeq β c) (n + 1),
    ← sum_range_add_sum_Ico _ (show (r : ℕ) + 1 ≤ n + 1 by omega)]
  have h1 : ∑ c ∈ range ((r : ℕ) + 1), hessenbergEntry β r c * hessenbergSeq β c =
      hessenbergSeq β (r + 1) := by
    rw [hessenbergSeq_succ]
    refine sum_congr rfl fun c hc => ?_
    unfold hessenbergEntry
    rw [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hc))]
  have h2 : ∑ c ∈ Ico ((r : ℕ) + 1) (n + 1), hessenbergEntry β r c * hessenbergSeq β c =
      if (r : ℕ) < n then -hessenbergSeq β (r + 1) else 0 := by
    rcases lt_or_ge (r : ℕ) n with hr | hr
    · rw [if_pos hr, sum_eq_single ((r : ℕ) + 1)]
      · unfold hessenbergEntry
        rw [if_neg (by omega), if_pos rfl]
        ring
      · intro c hc hcr
        rw [mem_Ico] at hc
        unfold hessenbergEntry
        rw [if_neg (by omega), if_neg (fun h => hcr h), zero_mul]
      · intro h
        exact absurd (mem_Ico.mpr ⟨le_rfl, by omega⟩) h
    · rw [if_neg (not_lt.mpr hr), Ico_eq_empty_of_le (by omega), sum_empty]
  rw [h1, h2]
  rcases lt_or_ge (r : ℕ) n with hr | hr
  · rw [if_pos hr, Pi.single_apply, if_neg (fun h => by rw [h, Fin.val_last] at hr; omega)]
    ring
  · have hrl : r = Fin.last n := Fin.ext (by rw [Fin.val_last]; omega)
    rw [if_neg (not_lt.mpr hr), hrl, Pi.single_eq_same, Fin.val_last, add_zero]

/-- The cofactor `adj(H_{n+1})_{0,last} = 1`. -/
theorem hessenbergMatrix_adjugate_zero_last (β : ℕ → ℕ → R) (n : ℕ) :
    (hessenbergMatrix β n).adjugate 0 (Fin.last n) = 1 := by
  rw [adjugate_apply, det_succ_row _ (Fin.last n)]
  rw [sum_eq_single 0]
  · rw [updateRow_self, Pi.single_eq_same, mul_one, Fin.val_last, Fin.val_zero, add_zero]
    -- the minor is lower triangular with diagonal `-1`
    have hlow : ((hessenbergMatrix β n).updateRow (Fin.last n) (Pi.single 0 1)).submatrix
        (Fin.last n).succAbove (0 : Fin (n + 1)).succAbove = fun i k : Fin n =>
          hessenbergEntry β i ((k : ℕ) + 1) := by
      funext i k
      simp only [submatrix_apply, Fin.succAbove_last, Fin.succAbove_zero]
      rw [updateRow_ne (Fin.castSucc_lt_last i).ne]
      rfl
    rw [hlow, det_of_lowerTriangular]
    · have hdiag : ∀ i : Fin n, hessenbergEntry β i ((i : ℕ) + 1) = -1 := fun i => by
        unfold hessenbergEntry
        rw [if_neg (by omega), if_pos rfl]
      simp only [hdiag, prod_const, card_univ, Fintype.card_fin]
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    · intro i k hik
      rw [OrderDual.toDual_lt_toDual] at hik
      have hik' : (i : ℕ) < k := hik
      dsimp only
      unfold hessenbergEntry
      rw [if_neg (by omega), if_neg (by omega)]
  · intro j _ hj
    rw [updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

/-- **The lower-Hessenberg determinant** (thm:fabius-hessenberg, generic form):
`det H_{n+1} = α_{n+1}` for the sequence of the recurrence. -/
theorem det_hessenbergMatrix (β : ℕ → ℕ → R) (n : ℕ) :
    (hessenbergMatrix β n).det = hessenbergSeq β (n + 1) := by
  have h := congrArg (fun v => (hessenbergMatrix β n).adjugate *ᵥ v) (hessenbergMatrix_mulVec β n)
  have h0 := congrFun h 0
  simp only [mulVec_mulVec, adjugate_mul] at h0
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, hessenbergSeq_zero,
    hessenbergMatrix_adjugate_zero_last] at h0
  exact h0

end Fabius
