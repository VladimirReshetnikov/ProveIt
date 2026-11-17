import IPRADerivations.Algebra.AdjugateInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Cayley–Hamilton for every size

Packet: `cayley_hamilton_ipra`, `sections/core.tex`, Theorem `thm:CH`, for `m × m` integer matrices of
every fixed size `m` with arbitrary integer-term entries.

The characteristic coefficients are explicit iPRA terms: `cf M k = (−1)^k ∑_{|S| = k} det M[S, S]`,
the signed sum of the `k × k` principal minors (each a `Mat.det` term), which is the coefficient of
`X^{m−k}` in `det(X I − M)` (Mathlib's `charpoly_coeff_eq_sum_minors`). The theorem
`cayley_hamilton` derives `∑_{k ≤ m} cf M k · M^{m−k} = 0` in iPRA, by evaluating both sides and
applying `aeval_self_charpoly`. The subsets of each size are summed in a fixed (noncomputably chosen)
order of a finite set; any order gives a provably equal term.
-/

namespace LeanProofs.IPRA.Algebra.CayleyHamiltonGeneral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Matrix Polynomial
open scoped Fm

variable {n m : ℕ} {Γ : List (Fm PTm n)}

/-- A finite list of integer terms, summed. -/
def zsumL : List (ZT n) → ZT n
  | [] => ZT.natLit 0
  | a :: l => a + zsumL l

theorem toZ_zsumL : ∀ l : List (ZT n), ZT.toZ Γ (zsumL l) = (l.map (ZT.toZ Γ)).sum
  | [] => by simp [zsumL]
  | a :: l => by simp [zsumL, toZ_zsumL l]

/-- The principal minor of `M` on the rows and columns of `s`. -/
def minorZ (M : Mat m n) (s : Finset (Fin m)) : ZT n :=
  Mat.det fun a b : Fin s.card => M (s.orderEmbOfFin rfl a) (s.orderEmbOfFin rfl b)

theorem toZ_minorZ (M : Mat m n) (s : Finset (Fin m)) :
    ZT.toZ Γ (minorZ M s) = ((Mat.toZ Γ M).submatrix (Subtype.val : s → Fin m) Subtype.val).det := by
  rw [minorZ, Mat.toZ_det, ← Matrix.det_submatrix_equiv_self (s.orderIsoOfFin rfl).toEquiv]
  congr 1

/-- `(−1)^k ∑_{|S| = k} det M[S, S]`, the coefficient of `X^{m−k}`. -/
noncomputable def cfZ (M : Mat m n) (k : ℕ) : ZT n :=
  ZT.signPow k (zsumL (((Finset.univ : Finset (Fin m)).powersetCard k).toList.map (minorZ M)))

theorem toZ_cfZ (M : Mat m n) {k : ℕ} (hk : k ≤ m) :
    ZT.toZ Γ (cfZ M k) = (Matrix.charpoly (Mat.toZ Γ M)).coeff (m - k) := by
  have h := Matrix.charpoly_coeff_eq_sum_minors (Mat.toZ Γ M) k (by simpa using hk)
  rw [Fintype.card_fin] at h
  rw [h, cfZ, ZT.toZ_signPow, toZ_zsumL, List.map_map]
  congr 1
  rw [← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro s _
  simp [toZ_minorZ]

/-- `M^j`. -/
def powM (M : Mat m n) : ℕ → Mat m n
  | 0 => Mat.one
  | j + 1 => Mat.mul (powM M j) M

theorem toZ_powM (M : Mat m n) : ∀ j, Mat.toZ Γ (powM M j) = (Mat.toZ Γ M) ^ j
  | 0 => by simp [powM]
  | j + 1 => by rw [powM, Mat.toZ_mul, toZ_powM M j, pow_succ]

/-- `∑_{i < K} f i` for integer matrices. -/
def msumFin : {K : ℕ} → (Fin K → Mat m n) → Mat m n
  | 0, _ => Mat.zero
  | _ + 1, f => Mat.add (f 0) (msumFin fun i => f i.succ)

theorem toZ_msumFin : ∀ {K : ℕ} (f : Fin K → Mat m n), Mat.toZ Γ (msumFin f) = ∑ i, Mat.toZ Γ (f i)
  | 0, f => by simp [msumFin]
  | K + 1, f => by rw [msumFin, Mat.toZ_add, toZ_msumFin, Fin.sum_univ_succ]

/-- `∑_{k ≤ m} cf M k · M^{m−k}`. -/
noncomputable def chZ (M : Mat m n) : Mat m n :=
  msumFin fun k : Fin (m + 1) => Mat.smul (cfZ M k) (powM M (m - k))

/-- `thm:CH`: `∑_{k ≤ m} cf M k · M^{m−k} = 0`. -/
theorem cayley_hamilton (M : Mat m n) : Γ ⊢[PRAAx] Mat.eqFm (chZ M) Mat.zero := by
  refine Mat.derive ?_
  rw [Mat.toZ_zero, chZ, toZ_msumFin]
  rcases subsingleton_or_nontrivial (Groth (Q Γ)) with hs | hs
  · exact Subsingleton.elim _ _
  have e : ∀ k : Fin (m + 1), Mat.toZ Γ (Mat.smul (cfZ M k) (powM M (m - k))) =
      (Matrix.charpoly (Mat.toZ Γ M)).coeff (m - k) • (Mat.toZ Γ M) ^ (m - k) := by
    intro k
    rw [Mat.toZ_smul, toZ_cfZ M (Nat.lt_succ_iff.mp k.isLt), toZ_powM]
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun k => (Matrix.charpoly (Mat.toZ Γ M)).coeff (m - k) • (Mat.toZ Γ M) ^ (m - k)),
    ← Finset.sum_range_reflect]
  have h := Matrix.aeval_self_charpoly (Mat.toZ Γ M)
  rw [Polynomial.aeval_eq_sum_range' (n := m + 1) (by simp)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show m - (m + 1 - 1 - j) = j by omega, Algebra.smul_def]

end LeanProofs.IPRA.Algebra.CayleyHamiltonGeneral
