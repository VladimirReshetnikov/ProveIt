import Mathlib.Data.Matrix.ColumnRowPartitioned
import IPRADerivations.Foundations.NullVectorDeterminant

/-!
# The dihedral Gram determinant (`spherical_trigonometry_ipra_2026-11-15`, (11.6)–(11.7))

Packet: `geometry/spherical_trigonometry_ipra_2026-11-15`, corollary "Dihedral Gram
determinant": "Let `G` be the `4 × 4` Gram matrix of the outward unit normals: `G_ii = 1`,
`G_ij = -cos θ_kl`. Then `det G = 0`, `G (Δ_1, Δ_2, Δ_3, Δ_4)ᵀ = 0` (11.7). Proof: Four vectors
in `ℝ³` are linearly dependent, so their Gram determinant vanishes. Equation (11.2), divided by
`2`, is precisely the displayed weighted null relation."

The derivation does not use linear dependence (which over a ring has no witness): a family of
`k` vectors with `d < k` coordinates is a `k × d` matrix `A`; padded with zero columns it is a
square matrix `B` with a zero column, and `A Aᵀ = B Bᵀ`, so `det(A Aᵀ) = det(B)² = 0`.

* `gram_det_ring`, `gram_null_ring`, `weighted_det_ring`, `weighted_null_ring`: the facts over
  a commutative ring;
* `gram`, `vsum`, `prodFin`: the Gram matrix of a family of integer vectors, its vector sum,
  and a finite product of integer terms;
* `gram_det`: for `d < k`, iPRA derives `det (gram N) = 0`, for arbitrary integer terms;
* `gram_null`: from `Σ_i N_i = 0`, iPRA derives `gram N · (1, …, 1)ᵀ = 0`;
* `weighted_det`, `weighted_null`: the packet's normalized form with denominators cleared. If
  `N_i · N_j = s_i s_j g_ij` (the packet's `s_i = 2Δ_i`, `g = G`), then
  `(Π_i s_i)² det g = 0`, and with closure `s_i (g s)_i = 0` for every `i`;
* `faces`, `faces_closure`: the four face-area vectors `b × c`, `c × a`, `a × b`,
  `(c − a) × (b − a)` of the tetrahedron with vertices `0, a, b, c`, and (11.2);
* `tetra_gram_det`, `tetra_gram_null`: both halves of (11.7) for these vectors, closed over
  the 18 natural-number variables of the three integer coordinate vectors.

The cancellation of the positive factors `s_i` (division by the areas) is under the packet's
nondegeneracy witness and is not performed.
-/

namespace LeanProofs.IPRA.Geometry.TetrahedralGram

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R]

/-- More vectors than coordinates: the Gram determinant vanishes. -/
theorem gram_det_ring {m d : ℕ} (A : Matrix (Fin m) (Fin d) R) (h : d < m) :
    (A * Aᵀ).det = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, m = d + (c + 1) := ⟨m - d - 1, by omega⟩
  let e : Fin d ⊕ Fin (c + 1) ≃ Fin (d + (c + 1)) := finSumFinEquiv
  let B : Matrix (Fin (d + (c + 1))) (Fin d ⊕ Fin (c + 1)) R := Matrix.fromCols A 0
  have hB : A * Aᵀ = (B.submatrix id e.symm) * (B.submatrix id e.symm)ᵀ := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    simp [B, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  have hz : (B.submatrix id e.symm).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero (e (Sum.inr 0)) (fun i => by simp [B])
  rw [hB, Matrix.det_mul, hz]
  exact MulZeroClass.zero_mul _

/-- A family with zero sum: the all-ones vector is a null vector of the Gram matrix. -/
theorem gram_null_ring {m d : ℕ} (A : Matrix (Fin m) (Fin d) R)
    (h : Aᵀ *ᵥ (fun _ => (1 : R)) = 0) : (A * Aᵀ) *ᵥ (fun _ => (1 : R)) = 0 := by
  rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- Clearing the scaling of a determinant: `det (s_i s_j g_ij) = (Π s_i)² det g`. -/
theorem weighted_det_ring {m : ℕ} (s : Fin m → R) (g : Matrix (Fin m) (Fin m) R) :
    (Matrix.of fun i j => s i * s j * g i j).det = (∏ i, s i) ^ 2 * g.det := by
  have e : (Matrix.of fun i j => s i * s j * g i j) =
      Matrix.of fun i j => s i * (Matrix.of fun i j => s j * g i j) i j := by
    ext i j
    simp only [Matrix.of_apply]
    ring
  rw [e, Matrix.det_mul_column, Matrix.det_mul_row]
  ring

/-- Clearing the scaling of a row sum: `Σ_j s_i s_j g_ij = s_i (g s)_i`. -/
theorem weighted_null_ring {m : ℕ} (s : Fin m → R) (g : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    s i * (g *ᵥ s) i = ((Matrix.of fun i j => s i * s j * g i j) *ᵥ (fun _ => (1 : R))) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {k d : ℕ}

/-- The Gram matrix of a family of integer vectors. -/
def gram (N : Fin k → Vec d n) : Mat k n := fun i j => Vec.dot (N i) (N j)

/-- The sum of a family of integer vectors. -/
def vsum (N : Fin k → Vec d n) : Vec d n := fun l => ZT.sumFin fun i => N i l

/-- A finite product of integer terms. -/
def prodFin : {k : ℕ} → (Fin k → ZT n) → ZT n
  | 0, _ => ZT.natLit 1
  | k + 1, f => f 0 * prodFin fun i : Fin k => f i.succ

theorem toZ_prodFin : {k : ℕ} → (f : Fin k → ZT n) →
    ZT.toZ Γ (prodFin f) = ∏ i, ZT.toZ Γ (f i)
  | 0, f => by simp [prodFin]
  | k + 1, f => by rw [prodFin, ZT.toZ_mul, toZ_prodFin, Fin.prod_univ_succ]

/-- The family as a `k × d` matrix of evaluations. -/
def rows (Γ : List (Fm PTm n)) (N : Fin k → Vec d n) : Matrix (Fin k) (Fin d) (Groth (Q Γ)) :=
  Matrix.of fun i => Vec.toZ Γ (N i)

theorem toZ_gram (N : Fin k → Vec d n) : Mat.toZ Γ (gram N) = rows Γ N * (rows Γ N)ᵀ := by
  ext i j
  simp [gram, rows, Matrix.mul_apply, dotProduct]

theorem toZ_vsum (N : Fin k → Vec d n) :
    Vec.toZ Γ (vsum N) = (rows Γ N)ᵀ *ᵥ (fun _ => (1 : Groth (Q Γ))) := by
  funext l
  simp [vsum, rows, Vec.toZ, Matrix.mulVec, dotProduct]

theorem toZ_ones : Vec.toZ Γ (fun _ : Fin k => (ZT.natLit 1 : ZT n)) = fun _ => 1 := by
  funext i
  simp [Vec.toZ]

theorem toZ_zeros : Vec.toZ Γ (fun _ : Fin k => (ZT.natLit 0 : ZT n)) = 0 := by
  funext i
  simp [Vec.toZ]

/-- (11.7), first half, in general: more vectors than coordinates gives `det (gram N) = 0`. -/
theorem gram_det (N : Fin k → Vec d n) (h : d < k) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (gram N)) (ZT.natLit 0) :=
  ZT.derive (by
    simp only [Mat.toZ_det, toZ_gram, ZT.toZ_natLit, Nat.cast_zero]
    exact gram_det_ring _ h)

/-- (11.7), second half, in general: closure gives the all-ones null vector. -/
theorem gram_null {N : Fin k → Vec d n}
    (h : Γ ⊢[PRAAx] Vec.eqFm (vsum N) (fun _ => ZT.natLit 0)) :
    Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec (gram N) (fun _ => ZT.natLit 1)) (fun _ => ZT.natLit 0) := by
  have e := Vec.toZ_eq h
  rw [toZ_vsum, toZ_zeros] at e
  refine Vec.derive ?_
  rw [Mat.toZ_mulVec, toZ_gram, toZ_ones, toZ_zeros]
  exact gram_null_ring _ e

/-- The normalized Gram determinant with denominators cleared: if `N_i · N_j = s_i s_j g_ij`
and there are more vectors than coordinates, then `(Π s_i)² det g = 0`. -/
theorem weighted_det {N : Fin k → Vec d n} {s : Vec k n} {g : Mat k n} (h : d < k)
    (hg : Γ ⊢[PRAAx] Mat.eqFm (gram N) (fun i j => s i * s j * g i j)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sq (prodFin s) * Mat.det g) (ZT.natLit 0) := by
  have e := Mat.toZ_eq hg
  have e' : Mat.toZ Γ (fun i j => s i * s j * g i j) =
      Matrix.of fun i j => Vec.toZ Γ s i * Vec.toZ Γ s j * Mat.toZ Γ g i j := by
    ext i j
    simp [Mat.toZ, Vec.toZ]
  have e₀ := gram_det_ring (rows Γ N) h
  rw [← toZ_gram, e, e', weighted_det_ring] at e₀
  refine ZT.derive ?_
  simp only [ZT.toZ_mul, ZT.toZ_sq, toZ_prodFin, Mat.toZ_det, ZT.toZ_natLit, Nat.cast_zero]
  exact e₀

/-- The weighted null relation with denominators cleared: if `N_i · N_j = s_i s_j g_ij` and
`Σ_i N_i = 0`, then `s_i (g s)_i = 0` for every `i`. -/
theorem weighted_null {N : Fin k → Vec d n} {s : Vec k n} {g : Mat k n}
    (hg : Γ ⊢[PRAAx] Mat.eqFm (gram N) (fun i j => s i * s j * g i j))
    (h : Γ ⊢[PRAAx] Vec.eqFm (vsum N) (fun _ => ZT.natLit 0)) (i : Fin k) :
    Γ ⊢[PRAAx] ZT.eq (s i * Mat.mulVec g s i) (ZT.natLit 0) := by
  have e := Mat.toZ_eq hg
  have e' : Mat.toZ Γ (fun i j => s i * s j * g i j) =
      Matrix.of fun i j => Vec.toZ Γ s i * Vec.toZ Γ s j * Mat.toZ Γ g i j := by
    ext i j
    simp [Mat.toZ, Vec.toZ]
  have e₀ := congrFun (Vec.toZ_eq (gram_null h)) i
  rw [Mat.toZ_mulVec, e, e', toZ_ones, ← weighted_null_ring, toZ_zeros] at e₀
  have e₁ : ZT.toZ Γ (Mat.mulVec g s i) = (Mat.toZ Γ g *ᵥ Vec.toZ Γ s) i := by
    rw [← Mat.toZ_mulVec]
    rfl
  refine ZT.derive ?_
  rw [ZT.toZ_mul, e₁, ZT.toZ_natLit, Nat.cast_zero]
  exact e₀

/-- The four face-area vectors of the tetrahedron with vertices `0, a, b, c` (all inward, or
all outward, according to the orientation of `a, b, c`). -/
def faces (a b c : Vec 3 n) : Fin 4 → Vec 3 n :=
  ![Vec.cross b c, Vec.cross c a, Vec.cross a b, Vec.cross (Vec.sub c a) (Vec.sub b a)]

/-- (11.2): the face-area vectors sum to zero. -/
theorem faces_closure (a b c : Vec 3 n) :
    Γ ⊢[PRAAx] Vec.eqFm (vsum (faces a b c)) (fun _ => ZT.natLit 0) :=
  Vec.derive (by
    funext l
    fin_cases l <;>
      simp [Vec.toZ, vsum, faces, Vec.cross, Vec.sub, Fin.sum_univ_four] <;> ring)

abbrev u : Vec 3 18 := Vec.vars 3 0 (by norm_num)
abbrev v : Vec 3 18 := Vec.vars 3 6 (by norm_num)
abbrev w : Vec 3 18 := Vec.vars 3 12 (by norm_num)

/-- (11.7), first half: the Gram determinant of the four face-area vectors vanishes. -/
theorem tetra_gram_det : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 18 (ZT.eq (Mat.det (gram (faces u v w))) (ZT.natLit 0)) :=
  closeUniv 18 (gram_det _ (by norm_num))

/-- (11.7), second half: the all-ones vector is a null vector of that Gram matrix. -/
theorem tetra_gram_null : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 18 (Vec.eqFm (Mat.mulVec (gram (faces u v w)) (fun _ => ZT.natLit 1))
      (fun _ => ZT.natLit 0)) :=
  closeUniv 18 (gram_null (faces_closure _ _ _))

end LeanProofs.IPRA.Geometry.TetrahedralGram
