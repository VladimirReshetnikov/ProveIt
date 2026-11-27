import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Core.Header

/-!
# Common zeros give norm zeros, for every matrix size (`ipra_presentations_to_witnesses`, `lem:norm-intersection-vanishing`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:norm-intersection-vanishing`:
"Put `v = (1, b, …, b^{m-1})`. Evaluating each monic reduction identity at `(a, b)` gives
`v M_G(a) = G(a, b) v = 0`. The adjugate identity, proved by finite determinant expansion,
yields `v M_G(a) adj(M_G(a)) = N_G(a) v`. Its first coordinate is `N_G(a)`, because `v_0 = 1`. It
therefore vanishes. This proof allows repeated roots, singular fibers and `m = 1`."

`Foundations/NormVanishing` has `m = 2` and `m = 3` as polynomial certificates. Here the size
`m` is arbitrary (a parameter of the Lean statement; each instance is one iPRA derivation),
using the determinant and adjugate of integer-term matrices of `Core/LinearAlgebra`:

* `conjFin_elim`: a finite conjunction gives each of its members;
* `Vec.toZ_eq`, `Mat.toZ_eq`: an iPRA equation of integer vectors (matrices), as an equation
  of evaluations;
* `null_det`: over a commutative ring, `Mᵀ v = 0` gives `v_i det M = 0` for every `i`;
* `adjugate_identity`: `M adj(M) = det(M) · 1`, as an iPRA matrix equation;
* `norm_vanish`: if iPRA derives `v M = 0` (as `Mᵀ v = 0`), it derives `v_i det M = 0`;
* `norm_vanish_unit`: with a coordinate `v_i = 1`, it derives `det M = 0`: the packet's
  `N_G(a) = 0`.

Not derived: the construction of `M_G(a)` from the monic reduction identities, and
`thm:norm-complete-intersection`.
-/

namespace LeanProofs.IPRA.Foundations.NullVectorDeterminant

open_ipra exports
open Matrix

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A finite conjunction gives each of its members. -/
theorem conjFin_elim : {k : ℕ} → {f : Fin k → Fm PTm n} → (Γ ⊢[PRAAx] conjFin f) →
    ∀ i, Γ ⊢[PRAAx] f i
  | 0, _, _, i => i.elim0
  | 1, f, h, i => by
    have e : i = 0 := Subsingleton.elim _ _
    subst e
    exact h
  | _ + 2, f, h, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Prf.andE₁ h
    · exact conjFin_elim (Prf.andE₂ h) j

/-- An iPRA equation of integer vectors, as an equation of evaluations. -/
theorem Vec.toZ_eq {k : ℕ} {u w : Vec k n} (h : Γ ⊢[PRAAx] Vec.eqFm u w) :
    Vec.toZ Γ u = Vec.toZ Γ w := by
  funext i
  exact ZT.toZ_eq (conjFin_elim h i)

/-- An iPRA equation of integer matrices, as an equation of evaluations. -/
theorem Mat.toZ_eq {k : ℕ} {M N : Mat k n} (h : Γ ⊢[PRAAx] Mat.eqFm M N) :
    Mat.toZ Γ M = Mat.toZ Γ N := by
  ext i j
  exact ZT.toZ_eq (conjFin_elim (conjFin_elim h i) j)

/-- A left null vector annihilates the determinant. -/
theorem null_det {k : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin k) (Fin k) R)
    (v : Fin k → R) (h : Mᵀ *ᵥ v = 0) (i : Fin k) : v i * M.det = 0 := by
  have h1 : (M.det • (1 : Matrix (Fin k) (Fin k) R)) *ᵥ v = 0 := by
    rw [← Matrix.det_transpose, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]
  have h2 := congrFun h1 i
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  have h3 : M.det * v i = 0 := by simpa using h2
  linear_combination h3

/-- The adjugate identity `M adj(M) = det(M) · 1`. -/
theorem adjugate_identity {k : ℕ} (M : Mat k n) :
    Γ ⊢[PRAAx] Mat.eqFm (Mat.mul M (Mat.adj M)) (Mat.smul (Mat.det M) Mat.one) :=
  Mat.derive (by
    simp only [Mat.toZ_mul, Mat.toZ_adj, Mat.toZ_smul, Mat.toZ_det, Mat.toZ_one]
    exact Matrix.mul_adjugate _)

/-- `lem:norm-intersection-vanishing` for every size: `v M = 0` gives `v_i det M = 0`. -/
theorem norm_vanish {k : ℕ} {M : Mat k n} {v : Vec k n}
    (h : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec (Mat.transpose M) v) (fun _ => ZT.natLit 0))
    (i : Fin k) : Γ ⊢[PRAAx] ZT.eq (v i * Mat.det M) (ZT.natLit 0) := by
  have hz : (Mat.toZ Γ M)ᵀ *ᵥ Vec.toZ Γ v = 0 := by
    rw [← Mat.toZ_transpose, ← Mat.toZ_mulVec, Vec.toZ_eq h]
    funext j
    simp [Vec.toZ]
  refine ZT.derive ?_
  simp only [ZT.toZ_mul, Mat.toZ_det, ZT.toZ_natLit, Nat.cast_zero]
  exact null_det _ _ hz i

/-- With a coordinate equal to `1` (the packet's `v_0 = 1`), the determinant vanishes. -/
theorem norm_vanish_unit {k : ℕ} {M : Mat k n} {v : Vec k n}
    (h : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec (Mat.transpose M) v) (fun _ => ZT.natLit 0))
    (i : Fin k) (hi : Γ ⊢[PRAAx] ZT.eq (v i) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det M) (ZT.natLit 0) := by
  have e := ZT.toZ_eq (norm_vanish h i)
  have e₁ := ZT.toZ_eq hi
  refine ZT.derive ?_
  simp only [ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero, Nat.cast_one] at e e₁ ⊢
  rw [e₁, _root_.one_mul] at e
  exact e

end LeanProofs.IPRA.Foundations.NullVectorDeterminant
