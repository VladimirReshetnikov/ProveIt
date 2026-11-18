import IPRADerivations.Foundations.NullVectorDeterminant

/-!
# The norm as an explicit ideal member (`ipra_presentations_to_witnesses`, `prop:norm-to-module`)

Packet: `foundations/ipra_presentations_to_witnesses`, proposition `prop:norm-to-module`, proof:
"Retain the quotients from the monic reductions used to construct `M_G`: for `0 ≤ j < m`,
`G Y^j = Σ_{i<m} (M_G)_{ij} Y^i + F h_j`. For the rows `b = (1, Y, …, Y^{m-1})` and
`h = (h_0, …, h_{m-1})`, this says `b M_G = G b − F h`. Right multiplication by the adjugate
gives `N_G b = G b adj(M_G) − F h adj(M_G)`. Its first coordinate is an explicit polynomial
identity `N_G(X) = U(X,Y) G(X,Y) + V(X,Y) F(X,Y)` (NM), where `U = (b adj(M_G))_0` and
`V = −(h adj(M_G))_0`. Thus no ideal-membership oracle is needed." And, for the boundary column
of the multiplication by `Y`: "write `−X^i f_t(X) = s_t(X) q(X) + r_t(X)` ... The exact identity
`Y X^i Y^{m-1} − Σ_{t<m} r_t(X) Y^t = X^i F + Σ_{t<m} s_t(X) q(X) Y^t` provides this boundary
column."

Both identities are derived for arbitrary integer terms and every size `m` (a parameter of the
Lean statement). The terms may contain variables, so an identity derived with `X`, `Y` free is
the identity at every pair of values:

* `membership_ring`, `boundary_ring`: the identities over a commutative ring;
* `norm_membership`: from `b M = G b − F h` (as `Mᵀ b = G b − F h`), iPRA derives
  `det(M) b = G (b adj M) − F (h adj M)`, coordinatewise;
* `norm_membership_unit`: with a coordinate `b_i = 1`, (NM):
  `det M = G (b adj M)_i − F (h adj M)_i`;
* `boundary_column`: from `−x f_t = s_t q + r_t` for every `t < m`,
  `y_m x − Σ_t r_t b_t = x (y_m + Σ_t f_t b_t) + Σ_t s_t q b_t`, where `x` is the value of
  `X^i`, `b_t` of `Y^t` and `y_m` of `Y^m`.

Not derived: the monic reduction that produces `M_G` and `h`, the monic division in `X`, and
the assembly of the `md` action columns into a unit-and-action certificate.
-/

namespace LeanProofs.IPRA.Foundations.NormMembership

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The adjugate turns `b M = G b − F h` into `det(M) b = G (b adj M) − F (h adj M)`. -/
theorem membership_ring (M : Matrix (Fin k) (Fin k) R) (b h : Fin k → R) (F G : R)
    (e : Mᵀ *ᵥ b = G • b - F • h) :
    M.det • b = G • (M.adjugateᵀ *ᵥ b) - F • (M.adjugateᵀ *ᵥ h) := by
  have h1 : M.adjugateᵀ *ᵥ (Mᵀ *ᵥ b) = M.det • b := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_adjugate,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [← h1, e, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]

/-- The boundary column of the multiplication by `Y`. -/
theorem boundary_ring (b f r s : Fin k → R) (x q yTop : R)
    (hd : ∀ t, -(x * f t) = s t * q + r t) :
    yTop * x - ∑ t, r t * b t = x * (yTop + ∑ t, f t * b t) + ∑ t, s t * q * b t := by
  have key : ∑ t, r t * b t + x * ∑ t, f t * b t + ∑ t, s t * q * b t = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun t _ => by linear_combination (-(b t)) * hd t
  linear_combination (-1 : R) * key

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {k : ℕ}

/-- `prop:norm-to-module`: from `b M = G b − F h`, the identity
`det(M) b = G (b adj M) − F (h adj M)`. -/
theorem norm_membership {M : Mat k n} {b h : Vec k n} {F G : ZT n}
    (e : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec (Mat.transpose M) b)
      (Vec.sub (Vec.smul G b) (Vec.smul F h))) :
    Γ ⊢[PRAAx] Vec.eqFm (Vec.smul (Mat.det M) b)
      (Vec.sub (Vec.smul G (Mat.mulVec (Mat.transpose (Mat.adj M)) b))
        (Vec.smul F (Mat.mulVec (Mat.transpose (Mat.adj M)) h))) := by
  have e' := Vec.toZ_eq e
  simp only [Mat.toZ_mulVec, Mat.toZ_transpose, Vec.toZ_sub, Vec.toZ_smul] at e'
  refine Vec.derive ?_
  simp only [Mat.toZ_mulVec, Mat.toZ_transpose, Mat.toZ_adj, Mat.toZ_det, Vec.toZ_sub,
    Vec.toZ_smul]
  exact membership_ring _ _ _ _ _ e'

/-- (NM): with a coordinate `b_i = 1`, the norm is `G U − F V'` with explicit cofactor terms
`U = (b adj M)_i`, `V' = (h adj M)_i`. -/
theorem norm_membership_unit {M : Mat k n} {b h : Vec k n} {F G : ZT n}
    (e : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec (Mat.transpose M) b)
      (Vec.sub (Vec.smul G b) (Vec.smul F h)))
    (i : Fin k) (hi : Γ ⊢[PRAAx] ZT.eq (b i) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det M)
      (G * Mat.mulVec (Mat.transpose (Mat.adj M)) b i -
        F * Mat.mulVec (Mat.transpose (Mat.adj M)) h i) := by
  have e₀ : Γ ⊢[PRAAx] ZT.eq (Mat.det M * b i)
      (G * Mat.mulVec (Mat.transpose (Mat.adj M)) b i -
        F * Mat.mulVec (Mat.transpose (Mat.adj M)) h i) :=
    conjFin_elim (norm_membership e) i
  have e₁ := ZT.toZ_eq e₀
  have e₂ := ZT.toZ_eq hi
  refine ZT.derive ?_
  rw [ZT.toZ_mul, e₂, ZT.toZ_natLit, Nat.cast_one, _root_.mul_one] at e₁
  exact e₁

/-- The boundary column of the multiplication by `Y` in `prop:norm-to-module`. -/
theorem boundary_column {b f r s : Vec k n} {x q yTop : ZT n}
    (hd : ∀ t, Γ ⊢[PRAAx] ZT.eq (-(x * f t)) (s t * q + r t)) :
    Γ ⊢[PRAAx] ZT.eq (yTop * x - ZT.sumFin fun t => r t * b t)
      (x * (yTop + ZT.sumFin fun t => f t * b t) + ZT.sumFin fun t => s t * q * b t) := by
  have e : ∀ t, -(ZT.toZ Γ x * ZT.toZ Γ (f t)) =
      ZT.toZ Γ (s t) * ZT.toZ Γ q + ZT.toZ Γ (r t) := fun t => by
    have := ZT.toZ_eq (hd t)
    simpa only [ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_add] using this
  refine ZT.derive ?_
  simp only [ZT.toZ_sub, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sumFin]
  exact boundary_ring _ _ _ _ _ _ _ e

end LeanProofs.IPRA.Foundations.NormMembership
