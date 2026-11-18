import IPRADerivations.Foundations.NullVectorDeterminant

/-!
# From a unit-and-action certificate to an elimination identity (`ipra_presentations_to_witnesses`, "Optional converse through one adjugate identity")

Packet: `foundations/ipra_presentations_to_witnesses`, the paragraph after
`thm:annihilator-to-module`: "suppose a unit-and-action certificate is given. Fix `k`, put
`C = X_k I − M_k`, and put `q_k(T) = det(T I − M_k)`. The action identities say, for the row
`b = (b_1, …, b_D)`, `b C = r`, `r_j = Σ_ℓ h_{kjℓ} F_ℓ`. Multiply by `adj C` and use the finite
cofactor identity `C adj C = (det C) I`. Coordinate `j` gives
`q_k(X_k) b_j = Σ_ℓ (Σ_t h_{ktℓ} (adj C)_{tj}) F_ℓ`. Multiply by `c_j`, sum over `j`, and use the
unit identity `1 − Σ_j c_j b_j = Σ_ℓ h_ℓ F_ℓ`. The result is an explicit identity
`q_k(X_k) = Σ_ℓ u_{kℓ} F_ℓ`, with `u_{kℓ} = q_k(X_k) h_ℓ + Σ_j c_j Σ_t h_{ktℓ} (adj C)_{tj}`."

Derived for arbitrary integer terms, every size `D` and every number `s` of equations (both
parameters of the Lean statement), on the determinant and adjugate of `Core/LinearAlgebra`:

* `converse_ring`, `converse_witness_ring`, `char_ring`: the identities over a commutative
  ring;
* `adjugate_converse`: from the action identities `(b C)_j = Σ_ℓ H_{jℓ} F_ℓ` and the unit
  identity `1 − c · b = Σ_ℓ h_ℓ F_ℓ`, iPRA derives `det C = Σ_ℓ u_ℓ F_ℓ` with the packet's
  explicit `u_ℓ = det(C) h_ℓ + Σ_j c_j Σ_t H_{tℓ} (adj C)_{tj}`;
* `char_vanish`: at a point where the residuals vanish, that is with `c · b = 1` and
  `b M = u b`, iPRA derives `det(u · 1 − M) = 0`: the observable value `u` is a root of the
  characteristic polynomial of `M`. No nonzero coordinate of `b` is selected, and no
  primitivity is used.

For rational data `M = A / Δ`, `u = a / q` the cleared action identity is `b (q A) = (Δ a) b`,
and `char_vanish` applies to the integer matrix `q A` and the value `Δ a`.

Not derived: the expansion of `det(T · 1 − M)` into coefficients of a monic polynomial of degree
`D`, hence the connection with the rational-root bounds of `Foundations/RationalRootDegree`.
-/

namespace LeanProofs.IPRA.Foundations.AdjugateConverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R] {k : ℕ}

/-- One adjugate identity: `b C = r` and `1 − c · b = e` give `det C = det(C) e + c · (r adj C)`. -/
theorem converse_ring (C : Matrix (Fin k) (Fin k) R) (b r c : Fin k → R) (e : R)
    (h : Cᵀ *ᵥ b = r) (hu : 1 - c ⬝ᵥ b = e) :
    C.det = C.det * e + c ⬝ᵥ (C.adjugateᵀ *ᵥ r) := by
  have h1 : C.adjugateᵀ *ᵥ r = C.det • b := by
    rw [← h, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_adjugate,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h1, dotProduct_smul, smul_eq_mul, ← hu]
  ring

/-- The same with the residuals written as combinations of `F_1, …, F_s`: the witnesses of
`det C` are `u_ℓ = det(C) h_ℓ + Σ_j c_j Σ_t H_{tℓ} (adj C)_{tj}`. -/
theorem converse_witness_ring {s : ℕ} (C : Matrix (Fin k) (Fin k) R) (b c : Fin k → R)
    (H : Matrix (Fin k) (Fin s) R) (hu F : Fin s → R)
    (h : Cᵀ *ᵥ b = H *ᵥ F) (hu' : 1 - c ⬝ᵥ b = hu ⬝ᵥ F) :
    C.det = ∑ ℓ, (C.det * hu ℓ + ∑ j, c j * ∑ t, H t ℓ * C.adjugate t j) * F ℓ := by
  have e2 : c ⬝ᵥ (C.adjugateᵀ *ᵥ (H *ᵥ F)) =
      ∑ ℓ, (∑ j, c j * ∑ t, H t ℓ * C.adjugate t j) * F ℓ := by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    simp only [dotProduct, Matrix.vecMul, Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun t _ => by ring
  refine (converse_ring C b _ c _ h hu').trans ?_
  rw [e2]
  simp only [dotProduct]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- With a unit combination and the eigenvector equation, the characteristic determinant
vanishes. -/
theorem char_ring (M : Matrix (Fin k) (Fin k) R) (b c : Fin k → R) (u : R)
    (h : Mᵀ *ᵥ b = u • b) (hu : c ⬝ᵥ b = 1) :
    (u • (1 : Matrix (Fin k) (Fin k) R) - M).det = 0 := by
  have h0 : (u • (1 : Matrix (Fin k) (Fin k) R) - M)ᵀ *ᵥ b = 0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, h, _root_.sub_self]
  refine (converse_ring _ b 0 c 0 h0 (by rw [hu, _root_.sub_self])).trans ?_
  simp

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {k : ℕ}

/-- The optional converse: a unit-and-action certificate gives the elimination identity
`det C = Σ_ℓ u_ℓ F_ℓ` with explicit witnesses. -/
theorem adjugate_converse {s : ℕ} {C : Mat k n} {b c : Vec k n} {H : Fin k → Fin s → ZT n}
    {hu F : Fin s → ZT n}
    (h : ∀ j, Γ ⊢[PRAAx] ZT.eq (Mat.mulVec (Mat.transpose C) b j)
      (ZT.sumFin fun ℓ => H j ℓ * F ℓ))
    (hu' : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 - Vec.dot c b) (ZT.sumFin fun ℓ => hu ℓ * F ℓ)) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det C)
      (ZT.sumFin fun ℓ => (Mat.det C * hu ℓ +
        ZT.sumFin fun j => c j * ZT.sumFin fun t => H t ℓ * Mat.adj C t j) * F ℓ) := by
  have e₁ : (Mat.toZ Γ C)ᵀ *ᵥ Vec.toZ Γ b =
      (Matrix.of fun j ℓ => ZT.toZ Γ (H j ℓ)) *ᵥ (fun ℓ => ZT.toZ Γ (F ℓ)) := by
    funext j
    rw [← Mat.toZ_transpose, ← Mat.toZ_mulVec, Vec.toZ_apply, ZT.toZ_eq (h j), ZT.toZ_sumFin]
    simp [Matrix.mulVec, dotProduct]
  have e₂ : 1 - Vec.toZ Γ c ⬝ᵥ Vec.toZ Γ b =
      (fun ℓ => ZT.toZ Γ (hu ℓ)) ⬝ᵥ (fun ℓ => ZT.toZ Γ (F ℓ)) := by
    have e := ZT.toZ_eq hu'
    rw [ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_one, Vec.toZ_dot, ZT.toZ_sumFin] at e
    rw [e]
    simp [dotProduct]
  refine ZT.derive ?_
  rw [Mat.toZ_det, ZT.toZ_sumFin]
  refine (converse_witness_ring _ _ _ _ _ _ e₁ e₂).trans ?_
  rw [← Mat.toZ_adj]
  exact Finset.sum_congr rfl fun ℓ _ => by simp

/-- At a point with `c · b = 1` and `b M = u b`, the value `u` is a root of the characteristic
polynomial: `det(u · 1 − M) = 0`. -/
theorem char_vanish {M : Mat k n} {b c : Vec k n} {u : ZT n}
    (hu : Γ ⊢[PRAAx] ZT.eq (Vec.dot c b) (ZT.natLit 1))
    (h : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec (Mat.transpose M) b) (Vec.smul u b)) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (Mat.sub (Mat.smul u Mat.one) M)) (ZT.natLit 0) := by
  have e₁ := Vec.toZ_eq h
  rw [Mat.toZ_mulVec, Mat.toZ_transpose, Vec.toZ_smul] at e₁
  have e₂ := ZT.toZ_eq hu
  rw [Vec.toZ_dot, ZT.toZ_natLit, Nat.cast_one] at e₂
  refine ZT.derive ?_
  rw [Mat.toZ_det, Mat.toZ_sub, Mat.toZ_smul, Mat.toZ_one, ZT.toZ_natLit, Nat.cast_zero]
  exact char_ring _ _ _ _ e₁ e₂

end LeanProofs.IPRA.Foundations.AdjugateConverse
