import IPRADerivations.Algebra.AdjugateInverse

/-!
# Similarity equivariance of the geometric median objective

Packet: `probability/median_ipra_constructive_proofs`, Proposition "Similarity equivariance": "If
`T(a) = c R a + b`, where `c > 0` and `R` preserves the Euclidean norm, then `G_{T(x)}(T(a)) = c G_x(a)`
… For each `i`, `‖T(x_i) − T(a)‖₂ = c ‖R(x_i − a)‖₂ = c ‖x_i − a‖₂`. Sum over `i`."

For integer vectors of every fixed dimension `k` (`Core/LinearAlgebra`) and a matrix `R` with a
derivable `Rᵀ R = I`, in squared form (norms of rational vectors are compared through their squares):

* `orth_norm`: `‖R v‖² = ‖v‖²`;
* `similarity_sq`: `‖T(x) − T(a)‖² = c² ‖x − a‖²` for `T(y) = c R y + b`.

Summing the square roots over the sample points is the reading of the proposition; the real square
roots and the geometric median itself are not formalized.
-/

namespace LeanProofs.IPRA.Probability.MedianSimilarity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.AdjugateInverse (toZ_of_eqFm)
open Matrix
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-- `T(y) = c R y + b`. -/
def simT (c : ZT n) (R : Mat k n) (b y : Vec k n) : Vec k n := Vec.add (Vec.smul c (Mat.mulVec R y)) b

/-- An orthogonal matrix preserves the squared norm. -/
theorem orth_norm {R : Mat k n} (h : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul (Mat.transpose R) R) Mat.one)
    (v : Vec k n) :
    Γ ⊢[PRAAx] ZT.eq (Vec.dot (Mat.mulVec R v) (Mat.mulVec R v)) (Vec.dot v v) := by
  have h' := toZ_of_eqFm h
  rw [Mat.toZ_mul, Mat.toZ_transpose, Mat.toZ_one] at h'
  refine ZT.derive ?_
  rw [Vec.toZ_dot, Vec.toZ_dot, Mat.toZ_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h', Matrix.one_mulVec]

/-- "Similarity equivariance", squared: `‖T(x) − T(a)‖² = c² ‖x − a‖²`. -/
theorem similarity_sq {R : Mat k n} (h : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul (Mat.transpose R) R) Mat.one)
    (c : ZT n) (b x a : Vec k n) :
    Γ ⊢[PRAAx] ZT.eq (Vec.dot (Vec.sub (simT c R b x) (simT c R b a)) (Vec.sub (simT c R b x) (simT c R b a)))
      (c * c * Vec.dot (Vec.sub x a) (Vec.sub x a)) := by
  have o := ZT.toZ_eq (orth_norm h (Vec.sub x a))
  refine ZT.derive ?_
  rw [Vec.toZ_dot, Vec.toZ_dot, Mat.toZ_mulVec] at o
  simp only [simT, Vec.toZ_dot, Vec.toZ_sub, Vec.toZ_add, Vec.toZ_smul, Mat.toZ_mulVec, ZT.toZ_mul] at o ⊢
  rw [Matrix.mulVec_sub] at o
  have e : ZT.toZ Γ c • (Mat.toZ Γ R *ᵥ Vec.toZ Γ x) + Vec.toZ Γ b -
      (ZT.toZ Γ c • (Mat.toZ Γ R *ᵥ Vec.toZ Γ a) + Vec.toZ Γ b) =
      ZT.toZ Γ c • (Mat.toZ Γ R *ᵥ Vec.toZ Γ x - Mat.toZ Γ R *ᵥ Vec.toZ Γ a) := by
    rw [smul_sub]; abel
  rw [e, smul_dotProduct, dotProduct_smul, o, smul_eq_mul, smul_eq_mul, ← _root_.mul_assoc]

end LeanProofs.IPRA.Probability.MedianSimilarity
