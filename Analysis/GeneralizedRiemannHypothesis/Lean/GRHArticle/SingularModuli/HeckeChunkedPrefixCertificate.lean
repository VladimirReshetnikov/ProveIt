import GRHArticle.SingularModuli.HeckePackedPrefixCertificate
import Mathlib.Data.List.SplitLengths

/-!
# Chunked evaluation of packed prefix certificates

The chunks change only how the packed integers are assembled. The same
divisibility test proves vanishing of the requested coefficients.
-/

namespace GRHArticle.SingularModuli

/-- Split the input into consecutive blocks of at most 48 coefficients. -/
def polynomialDigitChunks (l : List α) : List (List α) :=
  (List.replicate (l.length/48+1) 48).splitLengths l

@[simp] theorem flatten_polynomialDigitChunks (l : List α) :
    (polynomialDigitChunks l).flatten = l := by
  apply List.flatten_splitLengths
  rw [List.sum_replicate, smul_eq_mul]
  omega

namespace IntegerPolynomialExpression

/-- Evaluate with small blocks at the leaves of the expression. -/
def packedEvalChunked (w : ℕ) : IntegerPolynomialExpression → ℤ
  | .coefficients cs =>
    (packPolynomialDigitChunks w (polynomialDigitChunks (cs.map Int.toNat)) : ℤ) -
      (packPolynomialDigitChunks w (polynomialDigitChunks (cs.map fun a ↦ (-a).toNat)) : ℤ)
  | .add a b => a.packedEvalChunked w + b.packedEvalChunked w
  | .sub a b => a.packedEvalChunked w - b.packedEvalChunked w
  | .mul a b => a.packedEvalChunked w * b.packedEvalChunked w
  | .pow a n => a.packedEvalChunked w ^ n

theorem packedEvalChunked_eq (w : ℕ) (e : IntegerPolynomialExpression) :
    e.packedEvalChunked w = e.packedEval w := by
  induction e with
  | coefficients cs =>
    simp only [packedEvalChunked, packPolynomialDigitChunks_eq, flatten_polynomialDigitChunks]
    rfl
  | add a b ha hb => rw [packedEvalChunked, ha, hb, packedEval]
  | sub a b ha hb => rw [packedEvalChunked, ha, hb, packedEval]
  | mul a b ha hb => rw [packedEvalChunked, ha, hb, packedEval]
  | pow a n ha => rw [packedEvalChunked, ha, packedEval]

/-- Check for zero low coefficients using the chunked evaluator. -/
def checkZeroPrefixChunked (e : IntegerPolynomialExpression) (N : ℕ) : Prop :=
  let w := e.magnitudeBound.log2+1
  e.packedEvalChunked w % ((1 <<< (w*N) : ℕ) : ℤ) = 0

instance (e : IntegerPolynomialExpression) (N : ℕ) : Decidable (e.checkZeroPrefixChunked N) := by
  unfold checkZeroPrefixChunked
  infer_instance

theorem checkZeroPrefixChunked_iff (e : IntegerPolynomialExpression) (N : ℕ) :
    e.checkZeroPrefixChunked N ↔ e.checkZeroPrefix N := by
  unfold checkZeroPrefixChunked checkZeroPrefix
  dsimp only
  rw [packedEvalChunked_eq]

end IntegerPolynomialExpression

end GRHArticle.SingularModuli
