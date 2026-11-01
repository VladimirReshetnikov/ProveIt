# Finite sums of signed residual squares in IΣ₁ models

`InternalResidualSquares.squareSum_zero_iff` proves for any finite list of
integer-expression syntax and every assignment in any IΣ₁ model that a sum
of its squares is zero exactly when every individual residual is zero. The
proof represents each square by the square of the magnitude of its signed
pair, then uses the no-zero-divisor and zero-sum properties of the arithmetic
model. Its [paired replay](../../reviews/internal-residual-squares-model-replay/README.md)
matched on a historical provider.

This lemma supplies the conjunction step for a possible degree-4 gate
compiler. It does not yet encode a concrete equation, establish a degree
bound, construct positive witnesses for gate values, or provide a native
iPRA derivation; those are separate obligations.
