/-!
# Balanced integer arithmetic on dyadic intervals

The integer certificates combine adjacent blocks of the same size. Reducing
a sum or a product therefore requires logarithmic recursion depth.
-/

namespace GRHArticle.ProgressionFree

/-- Sum over a dyadic block with logarithmic recursion depth. -/
def integerDyadicSum (f : Nat → Nat) : Nat → Nat → Nat
  | 0, a => f a
  | h+1, a => integerDyadicSum f h a + integerDyadicSum f h (a+2^h)

/-- Multiply fixed-point integer factors, rounding down at each internal node. -/
def integerDyadicScaledProduct (scale : Nat) (f : Nat → Nat) : Nat → Nat → Nat
  | 0, a => f a
  | h+1, a => integerDyadicScaledProduct scale f h a *
      integerDyadicScaledProduct scale f h (a+2^h) / scale

end GRHArticle.ProgressionFree
