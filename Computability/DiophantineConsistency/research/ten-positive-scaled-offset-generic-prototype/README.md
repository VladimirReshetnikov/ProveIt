# Generic scaled first-ordinate offset

`TenPositiveScaledOffsetGeneric.scaled_offset` works in every IΣ₁ model. For
positive X,Y,μ and arbitrary r, let `P=X*(μY)²` and let
`K=2*ycoord(r+1,2*(P-1)+1)`. It constructs a natural ρ with

    K = (2r+1)+1 + μ²*ρ.

The proof uses the exact first-Pell ordinate residue and constructs the
multiple explicitly as `ρ=4*X*Y²*s`. It makes no claim that ρ is positive,
assumes no 80 graph zero, and does not itself construct the remaining
carrier, an 80 zero, an equivalence, or an iPRA proof.

The accepted guarded check `observations/offset-attempt01/` produced
`/tmp/scaled-offset-generic-atdyyldd/ScaledOffsetGeneric.olean`, SHA-256
`0b1b5c7eddec9074d267105c57590279518d71dd545daf2f5b35c20eb1d02b8e`.
The runner individually resolves, pins and rechecks its source-direct
`ArithmeticPellCongruences` object. Broader transitive source-object,
project/package and dynamic-library coverage remains inherited.
