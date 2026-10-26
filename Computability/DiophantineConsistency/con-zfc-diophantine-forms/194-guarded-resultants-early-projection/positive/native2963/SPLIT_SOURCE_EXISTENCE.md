# Checked unbounded existence for the split equation

[`SplitSourceExistence.lean`](Lean/DiophantineConsistency/SplitSourceExistence.lean)
closes the unbounded existence argument for any supplied source parameters
satisfying `SplitSourceWords.Valid`. Its main result is

```
HasZero d a
  iff exists z : Fin 31 -> Nat,
       some z_i>0 and every target coefficient of sourcePolynomial d z is zero.
```

For completeness it chooses the explicit power of two
`b=cofinalCap z=2^(sum_i z_i+1)`. Both every digit and their sum are below
`b`. Since every source weight is at most 116,

```
g=sum_i z_i*B^w_i <=(sum_i z_i)*B^116 < b*B^116.
```

A positive digit makes `g>0`. The checked bounded source contract therefore
constructs the free-carrier witnesses and a strictly positive final witness.
This proof-side choice of `b` does not occur inside the final polynomial
and adds no variable exponent to that equation. Soundness obtains the
decoded tuple from the checked ratio/source contract, and `g>0` forces some
digit to be positive. No boundedness or cofinality premise survives.

`HasZero` uses positive `b,g,h,s,w,C,i,n` and a natural absorbed CRT index.
Its strictly positive CRT input is `j_plus=j+1`. `positiveValue` exposes the
exact nine-coordinate order

```
b,g,h,s,w,C,i,j_plus,n.
```

`naturalValue` replaces every positive coordinate by its natural input plus
one. The internal absorbed index is exactly the seventh-indexed input
`x 7`, including zero. The module proves the bijective existence translation
for `Fin 9 -> Nat`, then its equivalence with the same nonzero source
coefficient witness and the corresponding negated no-zero statement.

These are integer evaluator/domain and existence theorems. They do not bind
the supplied kernels to a particular native source or fixed coefficient
tuple, and do not identify source zeros with machine halting or refutations.
The explicit nonzero-source-tuple condition must be preserved until a literal
source binding proves that the all-zero shifted tuple is excluded.

Regression checks include zero and unit digit tuples, their explicit caps
and codes, and the smallest positive tuple with internal `j=0`. All audited
proofs use only the standard Lean axioms.
