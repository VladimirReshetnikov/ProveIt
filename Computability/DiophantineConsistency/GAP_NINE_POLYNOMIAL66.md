# The checked H2082 nine-variable polynomial

`GapNinePolynomial66.polynomial ports a` supplies actual
`MvPolynomial (Fin 9) ℤ` data. Its finite scalar recipe uses every one of the
6 constant,36 linear and43 quadratic coefficient records in the checked
H2082 kernel tables. The four integer coefficient ports are ordered
`beta,K,MC,MF`; they remain parameters at this stage.

The natural input order is `b,g,h,s,w,C,i,j,n`. The recipe adds one to every
input except the internal CRT index `j`. It forms the source radix
`B=4096*2^(2*a)*b^2`, source block `L=b*B^2200`, actual source words and
reduced rank. Its binomial threshold is

```
N = 2^(15*a+79) * B^1162.
```

There is no extra factor `b` in that threshold. The remainder is the checked
free-carrier arithmetic tail and its four-factor norm finalizer. Every power
in the expression has a fixed natural exponent, so it is an ordinary integer
polynomial rather than an exponential Diophantine expression.

`eval_polynomial` gives its exact integer-ring evaluation.
`eval_polynomial_nat` proves that evaluation at any natural input vector is
exactly `GapNineSource66.naturalValue`, under the kernel/geometry validity
contract already discharged by the port-size bounds. Consequently
`exists_natural_zero_iff_source_portBounds` and its compact54 specialization
identify polynomial roots with the actual22 equations `GapSource66.rows`.
No source-zero or positive-source witness premise is supplied to the proof.

For the coherent compact54 widths429959 and434054, the half-height parameter
is432007, giving height exponent864014, radix scale exponent864026 and
threshold scale exponent6480184. `compact54_zero_iff_split59` also proves that
this actual H2082 polynomial and the earlier split116 polynomial have exactly
the same natural root existence, when `beta>0` and the stated port bounds
hold. It uses the checked positive affine source change.

The ring-homomorphism proofs use explicit finite coefficient-map branches.
`tools/generate_gap_nine_polynomial66.py --check` reproduces the file from the
checked H2082 table and frozen proof template without writing. Dedicated
checks audit all public theorems; only Lean's standard axioms occur.

This closes the actual polynomial-to-source arithmetic bridge. The separate
443/450-operation literal DAG identification, materialized whole-tuple native
calibration to ZFC refutation and the object-language ZFC biconditional remain
further obligations. No operation-count or exact-degree claim is inferred
solely from this polynomial definition.
