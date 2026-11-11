# A direct positive Pell root: 14 inputs, 79 operations, degree 60

This candidate has **14 strictly positive inputs, 79 live operations and
exact degree 60** at the authenticated compact44 ports. Its positive-zero
existence is equivalent to that of the reviewed 84/60 graph for arbitrary
integer ports with `beta>0`; it is submitted for independent review. This is
an external mathematical comparison. It is not a new Lean/iPRA theorem,
PDF/JSON file-semantics binding, provider-ancestry replay, or global minimum.

In the 84 graph put

```
b=J*beta, q=b+1, M=q³*b, m=X*Y²,
k=eta+zeta, ell=m*k, L=ell+k−r_old,
D=1+ell*(ell+k).
```

Its first residual is `A0_old=(M*L)²−M²*D=M²*(L²−D)`. The remaining
four residuals do not use the first-root input `r_old`. Replace that input
by a positive input tau and use the first residual

```
A0_new=tau²−D.
```

All other residuals, inputs and ports are retained. No equality of the two
whole output polynomials is asserted. The checker validates the exact graph
delta and the factor identity on finite signed-integer assignments; the
factor identity itself is a commutative-ring identity.

## Positive-zero maps

If the old graph vanishes, every squared residual is zero. Positive J and
beta imply `M>0`, so `L²=D`. Since positive inputs give
`D=1+ell*(ell+k)>0`, the integer `tau=|L|` is positive. Replacing the first
input by tau makes the new first residual zero while preserving all the
others.

Conversely, a positive new zero has `tau²=D`. Choose the old first input

```
r_old=ell+k+tau > 0.
```

Then `L=−tau`, the old first residual is zero, and every other residual is
unchanged. Thus both positive-zero existence implications hold, without
requiring the two first-coordinate values to agree. The cited 84 graph's
compact44 endpoint and external calibration limitations remain inherited.

## Count and degree

Relative to the 84 source, the literal graph deletes `M`, `L`, `Z=M*L`,
`M²`, and `M²*D`; it changes the remaining square to `tau²` and subtracts D.
Thus `84−5=79`. The checker verifies this exact row transformation, unique
names, liveness of every gate, all 14 inputs and all four fixed leaves, and
both P72/P115 compact44 payload hashes.

The first residual now has degree at most 22: `ell` has degree at most 11
and `k` at most 1. The unchanged main residual has degree at most 30 by the
exact cancellation proof in the reviewed 84 packet. The remaining
auxiliary, strong and guard residuals have degree at most 23, 22 and 3.
Hence the sum of squares has degree at most 60. The complete graph on an
all-inputs-equal ray with authenticated actual ports has degree 60 and
leading coefficient 979167194 modulo 1000000007, establishing exact
specialized integer degree 60.

This improves the named 84/60 graph by five operations at the same degree and
variable count, and trades more operations for lower degree against the
14-variable 65/150 PDF equation. These are numeric comparisons to named
records, not an internal proof about the PDF or global optimality.

```
python3 -I -S -B research/ordinary14-direct-pell79/check.py > /tmp/direct-pell79.json
cmp /tmp/direct-pell79.json research/ordinary14-direct-pell79/result.json
```

The finite checker does not substitute for the unbounded root argument or
the degree upper bound.

Independent mathematical review is recorded in
`../../reviews/ordinary14-direct-pell79-math-independent/`.
