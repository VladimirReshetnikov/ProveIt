# A q³ quotient: 13 natural inputs, 93 operations, degree 56

This external graph replaces the positive Y coordinate in the
[13/95/28 natural C-fold graph](../ordinary13-natural-cfold-forced-x95-degree28/)
by `Y=q³*s`, where `s=n_Y+1`. It has 13 nonnegative inputs and 93 live binary
operations. Its exact degree is 56 at the authenticated compact44 ports.
The operation saving trades against the parent's degree 28. The earlier
parent's compact-port calibration and endpoint qualifications remain inherited.

## Both zero maps in the intended models

Work in a model V of IΣ₁ with the repository's ordered natural-ring interface
and its signed difference ring. Assume beta is represented by a nonnegative
model natural; the remaining ports can be arbitrary signed model values for
this local transfer. Write

```
b = J*beta,  q = 1+b,  h=q³,  M=h*b,
Z = M*t + Y*b − h*Bt,
N = 1 + ell*(ell+k),
```

where `t=ell+k+r−k*C`, and the graph's `Y=n_Y+1` is positive. Then `q,h>0`
and N is a model natural. At any parent zero the first squared residual
vanishes, so `Z²=M²*N`. Regard signed Z as a difference of model naturals;
its natural magnitude has the same square. The equality supplies
`h² | |Z|²`. The existing model theorem
[`ArithmeticSquareDivisibility.dvd_of_square_dvd`](../../Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean)
then gives `h | |Z|`, hence `h | Z` in the difference ring. Since
`Z=h*b*t+Y*b−h*Bt`, it follows that `h | Y*b`.

There is no coprimality axiom hidden here: the polynomial identity

```
1 = h − b*(b² + 3*b + 3)
```

follows from `h=(1+b)³`. Multiplying by Y shows `h | Y`. Because Y and h are
positive, the quotient is a positive model natural `s`; write `s=n_Y'+1`.
The quotient exists in the nonstandard model itself, not merely in the
standard integers. The signed divisibility step and return to a natural
quotient use the usual magnitude/order properties of the model difference
ring; their application to this graph has not been elaborated in Lean.

Conversely, from any child valuation define `Y=h*(n_Y+1)` in the parent and
use its positive predecessor as parent `n_Y`; all other coordinates agree.
Set `Znew=b*(t+s)−Bt`. Direct ring identities give

```
Z = h*Znew
A0_parent = h² * A0_child.
```

The other three residuals agree exactly. Each full output is the sum of four
squares. Because `h>0`, the displayed residual identities establish both
zero maps, including positive quotient reconstruction; they do **not** assert
that the two full output polynomials are equal. No root-switch or extra
positivity of the first-root coordinate is needed for this local map.

## Size, fixed ports, and proof status

A source-pinned checker authenticates the compact P72/P115 port bytes and
checks their stated bounds. The degree upper bound is 56: the residual
syntactic bounds are 22, 21 and 22 for A0, Fam and g72. For A1, its apparent
higher leading term cancels using the checked all-ring identity

```
(U*(X+a*c)+H*S)² − U²*(1+(a²+H)*c²)
= U²*(2*X*a*c+X²−1−H*c²)
  + 2*U*(X+a*c)*H*S + H²*S².
```

The right side has degree at most 28. The complete output has degree at most
56, and an all-inputs-equal ray modulo 1,000,000,007 has degree 56 with
nonzero leading coefficient 785330250 at the authenticated ports. This proves
exact degree for that tuple, not for every possible port specialization.

For context, the compact-port natural candidates [13/95/28](../ordinary13-natural-cfold-forced-x95-degree28/),
[13/94/50](../ordinary13-natural-cfold-forced-x94-degree50/), and
[13/86/99](../ordinary13-natural-forced-w86/) trade operations against degree.
A distinct [13/82/56 positive-domain construction](../ordinary13-residue-first82/)
has an [independent external standard-integer review](../../reviews/ordinary13-residue-first82-independent/);
its domain and proof path differ. These examples are not an exhaustive
frontier. The compact ports also differ from the retained current-2011 PDF
ports; no equality of those encodings is asserted.

**No Lean model transfer or iPRA endpoint has been elaborated for this graph.**
The cited model square-divisibility theorem and the finite checker do not by
themselves discharge that endpoint or the parent's inherited ancestry.

## Reproduction

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-natural-qcube-quotient93-degree56/build.py
python3 -I -S -B research/ordinary13-natural-qcube-quotient93-degree56/check.py
```

The checker verifies the exact graph delta, liveness, free-ring identities,
source theorem signature, output wiring, compact port hashes and degree bounds.
Its deterministic output is [receipt.json](receipt.json); it does not invoke Lean.
