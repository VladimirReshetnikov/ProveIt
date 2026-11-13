# Forced positive coordinates: 14 natural inputs, 82 operations, degree 107

This is a proposed external reduction from the reviewed [natural-domain
85-operation graph](../ordinary14-root74-natural-cancel85/). It has the same
zero existence for natural inputs when `beta > 0` and `K0 >= 0`, with
arbitrary integer `MC` and `MF`; these are the port assumptions inherited
from the positive guard transformation. Its zero maps below are explicit.
The zero-transfer argument has received [independent review](../../reviews/ordinary14-root74-natural-forced82-independent/README.md). This packet does not provide a Lean or
iPRA theorem, a binding to the displayed PDF, a fresh provider replay, or an
optimality claim; all endpoint qualifications of the parent are inherited.

## Construction and zero transfers

In the 85 graph the natural inputs `n_f`, `n_r`, `n_y` are first incremented
to positive variables `f`, `r`, `y`. Delete those three gates and use the
corresponding natural inputs directly in their consumers. Leave all other
gates and inputs unchanged. Denote the new coordinates simply `f`, `r`,
`y` in the argument below. As a polynomial identity over the integers, the
82 output at `(f,r,y)` equals the 85 output at
`(n_f,n_r,n_y) = (f−1,r−1,y−1)`; the other coordinates agree. This identity
is meaningful for signed inputs, although the zero transfers below use only
natural inputs.

For a zero of the 82 graph, every other coordinate that was shifted by the
85 graph remains positive. In particular `q >= 2`, `X >= 2`, `Y >= 8`,
`k > 0`, `ell = X*Y^2*k > 0`, and `a = X*Y+Y > 0`. The unchanged product
of five integer factors is one. The argument in the reviewed
[75-operation parent](../ordinary14-negative-pell75/) still applies: the
first factor cannot be −1 by the negative-Pell lemma, and the three other
restricted factors cannot be −1 modulo 4. Those residue arguments are valid
for arbitrary integer `f`, `r`, and `y`; the negative-Pell lemma applies
because `m = X*Y^2 >= 2` and `k > 0`. Thus each factor equals +1, including

```
F0 = r² − ell*(ell+k) = 1
Fs = 1 + I² − Q = 1
Fa = y² − Q*(y²−V²) = 1
Q = Delta*(f²−1),  Delta = a²+4*a+3 > 1.
```

These equations force the three new natural coordinates to be positive:

* `r=0` contradicts `r² = 1+ell*(ell+k) > 0`.
* `f=0` gives `Q=−Delta < 0`, contradicting `Q=I² >= 0` from `Fs=1`.
* `y=0` gives `Q*V²=1` from `Fa=1`, impossible because the left side is
  divisible by `Delta > 1`.

Consequently `f−1`, `r−1`, and `y−1` are natural numbers and the displayed
polynomial identity maps the 82 zero to an 85 zero. Conversely, given any
85 zero, set `f=n_f+1`, `r=n_r+1`, `y=n_y+1` and retain the other
coordinates; the polynomial identity maps it to an 82 zero. These maps are
mutually inverse on zeros and are constructive as coordinate transformations;
the unbounded elementary sign and negative-Pell arguments they use are
mathematical arguments, not machine-checked Lean or internal-iPRA proofs.

## Count and exact degree

All 14 inputs, four fixed ports and 82 remaining binary-operation gates are
live. The affine input substitution does not increase the parent degree 107
upper bound. At the authenticated P72/P115 port values, the all-inputs-equal
ray modulo 1,000,000,007 has degree 107 and leading coefficient 419359493,
showing exact specialized integer degree 107. These statements concern the
candidate's straight-line graph and its specialized polynomial; there is no
claim that 82 operations are minimal.

The checker pins both graphs and the port bindings, verifies the exact DAG
edit and liveness, exercises signed-coordinate controls, and computes the
specialized ray. The structural DAG edit establishes the displayed affine
polynomial identity; finite tests do not establish the positivity argument.

```
python3 -I -S -B research/ordinary14-root74-natural-forced82/check.py > /tmp/forced82.json
cmp /tmp/forced82.json research/ordinary14-root74-natural-forced82/result.json
```
