# Independent review: 14-input negative-Pell unit finalizer

**PASS, external standard-integer mathematics.** For positive inputs and
arbitrary integer ports with `beta>0`, the 75-operation five-factor graph
and its 78-operation parent vanish at exactly the same assignments. The
authenticated compact44 graph has exact degree 107. This comparison is not
claimed for all signed inputs and is not a Lean/iPRA theorem, provider
replay, PDF/JSON binding or global minimum; parent endpoint qualifications
are inherited.

The positive-domain first factor cannot be −1: its negative-Pell equation
`r²−m(m+1)k²=−1` has no solution with `m≥2,k≥1`. If k is even, r² would
be 3 modulo 4; if k=1, the required square lies strictly between m² and
(m+1)². Otherwise choose a solution with least positive odd k≥3 and put
`D=m(m+1)`, `r′=(2m+1)r−2Dk`, `k′=(2m+1)k−2r`, taking r positive.
The inequalities `r>mk`, `((2m+1)k)²−(2r)²=k²+4>0`, and
`((2m+1)r)²−(2Dk)²=D(k²−4)−1>0` yield `r′>0` and `0<k′<k`.
The unit identity `(2m+1)²−4D=1` preserves the negative norm, contradicting
minimality. The excluded boundary matters: m=k=r=1 is a solution. In the
graph beta,J,w,s>0 give q≥2, X≥2 and Y≥8, hence m=XY²≥2.

The main factor `1+A1` is never −1 modulo 4 because
`U²(1+Delta c²)` is 0 or 1 modulo 4. The auxiliary factor Fa is a square
modulo 4 because `Q=Delta(f²−1)` is 0 or 1; the strong factor
`1+I²−Q` is 0, 1 or 2 modulo 4. If all five integer factors multiply to 1,
each is ±1. The four exclusions force those four factors to +1; therefore
the **unrestricted** fifth guard factor is +1 as well. This makes all five
parent residuals zero. Conversely, the parent's sum of squares vanishes only
when each residual is zero, making all factors 1.

The checker independently reconstructs all 75 rows and their liveness,
verifies the negative-Pell descent and squared-inequality identities in an
exact sparse integer polynomial ring, checks parity/boundary controls and
replays the author's finite receipt. It authenticates P72/P115 ports and
computes a different weighted affine degree ray modulo 1,000,000,009. The
factor degree bounds `22,30,30,22,3` give the upper bound 107; the nonzero
ray gives the matching lower bound. Finite controls do not replace the
well-founded integer descent above. No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-negative-pell75-independent/check.py
```

Compare stdout byte-for-byte with `result.json`.
