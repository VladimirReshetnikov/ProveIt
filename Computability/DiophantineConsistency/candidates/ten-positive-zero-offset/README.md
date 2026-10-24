# Ten strictly positive integers, 99 operations, degree 368

The complete equation is `N=0` in equation.json, whose arithmetic
definitions use ten strictly positive integer inputs and four fixed
coherent compact44 ports. It has **99 live operations**: 59
multiplications, 23 additions and 17 subtractions. Its exact total
degree is **368**, while direct syntactic degree propagation gives416.
All four fixed coefficient payloads are copied byte for byte from the
accepted 101-operation parent; no coefficient or domain is changed.

The new full Pell base is

    A=mu*Y*(X+1)+1,

in place of `mu*(Y*(X+1)+2)+1`. The root's ordinary proof establishes
soundness and completeness using the sharper direct ratio estimate
and fresh canonical witnesses. It does not equate the old and new
positive witness tuples. The unscaled source reconstructed in
soundness still has its prescribed source base `a+2`.

Within this new zero-offset polynomial, share the existing `muY`:
`mu*(X*Y+Y)=(mu*Y)*(X+1)`. This is a universal ring identity and makes
the 99-operation graph exactly equal to the unshared 100-operation
zero-offset graph. It does not establish pointwise equality with the
101-operation parent, whose base is different.

CUTS.json accounts for all 101 parent definitions. It deletes only
the private E,a,a2 definitions at parent rows5,6,12, inserts Xp1=X+1,
moves the existing muY definition before Am1, and changes that one
base multiplication. Every other definition, including the complete
13-operation weighted norm tail, is retained. Literal `a` is absent
from the new graph; `a=Y*(X+1)` remains a proof abbreviation.

The independent checker imports no producer or historical emitter.
It checks the complete cut/map, topology, liveness, whole payload and
source bindings, recursive symbolic front cuts, all35 weighted norm
coefficients, and the centered cancellation giving a unique degree368
leading term. The full omega leading form is

    2^7*q0^46*i^5*w^10*Y^19*(eta+zeta)^10
       *(q0-F-alpha)*(q0-F),  q0=beta*J.

Its fourth power has the nonzero coefficient `2^28*beta^184` at
`J^184*i^20*w^40*Y^76*eta^40*alpha^4*F^4`. The upper-degree and
nonzero-leading-form arguments are symbolic. Actual-tuple degree
lines and exact-rational small ratio controls supplement them; they
are not sampling proofs of the ordinary theorem.

PROOF.md is copied verbatim from the root's supplied zero-offset
ordinary proof. Its accepted universal source/controller dependencies
are copied and pinned, including the complete original tuple and
the separate BFS tuple transfer. No original/BFS K0 values are
identified, and no individual payload is substituted between tuples.
No new Lean or internal-ZFC theorem is claimed.

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_zero_offset.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-zero-offset/check.py
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_zero_offset.py --check
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-zero-offset/check.py
```

The four replay logs, CHECK.json/CHECK_OPTIMIZED.json and closed
MANIFEST.json are included. All earlier candidates and the canonical
equation page remain unchanged.
