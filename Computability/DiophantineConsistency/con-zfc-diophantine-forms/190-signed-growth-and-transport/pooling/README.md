# Signed Pell growth with four oriented power blocks

Three fully specified polynomial equations over unrestricted integers,
prepared for the ProveIt consistency program on 25 October 2026.

| Variables | Exact degree | Squared residuals | Binary arithmetic operations | Collected coefficient-height bound |
|---:|---:|---:|---:|---:|
| 130 | 12 | 70 | 2475 | <2^54 |
| 116 | 16 | 56 | 2433 | <2^84 |
| 107 | 32 | 47 | 2419 | <2^107 |

The largest literal constant is 2^20. The height column is a rigorously
proved upper bound on the fully expanded polynomial coefficients, not an
exact height or a bound on only the circuit constants.

Every JSON in `equations/` is a complete finite straight-line polynomial
circuit. Its input list is the full list of independently quantified integer
variables, and every other register is an abbreviation built from integer
constants, addition, subtraction, and multiplication. The output is the sum
of the squares of its declared residual registers. There are no variable
exponents, floors, division operations, or hidden predicates in those circuits.

`PROOF.md` supplies the new ordinary arithmetic proof. It composes the
standalone Pell-growth certificate with the signed affine horizon t=2+4z,
the existing affine radix, and oriented pooling of the remaining four bases.
The main reduction uses the retained request q^t to recover the horizon's
positive sign, so a square witness is unnecessary. A separate cofinal
binary-residue construction proves completeness; the growth quotient and
the beta-spacing multiplier remain independent.

The ordinary proof, composed with the identified inherited C222/ZF/ZFC
calibration, gives the ZFC-provable equivalence between nonsolvability and
Con(ZFC). This package does not claim a new complete Lean/Rocq build, global
minimality, or a proof of either consistency or inconsistency. The immediate
source-stage identity and ancestry are in `PROVENANCE.json`. The frozen
source216 stage has the same arithmetic/refutation calibration as the incoming
210-variable quartic; the changed horizon is an existence-preserving semantic
change, not a pointwise polynomial-coordinate bijection with that old quartic.

## Verification

Python 3.10 or later, standard library only:

```sh
python3 -B verify.py
python3 -O -B verify.py
python3 -B build.py --output /tmp/signed-pell-pools-rebuilt
```

Use a fresh output directory. The builder reproduces ten frozen JSON files
byte-for-byte. The independent checker imports no producer: it binds all
34 frame atoms, 13 principal Pell pairs, 15 exact-power requests, and the
literal horizon mutation; verifies the pooling identities and deleted private
coordinates; expands every final circuit block at its declared local cuts;
checks all acyclic unit pivots and polynomial inverse definitions; and proves
the exact degree using nonzero homogeneous specialization. Modular formal
derivative witnesses establish actual occurrence of every input variable.
Fifteen deliberate circuit/profile corruptions are rejected.

These finite checks establish polynomial identities and exact complexity.
They do not replace the separate unbounded arithmetic and logical proofs.

## Comparison boundary

The supplied Signed Horizons package contains 131/degree12, 117/degree16,
and 108/degree32 counterparts. The new equations remove one variable at each
matched degree. The degree16 and degree32 sources in that package have smaller
literal constants, so the new forms are not asserted to dominate every size
measure. The 107-variable degree32 source uses all four oriented bases in a
single pool; the 116-variable degree16 source uses a weighted (B,D) pool and
an unweighted (q,q+1) pool.

## Failed shortcut

Identifying the Pell-divisibility witness with the beta-spacing witness
would save another variable syntactically but breaks the available
completeness proof. In the proposed variant h=t+1 and F=d h(2v+1),
the identity y=F(2v+1) forces y=F^2/(d h). Every beta modulus
1+(i+1)y, for 0<=i<=t, is then at most 1+h y=1+F^2/d.
A pending multiset containing two positive labels already has encoded
weight (1+j_1 F)(1+j_2 F)>= (1+F)^2>1+F^2/d.
Canonical beta residues must be smaller than their respective moduli,
so this fused construction cannot complete such states using the retained
product encoding. Enlarging F does not resolve the obstruction. The
delivered equations retain independent witnesses.

## Files

- `source/`: pinned source216 and its exactly specified signed-horizon change.
- `sources/`: two explicit pooled residual systems and algebraic certificates.
- `certificates/`: three finite acyclic unit-pivot lists.
- `equations/`: complete final polynomial circuits and degree certificates.
- `code/`: new pool emitter and independent source/pooling checker.
- `inherited/`: unchanged circuit emitter, independent circuit checker, the
  ordinary oriented-pooling theorem, and retained provenance notices.
- `verification/`: successful normal and optimized-Python check receipts.

The source repository license is retained in `LICENSE`. This research is
AI-assisted; the independent checks mean separate implementations and
mathematical audits, not external human peer review.
