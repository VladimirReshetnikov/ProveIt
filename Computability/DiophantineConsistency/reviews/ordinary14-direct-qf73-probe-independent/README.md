# Independent review: direct-qF 73-gate probe

**PASS, external symbolic arithmetic.** The 73-operation graph has a
symbolically specified positive zero at the authenticated compact44 ports.
Its old F coordinate would be negative. Under the cited parent guard
calibration, no positive parent zero shares this witness's q and rank; a
parent zero at other parameters is not excluded. Thus this does not decide
unrestricted existence equivalence. The graph has exact degree 107 at the
authenticated ports. No Lean/iPRA theorem, PDF/JSON binding, provider replay
or global-minimum claim is made.

The checker independently reconstructs the one-row source deletion and
verifies the signed substitution `F=q−qF`. For the actual ports, with
`b=beta`, `q=b+1`, `t=2+2^L+2^(L+S)`, `qF=q+bt` and
`alpha=1+b(t−2)`, the exact scalar identities give `C=3b`,
`G=bq(1+t)+1−2b`, and `F=−bt<0`. Taking
`h=3(X+K0)+t+1` makes the guard factor exactly one. The independently
reconstructed finite rank has 7,080,832 bits, is 3 modulo 4, and has
`popcount((R−1)/2)=3,540,414≥3B+1`, where B=590069. Its huge power X and
Pell witnesses are specified symbolically, not expanded.

For the unbounded completion, the prescribed binomial Y has
`v₂(Y)=popcount((R−1)/2)−1≥3B`, hence `s=Y/q³>0`; R>2B also gives
`w=2^R/q>0` and `q² | X`. The reviewed Pell-floor argument applies to this
prescribed binomial and gives `Y<c/k<Y+1`, so eta and zeta are positive.
The first Pell recurrence gives `XY | k−R−1`, and `U=Yq² | XY`; therefore
the displayed gamma correction is integral. The same-index trace identity
gives a positive gamma0 and makes `Dstar=U d` after correction. The first
Pell norm gives the direct first factor +1. For the strong and auxiliary
factors, the reviewed aligned-index construction uses **R in both**
`c=psi_(a+2)(R)` and the auxiliary exponent; its `R≡3 (mod 4)` congruences
give integral positive T and make both factors +1. The guard is +1 by the
scalar identity, so all five factors are +1. The finite checker does not
materialize the enormous witness or replace these unbounded arguments.

At fixed q,R and actual beta, J and then G are fixed. A positive 74-parent
zero has C>0 from its guard factor and `K0≥0`, so `F+alpha<q` and
`G=b(q−F)+alpha≤bq−1`. The seed has `G>bq−1`. This excludes only parent
zeros at the **same q and R**, under the cited parent calibration; it does
not rule out different parent parameters.

The checker pins both graphs, checks all 73 rows and liveness, verifies the
guard and modified-carrier identities in an exact sparse integer polynomial
ring, reauthenticates the P72/P115 port bytes, independently reconstructs
the finite seed and replays the author receipt. A different weighted affine
ray modulo 1,000,000,009 has degree 107, matching the inherited upper bound.
An exact small aligned-index Pell control checks the strong and auxiliary
formulas but is not an actual-port witness or a proof of the unbounded
completion. No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-direct-qf73-probe-independent/check.py
```

Compare stdout byte-for-byte with `result.json`.
