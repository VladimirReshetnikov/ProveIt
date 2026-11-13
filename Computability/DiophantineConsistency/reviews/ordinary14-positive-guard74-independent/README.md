# Independent review: all-positive shifted guard

**PASS, external standard-integer mathematics.** For `beta>0`, `K0≥0` and
arbitrary other integer ports, the 14-positive-input 74-operation graph has
a positive zero exactly when its reviewed 75-operation parent does. The
authenticated compact44 graph has exact degree 107. This is not a new
Lean/iPRA theorem, provider replay, PDF/JSON binding, or global minimum;
the parent's endpoint and source qualifications are inherited.

The signed polynomial identity holds under `h_old=h−1` for arbitrary ports:
with `q=1+b` and `qF=q−F`, the new guard
`C(X+K0)+qF−bh` equals the parent's factor
`1+C(X+K0)−F−b h_old`. All four other factors omit h. A parent positive zero
therefore maps forward by taking `h=h_old+1`.

For the reverse map the new zero's four unchanged factors cannot be −1:
the first by the reviewed positive-domain negative-Pell argument and the
next three by the reviewed mod-4 exclusions. Since the five factors multiply
to 1, the new guard factor is +1. Hence `Bprime=C(X+K0)−F=b(h−1)`.
Under positive inputs and `beta>0`, `b>0`, q≥2 and X=q w≥q. If `C≤0`
then `Bprime<0`; if `C>0`, alpha≥1 gives `F≤q−2` and
`Bprime≥X−F≥2`. This uses `K0≥0`, so Bprime cannot be zero. Since h is a
positive integer, `h−1≥0`; the guard equation now forces `h−1>0`, which
is the positive old quotient. No machine calibration or assumptions on MC
or MF are needed for this local map. For K0<0 the simple nonzero argument
can fail: `q=3,F=alpha=w=1,K0=−2` gives `Bprime=0`; this is a scalar
control, not a claimed full graph zero or unrestricted nonequivalence.

The checker reconstructs the full 74-row graph and liveness, proves the
guard shift exactly in a sparse integer polynomial ring, confirms h has
only its single old-graph use and compares downstream DAGs after that cut.
It replays the parent and author receipts, checks the two Bprime sign cases
on finite controls, authenticates P72/P115 ports and computes a distinct
degree-107 weighted ray modulo 1,000,000,009. Affine h-translation preserves
the parent degree upper bound 107; the nonzero ray supplies the lower bound.
Finite controls do not replace the unbounded witness argument. No Lean
process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-positive-guard74-independent/check.py
```

Compare stdout byte-for-byte with `result.json`.
