# Independent review: thirteen-input unit-product finalizer

**PASS, external integer arithmetic.** For every integer assignment to inputs
and ports, the 80-operation unit-product graph vanishes exactly when its
81-operation four-square parent vanishes. The authenticated compact44 graph
has 13 live inputs and exact degree 99. This is not a Lean/iPRA theorem,
provider replay, PDF/JSON binding, or global minimum; the parent's endpoint
qualifications are inherited.

Each of the four product factors excludes −1 modulo 4 without positivity or
port assumptions. If b is even, the first factor is `1+Z²` modulo 4; if b is
odd, q is even and `Y=q³s` is divisible by 8, so `ell` is divisible by 4 and
the first factor is `Z²` modulo 4. For the main factor,
`Delta=a²+4a+3` is 0 or 3 modulo 4, so `1+Delta c²` is 0 or 1 and
`1+Dstar²−U²(1+Delta c²)` is never 3. Also `Q=Delta(f²−1)` is 0 or 1,
which makes `Fa=y²−Q(y²−V²)` a square modulo 4, and makes
`Fs=1+I²−Q` one of 0, 1 or 2.

If their product is 1 over the integers, every factor is a unit and hence
±1; their mod-4 exclusions force each to +1. The four parent residuals then
vanish. Conversely a zero of the parent's sum of four squares forces each
residual to vanish and makes every product factor 1. This proves same-input
zero equivalence over **all** integers, not an equality of polynomials.

The checker independently reconstructs all 80 source rows, verifies topology
and liveness, enumerates the full mod-4 controls including even and odd b,
and proves the first-residual cancellation in a sparse integer polynomial
ring. The degree upper bound is `17+30+30+22=99`, using the displayed
first-residual cancellation and the reviewed main-residual cancellation.
It reauthenticates the P72/P115 port bytes and obtains degree 99 on a
different weighted affine ray modulo 1,000,000,009. The author receipt is
replayed. Finite controls do not replace the unbounded unit argument above.
No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary13-unit-product80-independent/check.py
```

Compare stdout byte-for-byte with `result.json`.
