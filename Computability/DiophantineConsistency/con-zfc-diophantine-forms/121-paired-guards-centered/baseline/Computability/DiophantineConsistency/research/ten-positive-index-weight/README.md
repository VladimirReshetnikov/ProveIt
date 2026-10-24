# Ten-positive index weight: complete 98/360 and 103/332 candidates

Use the already computed first-index register k=eta+zeta in the transport
majorant L=kI+b. Before transport, the first Pell equation forces k>2A+X,
which supplies both complete negative-transport contradictions. The later
congruence W=1 modulo(q-1) and fresh positive completeness remain valid.
In fact k>H at every zero, and the polynomial shift nnew=nold+(k-H)IB
preserves the full center and is positive at every accepted old zero.

[PROOF.md](PROOF.md) proves both ordinary equivalences and their exact
nonzero leading forms. The complete arithmetic graphs are [zero98.json](zero98.json)
and [direct103.json](direct103.json), with ten strictly positive inputs,
98/103 live operations and exact degrees360/332. Every four-port coefficient
payload is copied together from the accepted parent. [check.py](check.py)
independently verifies the full literal maps, coefficients and degree proof.

The leading norm contribution is16*v0²*h0². The former omega^4 term no
longer controls total degree. This is a different equation with fresh n
witnesses, not a pointwise polynomial identity with its parent. No canonical
page, common report, frozen packet or Lean file is changed.

```sh
python Computability/DiophantineConsistency/research/ten-positive-index-weight/build.py --check
python -O Computability/DiophantineConsistency/research/ten-positive-index-weight/build.py --check
python Computability/DiophantineConsistency/research/ten-positive-index-weight/check.py --output /tmp/index-weight-normal.json
python -O Computability/DiophantineConsistency/research/ten-positive-index-weight/check.py --output /tmp/index-weight-optimized.json
```
