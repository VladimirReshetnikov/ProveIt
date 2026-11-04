# Odd-ordinate exclusion of one partial assignment

For the fixed-payload partial assignment in [the positive-carrier example](../trace74-large-f-positive-carrier-scalar/README.md), write `q=beta+1`, `X=q^4`, `Y=q^3`, `k=8q^10+4`, and `eta=1`. The checked graph-zero theorem `Trace74Fold.graph_odd_ordinate` requires, for a positive 74 zero with the stated model and positivity hypotheses, `c=y_r(A-1)` for a positive odd `r`, where `A=Y(X+1)` and `c=kY+eta`. The checked `ArithmeticPellRecurrence.ordinate_strictMono` makes this sequence strictly increasing in its index.

The independent finite calculation here substitutes the partial assignment into the same displayed formulas and uses the Pell recurrence over sparse integer polynomials. It verifies `A=q^7+q^3`, `c=8q^13+4q^3+1`, `y_1=1`, and

```
y_3-c = 4q^13(q-2) + 8q^10 + 8q^7 + 4q^6 + 4q^3 + 2 > 0.
```

The fixed beta payload gives `q=2^(67*8807)≥32`, so `1<c<y_3`. Strict monotonicity excludes every positive odd index: index 1 is too small and every later positive odd index is at least 3. Thus this specific scalar assignment cannot satisfy the graph-zero odd-ordinate consequence under the indicated interpretation. The assignment had already been presented only as a partial witness, with no full graph zero or second Pell/adjacent witness.

Run `python3 -I -S -B research/trace74-odd-ordinate-partial-exclusion/check.py` from `Computability/DiophantineConsistency`. The author run exited 0, with empty stderr; checker SHA-256 `8921bba26f8398277c5ce2ca6535d15ef9a9453a2c6db79be4e0b356b4332a63` and stdout SHA-256 `f6416bea7ad3e52765e1cbf2efeed817bc835de38233944cf5ecf0d2725b5e9d`. An initial proposed gap formula had coefficient 4 for `q^7`; the recurrence check exposed that typo and the correct coefficient is 8, as recorded above. The failed temporary output was overwritten, so no preserved failed-run receipt is claimed.

This is an external integer calculation using pinned source bytes and a previously checked theorem, not a Lean theorem binding the raw beta payload to a symbolic model port. It excludes neither other assignments with large F nor any general individual bound on F or C. The Fold theorem's provider and ancestry limitations remain those described in [its audit](../../reviews/trace74-guardfree-fold-result-independent/README.md).

Independent arithmetic and scope audit: [odd-ordinate partial exclusion v2](../../reviews/trace74-odd-ordinate-partial-exclusion-v2-independent/README.md), SHA-256 `5144aea17b5cc4b60e92bf9f22ee4accb90d64f8d33a7ce4ad141bfca11ef20b`.
