# Independent review of the 13/88 unshifted-s full-zero probe

The 87-row probe removes exactly the s shift from the pinned 13/88 graph and retargets its uses to `n_s`. An independent exact sparse-polynomial evaluation verifies that all four residuals and the complete output vanish identically for the five-parameter family with `n_s=0`. P72/P115 port bytes and the inequalities for a nonnegative compact witness are independently authenticated; the original receipt also reproduces.

This family explicitly respects the graph's `X=q*w`, unlike the 13/89 family. Taking `h=ceil((K0+2)/beta)` and `w=beta*h-K0-1` gives w>=1 and `X=(beta+1)w`; `X+K0=beta*(w+h)-1` makes `Bt=beta*((beta-1)*(w+h)-1)`. For beta>=3 and the other ports natural, every coordinate in the family is nonnegative. The remaining polynomial identities give each residual zero; authenticated compact ports satisfy the hypotheses.

Therefore this 87-row probe has an actual standard-natural zero with s=0, even at the compact ports, and s is not forced positive. This does not decide whether its global zero existence differs from the 13/88 parent, establish an iPRA equivalence, or bind the current-2011 PDF. No Lean elaboration was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue88-unshift-s-full-zero-independent/check.py | cmp - reviews/ordinary13-residue88-unshift-s-full-zero-independent/result.json
python3 -I -S -B research/ordinary13-residue88-unshift-s-full-zero/check.py | cmp - research/ordinary13-residue88-unshift-s-full-zero/receipt.json
```
