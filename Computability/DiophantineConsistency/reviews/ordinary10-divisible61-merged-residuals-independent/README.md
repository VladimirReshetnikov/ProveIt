# Independent review of the merged-residual probe

The literal 60-row probe and the stated q=4 counterexample check out. Replacing the carrier and first-norm squares by the square of their signed sum admits a zero at a natural input where the original 61-row graph is positive. This is a pointwise, noncompact counterexample to that encoding, not a proof of different existential zero status or a lower bound for other encodings.

The general map is correct for any original zero with `b=beta*J>0`. Keeping all other inputs fixed and replacing

```text
tau ↦ tau+b,    h ↦ h+2*tau+b
```

changes the first-norm residual by `d=b*(2*tau+b)>0` and the carrier residual by `-d`. The actual main residual has no dependency on h or tau, so it stays zero. The probe therefore gives zero, while the original output at the changed input is exactly `2*d²>0`. The new inputs are natural; this conditional map does not assume a compact-port zero exists.

For the published noncompact `(beta,K0,MC,MF)=(3,1,1,1)` example, the independent checker reconstructs the finite first and main Pell witnesses by linear iteration, checks the original 61-row zero, applies the map, and evaluates every row of both literal graphs. It confirms the changed main residual remains zero and the two other residuals are nonzero opposites. This review reuses the q=4 witness recorded by the same reviewer in a previous packet, but independently evaluates the reviewed probe's exact rows and transformation. The checked mask inequalities are `MC<beta` and `MF<2*beta`; the actual compact tuple is not tested.

The literal edit removes the two individual residual-square rows, inserts the signed-sum and its square, and redirects the output to that square plus `A1²`. The checker verifies the precise ordered source edit, all row dependencies and liveness, the generic polynomial identity and the complete concrete evaluation. It uses a 192 MiB address-space cap, 10-second CPU cap and zero core-file limit. Neither finite controls nor the generic pointwise map prove anything about other possible witness transformations.

From `Computability/DiophantineConsistency`:

```sh
timeout 15s python3 -I -S -B reviews/ordinary10-divisible61-merged-residuals-independent/check.py | cmp - reviews/ordinary10-divisible61-merged-residuals-independent/receipt.json
```

No Lean, build, staging, provider audit or iPRA proof was run.
