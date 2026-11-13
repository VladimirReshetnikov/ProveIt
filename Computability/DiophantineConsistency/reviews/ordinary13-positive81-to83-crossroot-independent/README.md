# Independent review of positive 81/83 cross-root source

This is a source and mathematical review of
`research/ordinary13-positive81-to83-model-draft/`; no Lean, build, or
provider check was run. The independent receipt regenerates both graph
literals byte for byte, checks the exact JSON row delta, and proves that the
three non-first residual dependency graphs do not use coordinate 8. It also
reproduces the previously recorded exact symbolic 81-to-85 residual check.

Both literal outputs are sums of squares of `A0`, `A1`, `Fa-1` and `g72`.
A zero forces the last three residuals to be `0,1,0` in the ordered
difference ring. Changing only r preserves those three because their full
literal dependency graphs omit r. Thus `zero81_to83` is correctly conditional
on a target-83 first residual zero, and `zero83_to81` is correctly conditional
on a target-81 first residual zero. Each direction changes the same coordinate
8 and retains every other witness. Positivity of the new r is supplied
separately by the cut when the model-positive witness is constructed.

`CrossRootCut K` quantifies over every intended model and every all-positive
valuation. Its first clause requires a positive r making the 83 first
residual zero at each 81 zero; its second clause requires a positive r making
the 81 first residual zero at each 83 zero. Both clauses remain hypotheses.
`sameNoZero` uses the second clause for an 83 counterexample to 81 no-zero,
and the first for an 81 counterexample to 83 no-zero. The bridge consequently
requires both this cut and `PolynomialBridge` for the **exact positiveShift
83 graph** at the same tuple; the native 85 client carries both assumptions.

The fact-level target-root helper takes a *natural positive* target carrier
`P=b*t`, positive t, and `ell<tau`, and constructs
`r=k*(P-1)+t+(tau-ell)>0`. Its claimed root identity follows by exact
polynomial normalization after `P=b*t`; the positivity premises justify the
natural subtractions. The helper does **not** extract P or tau from either
graph, show the target carrier is positive/divisible, or establish the target
first residual zero without the matching first norm. Those missing all-model
facts are precisely the content needed to establish `CrossRootCut`.

The one-way prototype client applies the source's 81→80 zero implication,
lower/lift inverse on a positive tuple, the 89 graph equivalence, and the
forward 89→85 graph equivalence, all with the same ports. Its image is the
exact `up (lower v)` tuple; it assumes neither `CrossRootCut` nor inverse eta
forcing. The literal/field identity check is not a Lean proof of these
imported mappings, nor does it establish the exact positive-index or power
calibration needed for the harder companion carrier.

All `simp`, `ring`, `nlinarith`, model instances, imported source/object
providers, `#print axioms`, fixed port/physical file binding, parent bridge,
and end-to-end iPRA/ZFC statement remain unverified. The author and this
review both keep those limits explicit.

Reproduce the receipt from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive81-to83-crossroot-independent/check.py
```
