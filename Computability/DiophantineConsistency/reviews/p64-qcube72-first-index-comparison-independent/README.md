# Independent review of the generic first-index comparison

**PASS within the recorded direct-provider scope.** The no-Lean `check.py`
checks attempt02's retained and terminal receipt and log, Lean source, runner,
helper and output object hashes, and the recorded direct guards. The sole
direct project provider, `ArithmeticAdaptiveIndexComparison2011`, is a
pinned captured object whose source-to-object and transitive ancestry is not
independently reconstructed here. The theorem's axiom report contains only
`propext`, `Classical.choice`, and `Quot.sound`. This is not a Lean replay;
dynamic and between-sample ancestry remains inherited.

For an `IΣ₁` model the theorem takes model elements `X,Y,k,eta,n,m`, assumes
`X>0`, `Y≥2`, `eta>0`,
`2*ycoord n (2*(X*Y*Y−1)+1)=k`, and
`ycoord m (X*Y+Y)=k*Y+eta`; the subtractions are those of the model. It
concludes `n<m`. The proof bounds the main recurrence base by the first
recurrence base, then uses monotonicity in the index and the base. If `m≤n`,
the supplied coordinate equations give `k*Y+eta≤k`, contradicting `Y≥2` and
`eta>0`.

This is a generic conditional comparison. It does not by itself extract the
first index from an actual 72-graph zero, specialize compact ports, prove
`m=R`, prove the first-index congruence, establish a 72-to-76 reverse map,
or give an iPRA endpoint. The original source's “Unchecked draft” header is
retained byte-for-byte; the recorded attempt02 is the passing check.

Run while the captured temporary paths remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-first-index-comparison-independent/check.py
```
