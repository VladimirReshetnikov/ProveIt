# One named-import producer receipt

The [141-input triage](../trace75-upstream-141-inventory/README.md) placed
`ScaledOffsetGeneric` among 11 candidates without the earlier scanner's
top-level direct-import comparison records. Its retained producer receipt does
contain a named `pins.direct_imports` map, however. The read-only `check.py`
checks that map before and after, the recorded output at the actual final
selected realpath, source snapshot and copied-source hashes, logs, and the
single explicit import `DiophantineConsistency.ArithmeticPellCongruences`
against the final selected `.olean` hash. The producer and selected realpaths
are recorded separately in the captured stdout.

Attempt01 exited 0. Checker SHA-256 is
`3f35c84e4a4b0845e87fea9dde086072bb01babfa6c7ee05eeb9a15ed868ab1a`,
terminal SHA-256 is
`c8d295ed11436af67c5bbbc673ea5794c3059edc0084fb1b4427ae7dc8e05049`,
and stdout SHA-256 is
`44dc03a3ccf92c985ccfe5a6b3da34b1dcdc97fbb509d1d7a4a9dbc99601c2fd`.
The [independent audit](../../reviews/trace75-upstream-scaled-offset-provenance-independent/README.md)
rechecked the named edge and its limited provenance boundary.

This is evidence about one explicit direct `.olean` selection. The receipt
does not authenticate implicit `Init`, complete companion bundles, package
and dynamic ancestry, or the upstream producer's source-to-object closure.
It does not alter the final endpoint's remaining ancestry and file-binding
limits. No Lean was invoked.
