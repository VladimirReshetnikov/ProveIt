# Independent review: ScaledOffsetGeneric named-import receipt

PASS for the bounded capture in `research/trace75-upstream-scaled-offset-provenance/`. We independently rehashed the recorded successful producer receipt and before/after pins, actual selected output realpath and hash, source snapshot and copied-source hashes, both logs and captured header. The source has one explicit import, `DiophantineConsistency.ArithmeticPellCongruences`; the receipt's named `pins.direct_imports` map records its `.olean` path and hash before and after, and that hash matches the final selected `.olean`. Producer and selected input realpaths are reported separately.

The receipt does not authenticate implicit `Init`, complete direct companion bundles, transitive source/object or package/dynamic provenance, or external equation-file binding. This is one explicit direct edge, not a full closure proof or independent Lean replay.

Checker SHA `3f35c84e4a4b0845e87fea9dde086072bb01babfa6c7ee05eeb9a15ed868ab1a`, terminal SHA `c8d295ed11436af67c5bbbc673ea5794c3059edc0084fb1b4427ae7dc8e05049`, stdout SHA `44dc03a3ccf92c985ccfe5a6b3da34b1dcdc97fbb509d1d7a4a9dbc99601c2fd`. Our independent checker and output are alongside; no Lean was run.
