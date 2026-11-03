# Nine-variable peer replay: stages 66–70

The guarded peer completed `IPRAReferenceAddOneOpen`,
`IPRAErasedInductionObligation`, `IPRAReferenceInductionConversion`,
`IPRAExplicitZFCReduction` and `ModelJonesNine`. Both author and peer ledger
checks passed; all five source hashes and complete compiler logs match after
source-path normalization. Stages 66–69 have matching direct-input and output
object hashes.

Stage 70 `ModelJonesNine` reused the author's source-bound warning baseline;
its compiler logs match but its object hashes differ. It directly imports
the differing stage-24 `ModelJonesSyntax` objects described in the
[stage 21–25 review](../nine-variable-ipra-peer-stages-twentyone-twentyfive/README.md).
The stage-70 output objects have equal sizes; in each, the respective source
pathname occurs once in an equally sized padded region. Replacing the three
path-length fields and the padded pathname transforms the complete author
bytes into the peer bytes. This is a byte-level observation and does not
prove that Lean's binary serialization or the differing stage-24 imports
are semantically interchangeable. No exact paired byte match is claimed for
stage 70.

[`audit.py`](audit.py) checks both ledgers, the complete byte observation,
source/log comparison and raw direct-input hash differences.
[`capture.py`](capture.py) retains source snapshots, receipts, dependency
listings, compiler output and terminal receipt under
[`observations`](observations/). Repeating the audit requires the live `/tmp`
overlays. The checks are sampled, and earlier project, package-transitive
and dynamic ancestry remains inherited. These five stages do not include an
unconditional nine-variable endpoint.
