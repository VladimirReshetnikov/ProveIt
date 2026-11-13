# Nine-variable peer replay: stages 71–75

The guarded peer completed `ShortEquation`, `ShortCircuit`, `ConsecutivePell`,
`TotalDegreeBound` and `ShortSystem`. Both author and peer ledger checks
passed; all five source hashes, normalized complete compiler logs, and direct
input object hashes match. Stages 71–74 also have identical output object
hashes.

Stage 75 `ShortSystem` reused the author's source-bound warning baseline and
its object hashes differ. The two output files have equal sizes, and their
respective source pathnames occur once in equally sized padded regions.
Replacing the three path-length fields and the padded pathname transforms the
complete author bytes into the peer bytes. This is a byte-level observation,
not a proof of Lean binary-format semantics or semantic interchangeability;
no exact paired byte match is claimed for stage 75.

[`audit.py`](audit.py) checks both ledgers, the complete byte observation,
source/log comparison and raw direct input hashes. [`capture.py`](capture.py)
retains source snapshots, receipts, dependency listings, compiler output and
terminal receipt under [`observations`](observations/). Repeating the audit
requires the live `/tmp` overlays. Checks are sampled and earlier project,
package-transitive and dynamic ancestry remains inherited. These stages do
not include an unconditional nine-variable endpoint.
