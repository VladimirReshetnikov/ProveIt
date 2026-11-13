# Equal-length nine-variable replay: stages 27–31

The guarded equal-length-root verification replay completed
`WitnessCompaction`, `CompactedJonesSyntax`, `ComputationRepresentation`,
`ScalarPRCode` and `ComposeRepresentation`. The retained audit checks the
entire prefix 1–31: each author/verification output is byte-identical or
becomes byte-identical by replacing its single embedded source pathname with
the same-length verification pathname. Any differing direct-input hash
must correspond exactly to a previously checked predecessor. Direct and
companion guard records match after mapping only those verified predecessor
hashes and normalizing overlay roots; sources and complete compiler logs
match under source-path normalization.

[`audit.py`](audit.py) and [`capture.py`](capture.py) retain the prefix
result, source snapshots, receipts, dependency listings and compiler logs
for these five stages under [`observations`](observations/). The prior
[1–26 prefix](../nine-variable-ipra-equal-length-prefix-ledger/README.md)
is a separate frozen packet. These are sampled byte-level checks, not a proof
of Lean object-format semantics or a claim that all raw object hashes match.
Author warning baselines and historical project, package and dynamic ancestry
remain inherited; neither endpoint has been reached in this replay. Live
`/tmp` overlays are needed to repeat the check.
