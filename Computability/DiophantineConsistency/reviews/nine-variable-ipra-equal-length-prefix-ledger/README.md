# Equal-length source-root nine-variable prefix replay

The guarded verification overlay `/tmp/nine-ipra-guarded-verify-20261102-a`
uses a source-root pathname of the same length as the historical author root.
It extends the earlier [six-stage diagnostic](../nine-variable-ipra-equal-length-diagnostic/README.md)
using the same pinned 104-stage plan and registered author warning baselines.

The captured [stages 7–11](observations/stages-007-011/audit.json) and
[stages 12–16](observations/stages-012-016/audit.json) and
[stages 17–21](observations/stages-017-021/audit.json) and
[stages 22–26](observations/stages-022-026/audit.json) pass comparisons of
their complete prefixes. Through stage 26, every author/verification output is
either byte-identical or becomes byte-identical by replacing its **single**
embedded author source pathname with the verification pathname of the same
length. For each direct input hash difference, the audit requires that both
hashes belong to a previously checked predecessor. It then compares all
direct-input and candidate/companion guard records after normalizing the root
paths and those explicitly established predecessor hashes. Source hashes and
complete compiler logs also match under source-path normalization.

Stage 24 `ModelJonesSyntax` was the second earlier unequal-length-path case
that left aligned-word deltas after pathname-record replacement. In this
equal-length run it has matching direct input hashes, and replacing its
single equal-length source pathname makes the entire output byte-for-byte
equal to the author's. This provides further evidence for a path-layout
explanation without proving the Lean serialization format or resolving the
raw differing hashes in the earlier peer run.

[`audit.py`](audit.py) performs this prefix comparison, and [`capture.py`](capture.py)
retains its output, source snapshots, receipts, compiler logs and dependency
listings for each captured batch. Passing `--upto N` checks the entire prefix
through N while both live `/tmp` overlays remain available. The comparison is
a byte-level observation, not a theorem of Lean object-file semantics or a
claim that all raw object hashes match. Guards are sampled, warning baselines
and historical project/package/dynamic ancestry are inherited, and the
nine-variable endpoints are not yet reached in this diagnostic replay.
