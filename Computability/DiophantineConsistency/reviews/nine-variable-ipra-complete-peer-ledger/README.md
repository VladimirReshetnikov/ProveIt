# Complete nine-variable author/peer ledger audit

Both guarded historical-provider ledgers record all **104 stages**, including
the CURRENT2011 nine-variable endpoint at stage 80, its 15-report axiom
client at stage 81, and the distinct enumerator-based nine-variable endpoint
at stage 104. The aggregate [`audit.py`](audit.py) reruns both guarded
`--check` commands without invoking Lean, validates all 22 retained comparison
packets and their stage coverage, rechecks every captured/live receipt,
source, dependency listing, compiler log and live object hash, and records
every raw direct-input and output-object hash difference. The successful
[`observations/audit.json`](observations/audit.json) is the complete 104-row
catalogue; its terminal receipt and exact audit source are retained alongside
it.

All 104 corresponding source hashes and complete compiler logs agree after
normalizing source paths. The two endpoint object hashes and the stage-81
client object hashes match. The audit checks the exact no-hypothesis native,
standard and equality-only endpoint source statements against the respective
no-zero expression and selected mapped refutation negation. It also checks
all 15 stage-81 and four stage-104 source-named axiom reports; every report
lists only `propext`, `Classical.choice` and `Quot.sound` as Lean metatheory
dependencies, not as object-theory axioms.

**The full chain is not an exact object replay.** Twenty of the 104 output
objects have differing raw hashes, and 28 stages have at least one
different-hash direct input (31 differing stage/input pairs in total). The
JSON catalogue records both hashes and module names for every such case.
The individual packets provide whole-file byte observations. For most
differing objects they isolate a source-path record; for stages 6 and 24 an
eight-byte path-record size change leaves aligned-word differences, which are
consistent with relocation but have no proved binary-format interpretation.
The [equal-length-root diagnostic](../nine-variable-ipra-equal-length-diagnostic/README.md)
gives additional scoped evidence for stage 6. Neither endpoint's matching
output hash establishes that all differing imports are semantically
interchangeable.

The comparison packets are:

- [1–5](../nine-variable-ipra-peer-first-five/README.md),
  [6–10](../nine-variable-ipra-peer-stages-six-ten/README.md),
  [11–15](../nine-variable-ipra-peer-stages-eleven-fifteen/README.md),
  [16–20](../nine-variable-ipra-peer-stages-sixteen-twenty/README.md),
  [21–25](../nine-variable-ipra-peer-stages-twentyone-twentyfive/README.md).
- [26–30](../nine-variable-ipra-peer-stages-26-30/README.md),
  [31–35](../nine-variable-ipra-peer-stages-31-35/README.md),
  [36–40](../nine-variable-ipra-peer-stages-36-40/README.md),
  [41–45](../nine-variable-ipra-peer-stages-41-45/README.md),
  [46–50](../nine-variable-ipra-peer-stages-46-50/README.md).
- [51–55](../nine-variable-ipra-peer-stages-51-55/README.md),
  [56–60](../nine-variable-ipra-peer-stages-56-60/README.md),
  [61–65](../nine-variable-ipra-peer-stages-61-65/README.md),
  [66–70](../nine-variable-ipra-peer-stages-66-70/README.md),
  [71–75](../nine-variable-ipra-peer-stages-71-75/README.md).
- [76–80](../nine-variable-ipra-peer-stages-76-80/README.md),
  [81](../nine-variable-ipra-peer-stage-81/README.md),
  [82–86](../nine-variable-ipra-peer-stages-82-86/README.md),
  [87–91](../nine-variable-ipra-peer-stages-87-91/README.md),
  [92–96](../nine-variable-ipra-peer-stages-92-96/README.md),
  [97–101](../nine-variable-ipra-peer-stages-97-101/README.md),
  [102–104](../nine-variable-ipra-peer-stages-102-104/README.md).

The peer reused documented author warning baselines and the historical parent
provider. Guards are sampled at recorded boundaries; neither the complete
transitive project/package/dynamic ancestry nor a document/PDF transcription
is authenticated by these checks. Repeating the audit requires the live
author and peer `/tmp` overlays. This packet runs no new Lean process and does
not assert that an exact paired closure or either consistency statement has
been proved in the metatheory.
