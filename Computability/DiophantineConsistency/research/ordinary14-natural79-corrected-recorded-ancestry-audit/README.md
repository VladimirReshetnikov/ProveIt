# Corrected natural-79 frontier: recorded P72/base ancestry

This read-only audit expands the independently reviewed [natural-80 recorded
ancestry](../ordinary14-natural80-recorded-ancestry-audit/README.md) from its 40
lexical project seeds to the 41 in the [corrected natural-79 ordered
plan](../ordinary14-natural79-corrected-ordered-provider-plan/README.md).
It follows the retained producer records' project edges; it does not run Lean,
create outputs or alter evidence.

The only added seed is `DiophantineConsistency.Compact44.ReducedNormSigned`;
no natural-80 seed was dropped. Its recorded P72 producer is row 69. It was
already in the 40-seed **recorded** closure, so adding it introduces **zero**
new recorded project ancestors. Both traversals reach the same 627 P72 and
919 base producers, 4,414 recorded edges and 80 distinct external leaf names.
The reached-module, row-file and external-leaf digests and external binding
observations match the pinned natural-80 receipt.

The inspector checks all 41 selected project seed source/object paths, resolved
paths and hashes against the ordered plan and producer records. For the full
reached closure it rechecks producer source and object hashes, P72 snapshot
hashes, recorded project edge hashes and producer targets, producer ordering,
the 919 recorded base links, and recorded guard/output slots. Of **29,860**
distinct checked slots, 1,751 were present and 28,109 absent; no mismatch was
observed. Row 69's source hash, object hash, row hash, two recorded direct
dependencies and count of 60 direct guard slots are in the receipt.

These checks revalidate the recorded evidence against the observed files; they
do **not** independently authenticate all producers. The pinned P72 progress
metadata anchors its last row; other P72 row hashes, including row 69, are
observations rather than independently anchored producer attestations. The
inspector follows recorded project edges and stops at recorded external direct
leaves; it does not establish a complete package/toolchain, implicit import,
runtime or companion closure, Lean search order, compatibility or successful
elaboration. Reads are non-atomic and cached; changes during or after the audit
may be missed. No immutable snapshot, resource slot or output path is reserved.
The five missing source candidates are separate prospective stages, not existing
producer seeds, and are outside this closure check.

No internal iPRA proof or binding to the separate Carrier65 PDF follows from
this audit. Future compilation still requires independently reviewed provider,
companion, output-collision, resource and postflight controls.

An [independent review](../../reviews/ordinary14-natural79-corrected-recorded-ancestry-independent/README.md)
reconstructs the seed closure and rechecks the recorded observations without
authenticating unrecorded historical or runtime dependencies.

From the repository root, while the pinned retained roots remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-corrected-recorded-ancestry-audit/inspect.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-corrected-recorded-ancestry-audit/observation.json
```
