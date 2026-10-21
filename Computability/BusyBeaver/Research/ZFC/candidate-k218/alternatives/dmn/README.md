# DMN: swap the MP and DROP command tags

This is an accepted **218-working-state alternative**, with 436 transition rows and a separate halt. Its ordinary reviewed proof, together with the inherited numerical-calculus calibration, establishes the ZFC-formalizable equivalence `blank nonhalting ↔ Con(ZFC)`. It supplies no new compiled exact-table Lean/Rocq or internal PA endpoint, and makes no unconditional nonhalting or minimality claim. The [primary K218](../../README.md) remains primary; this is not a 217-state improvement.

This alternative assigns command tag 0 to DROP, tag 1 to MP and tag 2 to NIP. It retains each command body and recodes finite proof programs. Its complete blank initialization is shorter and reaches counters 2 instead of 3; cofinal enumeration covers either seed. It still has 205 distinct source subtrees and 218 working states.

## Literal machine and source

- [Compact table](k218.tm): working labels 0–217, initial state 0, halt 218.
- [Native table](k218.native.tm): inherited labels, initial state 0, dispatcher 84, halt 254.
- [Complete source](sites218.json) and [native-to-compact bijection](canonical-map.json).
- [Proof exposition](proof.md) and [exact provenance/evidence pins](provenance.json).

The machine is deterministic and binary, on a two-way infinite single tape initially all 0, with initial head position 0 and L/R moves. Each noncomment row is `state read write direction next`; the halt has no outgoing rows and is excluded from the working-state count.

The exact change from the pinned primary 218 native table is:

```text
135 1 1 R 12   ->  135 1 1 R 143
185 1 1 R 143  ->  185 1 1 R 12
```

Pair this table with its own source and compiler argument. The native SHA-256 is `0e2b4c9fb78158c69b95bf854d34ac256f63acffd6224b5108806ace638f46f1`; compact SHA-256 is `054454682fbdaea8db3e4835f3d7119b24125bfee230f8eda8e4e41bc1166ce0`.

## Fresh evidence and reproduction

Root's fresh symbolic replay proved **6,167 guarded interfaces**, 1,516,795 symbolic rules, all 436 rows and minimum positive duration 12. Its domain is independent arbitrary natural primary registers, extra gap, arbitrary first spare value and arbitrary finite remaining spare list, with complete tape endpoints. The 4,000-step bound limits proof construction; it does not bound the represented values or machine time. This is an ordinary inductive checker, not a proof-assistant kernel result.

A fresh independent dense-tape replay reached dispatcher 84 at head -4 after **123,776 transitions**, gap 23, logical registers `[2, 0, 0, 0, 2, 0, 0, 0, 0]`, 72 one-valued spare blocks and 159 one cells. The entire tape equals the expected root frame; the exterior is 0. This finite startup and the universal runtime are separate parts of the calibration.

See the [fresh runtime](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source151/dmn-runtime/runtime.json), [complete startup/source audit](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source151/selected-audit.json), [actual commands](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source151/executions.json), and [fresh receipt comparison](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source151/fresh-review.json). Full case records, raw logs and selected reproduction code are retained with those host records. The [Source151 reproduction guide](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake191-source151-reproduction.md) restores the delivered layout and identifies the selected leaves. Do not substitute a stored-receipt audit for the fresh runtime or invoke historical broad searches to reproduce this candidate.

## Attribution

Source151, `zfc-217-state-search.zip`, arrived in `7071e5041ee316d087661b658362feed159901ef`, based on `9adcaff0a72486ecc81242e0eca86e428c74879e`. The [intake note](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-191.md), [placement map](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-placement.json) and [full source review](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake191-source151-review.md) preserve the report, proof inputs, experimental limitations and recovery route. This directory contains a new summary, not a copy of the delivered main manuscript.

The submission contributes this source/table and its ordinary calibration. ProveIt supplies the inherited construction, calculus and runtime machinery. Root reviewed and executed the new fresh checks; `drop_contract` independently read the candidate arguments and prepared this publication. The exact supplied [license](LICENSE) is retained. No candidate was executed during publication preparation.
