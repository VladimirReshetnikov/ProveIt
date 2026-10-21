# Omit the successful-MP dummy zero push

This is an accepted **218-working-state alternative**, with 436 transition rows and a separate halt. Its ordinary reviewed proof, together with the inherited numerical-calculus calibration, establishes the ZFC-formalizable equivalence `blank nonhalting ↔ Con(ZFC)`. It supplies no new compiled exact-table Lean/Rocq or internal PA endpoint, and makes no unconditional nonhalting or minimality claim. The [primary K218](../../README.md) remains primary; this is not a 217-state improvement.

This alternative removes the zero pushed onto the work stack after successful modus ponens. The exact source loses 19 primitive occurrences, while its source graph and physical table retain 205 distinct subtrees and 218 working states. Its proof compiler removes one final cleanup NIP. It is intentionally not execution-trace equivalent to the original enumerator.

## Literal machine and source

- [Compact table](k218.tm): working labels 0–217, initial state 0, halt 218.
- [Native table](k218.native.tm): inherited labels, initial state 0, dispatcher 84, halt 254.
- [Complete source](sites218.json) and [native-to-compact bijection](canonical-map.json).
- [Proof exposition](proof.md) and [exact provenance/evidence pins](provenance.json).

The machine is deterministic and binary, on a two-way infinite single tape initially all 0, with initial head position 0 and L/R moves. Each noncomment row is `state read write direction next`; the halt has no outgoing rows and is excluded from the working-state count.

The exact change from the pinned primary 218 native table is:

```text
164 1 1 R 98  ->  164 1 1 R 114
```

Pair this table with its own source and compiler argument. The native SHA-256 is `7d820254e777eb96108887f5ef6d6c2ae8af8ce70b8728dcdcdc97f85ec235d8`; compact SHA-256 is `e21b657e690ef72fc45c544c3bd1b3ecfd3be6d2d9c58a7cddaa9bd72d8c95bd`.

## Fresh evidence and reproduction

Root's fresh symbolic replay proved **6,142 guarded interfaces**, 1,511,359 symbolic rules, all 436 rows and minimum positive duration 12. Its domain is independent arbitrary natural primary registers, extra gap, arbitrary first spare value and arbitrary finite remaining spare list, with complete tape endpoints. The 4,000-step bound limits proof construction; it does not bound the represented values or machine time. This is an ordinary inductive checker, not a proof-assistant kernel result.

A fresh independent dense-tape replay reached dispatcher 84 at head -5 after **312,909 transitions**, gap 80, logical registers `[3, 0, 0, 0, 3, 0, 0, 0, 0]`, 130 one-valued spare blocks and 277 one cells. The entire tape equals the expected root frame; the exterior is 0. This finite startup and the universal runtime are separate parts of the calibration.

See the [fresh runtime](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source151/omit-runtime/runtime.json), [complete startup/source audit](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source151/selected-audit.json), [actual commands](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source151/executions.json), and [fresh receipt comparison](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source151/fresh-review.json). Full case records, raw logs and selected reproduction code are retained with those host records. The [Source151 reproduction guide](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake191-source151-reproduction.md) restores the delivered layout and identifies the selected leaves. Do not substitute a stored-receipt audit for the fresh runtime or invoke historical broad searches to reproduce this candidate.

## Attribution

Source151, `zfc-217-state-search.zip`, arrived in `7071e5041ee316d087661b658362feed159901ef`, based on `9adcaff0a72486ecc81242e0eca86e428c74879e`. The [intake note](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-191.md), [placement map](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-placement.json) and [full source review](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake191-source151-review.md) preserve the report, proof inputs, experimental limitations and recovery route. This directory contains a new summary, not a copy of the delivered main manuscript.

The submission contributes this source/table and its ordinary calibration. ProveIt supplies the inherited construction, calculus and runtime machinery. Root reviewed and executed the new fresh checks; `drop_contract` independently read the candidate arguments and prepared this publication. The exact supplied [license](LICENSE) is retained. No candidate was executed during publication preparation.
