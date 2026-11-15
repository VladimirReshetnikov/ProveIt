# PA194H5X and PA194JH5X

## Result

This package constructs **two new 194-state, two-symbol, single-tape Turing machines** whose blank-input nonhalting is equivalent to **Con(PA) in iPRA**. They implement new, uniformly interderivable numerical axiom presentations. **No valid machine below 194 working states is established here.**

The main report is [report/report.pdf](report/report.pdf), with its complete LaTeX source in [report/report.tex](report/report.tex). It includes the written proof, comparison of all 139 recognized spanning 194-state graph classes in the supplied corpus, both complete transition tables, and the reduction-search results.

The result is a **written mathematical iPRA proof with executable finite certificates and an explicitly retained calibration dependency**. It is not a newly completed end-to-end Lean or Rocq theorem. The current repository's machine-specific Lean reductions remain open. The complete PA-to-numerical proof compiler was not reimplemented here; its revised written construction is preserved in the exact AX11H archive identified below.

## What is new

Write `A -> B = I(A,B)`, where `I(A,B)=4 p(A,B)` and `p` is Cantor pairing. The quantifier constructor is `U(d,B)=I(B,d)+2`; equality is `E(a,b)=I(a,b)+3`; the designated contradiction code is 1.

**PA194H5X** replaces the fifth axiom family

    U(D, E(H,D) -> 1) -> 1

by

    U(D, E(H,D) -> 1) -> A,

with A independent of D and H. The old calculus derives every new instance using its explosion theorem. Setting A=1 recovers the old family exactly. The supplied symbolic Hilbert templates and independent checker verify these uniform derivations.

**PA194JH5X** additionally replaces the first head

    (X -> 1) -> H,  where X = U(D, U(D,H) -> 1),

by

    (X -> H) -> H.

This coupled change is valid because the new witness head supplies explosion through a separate 16-line derivation using the diagonal and distribution schemas, without the old first head or Peirce. The two-way first-head certificates have 95 and 72 lines over the explicitly retained derived implication basis. No propositional truth-table oracle is used.

Both machines use the ordinary, unexchanged sixth head; explicit-binder generalization `U(c,h)`; visible successful MP without a dummy push; cache-only Shift halting; and the eleven-entry AX interface with its actual fourth field. The ordinary and exchanged sixth heads are connected by independently replayed K/S premise-exchange certificates.

## Exact machine specifications

For both dense tables: working controls **0 through 193**, start **0**, halt **194**, alphabet **{0,1}**, all-zero two-way infinite tape, initial head coordinate **0**. A row is `state read write L/R next`. Entering halt occurs after the indicated write and move. Halt is excluded from the working-state count.

| Quantity | PA194H5X | PA194JH5X |
|---|---:|---:|
| Working states | 194 | 194 |
| Fixed + readers - simultaneous folds | 134 + 69 - 9 | 134 + 69 - 9 |
| AX macro tokens | 189 | 188 |
| Primitive source sites | 3,677 | 3,683 |
| Source outcomes, independently replayed | 4,786 | 4,794 |
| Independent symbolic execution events | 1,110,171 | 1,097,281 |
| Complete blank startup transitions | 57,922 | 57,922 |
| Maximum source path length | 40 | 34 |
| Smallest affine duration constant | 3 | 3 |

The independent physical checks cover nine arbitrary natural primary registers, an arbitrary nonempty finite spare list, arbitrary nonnegative gap, both decrement branches, four list traversals derived from the literal rows, complete frame closure, and the whole blank initialization. They are not tests on a small range of register values. Uniform interpretation of the symbolic rules in iPRA is a separate written proof included in the retained calibration.

Dense table SHA-256:

```text
PA194H5X
caffdd9f10d87d0d050eff07ab8f6e8edd9ab443aa94c948f03ee5316e37b614

PA194JH5X
70be32fe352ee0fb29581f1037948f429334cfc9c6bcaa813aba43c4efba0148
```

The native tables use start 74 and halt 254. The exact dense/native bijections are supplied. Every working control is graph-reachable from start 0; this does not assert that each control occurs on the actual blank run.

## Reproduce the positive results

Python 3.10 or later and its standard library suffice. From the extracted package root:

```sh
python3 -B verify.py --rebuild --integrity --work /tmp/pa194-witness-replay
```

Use a fresh, nonexistent work directory. Do not use `-O` or `PYTHONOPTIMIZE`. The driver:

1. Checks the package hashes and exact retained calibration identity.
2. Reconstructs both tables from frozen grammars and folds, without an optimization search.
3. Compares eight core reconstruction artifacts byte for byte.
4. Matches every primitive source operation and edge to arithmetic templates and checks the complete AX emitters and command-word contracts.
5. Regenerates all literal contracts, the complete startups, and the affine/frame-closure audits.
6. Replays the h5X, J, generalized J_A, and premise-exchange proof templates.
7. Rechecks exact structural novelty and the sealed comparison packet.

The observed complete replay passed all 16 orchestration checks. Its record is `verification/final_run/verification.json`; its component logs and receipts are retained alongside it. The final integrity manifest is `SHA256SUMS`.

To build the PDF, run:

```sh
python3 report/build_report.py
```

This uses installed pdfTeX, packages and scalable fonts. It has an isolated local-format fallback for an unconfigured TeX Live installation. It makes no network requests or system changes. On a normally configured installation, `latexmk -pdf report.tex` inside `report/` also works.

## Comparison scope and novelty

The source snapshot is:

```text
VladimirReshetnikov/ProveIt
8d31445d858761a8f6150c2e5012adae8895e932
```

The comparison accounts for **87 filed packets plus six incoming deliveries**, verifies all **27,459 PA/incoming source blobs**, and recognizes **4,468 matrix occurrences**, **879 normalized labeled identities**, and **721 spanning graph classes** over all sizes. Seven disconnected identities are recorded separately.

There are **139 spanning 194-state classes**, plus two disconnected diagnostics. Their attributed statuses are 67 principal, seven supplementary, 47 auxiliary, four seed, and 14 rejected constructions. Those labels describe what the source packets claim; they are not 67 independently audited iPRA calibrations. The 54 spanning 193-state classes are rejected or diagnostic inputs, not accepted smaller solutions.

Both new tables are absent from all 139 frontier classes and distinct from each other after allowing arbitrary control renaming, any spanning root, global left/right reflection, global symbol exchange, and ignored final write/move decorations. Exact full canonical tuples are compared, not merely hashes. Global symbol exchange is an enlarged structural test; it is not asserted to preserve the all-zero blank specification.

The 93-delivery ledger, every frontier mechanism/status annotation, all-size distribution, all occurrences and source locators, endpoint identity audit, and 346 representative tables through 196 states are in `comparison/`. That subpacket remains sealed and independently replayable:

```sh
python3 -B comparison/verify_packet.py
```

The recognizers cover the documented literal and JSON formats and recursive ZIP payloads. They do not execute arbitrary generators or reconstruct every table printed only in prose. The named architectures and reports are compared separately. The exact pinned upstream corpus is needed only to rebuild the full source census; core machine verification and novelty replay work offline.

## Proof dependency

The full revised AX11H archive is preserved at:

```text
references/pa194_ax11h_research_2026-11-14.zip
SHA-256 93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075
```

It corresponds to the revised filed directory `pa194_ax11h_research_2026-11-14_2`, not the older same-name packet. Its mathematical papers are also extracted under `references/baseline_proof/`. They address the physical/source and source/command bridges, current Foundation adapter, finite-demand forward compiler, reverse soundness and intuitionistic transfer.

The consistency endpoint is `DiophantineConsistency.IPRAPA196Consistency.nativePAConsistency`, the negation of the native reading of the mapped Foundation PA-refutation predicate. The current Foundation gitlink is `32e1a0956a8622fad067328ca1959729a7634428`. Exact source/hash comparisons are in `comparison/foundation_endpoint_audit.{md,json}`.

The new mathematical proof first obtains positive halting equivalence with the calibrated QAX11H machine by explicit PR maps. Intuitionistic negation then gives the desired Con(PA) equivalence. It assumes neither Con(PA) nor a reflection principle. Its proof-assistant formalization remains to be completed.

## Unsuccessful reduction work

`research/grammar/` preserves source templates, PRNG seeds, deterministic candidate inputs, mutation programs, logs, and completion/checkpoint status. Besides the two accepted machines, it explores the proved 187-token J_A+h5X presentation, radix changes, consequent variants, head order and argument permutations, and grammar sharing. All 18 randomized runs finished, with 187,622,892 mutation trials and 31,317,681 accepted mutations; these are not counts of distinct machines. A smaller macro word is not a smaller literal machine; restored copies can add primitive sites and destroy shared reader subtrees.

`research/runtime/` contains the complete-context collector and finite physical searches. On H5X these include all 18,721 pair quotients, all 193 noninitial deletion targets, all 362,880 register allocations for the specified tagged-fold rule, shared selectors, a coupled quotient/row screen, and selected neutral-row-plus-quotient experiments. The secondary JH5X screens are recorded separately. None produces a valid 193-state machine. A final shorter-header audit also certifies the JH5X runtime with a 36-cell minimum header, but all blank starts of its fixed Runtime193 splice halt or enter certified rays; shrinking the header does not repair that core. See `research/runtime/header_feasibility/`.

The runtime packet has positive controls and a portable C++17/Python replay:

```sh
python3 -B research/runtime/replay.py --work /tmp/pa194-physical
```

Use `--extended` for the larger finite searches and `--regenerate-contexts` for the symbolic window collector. A radius/step cutoff restricts a search; it is never a divergence proof. Frozen-context compound mutations are identified as heuristic discovery. No empty search result proves a lower bound of 194.

## Attribution

This package reuses and attributes the pinned source compiler, arithmetic engine, symbolic literal verifier, proof-calibration materials, and census parsers. Their source notices, licenses, and exact provenance are retained. The new contributions are the independent witness consequent and its bootstrap, the coupled J/J_A proof translations, two new literal implementations, complete source/physical replay for those implementations, the current corpus comparison, and the fresh reduction methods and search records. See `NOTICE.md`, `PROJECT_PROVENANCE.json`, and the component provenance files.
