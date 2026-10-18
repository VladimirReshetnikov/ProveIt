# Exact 245-state table in Lean

[TableRouting245.lean](../../Lean/BusyBeaver/ZFC/TableRouting245.lean)
defines the exact [routed candidate](candidate-routing245/README.md): 245
working states, 490 binary actions, blank start 0, dispatcher 88, and separate
halt 245. The terminal action retains its write and movement. The literal
table, old labels and inverse numbering match the delivered machine exactly.

Lean checked **64 named theorems and 64 typed callers**. They establish the
table size, target bounds, unique halt action, the state-numbering inverse,
incoming-edge facts, and 46 core arithmetic and selector rows. The 46 rows
agree with the 246 machine in old labels; this does not establish equivalence
of the complete machines. Canonical numbers differ where old label 247 was
removed, including old label 255, which is now canonical 244.

The numbering inverse is proved on actual canonical working states. The
total old-label lookup returns canonical 0 on absent labels; it does not
assert that those absent labels are working states. In particular, the
unique halt is old state 77 reading one, whose action writes one, moves right
and terminates. The incoming characterization for old state 255 includes its
read-zero self-loop as well as the edge from old state 75.

The first source and audit runs passed in **21.854 and 0.393 seconds**, with
zero warnings. Six axiom reports are empty and 58 use only standard
`propext`. Finite proofs use `decide +kernel` with default proof limits.
The [actual execution record](results/table-routing245-verification.json)
has SHA-256
`bb53b70f1a775b915d9b335a4ce1378c8350f771aca6aa007c0227989fd87281`.
The checked source is
`a00da51f6c813bdbb9ff573ba75a0a6cb1e7f1eb9d630758b5b1bfed4a5b673b`;
its fresh object is
`4dc4e2697143378811e5d6be4de65527df37534abcc97baa91d3d23665cc3b6b`.

Only the previously checked `BusyBeaver.Core` source/object pair is reused.
The exact compiler and implicit `Init` object are pinned. Source and audit
run serially with `-j1 -M4096` under one shared 120-second limit. The guard
records the newly compiled source object before the audit and checks its
identity, every input and every provider afterwards. It performs no
dependency build, download or compiler-version query. The
[history](results/table-routing245-history.json) retains the executed guard,
emitter, source, audit, logs, earlier unexecuted header revision, and
independent source, preparation and actual-execution reviews.

## Reproduction

From this directory:

```sh
python3 -B generate_table_routing245.py --check
python3 -B check_table_routing245.py --output /tmp/routing245-table-prepared --prepare-only
python3 -B check_table_routing245.py --output /tmp/routing245-table-checked
```

Use fresh output directories outside the checkout. Preparation runs no proof
command. Compilation requires the exact existing Core object and toolchain
recorded in the parent evidence; the guard accepts path overrides but rejects
changed bytes. The [publication record](results/table-routing245-publication.json)
distinguishes the actually executed scratch guard from its maintained path
defaults and the new standalone source generator. Published Lean source and
audit are byte-identical to the successful run.

This unit proves finite table facts. The reassociated source tree, decoder
coverage with padding 64, unbounded runtime simulation, 407,915-step blank
initialization, and complete 245-state consistency endpoint still need Lean
proofs. PA internalization remains a separate obligation. The closed
[246-state external endpoint](prefix246_binary.md) remains the formal baseline.
