# U209: compatible contextual decoder reductions for Con(PA)

Research prepared for Vladimir Reshetnikov, 29 October 2026.

This archive contains a concrete **209-working-state, binary, single-tape
Turing-machine candidate**, including its complete blank initializer. It has
418 transition rows, working states 0 through 208, and separate halt label 209.
A separately verified 210-state construction is also included.

Read **report.pdf** for the comparison, mathematical construction, proofs,
verification results, proof boundary, and complete U209 transition table.
The editable master is **report.tex**, with included TeX sections in **paper/**.

## Main result

The three supplied U211 proposals are different machines with the same source
primitive word and full ordinal control-flow graph. Their rooted labeled
transition graphs are pairwise nonisomorphic. They remove native states 180,
181, and 218, respectively.

The new construction makes all three savings compatible. Starting from the
Research U211, eight source reassociations permit deletion of 218 and produce
U210. A new eight-factor reassociation across a shared runtime helper then
creates the context needed to delete 180. Three additional source rotations
and the arithmetic entry repair complete U209.

The key additional freedom is that the shared backward helper reaches state
204 scanning zero. Its 204/0 branch remains fixed while its 204/1 branch can
change with the source layout. This preserves the Research savings while
enabling both other reductions.

## Exact machine conventions

- `machine/u209.tm`: primary dense table, states 0–208, halt 209.
- `machine/u210.tm`: secondary dense table, states 0–209, halt 210.
- One two-way infinite tape, one head, alphabet {0,1}, blank symbol 0.
- Start in state 0, head at coordinate 0, every tape cell initially 0.
- Only left and right moves. Every working state has both binary rows.
- `q b w D r` means read b, write w, move D, enter r. Entering halt ends
  the computation after that write/move.
- `#! start 0` is metadata, not a transition.
- Native tables preserve sparse historical labels and separate halt label
  254. The state-map JSON files give exact checked dense bijections.

Dense U209 SHA-256:

```text
bda91bd40880f96edef104246d22797fe281355cf03610ab7e93e7923be8aa16
```

Native U209 SHA-256:

```text
4564c4876f9b18725bfb3505ec1f50d1ebce572502f2c6381ad673ecfdc3c3e1
```

Final U209 source SHA-256:

```text
912724f29b0de28b3326c710fdf1f3863ebd07058c6db1a9b4bbaffb3ae5e3f3
```

## Verification and proof status

| Fresh result | U210 | U209 |
|---|---:|---:|
| Working states / rows | 210 / 420 | 209 / 418 |
| Guarded arbitrary-natural primitive contracts | 5,084 | 5,084 |
| Literal rows covered | 420 / 420 | 418 / 418 |
| Symbolic inference applications | 1,249,857 | 1,248,748 |
| Minimum primitive-duration constant | 5 | 5 |
| Final internal-prefix bindings | 3,908 | 3,908 |
| Semantic negative controls rejected | 9 | 11 |
| Exact common blank startup | 48,140 steps | 48,140 steps |

The symbolic contracts quantify over arbitrary natural primary registers,
arbitrary natural extra header gap, and arbitrary nonempty finite spare lists.
They compare complete tape endpoints, including the zero exterior. They use
literal transitions and mathematical unary/list induction, rather than bounded
tests on sample register values.

The source keeps all 3,909 primitives and all 5,083 nonhalt ordinal successor
edges. Both candidates have 197 distinct syntactic subtrees, maximum address
depth 41, and maximum consecutive-zero run 6. The source control graph is
checked with two algorithms.

The new result is an ordinary PA-formalizable halting-preservation proof from
the exact Research U211 parent. Composing it with the retained numerical
proof-calculus, protected-startup, compiler, and unary-theory arguments gives
the intended mathematical endpoint:

```text
PA proves not Halt(U209, blank) iff Con(U) iff Con(PA).
```

**This is not a newly exported end-to-end Lean, Rocq, MM0, or PA proof object.**
Python is not a proof-assistant kernel. The different K215/ZFC theorem does not
certify U209. The manuscript and audit notes identify the inherited calibration
and its exact status. No consistency assumption is needed for the biconditional;
unconditional nonhalting is not asserted.

Some source-reassociation intermediates have seven-zero address runs and are
not claimed to be complete correct runtimes. Their source CFG identities hold.
Only the final source layouts are used for the full literal runtime theorem;
both final tables passed that theorem's complete executable derivation.

The final U209 local fold applies on every common initial tape in state 0.
Its one-step old cases expand to 5, 3, 1, or 1 new steps. The resulting local
time bound does not extend across the preceding source-address changes.

## Reproduce offline

Requirements: Python 3.10+ with the standard library. No network, optimizer,
solver, or proof-assistant installation is needed. Run from this directory:

```sh
python3 reproduce.py --quick
python3 reproduce.py
python3 reproduce.py --both
```

The quick command verifies the payload manifest, rebuilds both machines,
binds comparison snapshots to the retained original ZIP members, checks the
three-way literal/source comparison, reruns both independent finite audits
and both exact startups, and validates the sealed runtime records as data.
It explicitly skips fresh universal runtime derivations.

The default additionally rederives all U209 primitive contracts. `--both`
freshly rederives both complete suites and compares the resulting per-case
records to those delivered. Allow a few minutes per machine, depending on the
computer. All generated results go to `build/`; delivered evidence is unchanged.

The independent finite checkers use explicit exceptions and were verified
under normal Python and `python3 -O`. Full runtime replay requires assertions
and refuses optimized Python.

To compile the report, install a standard LaTeX distribution and run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Verify the delivered manifest first. Recompiling can alter PDF metadata and
therefore its hash; this does not change the machine files.

## Input comparison and provenance

The comparison is pinned to ProveIt commit
`da4ab9dd68ccfc47ac852118601eaf1fdae53795`. All four unchanged input archives
are preserved in `inputs/`, including all nested earlier theory and machine
dependencies. `provenance.json` records their precise identities.

All three original finite replay suites passed freshly in separate copies.
Their original full runtime suites were not rerun for the comparison; those
historical receipts are distinguished from the fresh new U210/U209 derivations.

The literal machines search the inherited numerical calculus calibrated to
unrestricted weak cover with irreflexivity. They do not execute the separate
positive dyadic emitter in the unary-theory archive.

## Artifact map

| Directory | Contents |
|---|---|
| `machine/` | Dense/native U209 and U210; state bijections |
| `source/` | Final source occurrence/address maps |
| `intermediates/` | Immediate prefold tables for local proofs |
| `code/` | Deterministic builder, independent auditors, startup, comparison, runtime |
| `evidence/` | Fresh runtime cases and summaries, finite receipts, startup frames |
| `comparison/` | Exact three-input snapshots, census, original finite replay logs |
| `inputs/` | Four original archives and short construction recipes |
| `proofs/` | New reduction, theory, runtime, and comparison audit notes |
| `paper/` | Editable report sections and generated exact transition table |

`MANIFEST.json` covers every delivered payload file except itself. `build/`,
Python bytecode, and TeX auxiliary files are excluded from the release.

The construction is new relative to the reviewed proposals. No global
minimality, discovery-priority, or independently ratified record claim is made.
See `NOTICE.md` for attribution and retained notices.
