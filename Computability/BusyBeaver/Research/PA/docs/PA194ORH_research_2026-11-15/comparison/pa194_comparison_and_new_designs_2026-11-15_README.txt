# Two new 194-state PA consistency machines

Research dates: **14–15 November 2026**. ProveIt snapshot:
`8d31445d858761a8f6150c2e5012adae8895e932`.

A final reconciliation with `ef0839bf15d8b556bc1e1634e6ad310adbcd4fe3`
confirmed exact equality of all 747 table-class keys and all 139 spanning
194-state keys. That update files the same six incoming archives into PA
research directories. The original comparison remains frozen and
reproducible; the late snapshot receipt and path mappings are in
`comparison/`.

Start with **`report/report.pdf`**. Its complete LaTeX source is
`report/report.tex`, the two generated appendices, and the included proof
fragment in `composites/composite_proof.tex`.

## Result

No justified machine below 194 working states was obtained. This archive
supplies two new binary, single-tape, blank-input constructions:

| Machine | Working states | Transitions | Exact seed-frame startup |
| --- | ---: | ---: | ---: |
| PA194AX11H_SF | 194 | 388 | 57,918 steps |
| PA194LC_AX11H_SF | 194 | 388 | 57,918 steps |

Both dense tables start at control 0, have working controls 0 through 193,
and have a separate halt label 194. The tape is two-way infinite and
initially all zero. There are no stationary moves or externally supplied
initial data. Native numbering uses start 74 and halt 254; native control
194 is a working state.

For each new machine N and its immediate parent M, the new written proof
establishes in iPRA, with absorbing halting-by-time semantics,

    H_M(t) -> H_N(3*t)
    H_N(t) -> H_M(3*t).

Thus iPRA proves equivalence of their halting and nonhalting sentences.
This direct relative proof needs only the literal finite row identities,
predecessor invariants, primitive-recursive clocks and quantifier-free
induction. It has no PA-consistency or source-calculus hypothesis.

The absolute conclusion

    iPRA proves nonhalting(N) <-> Con(PA)

imports the exact revised **written AX11H calibration** retained under
`references/ax11h_calibration.zip`. The companion also uses the supplied
LC-to-AX11H relative proof. The report identifies the exact Foundation
predicate and all dependencies. No new end-to-end Lean or Rocq kernel
proof is claimed. Finite executable checks do not substitute for that
inherited mathematical calibration.

## Exact new tables

`composites/machines/PA194AX11H_SF/machine.tm`

SHA-256:
`23fc656adc1afbe9e63f3a56df6e0c73a4f15a6d1493f2048aebaf00c9483ad2`

`composites/machines/PA194LC_AX11H_SF/machine.tm`

SHA-256:
`e9c6864d7fb452dff86a38e561f39a2dac0ddb873369fdfa3c1e7a88edcac7bf`

A row is `state read write L-or-R next-state`. Each directory also
contains the native table, the selector intermediate, labels, construction
metadata and the independent verification receipt. Both complete dense
tables are printed in the PDF.

## Comparison and novelty

The comparison covers 87 filed research packets and all six incoming archives at that snapshot, for 93 delivery records. It supplies all **139 spanning
194-state classes**, plus one disconnected 194-control diagnostic. The
complete 140-table index distinguishes reported principal constructions,
supplements, auxiliaries, seeds and rejected experiments. These roles are
attributed report claims, not independent consistency proofs.

The new machines have no match among those tables and are mutually
distinct. The exact tuple comparator also allows every spanning root,
arbitrary control names, tape reflection, global symbol exchange and
ignored terminal-edge write/move decorations. It completed 215,728
comparisons. Global symbol exchange is an extra structural comparison,
not a zero-blank semantic equivalence.

All six changed rows in each new construction are used during blank
initialization. The compatible selector/acceleration composition changes
recurring physical behavior, not only state names or unused transitions.
The report attributes the individual ingredients to the incoming work and
explains why the other proposed selector pair cannot be copied into AX11H.

## Replay

Python 3.10 or later and the standard library suffice for the main checks.
Assertions must remain enabled; do not use `python -O`.

```sh
python3 -B reproduce.py
```

This checks the manifest, reconstructs both new machines in a temporary
copy, compares all core output bytes, checks the independent finite proof
premises and exact startup synchronization, and repeats the complete graph
novelty and frozen-corpus audits. Output is written to a fresh temporary
directory, whose path is printed. Specify `--output PATH` for another
location. Frozen delivered artifacts are preserved.

```sh
python3 -B reproduce.py --lc
```

The additional flag replays the inherited LC dependency: both sets of
4,778 source outcomes, generic list lemmas, startup, and affine clock
audit. This full replay was completed during this research; its receipts
are already under `verification/inventory_composites/`.

```sh
python3 -B reproduce.py --research
```

The research mode also needs a C++17 compiler. It repeats the portable
physical-search suite and the source/arithmetic experiments. It can take
several minutes. For the larger 530-table physical suites, use the
individual `research/physical/reproduce.py --all` command documented there.

The default frozen census audit checks every representative and the
recorded catalog identities. To download and independently reparse the
six exact pinned incoming archives, use:

```sh
python3 -B comparison/audit.py --refresh --output /tmp/pa194-recensus.json
```

No checker is described as a proof-assistant kernel verification of the
absolute arithmetic derivation.

## Contents

- `report/`: the compiled PDF, complete LaTeX source, exact table appendices
  and appendix generator.
- `composites/`: deterministic constructors, independent row and startup
  checker, direct relative proof, novelty checker and all machine tables.
- `comparison/`: all 140 representatives, the 93-delivery ledger, 27-family
  comparison, source identities and portable census audit.
- `references/`: the exact revised AX11H archive, exposed written proof
  fragments, and the full standalone LC relative-proof dependency.
- `verification/`: completed fresh evidence, including the full LC replay.
- `research/physical/`: bounded local, common-future, predecessor and
  recursive state-fold searches, with frozen inputs and receipts.
- `research/closed_macro/`: joint reassociation searches outside the axiom
  reader, covering 13,125 distinct raw tables at depths two through four.
- `research/theory/`: the reversed-Cantor experiment and independent proof
  reviews. The arithmetic candidate is explicitly uncertified and is not
  presented as a consistency-machine construction.
- `research/related_projects/`: pinned current README sources for the
  suggested ZFC, DiophantineConsistency and ConciseIPRA programs.
- `MANIFEST.sha256`: release-file integrity hashes.

## Compile the report

Use a normal TeX Live installation with pdfLaTeX and the packages named in
the preamble:

```sh
cd report
python3 -B generate_appendices.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report includes further research questions. No global state-count
lower bound or worldwide novelty claim is made. Source licenses and
attribution notices are retained with each imported component.
