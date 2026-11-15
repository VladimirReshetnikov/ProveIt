# Five new 194-state machines for the PA consistency program

Research date: **14 November 2026**. Initial ProveIt snapshot:
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2`; final comparison snapshot:
`603c58ca3bd6bf3222fcfc4e308e6b079f65d573`.

Start with **`report/report.pdf`**. The full LaTeX source is
`report/report.tex` and its included fragments. The principal machine is
**`additional/PA194LC_AX11H/machine.tm`**.

## Result and proof boundary

No verified machine below 194 working states was found. This release supplies
five new binary, single-tape, blank-input machines with 194 working states:

| Machine | Exact source preserved | Construction and proof |
| --- | --- | --- |
| **PA194LC_AX11H** | All 3,671 resolved AX11H instructions | Three-row loop-continuation patch; explicit relative iPRA proof; absolute Con(PA) corollary importing the revised AX11H written calibration |
| PA194LC | All 3,673 resolved original-primary instructions | Three-row loop-continuation patch and explicit relative iPRA proof |
| PA194LC_A | Same original-primary source | First sibling loop association and explicit relative iPRA proof |
| PA194LC_B | Same original-primary source | Second sibling loop association and explicit relative iPRA proof |
| PA194LC_C | Same original-primary source | Third sibling loop association and explicit relative iPRA proof |

The five graphs are mutually distinct and distinct from all **110** complete
194-state graphs in the final audited snapshot, even under arbitrary working
state renaming, any spanning initial root, global tape reflection, symbol
exchange and ignored terminal-edge write/move decoration. Symbol exchange
is used for structural comparison, not as a fixed-zero-blank equivalence.

The main written result is

```
iPRA proves: nonhalting(PA194LC_AX11H) <-> Con(PA).
```

This is an ordinary computer-assisted mathematical proof using an explicitly
imported theorem: the revised AX11H packet's written absolute calibration.
The unchanged upstream ZIP is included as
`reference/ax11h_calibration_603c58c.zip`, together with the focused review
and upstream finite-check receipt under `verification/`. The report identifies
the exact Foundation `nativePAConsistency` predicate and its dependency.
**No new end-to-end Lean or Rocq kernel theorem is claimed.** The review and
finite checks are not represented as an independent full reconstruction of
the imported arithmetic proof.

For the parent AX11H machine `MH` and new machine `MLH`, let `H_M(t)` mean
halted **by** time `t`, with absorbing terminal semantics. The new relative
proof supplies explicit primitive-recursive witnesses:

```
H_MH(t)  -> H_MLH(13*t*t + 707*t + 58616)
H_MLH(t) -> H_MH(13*t*t + 707*t + 58616).
```

The original-primary PA194LC pair has bound `13*t*t + 707*t + 58848`.
For any ordered pair among the original primary and its four LC variants,
the uniform bound is `13*t*t + 707*t + 59014`. Their directly established
results are relative iPRA equivalences; an absolute conclusion for that
separate family still imports its corresponding primary calibration.

The retained **PA194GAX11** composition is an independently checked
concurrent reproduction. The final snapshot contains an identical table
named PA194AX11G. It is **excluded from the five-new-machine claim**. Its
own source/command proof and full physical checks remain useful comparison
artifacts; that reproduction retains the stated weak-arithmetic witness
internalization obligation.

## Exact principal machine

`additional/PA194LC_AX11H/machine.tm` has working states `0,...,193`, initial
state 0, terminal label 194, alphabet `{0,1}`, and 388 rows. A row is

```
control  read  write  L-or-R  next-control
```

The tape is two-way infinite and initially all zero; no stay-put moves are
used. The terminal control is excluded from the count. Dense SHA-256:

`5f10f071e7118ff33aba822e05bae0331b4c78508656c3e945c31b0c6788f9c5`.

Native SHA-256:

`e7800298659a5768a8aabfbd0cfd0ea42af241ed2a10b0cc1dbf64ed8aff1112`.

In the pinned AX11H native numbering (start 74, dispatcher 84, halt 254),
the only changed rows are:

| Row | AX11H parent | PA194LC_AX11H |
| --- | --- | --- |
| `(139,0)` | `0 R 190` | `0 R 99` |
| `(139,1)` | `0 L 16` | `1 R 190` |
| `(190,1)` | `1 R 99` | `1 L 73` |

The raw construction has 201 controls; seven checked contextual folds
leave 194. All source instructions and successors are unchanged, although
305 primitive addresses and 61 recurring constructor loops change physical
implementation. Blank startup takes 57,922 transitions. Fresh independent
checks derive four generic list lemmas from literal rows and verify all
4,778 source outcomes for each of the parent and new tables. The new
successful constructor iteration takes six more physical transitions.

Do not apply native labels to a dense table. `labels.json` supplies the
exact native/dense bijection. The full dense table is also printed in the
report, together with the original-primary PA194LC table.

## Reproduce

Python 3.10+ and its standard library suffice. Assertions must be enabled;
do not use Python's `-O` option. Run from this archive's root:

```sh
python3 -B reproduce.py --out /tmp/pa194-replay
python3 -B reproduce.py --physical --out /tmp/pa194-full-replay
```

The default rebuilds all five new machines in isolated temporary directories,
compares the generated artifacts byte for byte, binds the recorded literal-row
certificates to the released table and contract hashes, replays source and
startup checks and the affine clock bounds, and checks novelty against all
110 prior graphs. It also verifies the exact archived calibration hash.
The replay writes only to the selected external evidence directory; if
`--out` is omitted it creates a temporary directory and reports its location.

`--physical` additionally regenerates the universal symbolic contracts for
the original primary, its four new LC variants, AX11H and LC_AX11H. It can
take several minutes. The included completed physical receipts correspond
to the exact released tables. The default explicitly records that it did
not regenerate them. Neither mode is a proof-assistant kernel check or a
verification of the full imported arithmetic derivation.

Individual commands:

```sh
python3 -B additional/PA194LC_AX11H/verify_all.py --output /tmp/lc-ax11h-check
python3 -B late_snapshot/check_novelty.py --out /tmp/pa194-novelty.json
python3 -B construction/build.py --output /tmp/pa194lc-build
python3 -B research/enumerate_loop_trees.py
python3 -B research/patch_loop_corpus.py
python3 -B research/reject_false193.py
python3 -B additional/PA194GAX11/verify_all.py --output /tmp/gax11-check
python3 -B research/incoming_edge_search/replay.py --output /tmp/edge-search.json
```

The incoming-edge search additionally needs a C++17 compiler. Its default
replay covers 94 frozen inputs from the initial snapshot. Use `--index 0`
for one input; its README gives the exact window and detour bounds. The
optional `--quick` modes of the additional verifiers explicitly skip their
physical replays. Direct individual builders may rewrite their generated
artifacts; the root and additional combined wrappers preserve frozen files.

## Contents and comparison scope

- `report/`: PDF, complete LaTeX source, two complete transition tables,
  94-graph and 82-packet appendices, and the 16-graph late addendum.
- `additional/PA194LC_AX11H/`: principal construction, literal tables,
  source identity, frozen parent, independent contracts, clocks, standalone
  relative proof in TeX/PDF, and portable combined verifier.
- `machines/`: four original-primary LC constructions with full source,
  tables, folds, startup records, contracts and table-bound receipts.
- `reference/`: the original primary and the unchanged revised AX11H
  calibration ZIP.
- `construction/`: deterministic builder for the four original-primary
  loop variants and their exact tree/fold specifications.
- `verification/`: literal-row symbolic interpreter, independent source
  resolvers, clock bounds, proof reviews and recorded completed checks.
- `comparison/`: preserved initial 82-packet/94-graph census, locators,
  frozen representatives, family comparison and census regeneration tool.
- `late_snapshot/`: repeated final census, 16 new prior graphs, exact five
  incoming ZIP identities, frozen READMEs and completed 110-graph novelty check.
- `research/`: 4,104-tree enumeration, 96-table cross-composition screen,
  94-graph incoming-edge deletion search, other bounded searches, and an
  explicitly rejected 193-state source mismatch with a reproducer.
- `additional/PA194GAX11/`: concurrent AX11G reproduction, source/command
  argument, full finite checks and search ledger.
- `licenses/`: preserved notices for inherited source material.
- `SHA256SUMS`: hashes for every release file except the manifest itself.

The comparison includes reported constructions, auxiliaries, seeds and
rejected experiments. The 110 graphs are not 110 established consistency
theorems. Tables available only through unexecuted generators or only printed
in TeX are outside the literal/explicit-JSON census recognizers; the packet
narrative also reviews the supplied README claims. The initial census and
its old novelty receipt are preserved as historical evidence and are
superseded for final novelty by `late_snapshot/novelty.json`.

## Compile the report

A normal TeX Live installation with pdfLaTeX and the preamble's packages
is sufficient:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The initial appendix generator is run from the archive root:

```sh
python3 -B report/generate_appendices.py --data comparison --output report
```

`PROVENANCE.json` records the exact source snapshots and proof dependency.
No network access is needed to rebuild the new machines or replay the
frozen evidence. Regenerating a full census from Git requires the stated
pinned repository objects.
