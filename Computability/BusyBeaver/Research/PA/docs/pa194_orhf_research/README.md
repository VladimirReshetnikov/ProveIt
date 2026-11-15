# Two 194-state PA consistency machines

## Result

**No justified machine with fewer than 194 working states was obtained.** This package supplies two new 194-state compositions, PA194ORHF and PA194ORHBF, with complete transition tables, an ordinary written iPRA transfer proof, finite certificates, a comparison of the supplied designs, and reproducible search evidence.

The new machines combine the supplied ORH operand reassociation with two recurring three-to-one transition shortcuts. ORHBF additionally uses the supplied B history selector. These mechanisms are attributed to their original packets; the contribution is the newly verified compositions, the simultaneous-shortcut invariant and exact clock, and the comparative research. There is no claim to have invented the constituent mechanisms.

The same absolute endpoint follows by composing the new relative iPRA theorems with the **inherited revised AX11H written calibration**:

    iPRA proves Con(PA) iff the new machine does not halt on blank input.

The exact PA predicate is the current Foundation predicate identified by that calibration. This package does not supply a newly completed end-to-end Lean or Rocq formalization. The ten inherited proof manuscripts and their source identities are retained explicitly. The finite Python checks are mathematical evidence accompanying the written proofs, not a proof-assistant kernel or an independent reconstruction of every inherited proof template.

## Read first

- `report/pa194_orhf_report.pdf`: the complete report, proofs, comparison, full tables, and 104-design roster.
- `report/pa194_orhf_report.tex` and the adjacent generated `.tex` files: the editable paper.
- `proof/shortcut_stuttering.tex`: the new complete-tape invariant and exact iPRA clock argument.
- `proof/selector_transfer.tex`: the B companion's finite local simulation and iPRA transfer.
- `proof/calibration_audit.tex`: inherited proof dependencies, scope of review, and source-level experiments.

## Exact machine model

Deterministic, single tape, two-way infinite binary tape; all cells initially zero; head initially at coordinate zero; one-cell L/R moves only. Working controls are `0..193`, initial control `0`, terminal halt label `194`. The halt label is excluded from the state count and has no outgoing rows. Both complete dense tables have 388 rows in `state read write direction next` format.

Native tables and bijections are also supplied. In native notation the initial control is `74` and the halt label is `254`. **Native label 194 is a working control.** Do not confuse it with the dense halt label.

| Machine | States | Rows | Complete blank initialization | Dense table SHA-256 |
|---|---:|---:|---:|---|
| PA194ORHF | 194 | 388 | 57,890 transitions | `9818435880b25294c15c1f9852ecad44af53a8e185410eeeb6c0ec99a69de6a6` |
| PA194ORHBF | 194 | 388 | 57,982 transitions | `c8cdfc187b0155c0baa9e4d5c0141dad184ae95f1a712b22b64dc0e013c1e247` |

Each complete initialization saves exactly 52 transitions relative to its respective unaccelerated parent. This is not a claim about a finite total halting time. The ongoing speed relation is the exact clock in the report.

## Reproduce the finite checks

Use Python 3.10 or later, with assertions enabled. No external repository, network, third-party Python package, or search is needed for the default replay. From this directory:

```sh
python3 -B verify_all.py
```

It verifies `SHA256SUMS`, reconstructs both literal machines into temporary directories, checks complete blank initialization and exact byte identity, replays the simultaneous-shortcut and B-selector certificates, binds the stored independent source-check receipts and inherited AX11H-to-ORH source/clock certificate, and compares both machines against the retained 548 spanning prior graphs plus two diagnostic tables.

For the longer independent symbolic replay of every source outcome:

```sh
python3 -B verify_all.py --literal
```

This derives the four unary-list lemmas from the actual rows and checks 4,778 source outcomes per machine, arbitrary primary registers, both decrement branches, arbitrary nonempty finite spare lists, exact frame closure and positive clocks. The recorded original replay is `verification/literal_replay.log`; per-machine contracts and receipts are in `machines/*/independent/`. Optional replay writes only into a temporary reconstruction.

To recompute all pinned catalog identities as well:

```sh
python3 -B verify_all.py --coverage
```

The default replay checks the finite literal facts, not the inherited PA-proof compiler theorem. Read the proof boundary in the report before interpreting a PASS result.

## Contents and provenance

- `machines/`: two new dense/native tables, label maps, source metadata, construction receipts, and independent symbolic contracts.
- `construction/`: deterministic reconstruction from the retained ORH parent.
- `verification/`: independent physical checker, finite shortcut verifier, receipts, and release validation.
- `comparison/`: all 104 named positive-claim designs with aliases and provenance; all 528 filed 194-state classes plus incoming additions; 55 catalogued 193-state tables and their complete 10,615-start audit; exact coverage and novelty scripts. See its README for recognition limits.
- `research/`: completed exhaustive register-allocation enumeration, expanded grammar-search inputs and recorded runs, local shortcut discovery, and explicitly scoped negative results.
- `reference/`: exact ORH and ORHB parent tables, ORH proof dependency, revised AX11H proof manuscripts and original calibration archive. `reference/ORH_proof/upstream_validation/` contains **inherited ORH/OR receipts**, not receipts for the new machines.
- `licenses/`: retained upstream licenses and notices.

All source comparisons are pinned to ProveIt commit:

`883da8d55452ea097910ed2509a1eefc833ce292`

[Pinned PA research](https://github.com/VladimirReshetnikov/ProveIt/tree/883da8d55452ea097910ed2509a1eefc833ce292/Computability/BusyBeaver/Research/PA) · [Pinned incoming packets](https://github.com/VladimirReshetnikov/ProveIt/tree/883da8d55452ea097910ed2509a1eefc833ce292/docs/incoming)

Novelty is relative to the recognized tables in those supplied directories, with documented parser exclusions. Graph comparison allows arbitrary state renaming and root, reflection, symbol exchange, and ignored write/move decorations on halt entry. It is not a claim of behavioral inequivalence: the constructions are deliberately halting-equivalent.

## Compile the report

With a conventional TeX Live installation:

```sh
python3 report/generate_data.py
cd report
pdflatex -halt-on-error pa194_orhf_report.tex
pdflatex -halt-on-error pa194_orhf_report.tex
```

The included `report/compile_in_session.py` is only an optional helper for the original Linux environment's broken system TeX cache. A normal TeX installation does not need it. The PDF was rendered and visually checked after compilation. Recompiling or editing files naturally changes the frozen release hashes; preserve the original release separately if you want to run its integrity check unchanged.

## Limits of the reduction search

The completed 9! allocation enumeration excludes an eighth disjoint fold only under its exact predecessor-bit/three-step provider rule. Heuristic macro searches found no accepted strict reduction; two runs ended at recorded resource-limited prefixes and one completed its specified time budget. The four capped executions in the 193-state audit remain unclassified by that bounded screen itself, and their source constructions have separate retained rejection reasons. No general lower bound of 194 states is claimed.
