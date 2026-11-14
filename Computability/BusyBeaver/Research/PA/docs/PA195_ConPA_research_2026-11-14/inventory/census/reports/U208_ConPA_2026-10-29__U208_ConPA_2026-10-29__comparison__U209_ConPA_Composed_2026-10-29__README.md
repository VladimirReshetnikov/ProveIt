# U209: composing three reductions for Con(PA)

This package supplies an explicit **209-working-state, binary, one-tape Turing machine**, improving on the three supplied 211-state candidates. Dense working labels are 0–208, the initial label is 0, and 209 is the separate halt label. The tape is indexed by the integers, initially all zero, with the head at coordinate zero. Initialization is included.

Read **report.pdf** for the comparison, construction, proofs, verification, inherited arithmetic calibration, further research questions, and complete transition table. The editable main source is **report.tex**; its included sections/tables are in `paper/`.

## What is new

The three U211 proposals remove different native states but need incompatible source associations. A new common association and transport of the closed continuation at native 116 make all three deletions compatible:

```
180 -> 163
181 -> 220
218 -> 157
```

The Research proposal's selector moves from native 129 to native 217. The final changed keeper rows are:

```
163 0 0 L 211
220 0 0 L 217
```

The deterministic construction performs 30 closed-factor rotations, a five-state label permutation, the inherited contextual entry repair, and three guarded deletions. It keeps all 3,909 ordered source primitives and every ordinal control successor. The final simultaneous fold has 10 exhaustive two-cell cases and 414 ordinary-row identities. The exact time change against the final 212-state prefold table is `Tnew = Tpre + 2*n3 + 4*n5`, hence `Tpre <= Tnew <= 5*Tpre`. This time comparison does not cover source readdressing.

## Proof status

The new conventional mathematical preservation proof, composed with the retained U-specific calibration, gives the PA-formalizable endpoint

```
PA proves: not Halt(U209, blank) <-> Con(U) <-> Con(PA).
```

The executable checks support that mathematical argument. **There is no newly kernel-checked PA derivation, Lean, Rocq, or MM0 endpoint for U209.** The complete numerical-calculus soundness/completeness, nonzero-start protection, fair-search proof, and U/PA interpretation remain inherited mathematical dependencies, retained in the archive and reviewed in the report. No unconditional consistency, nonhalting, or optimality assertion is made.

## Offline reproduction

Requirements: Python 3.10+ and the standard library. From this directory:

```sh
python3 reproduce.py
```

This checks frozen hashes, reconstructs the literal machine, independently checks source control flow and grouped decoder prefixes, checks the simultaneous fold and arithmetic-entry repair, runs an independent fold auditor, replays the exact blank prefix, and derives every final-table primitive contract. It requires no network or discovery search.

```sh
python3 reproduce.py --quick
```

The quick command **explicitly skips full symbolic-runtime replay**. Its receipt records this omission. The full command refuses `-O` or `PYTHONOPTIMIZE`, because the inherited symbolic engine uses assertions. The finite fold checker is also deliberately run under `-O`; its checks use explicit exceptions.

To regenerate the PDF, install `pdflatex` and the normal TeX packages used in `report.tex`:

```sh
python3 reproduce.py --quick --pdf
```

`SHA256SUMS` covers frozen source, input, machine, reference and report-source files. It excludes generated PDF metadata, TeX auxiliary files, and replay receipts with variable timing. Full runtime receipts bind the exact machine/source hashes and contain per-contract evidence.

## Fresh checks

| Check | Result |
|---|---:|
| Working states / literal rows | 209 / 418 |
| Ordered source occurrences | 3,909 |
| Distinct source subtrees | 197 |
| Source control edges | 5,083 |
| Maximum address depth / zero run | 42 / 6 |
| Complete primitive contracts | 5,084 |
| Literal row coverage | 418 / 418 |
| Symbolic inference applications | 1,250,049 |
| Minimum duration constant | 5 |
| Exact blank initialization | 48,140 steps |
| Startup one-cells | 120 |
| Exceptional final-fold cases | 10 |
| Arithmetic-entry repair cases | 2 |

The symbolic contracts cover arbitrary natural primary registers and gap, arbitrary natural first-spare value, arbitrary finite spare tail, and both zero exteriors. They are not bounded numerical simulations.

Some unfinished source rotations temporarily violate decoder admissibility: stage 17 has a seven-zero run, repaired at stage 18. The builder checks source CFG preservation at every rotation; whole-runtime correctness is asserted for the final machine. The independent grouped audit explicitly records that temporary obstruction rather than silently ignoring it.

## Files

- `machine/u209.tm`: complete dense table, 209 working states and separate halt 209.
- `machine/u209.native.tm`: same machine with inherited native labels and halt 254.
- `machine/rotated212.native.tm`: final prefold table used by the local theorem.
- `machine/sites.json`, `state_map.json`, `construction.json`: source, exact relabeling, complete deterministic recipe and stage identities.
- `inputs/`: pinned common U212 table and source.
- `code/`: portable construction and verification code; `code/runtime/` retains the native symbolic engine with provenance.
- `evidence/`: final exact/symbolic receipts, per-contract runtime records and independent mathematical reviews.
- `comparison/`: fresh results and fingerprints for all three supplied U211 proposals.
- `reference/`: the four original requested archives, the recovered complete U222 calibration packet, source/ancestry manifests, licenses and notices.

The direct U222 archive repairs a documentation omission in the compact U212 ancestry retained by Research and Rotated. It was recovered byte-for-byte from Contextual's complete nested ancestry and matches the old U218 dependency hash. The original supplied packets remain unchanged.

## Exact identities

Dense U209 SHA-256:

```
3a69998d818b6e637e33dc0a2412538e49179a501496d5c252c7f68ff2af78be
```

Native U209 SHA-256:

```
8e058789f2f11a448db7212bf2e32317fbd5027c6043cfd0e7791532bc3256cb
```

Source SHA-256:

```
cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164
```

Repository review snapshot: `VladimirReshetnikov/ProveIt` at `da4ab9dd68ccfc47ac852118601eaf1fdae53795`. Exact source URLs and archive hashes are in `reference/source_manifest.json`.

See `NOTICE.md` for attribution and the report for the precise theorem scopes.
