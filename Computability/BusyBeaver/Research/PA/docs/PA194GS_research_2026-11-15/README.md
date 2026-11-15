# PA194GS — gate exposure and reassociation

**Result:** a new, fully specified 194-state binary blank-start Turing machine. No verified machine below 194 states was obtained.

Start with **`report/report.pdf`**; its editable source is **`report/report.tex`**. The report contains the new construction and relative proof, the complete 388-action transition table, the comparison of 104 named constructions, and the unsuccessful reduction research. All main verification commands work offline.

## The theorem and its dependency

Let `M0` be the exact revised PA194AX11H table and `M1` the delivered PA194GS table. With

```text
L(t) = 2*t,
```

the written relative proof establishes in intuitionistic PRA both pointwise implications

```text
HaltBy(M0, t) -> HaltBy(M1, L(t))
HaltBy(M1, t) -> HaltBy(M0, L(t)).
```

A separate general clock proof gives the weaker explicit bound `P(t) = 9*t*t + 707*t + 58620`; the factor-two bound follows by comparing all aligned affine duration vectors. Consequently, using the revised AX11H written calibration supplied in the repository,

```text
iPRA proves Con(PA) <-> not Halt_blank(PA194GS).
```

The exact consistency predicate is the inherited `nativePAConsistency`, the negation of `nativePARefutation`, at Foundation dependency `32e1a0956a8622fad067328ca1959729a7634428`. No consistency assumption is made in this equivalence.

The absolute PA calibration is an explicit inherited mathematical dependency, retained under `reference/calibration_AX11H/`. This package supplies a new relative implementation argument and its own literal certificates. It does **not** supply a new end-to-end Lean kernel proof or independently reimplement the entire PA proof compiler. The report distinguishes ordinary mathematical proofs, executable finite bindings, and the repository's still-open formal endpoint.

## Machine conventions

- One head and one two-way infinite tape; alphabet `{0,1}`.
- All cells initially zero, head initially at coordinate zero.
- Dense working controls `0..193`, start `0`, separate halt label `194`.
- Exactly 388 rows; every row writes one bit and moves one cell left or right.
- No externally prepared register file or initial data.
- Native labels use start `74`, source boundary `84`, halt `254`; `labels.json` binds the labelings.

The canonical table is `machine/machine.tm`. Each row is

```text
current_state read_bit write_bit L_or_R next_state
```

| Object | SHA-256 |
|---|---|
| New dense table | `64ac4ba569b770688a39a1545d5536ad631d15dbb756a0584a8956a83943b3a8` |
| New native table | `adef88c26ecaa0ab570e10a915fdf2e22a7c0b546fdac9deb1be9427350e60ee` |
| Calibrated AX11H parent | `c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a` |

## The design change

The old AX grammar treats `node150 = (node146,node149)` as one fixed macro. Expose its two existing entries and change the guarded tail from

```text
((U,V),Push)  ->  (U,(V,Push)).
```

The old codes `U=00`, `V=01`, `Push=1` become `U=0`, `V=10`, `Push=11`. Fixed selector `221` disappears and reader `2067` is added. The allocation is **133 fixed + 68 reader − 7 contextual folds = 194**. Six native row addresses change: two disappear, two are edited, and two are added.

Both guard comparisons remain. Every one of the 3,671 resolved source instructions, including all targets, is identical to AX11H. Exactly 49 instruction addresses change: 12 shorten, 18 change bits at equal length, and 19 lengthen. This changes the actual decoder interface and recurring tape addresses. It is not a control relabeling or an inserted delay.

## Verification completed

- Deterministic reconstruction and byte comparison of ten core output files.
- Independent tree expansion and source resolution with no builder/compiler imports.
- All 28 simultaneous local fold cases.
- Dense/native literal conjugacy and all 194 controls graph-reachable from start.
- All **4,778** universal source outcomes, over arbitrary natural registers, nonnegative slack, and arbitrary nonempty finite spare lists.
- Four generic list-traversal lemmas freshly derived from literal rows; no arithmetic box oracles in the independent verifier.
- **1,101,826** symbolic events, maximum 403 per outcome, minimum live duration constant 3.
- All 4,777 nonhalting padded successors, zero head displacement, zero address overflow, and nonnegative affine durations.
- Exact complete-tape blank startup in **57,922** transitions, at native state 84 with head −2.
- Independent arithmetic review of the common clock bound `57922 + 9*k*k + 689*k`, both polynomial witness maps, and the stronger factor-two bounds from aligned duration vectors.
- Exact structural novelty against **548 spanning 194-state graph classes and two nonspanning diagnostics**.

`verification/release_full.json` records the portable full replay. The written interpretation of symbolic rules by quantifier-free induction is part of the proof; a Python PASS is not presented as a Lean theorem.

## Reproduce

Python 3.10+ and the standard library suffice. Keep assertions enabled; do not use `-O`.

```sh
python3 -B verify_all.py --quick
python3 -B verify_all.py
python3 -B build.py --output rebuild
```

Quick mode rebuilds the machine, checks source identity, all local folds, whole blank startup, saved certificate bindings, affine clocks, and structural novelty. Full mode also regenerates all independent literal contracts and compares their exact bytes. Temporary directories are used so the delivered receipts stay unchanged. The full run took approximately 75 seconds in the delivery environment; machine speed affects that timing.

To regenerate the PDF with an installed TeX distribution:

```sh
make report
```

The build helper can create a temporary LaTeX format/font map if a minimal TeX installation supplies the source packages but has not generated its formats. It does not install packages or access the network. Optional searches require C++17 and have their own scoped READMEs.

## Comparison and unsuccessful strict reductions

The pinned repository commit is `7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`. The census retrieved all 1,166 tracked PA `.tm` files with exact Git-blob checks and recursively inspected six tracked and six incoming ZIPs. It recognized 5,912 table occurrences and 104 named construction classes. The named ledger records mechanisms, provenance and attributed proof strengths.

The recognition boundary is explicit: arbitrary generators, prose-only representations, and all 12,346 direct tracked JSON files were not exhaustively evaluated. Exact novelty is with respect to the documented literal corpus, whose 550 representatives are included. The checker permits every spanning root, state renaming, reflection, global bit exchange and ignored halt-entry write/move. Bit exchange is only a structural comparison, not an all-zero behavior equivalence.

The initial seven exposed-gate searches made 13,446,433 proposals, and seven further family runs made 12,633,111. A final audit discovered that their inherited expanded-copy scorer assigned `node69` to native entry 30 instead of 179 and used a constant fixed-control charge. Those historical nominal scores are explicitly qualified. Apparent 193-state nominees failed literal source contracts. After the entry and reachability pricing were corrected, all **900 saved grammars repriced at 194**. Four corrected H/GDH runs made **7,663,786 proposals**, again with no strict-reduction hit. Exact logs, the macro audit, and the rejected candidates are under `research/gate_search/`. The validated PA194GS table does not expand copy H and is unaffected.

Physical and history-fold screens also returned no accepted strict reduction. Their scopes, time budgets, completed finite closures and nonexhaustive closures are stated in the relevant receipts.

A concrete 193-state shortened-scanner nominee is retained in `research/rejected_scanner193/`. It fails the physical zero-decrement contract at source site 50 and is not a consistency-machine result. A U/E tag swap is a sound alternative numerical presentation. Its historical matching price was 199, but exact simultaneous-fold repricing gives 202 controls and no full physical/startup certificate; it is not a successful ≤194 construction. No negative result is a universal lower bound.

## Package map

| Path | Contents |
|---|---|
| `report/` | Main LaTeX/PDF, generated transition table and full 104-name ledger, supplementary proof fragments. |
| `machine/` | Exact dense/native table, unfolded new table, source, folds and independent literal contracts. |
| `verification/` | Portable source/startup/runtime/clock/novelty checkers and receipts. |
| `reference/AX11H/` | Exact parent table, source, and inherited independent contracts. |
| `reference/calibration_AX11H/` | Ten inherited written calibration proofs, manifests and README. |
| `comparison/` | Census records, named ledger, graph identities and all 550 comparison representatives. |
| `research/` | Bounded reduction searches, failed 193 nominee, numerical recoding, and exploratory notes. |
| `vendor/`, `licenses/` | Attributed inherited helpers and original license texts. |
| `PROVENANCE.json`, `NOTICE.md`, `SHA256SUMS` | Credit, dependency boundaries, and release-file checksums. |

The supplementary `report/gate_relative_proof.tex` uses the alternative convention `d(H)=1`; the main paper uses stopped durations `D(H)=0`. Both are valid, but their lower-clock invariants must not be mixed. Only the main convention is used in `report.pdf`.
