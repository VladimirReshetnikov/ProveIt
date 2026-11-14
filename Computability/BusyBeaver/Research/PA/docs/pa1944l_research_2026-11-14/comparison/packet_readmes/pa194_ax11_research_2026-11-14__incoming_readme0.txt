# PA194AX11: a new 194-state consistency machine

This research packet supplies **PA194AX11**, a materially different 194-state Turing machine whose blank-tape nonhalting is provably equivalent in ordinary Peano arithmetic to `Con(PA)`. It also supplies **PA194QH5**, a second new 194-state composition, a comparison of all 66 pinned PA research deliveries, complete transition tables, mathematical proofs, reconstruction programs, and executable source/tape certificates. **No verified machine with fewer than 194 working states was obtained.**

Read [report/main.pdf](report/main.pdf) for the complete report, proofs, both transition tables, and comparison appendices. Its source is [report/main.tex](report/main.tex). The shorter corpus analysis is [comparison/design_comparison.md](comparison/design_comparison.md).

## Exact claim and machine conventions

For each delivered machine `M`, the ordinary mathematical argument establishes

```text
PA proves:  not Halt_blank(M)  <->  Con(PA).
```

The argument combines the identified inherited numerical-calculus calibration with new command compilers, source bindings, universal symbolic tape contracts, and complete blank initialization. It does not assert that PA proves its own consistency or proves either machine nonhalting. Actual nonhalting follows assuming PA is consistent. No newly kernel-checked end-to-end Lean/Rocq theorem or iPRA endpoint is claimed; the included inherited Lean modules are reference material with their import dependencies recorded.

Both dense tables use one two-way infinite tape, alphabet `{0,1}`, an all-zero initial tape, initial head position `0`, and initial state `0`. Working states are `0..193`; terminal label `194` is separate and is **not counted** among the 194 states. There are exactly 388 rows, in the format:

```text
current_state  read_bit  write_bit  L_or_R  next_state
```

There are no outgoing rows for the halt label. Native tables use initial state `74` and halt label `254`; each `machine/labels.json` supplies the exact dense/native relabeling. Native labels are not state counts.

| Machine | Dense table | Change to recurring computation |
|---|---|---|
| **PA194AX11** | [primary/machine/machine.tm](primary/machine/machine.tm) | AX pushes its guard and falls through into MP's parameter reader; MP's former dummy push is removed. The resulting AX stack has eleven entries. |
| **PA194QH5** | [secondary_qh5/machine/machine.tm](secondary_qh5/machine/machine.tm) | Coefficient-five formula coding combined with exchanged quantifier-distribution premises, no-push MP, and cached-head-only Shift. |

SHA-256 of the exact dense table bytes:

```text
PA194AX11  1a7defae031c322a5577a3f2cb77d4c3bbc3242c7246f35f073d4dcf12a191d0
PA194QH5   94c85547b3edd0df0a441d45bf22abb52711f2b27cc9e680999232285757dba5
```

Native table SHA-256:

```text
PA194AX11  d3a05be40a7e0a5b33a0f7fe52ad96f05395fd858049178808a68b52d6d1f129
PA194QH5   45c649af2600c2cfa8bbb07ce2a674e07945d985af6c9fc8aaa8563df1225c05
```

### The fourth AX operand is essential

The new AX command consumes an additional encoded parameter `z` because it enters the **full MP field reader**. For incoming store `(t,w,d,h)`, its effect is

```text
(t,w,d,h) -> (0, [G,Gamma,L6,...,L1,rho,U(d,h),t ; w], z, 0).
```

There are ten generated theorem entries plus the saved old top `t`. The `z` field is real and need not be zero. Soundness covers every `z`; the proof compiler explicitly chooses `z=0`, and the scheduler uses the corrected four-field encoding. PA194AX11 retains the original **sum-based Shift guard**. Its new Pop safely preserves visible code `1`, so the compiled contradiction word ends with a plain Shift. See [proof/ax11_preservation.tex](proof/ax11_preservation.tex), [proof/ax11_commands.py](proof/ax11_commands.py), and the independent review in [comparison/independent_review.md](comparison/independent_review.md).

## Reproduce the verification

Use **Python 3.10 or later, standard library only**, from this archive's root. No network, repository checkout, C++ compiler, or proof-assistant installation is required for the combined verifier. Keep assertions enabled: do not use `python -O`, and unset `PYTHONOPTIMIZE` if it is set.

Full verification is the default:

```sh
python3 -B verify_all.py --receipt fresh_full_verification.json
```

It verifies the pinned input hashes, deterministically reconstructs both tables and source artifacts, checks the source splices and command algebra, runs the construction symbolic checks, **replays both independent literal-tape checkers**, and compares the regenerated receipts and certificates with the delivered evidence. It also repeats exact graph-novelty checks against all 76 old 194-state classes. Successful completion prints `"status": "PASS"`; a failed condition exits with an error. Temporary reconstruction and replay outputs are removed automatically; only the optional `--receipt` destination is retained.

The quicker alternative is:

```sh
python3 -B verify_all.py --quick --receipt fresh_quick_verification.json
```

`--quick` still rebuilds both machines, runs the construction symbolic checks, checks source and command bindings, and repeats novelty checks. It **skips only the two independent physical replays**, checking their delivered full receipts, tables, source files, and certificate hashes instead. Its receipt explicitly records that omission. The integrity manifest [verification_inputs.json](verification_inputs.json) binds the released inputs; it is not itself a proof-assistant theorem. Neither mode runs the optional bounded C++ research searches, rebuilds the full upstream census, or compiles the report.

The released full run passed from an isolated temporary copy, including both independent physical replays and both novelty comparisons. The complete observed result is [verification_full_receipt.json](verification_full_receipt.json); [verification_full.log](verification_full.log) records stage completion.

Recorded independent physical results are:

| Quantity | PA194AX11 | PA194QH5 |
|---|---:|---:|
| Source instruction sites | 3,672 | 3,714 |
| Universal source outcome contracts | 4,779 | 4,815 |
| Literal-row generic list lemmas | 4 | 4 |
| Symbolic operations | 1,078,230 | 1,150,677 |
| Complete blank initialization steps | 58,154 | 58,088 |

The symbolic contracts cover arbitrary natural register values, an arbitrary finite nonempty spare list, and an affine tape gap. These counts describe verification work and initialization, not a bound on the machines' full executions.

## Comparison and unsuccessful reductions

The comparison is pinned to [ProveIt commit 2337ce611a26e308697ccbddb2a1636f989f01c3](https://github.com/VladimirReshetnikov/ProveIt/tree/2337ce611a26e308697ccbddb2a1636f989f01c3): **61 filed PA packets plus five incoming archives**. The literal/explicit-JSON census finds **76 prior 194-state graph classes**, including auxiliaries and rejected designs; this is not a count of 76 established consistency theorems. The ledger distinguishes principal constructions, supplementary constructions, validated rotations, exploratory objects, and failures.

Both new tables are distinct from all 76 classes under state renaming, any spanning initial root, global tape reflection, global symbol complementation, and suppression of the terminal halt-edge action. The comparison uses exact canonical tuples. Scope, recognizer limitations, duplicates, and every recognized occurrence are documented in `comparison/`.

The inherited 193-state candidates fail for different reasons: a coefficient-three calculus is inconsistent, while Runtime193 lacks a suitable blank startup. New bounded pair/triple startup searches and new grammar/scanner experiments also yielded no verified sub-194 machine. Their negative results apply only to their stated pools and bounds; **no 194-state lower bound is claimed**.

## Artifact map

| Location | Contents |
|---|---|
| `report/` | Main TeX/PDF report, mathematical fragments, generated ledgers, complete transition tables |
| `primary/` | PA194AX11 literal tables, pinned inputs, builder, source checker, independent tape checker, receipts, provenance |
| `proof/` | New AX11 proof fragment, exact command checker, scheduler and command receipt |
| `secondary_qh5/` | Complete QH5 construction, proof, verifier, exchange certificate, physical evidence, provenance |
| `comparison/` | All-66 delivery ledger, all-76 frontier, census, table recognizers, novelty receipts, independent review |
| `references/logical/` | Retained mathematical calibration dependencies; historical controller descriptions are superseded by the new proofs |
| `references/lean/` | Unchanged selected Lean modules and local import closure; external `Std` imports are listed |
| `research/startup_repair/` | Bounded Runtime193 pair/triple search, inputs, logs, exact reproduction commands and limitations |
| `primary/research/` | AX11 grammar search and five-way scanner exploration, with separate instructions and results |
| `verification_inputs.json`, `verify_all.py` | Released-input integrity binding and combined offline verifier |

To rescan the original corpus, obtain the pinned repository and run:

```sh
python3 -B comparison/scanner/audit_current.py --repo /path/to/ProveIt --output /tmp/pa-census
```

To rebuild the document with a TeX installation providing the packages in its preamble, run `pdflatex -interaction=nonstopmode -halt-on-error main.tex` twice from `report/`. The supplied PDF is ready to read without TeX.

See [NOTICE.md](NOTICE.md), both `PROVENANCE.json` files, and the preserved `licenses/` directories for upstream sources and license notices.
