# GC215: command-tag generalization and conditional decoder sharing

This packet constructs a new deterministic binary Turing machine with **215 working states and 430 transition rows**, including blank-tape initialization. It uses one two-way infinite tape, symbols 0 and 1, and L/R moves. The halt state is separate and excluded from the count.

The ordinary mathematical argument, using the pinned ProveIt numerical-calculus calibration, establishes

```text
ZFC proves: not Halt(GC215, blank) <-> Con(ZFC).
```

**This is a materially different 215-state candidate; a 214-state construction was not obtained.** The generator now uses its command tag as the generalization binder. A new conditional decoder merge pays for the additional source role. This packet supplies a fresh arbitrary-natural primitive-runtime proof and a complete blank-start connection. It does not claim a new compiled Lean/Rocq endpoint, an internal PA proof, unconditional nonhalting, or a minimum-state result.

## Main artifacts

- `report/report.tex`, `report/report.pdf`: 19-page paper, proof boundaries, research findings, and complete dense transition table.
- `machine/gc215.tm`: dense labels 0–214, start 0, halt 215, dispatcher 81.
- `machine/gc215.native.tm`: diagnostic native labels, start 0, halt 254, dispatcher 84.
- `machine/native-to-dense.json`: exact reversible renaming.
- `source/gc215.sites.json`: full 4,732-primitive source; 202 distinct subtrees.
- `source/table_recipe.json`: deterministic table construction, with no optimizer needed for replay.
- `evidence/`: exact source, runtime, merge and blank-start records.
- `proofs/`: logical/compiler arguments and researched alternatives.
- `research/`: independently checked logical certificates and explicitly scoped experiments.
- `reference/`: pinned immediate inputs, inherited logical certificate and comparison corpus.

## What changes

The predecessor's axiom generator emits `Q_U(oldH)`, with `U` the incoming arithmetic counter. GC215 emits `Q_C(oldH)`, with `C` the decoded AX command tag. Every other emitted row and the full gated set-theoretic bundle are unchanged. The compiled generalization block consequently omits the counter-loading command `J(i)`.

Only two register operands in the ordered primitive source change: ordinal 44 changes `CD4` to `CD3`, and ordinal 49 changes `CI4` to `CI3`. All source addresses and control-flow targets remain unchanged. The source gains one shared decoder role. A physical merge of native roles 129 and 310 recovers that state by reading an origin marker in the preceding tape cell through existing helper 216.

## Verified results

| Obligation | Result |
|---|---|
| Working states / rows | 215 / 430 |
| Source leaves / distinct subtrees | 4,732 / 202 |
| Complete guarded primitive cases | 6,151 |
| Symbolic proof rules | 1,617,679 |
| Runtime row coverage | All 430 rows |
| Minimum duration constant | 5 |
| Exact blank prefix | 68,710 transitions |
| Blank checkpoint | Native state 84, head −2, header 62, gap 0 |
| Logical registers at checkpoint | `[1,0,0,0,0,0,0,18,0]` |
| Spare blocks / one cells | 63 zero-valued spares / 100 one cells |

The runtime domain is arbitrary natural primary registers, arbitrary natural gap, arbitrary nonempty finite spare list, and the complete zero exterior. Its checker applies literal transitions, unary induction, and finite-list induction. A fresh packaged replay passed in 222.43 seconds; the full result is in `evidence/portable_full_replay.json`. This is stronger than bounded sample execution; it remains an ordinary executable mathematical proof system rather than a proof-assistant kernel.

## Offline reproduction

Python 3 with its standard library is sufficient. Assertions must be enabled.

```sh
python3 verify.py
python3 verify.py --runtime
```

The first command reconstructs the tables, audits the source and decoder merge, replays all 68,710 blank transitions, checks the logical certificates and graph comparison, and audits saved runtime metadata. Two independently implemented startup readers are used, including a separate native/dense bytearray simulator. The second command additionally rederives every universal primitive case and compares it with the delivered case record. It usually takes several minutes. Outputs go to a temporary directory, or to a directory supplied with `--work`.

To rebuild the PDF:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The optional bounded search scripts and exact radius-five invariant audits are in `research/physical-search/`. Their README gives separate replay commands; no C++ compiler is needed by `verify.py`. The research source-cost audit runs automatically and independently recomputes costs for 18 delivered source files.

## New formalism result

The packet also proves that the sixth numerical axiom `(exists_i Q_i A) -> A` may be restricted to matrix codes `A > i`, or more generally `A > g(i)` for a specified total primitive-recursive cutoff. The restricted calculus derives exactly the same raw natural codes as the original. The explicit certificate has 107 proof nodes and 124 term nodes and is checked by two independent readers. This restriction is a research result toward a smaller generator; **GC215 itself retains the original unrestricted sixth row**.

## Repository pin and attribution

The source snapshot is ProveIt commit `34b63b3b197b0a5f285a229d91bc163fcc42ab93`, including the six current ZIP inputs under `docs/incoming`. The immediate physical/source predecessor is `ST215_Direct_Transfer_2026-10-21.zip`. Its source language, arithmetic macros, direct transfer operation, dominated-rho8 certificate, protected-tail argument, and symbolic proof engine are inherited. `NOTICE.md` and `licenses/` preserve their attribution and proof boundaries.

The new contribution is the command-tag generalization interface and compiler, the exact new source/table allocation and conditional decoder merge, fresh complete verification and integration, the quantifier-padding certificate, and the explicitly identified supplementary investigations. All novelty claims are relative to the pinned comparison corpus, not to every construction in the literature.
