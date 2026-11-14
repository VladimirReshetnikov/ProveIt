# PA194AX11QH research package

**Result:** a new concrete 194-working-state, binary, single-tape machine; a comparison of the current PA corpus; independently replayable construction certificates; and a written analysis of the weak-arithmetic proof obligations.

**The requested absolute result remains unproved.** This package establishes neither an accepted machine below 194 states nor the statement `iPRA ⊢ NH(PA194AX11QH) ↔ Con(PA)`. The pinned repository explicitly leaves the physical primary PA194 calibration open. A relative argument cannot supply that missing premise. No Lean or Rocq kernel was run for a new endpoint in this research.

The report supplies an ordinary written proof of `iPRA ⊢ Halt(primary PA194) ↔ Halt(PA194AX11QH)` and its nonhalting counterpart, supported by explicit finite certificates. A separate assistant review memo is retained in `proof/REVIEW.md`. This relative result transfers an eventual consistency calibration; it does not establish the calibration premise.

Read **report/report.pdf** for the full account, including the complete transition table, command semantics, numerical calculus, relative proof analysis, all principal comparisons, and unsuccessful reduction searches. The matching complete LaTeX sources are in the same directory.

## Exact machine

| Item | Value |
|---|---|
| Name | PA194AX11QH |
| Alphabet | 0, 1 |
| Tape | One two-way infinite tape, initially all zero |
| Head | Initially at coordinate zero |
| Start state | 0 |
| Working states | 0 through 193 |
| Separate terminal label | 194 |
| Transitions | 388; each writes a bit and moves L or R |
| Dense table | candidate/machine/machine.tm |
| Dense SHA-256 | 19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50 |
| Native start / terminal | 74 / 254 |
| Native SHA-256 | 424bd5175bbca161e76af485f1eda03f2f169d90afe80563035b60289361bf07 |

The new composition combines AX11's eleven-entry, four-parameter axiom command, Q premise exchange, no-push modus ponens, and H's cached-only contradiction guard. Its state count is `134 + 67 - 7 = 194`. The contribution is a distinct recurring command protocol and exact source/table implementation, rather than a renumbered copy. Full canonical tuples find no match among the 82 recognized spanning 194-state graphs, including reflection, symbol exchange, and omission of terminal-edge write/move effects.

## What is included

| Directory or file | Contents |
|---|---|
| report/ | PDF, all TeX inputs, generated comparison/transition tables, table-generation script |
| candidate/ | Rebuildable construction, dense/native/raw tables, source program, local folds, command checks, independent literal interpreter certificates, search sources and logs |
| baseline/ | Fresh independent literal-row replay for the pinned primary PA194 table |
| comparison/ | 72-packet ledger, 40-principal-design comparison, 82-graph frontier, 193-state diagnostics, complete recognized occurrences and portable census/novelty scripts |
| proof/ | Explicit restricted-implication premise-exchange proof DAG, checker, receipt and its exact Lean source input |
| research/runtime/ | Local synthesis sources, context envelope, negative results and independently replayable rejected-startup certificates |
| references/ | Pinned status READMEs and focused unmodified Lean reference sources; not a complete Lean project |
| checks/ | Fresh aggregate replay logs and receipts for the delivered package |
| licenses/ | Retained imported copyright and license notices |
| STATUS.json | Machine-readable result and proof-status boundaries |
| PROVENANCE.json | Source snapshot, artifact origins and audit scope |
| SHA256SUMS | SHA-256 for every shipped file except itself |

## Offline replay

Use Python 3.10 or newer and its standard library. Keep assertions enabled: do not use `-O`, and do not set `PYTHONOPTIMIZE`.

```sh
python3 -B verify_all.py --output fresh_checks
```

This rebuilds and verifies the new construction, independently replays every primitive source outcome and full blank initialization, checks the complete AX and non-AX source bindings, checks the old primary machine with the same literal-row engine, compares full graph canonical forms with the frozen corpus, checks the 18,897-row restricted-implication proof, and replays every finite prefix underlying the rejected 193-state core classification. It checks the manifest when present. Output goes to the specified directory; use a new directory to preserve the recorded receipts.

The complete replay is computationally heavier than checking a few sample runs. It covers arbitrary natural register values and arbitrary finite spare lists through explicit symbolic contracts. These are executable mathematical certificates with a stated trust boundary, not a proof-assistant verification of the full consistency equivalence.

The original corpus scan can be reproduced against a checkout of the exact pinned commit using `comparison/census.py`. See `comparison/README.txt` for the command and supported formats. Parameterized generators, TeX-only tables, JSONL streams, and opaque binary encodings are outside the automatic table recognizer; the packet ledger separately covers the named proposals.

Optional heuristic searches additionally need a C++17 compiler. They are not needed to rebuild or verify the candidate. Their negative outcomes prove no general lower bound.

## Rebuild the report

With a normal TeX Live installation including Latin Modern, AMS packages, microtype, geometry, booktabs, longtable, enumitem, xurl, hyperref, listings and fancyhdr:

```sh
cd report
python3 generate_tables.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Run a third pass if TeX still requests updated table widths or references. The supplied PDF was compiled from these sources and visually reviewed.

## Snapshot and attribution

Source: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/1c9524d8bf2e0a27b9a16ff622359927f536e663), commit `1c9524d8bf2e0a27b9a16ff622359927f536e663`.

The underlying algorithms, imported symbolic engines, historical machines and mechanism names are attributed in the component provenance files. James Chang, Andrew James Wade and ProveIt notices are retained. New work is provided under the included ProveIt MIT terms. The historical evidence classifications do not assert that this research independently reproved every packet's arithmetic claim.
