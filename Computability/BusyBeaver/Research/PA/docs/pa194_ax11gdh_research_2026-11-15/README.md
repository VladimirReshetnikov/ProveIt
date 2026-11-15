# A new PA194 command design and four literal realizations

## Result

No valid machine with fewer than 194 working states was found. This archive delivers the requested fallback: a materially different command design, **PA194AX11GDH**, with four distinct 194-state realizations.

Read **report/pa194_ax11gdh.pdf** for the complete argument, 31-family comparison, reduction experiments and all four full transition tables. Its LaTeX source is included.

All machines use one two-way tape, alphabet `{0,1}`, a zero-blank initial tape, initial head coordinate 0 and dense start control 0. Working controls are 0–193; dense control 194 is the halt and is not counted. Each table has 388 rows in the format `state read write L|R next`. All 194 working controls are reachable in the control graph; this does not assert they are all visited by the blank run. Native start/halt labels are 74/254, with a bijection in `labels.json`.

| Machine | Dense table | Source sites / outcomes | Startup |
|---|---|---:|---:|
| PA194AX11GDH | `machine/machine.tm` | 3,671 / 4,778 | 57,922 |
| PA194AX11GDHS | `companions/HS/machine/machine.tm` | 3,668 / 4,774 | 57,768 |
| PA194AX11GDHF | `companions/F/machine/machine.tm` | 3,671 / 4,778 | 57,870 |
| PA194AX11GDHR | `companions/R/PA194AX11GDHR/machine.tm` | 3,671 / 4,778 | 58,022 |

Startup counts transitions to the complete canonical source frame, not a halting time.

## New semantics and mathematical status

AX11GDH combines the diagonal `Gamma(d+x)`, explicit generalization binder `U(c,h)` using the raw cache, ordinary distribution, eleven protected entries, a genuine fourth operand `z`, visible no-push MP and cached-only halting. Relative to incoming GDH, native row 2068/read 1 changes from `0 L 302` to `1 R 19`: the recurring AX return becomes Push followed by the full MP operand reader. H costs 134 fixed+69 readers−9 folds=194; HS costs 135+69−10=194.

The new written proof supplies exact AX equations, selectors, Push/Pop, generalization, MP, an all-store refutation compiler, fair scheduling, syntactic soundness and primitive-recursive positive clocks. With the **updated AX11H written iPRA calibration**, it obtains for each machine:

**iPRA proves: Con(PA) iff the zero-blank machine does not halt.**

That inherited calibration is explicitly identified; its ten written sources are under `references/AX11H_written_sources/`. This package does not reconstruct every inherited fixed proof leaf or complete the Lean development. Python checks bind exact artifacts and establish finite/symbolic proof premises; they are not an end-to-end proof-assistant theorem about PA. The mathematical proof and scope of the inherited review are in `proof/` and the PDF.

F applies the earlier AX11GH/GHS two-shortcut method to H: parent halting by t implies F halting by t, and F halting by t implies parent halting by 3t. R replaces unsafe runtime-only history sharing with a dedicated helper: parent halting by t implies R halting by 5t, and R halting by t implies parent halting by t. Their proofs use explicit primitive-recursive clocks and quantifier-free induction.

## Offline verification

Python 3 and the standard library suffice. Keep assertions enabled; do not use `python -O`.

```sh
python3 -B verify_all.py --full --jobs 2
```

This reconstructs all four tables, repeats H/HS source bindings, replays all four independent physical audits, and checks exact graph novelty against 521 reference classes and all six new-machine pairs. `--jobs` accepts 1–4. Without `--full`, recorded physical contracts are bound to the exact artifacts instead of rerunning their symbolic executions. The delivered full-run receipt is `verification/full_package_replay.json`.

The independent contracts cover nine arbitrary natural primary registers, header distance 48+g for arbitrary g≥0, an arbitrary nonempty finite spare list and both branches of every decrement. Four list lemmas are derived from literal rows without arithmetic-box oracles. All durations have positive constant at least 3. Startup checks compare the whole tape, including its blank exterior.

Individual builds:

```sh
python3 -B build.py --output /tmp/PA194AX11GDH
python3 -B companions/HS/build.py --output /tmp/PA194AX11GDHS
python3 -B build_fast.py --parent machine --output /tmp/PA194AX11GDHF
python3 -B companions/R/build_helper.py --output /tmp/PA194AX11GDHR
```

## Corpus and reduction research

Pinned repository snapshot: `793c68737d94bffa4e32a75bce6cc8058d6d22f0`.

`comparison/` covers all 93 filed deliveries and 4 current incoming archives, grouped into 31 mechanism families. It records 83 named principal/supplementary graph classes and 521 total 194-control classes: 520 spanning and 1 disconnected diagnostic. Rejected and auxiliary tables are explicitly classified; these are not 521 consistency theorems. The filed catalog is an attributed census; incoming direct/nested archives and explicit JSON tables were reparsed. All 521 representative tables are included.

The exact novelty screen permits arbitrary control renaming, any spanning root, reflection, global symbol exchange and ignored terminal-edge actions. Symbol exchange is structural only, not a zero-blank semantic equivalence. No worldwide novelty claim is made.

`research/grammar_search/` and `research/exchanged_heads/` retain completed grammar investigations. `research/core_reductions/` contains protected-row, local-acceleration and runtime193 bootstrap searches, plus a concrete scanner counterexample. `research/header_span/` proves universal local contracts at header distance 38 for the unchanged inherited 193-state runtime. It still has no validated blank initialization and is not a sub-194 consistency machine. Each experiment records its bounds and inconclusive outcomes; no negative search is a state-count lower bound. Optional searches require a C++17 compiler.

## PDF and integrity

From the archive root, with a normal LaTeX installation:

```sh
python3 report/generate_tables.py
pdflatex -interaction=nonstopmode -halt-on-error -output-directory report report/pa194_ax11gdh.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory report report/pa194_ax11gdh.tex
```

Dependencies are standard LaTeX, Latin Modern, AMS packages, geometry, booktabs, longtable, array, xcolor, microtype, fancyhdr, hyperref and xurl. `SHA256SUMS` covers every delivered file except itself:

```sh
sha256sum -c SHA256SUMS
```

See `NOTICE.md`, `licenses/`, companion notices and research provenance files for inherited authorship and licensing. Numerical-calculus, engine and acceleration techniques retain their upstream credit.
