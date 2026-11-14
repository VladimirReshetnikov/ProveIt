# PA194N: a new 194-state PA consistency machine

**Result:** a materially different, fully specified **194-working-state**, binary,
one-tape, blank-start machine. No verified machine with fewer than 194 states
was obtained. The report gives the ordinary mathematical argument

    PA proves: not Halt(PA194N, blank) if and only if Con(PA).

The numerical-calculus/PA calibration is explicitly inherited. This release
provides the new ten-entry proof-to-command compiler, exact source change,
literal construction, two universal physical checks, complete blank seed,
and a comparison against the supplied corpus. It does **not** claim a newly
kernel-checked Lean/Rocq or iPRA endpoint.

## Read first

- `report/pa194N_conpa.pdf`: report, construction, proof, comparison, exact table and archive ledger.
- `report/pa194N_conpa.tex`: editable LaTeX source, with all included fragments alongside it.
- `construction/machine/pa194N.tm`: definitive dense transition table.
- `RESULTS.json`: exact machine identities and verification scopes.

The tape is two-way infinite, initially zero everywhere. The head starts at
coordinate zero in state 0. Working states are 0 through 193; 194 is the
separate terminal label. Every transition writes a bit and moves L or R.
There are 388 rows. The dense table SHA-256 is:

```
37f7e909724cab7fd667db28f89b9c81653d2576c033750e783b40b3289c04f9
```

## What changes

The primary PA194 native row `(164,1)` changes from `1 R 98` to `1 R 114`.
This bypasses a 19-instruction dummy-zero push after successful modus ponens.
The axiom source and seven decoder folds stay fixed. The count is
`134 fixed controls + 67 AX readers - 7 folds = 194`.

For a store `(t,w,d,h)` and MP parameter `x`, put `b=d+x`. On success,
`I(t,b)=h`, PA194N returns `(b,w,b,0)`. The original controller returns
`(b,[0;w],b,0)`, while the cached PA194C controller returns `(0,w,0,b)`.
PA194N retains the original Shift test `t+h=1`.

A useful exact identity is `MP(0)(t,w,0,h) = (0,w,0,0)` for arbitrary `t,w,h`.
Thus one command implements Discard. The proof compiler is adjusted to the
nine generated AX heads plus the saved old top; it supplies a reserved zero
below MP premises and removes it explicitly. Cantor zero-stack collapse,
the implication-code-zero alias, early halts, and arbitrary carried stores
are all addressed.

The general no-push idea appeared in earlier 196-state PA and 216-state ZFC
work. The new result is its certified 194-state composition and the exact
proof interface here. The literal graph differs from all 8 prior 194-state
classes, including supplementary and rejected tables, even under state
renaming, arbitrary graph-reaching roots, reflection and symbol complement.

## Verification

| Quantity | Result |
|---|---:|
| Working states / rows | 194 / 388 |
| Primitive source sites / outcomes | 3,654 / 4,755 |
| Construction symbolic steps | 1,473,292 |
| Independent symbolic steps | 1,073,769 |
| Independent maximum per outcome | 397 |
| Minimum physical-duration constant | 3 |
| Exact blank initialization | 58,154 transitions |

These are universal symbolic checks of arbitrary natural register values,
both decrement outcomes, an arbitrary nonempty spare list and affine gap.
The independent checker rederives four generic list lemmas from literal
rows and uses two independent source-graph resolvers. The startup checks
compare the complete tape. Finite simulation is not used as evidence for
infinite nonhalting.

## Reproduce the accepted result

Python 3.10+ and its standard library suffice. No network, external checkout,
solver, proof assistant, or heuristic search is needed. Keep assertions enabled.
From any current directory:

```sh
python3 -B /absolute/path/to/pa194N_conpa_2026-11-13/verify_all.py
```

The default command verifies integrity and bindings, command identities,
exact graph novelty, the construction with all physical contracts, and the
independent literal-tape replay. It writes evidence into a new temporary
directory and leaves this packet unchanged. Full replay can take several
minutes. Use `--work /new/nonexistent/directory` to select the evidence path.

```sh
python3 -B verify_all.py --quick
```

Quick mode checks integrity, bindings, command identities and graph novelty;
it **omits** the two universal physical replays. Existing recorded receipts
are not presented as newly rerun physical checks.

To compile the report with a standard TeX Live installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa194N_conpa.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194N_conpa.tex
```

Rebuilding the PDF may change metadata and invalidate its original manifest
entry. Preserve the supplied release before modifying or rebuilding it.

## Comparison and research

The snapshot is `VladimirReshetnikov/ProveIt@17f92105e2bc4317feae6c219cb2143437b482ff`.
The audit covers 36 extracted packets and 26 incoming ZIPs (21 overlap), hence
41 top-level packets. It scans nested archives and distinguishes supported,
supplementary and rejected tables. The exact numeric-table census recognizes
4,417 occurrences, 620 byte identities, and 446 root-free graph classes.
Counts describe this parser and snapshot; they are not state lower bounds.

`comparison/packet_ledger.csv` identifies every packet contribution.
`comparison/frontier194.csv` distinguishes all prior 194-state graph classes.
`comparison/census/` records every recognized byte identity and source locator,
and retains literal tables with at most 196 states, permitting the 194-state
novelty check without the full repository. To repeat
the entire census, provide the pinned checkout:

```sh
python3 comparison/audit_census.py --repo /path/to/pinned/ProveIt --output /new/census
```

`research/decoder/` records deeper macro expansion and broader contextual
fold searches. `research/physical/` records local contractions, a new
incoming-edge bypass operator, and exact negative bounds. None supplies a
193-state theorem; their heuristic failures do not imply minimality.
The accepted theorem does not depend on replaying any discovery search.

## Files, ancestry, and licenses

- `construction/`: deterministic builder, source map, input pins, original-register references and exact machine.
- `verification/independent/`: separate literal-tape checker and all recorded derivations.
- `construction/mathematics/`: executable free-term command checks.
- `mathematics/`: full new proof and independent mathematical review.
- `references/logical/`: unchanged inherited PA-calibration sources.
- `comparison/`: complete ledger, parser, literal census and exact novelty check.
- `research/`: optional discovery material with its separate evidence limits.
- `licenses/`: retained upstream notices; local reference directories retain additional notices.
- `MANIFEST.json`: SHA-256 of every release file except the manifest itself.

The repository's proof-assistant work, James Chang's compiler and numerical
source, and inherited symbolic engines retain their supplied attribution.
No external repository changes were published.
