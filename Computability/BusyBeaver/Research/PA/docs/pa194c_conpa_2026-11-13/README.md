# PA194C: a cached-head 194-state machine for Con(PA)

**Result:** a materially different 194-state binary, single-tape, blank-start Turing machine. No verified machine below 194 states was obtained in the documented bounded searches.

The ordinary mathematical proof gives

    PA proves: Nonhalting(PA194C, blank tape) iff Con(PA).

The new construction combines the supplied PA194 67-reader/seven-fold decoder with the cached-head Shift/MP controller of supplied 195C. Six native rows change, and the complete 3,649-site source graph equals the supplied 195C graph. Both physical verification implementations pass all 4,749 arbitrary-register outcomes, and the exact whole-tape startup takes 57,922 transitions.

This is an ordinary mathematical PA-calibration result with executable finite and symbolic certificates. **A newly compiled end-to-end Lean or Rocq theorem is not claimed.** The report separates the inherited logical calibration from the newly checked composition.

## Read the report

`report/pa194c_conpa.pdf` contains the construction, comparison, proof, complete transition table, all-34-archive ledger, search limitations, and further research questions. The LaTeX source and its three included files are alongside it.

## Literal machine

- `tables/pa194C.tm`: working states 0 through 193, initial state 0, terminal halt label 194.
- `tables/pa194C.native.tm`: equivalent native labels, initial 74, halt 254.
- `tables/pa194C.labels.json`: dense-to-native conjugacy, including halt.
- `tables/pa194C_raw201.native.tm`: raw parent before the seven folds.

A row is `current_state read_bit write_bit direction next_state`. The alphabet is `{0,1}`; blank is 0; the head begins at 0 on the all-zero two-way infinite tape; every move is L or R. The 194 working states include initialization and exclude the terminal label. There are exactly 388 transitions.

Dense-table SHA-256:

    d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b

Native-table SHA-256:

    b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c

## Reproduce

Python 3.10 or later and the standard library suffice. Keep assertions enabled: do not use `-O` or `PYTHONOPTIMIZE`.

```sh
python3 -B verify_all.py
```

The individual commands are:

```sh
python3 -B construction/build.py
python3 -B verification/check_commands.py
python3 -B verification/check_physical.py
python3 -B verification/check_novelty.py
```

The independent physical checker derives its generic list lemmas from the literal rows and does not import the compiler or its arithmetic-box oracle. It can take several minutes. It writes fresh receipts to a temporary directory; supply `--output PATH` to choose a destination. The builder likewise accepts `--output PATH` for reconstructed tables and fresh receipts.

The physical checks cover nine independent arbitrary natural register values, both decrement outcomes, an arbitrary finite nonempty spare list, and an affine zero gap. They are universal symbolic contracts, not bounded register samples. Symbolic checker step counts are not physical runtime bounds.

```sh
python3 -B comparison/replay_census.py
```

reproduces the incremental comparison offline. It uses the frozen inherited census plus the exact Git delta and both added archives. It does not rerun the original 32-archive census. Recognition is limited to complete numeric binary `.tm`/`.txt` files; arbitrary source/JSON-only encodings require source review. The current inventory contains 34 archives, 2,473 table occurrences, 594 byte forms and 430 root-free graph classes. At 194 there are five byte forms in three classes, including the rejected scanner table. The new graph is different from all three under arbitrary state renaming and global tape reflection.

To compile the report in a normal TeX Live installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa194c_conpa.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194c_conpa.tex
```

## Observed checks

| Check | Result |
|---|---:|
| State count | 134 fixed + 67 raw readers - 7 folds = 194 |
| Source sites / outcomes | 3,649 / 4,749 |
| Construction symbolic steps / maximum | 1,507,397 / 506 |
| Independent symbolic steps / maximum | 1,096,302 / 403 |
| Independent positive-duration constant minimum | 3 |
| Literal-row generic list lemmas | 4 |
| Simultaneous local fold cases / incoming rows | 28 / 23 |
| Whole-tape blank startup | 57,922 |
| Cached ten-entry command algebra cases | 188 |
| Prior 194 graph classes compared | 3 |

## Searches below 194

Four completed compiler searches made 27,851,976 proposals: 9,385,957 for
fixed-word reassociation, 8,955,769 with parameter permutations, 2,615,187
with axiom-head reordering, and 6,895,063 with stricter scanner constraints.
The first three retained the existing best of 60 effective readers with
134 fixed controls. The scanner run's best grammar still violated its
address constraints. These counts are proposals, not distinct machines.

The structural searches include two-sided local convergence, jointly changed
action rows, and attempts to remove scanner control 34. Direct deletion
fails 113 universal outcomes for each of PA194 and PA194C. A source-preserving
rotation and jump retag shorten a recurring address, but all tested one-row
routes and all 698 two-row candidates that preserve the arithmetic interfaces
fail the physical contracts. A further 1,308 candidates alter those interfaces
and remain unverified. None is asserted to be a smaller consistency machine.

`research/compiler/search_summary.json` and `research/structural/RESULTS.json`
give the exact families, parameters, observed counters and limitations.
Interrupted runs report their last recorded counters, not invented final
counts. These are bounded negative results, not a state-count lower bound.

## Package layout

- `construction/`, `source/`, `tables/`: deterministic new construction and exact data.
- `verification/`: independent physical, command and graph checks.
- `evidence/`: observed successful receipts and logs.
- `comparison/`: current census, frontier comparison, all-archive ledger and provenance.
- `research/`: bounded searches and their limitations; no lower-bound claim.
- `reference/pa194/`: frozen, attributed supplied PA194 packet, including its original proof sources and licenses.
- `reference/cached/`: cached-controller proof, command checker, and exact 195C parent data.
- `reference/archives/`: the two new archive inputs required for the incremental census replay.

Existing reports under `reference/` describe their own historical constructions and search dates. The root report and `RESULTS.json` describe the present release. Experimental and rejected tables are retained for audit, not designated as results.

## Provenance

Repository snapshot: `b88235336c63a247852fe8ec7f931d51f953632d`.

Inherited census snapshot: `5ed5a41fa5932433111eea096311364c6087e8e3`.

The new contribution is the verified composition, its literal-table/source binding, its novelty comparison and the documented searches. The numerical calculus, separate-head construction, successful seven-fold decoder and cached controller are credited to the supplied work. James Chang, ProveIt and Wade licenses are preserved in the reference directories. No external repository update is required to reproduce the package.
