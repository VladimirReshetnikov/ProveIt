# PA194B and PA194G: two new 194-state machines for PA consistency

**No verified machine with fewer than 194 working states was obtained.**
This package supplies two materially different 194-state designs, the
fallback requested in the task, with complete literal tables, ordinary
mathematical proofs, executable certificates, and a comparison of the
supplied collection.

Start with **`report/pa194_report.pdf`**. Its complete LaTeX source is
`report/pa194_report.tex`; all included fragments are in the same directory.
Both full transition tables are printed in the report. The detailed
comparison is also available as `comparison/comparison_narrative.md`, with
JSON and CSV ledgers for every packet and recognized graph class.

## Results

| Property | PA194B | PA194G |
|---|---|---|
| Dense table | `machine/pa194B.tm` | `generalizer/machine.tm` |
| Working states / rows | 194 / 388 | 194 / 388 |
| Start / terminal halt | 0 / 194 | 0 / 194 |
| New design | Dedicated history selector in the recurring physical decoder | AX operand controls the binder of its saved generalization |
| New proof | Exact all-tape halting transfer from primary PA194; each old step expands to 1–5 steps | New all-store command compiler plus checked literal source implementation |
| Primitive source sites | 3,673 | 3,654 |
| Arbitrary-register source outcomes checked | 4,780 | 4,755 |
| Exact blank startup to source frame | 58,242 transitions | 58,154 transitions |
| Short novelty certificate | 22 self loops; every prior graph has 21 | 88 working controls of indegree one; no prior graph has 88 |

Both machines use one two-way infinite tape, alphabet `{0,1}`, blank symbol
zero, initial head coordinate zero, and only left/right moves. Halt label
194 has no outgoing transitions and is **not** one of the 194 working
states. Every row is `state read write direction successor`.

The ordinary arithmetic conclusion for each machine `M` is

    PA proves: not Halt(M, blank) if and only if Con(PA).

The proof composes the new physical/command arguments with the explicitly
retained written PA calibration from the supplied research. **This is not
a new end-to-end Lean, Rocq, or iPRA formalization.** Finite startup runs
and Python receipts are not substituted for the unbounded mathematical
arguments or for that inherited calibration. The report separates each
dependency and explains how the finite proof/trace transformations are
arithmetized in PA.

### Exact dense-table hashes

```text
PA194B  b2bcdb6c3816a1fbade699a79e431e4b530ec341aaf516c911920d43f9995397
PA194G  28bd991a84200351f36c98afac369ab5a555eb8793821ad35555f0aa4a0fdeeb
```

## What changes

PA194B joins native readers 88 and 301, whose immediate predecessor cells
record different history bits, and repurposes 301 as a dedicated selector.
It changes exactly four native transition rows. The small independent
checker audits all incoming edges, 384 ordinary row cases, and four exact
two-cell identities with arbitrary exterior tape. It also reconstructs
the native baseline from the pinned primary dense table and label map.
The arithmetic marker that breaks the earlier Runtime193 startup remains
unchanged. The new selector is exercised 55 times during blank startup.

PA194G changes the saved AX head from `U(d,h)` to `U(c,h)`, where `c` is
the explicit first operand and `h` is the incoming cached theorem. It
retains the existing Q distribution orientation, no-push MP, and sum Shift.
The revised generalization word is

    Push; Shift; AX_{i,0,0}; Shift^10

and needs no offset-setting command. The complete arbitrary-store proof
includes all axiom selectors, total Pop even for top code one, the
reserved-zero MP compiler, zero-pair aliases, the cofinal scheduler
argument, and the soundness annotation. The literal implementation uses
134 fixed controls plus 67 readers minus seven compatible contextual folds.

## Reproduce the checks

Python 3.10+ and its standard library suffice for construction and
verification. Run without `-O` and without `PYTHONOPTIMIZE`; inherited
symbolic engines use assertions. No network or repository checkout is
needed for these checks.

From this directory, the compact checks are:

```sh
python3 -B verification/check_transfer.py
python3 -B generalizer/check_commands.py
python3 -B comparison/replay/verify_generalizer_novelty.py --candidate generalizer/machine.tm --output verification/generalizer_novelty.json
```

Or run `make verify`. The complete constructors/source checks are:

```sh
python3 -B verify_build.py
python3 -B generalizer/build.py --output verification/generalizer_rebuild
```

Or run `make runtime`. PA194G additionally has a separate literal-tape
checker that derives the register-list induction lemmas from its actual
rows and uses two source resolvers. It can take several minutes:

```sh
cd generalizer
python3 -B independent/check.py . --output independent/replay
```

The observed PASS receipts are already included. The independent G run
checks all 4,755 outcomes in 1,078,742 symbolic steps, maximum 379. Symbolic
iteration counts are not bounds on concrete arbitrary-register runtimes.
The four list lemmas are inductive, not samples of small register values.

For the report, a normal TeX Live installation with pdfLaTeX, Latin Modern,
AMS packages, microtype, longtable, enumitem, fancyhdr and hyperref suffices:

```sh
make tables
make pdf
```

Verify `SHA256SUMS` before regenerating outputs if checking release
integrity. Regenerated receipt metadata or PDF dates can change even when
the substantive content is the same.

## Comparison scope and failed reductions

All repository comparisons are pinned to commit
`4be5c6e3a10292a7466f5d3687e3b39615ff049b` of
`https://github.com/VladimirReshetnikov/ProveIt`.

The audit covers all 61 filed packets and 11 current incoming archives.
It recognizes 3,422 literal/explicit-JSON table occurrences, 752 normalized
identities and 638 spanning graph classes, including 82 at 194 states and
53 rejected or uncalibrated classes at 193. The historical catalogue's 535
entries were separately rechecked. These are inventory counts, not claims
that every listed graph has a proved PA calibration. Arbitrary generators
and prose/Lean encodings are outside the table recognizers' scope.

The two new graphs differ from each other and from every one of the 82
prior 194-state graphs, even allowing state renaming, any spanning root,
reflection, global symbol exchange, and ignored actions on terminal edges.
Both simple invariant checks and exact canonical comparisons are included.

A fresh replay of every possible start in the 52 prior runtime193
experiment graphs resolves all 10,036 runs in at most 117 transitions:
106 halt and 9,930 enter certified outward rays. There are no cutoffs.
The other 193-state class is rejected by a logical refutation of its
coefficient-three calculus. None of this is a lower bound for arbitrary
193-state Turing machines.

Optional new searches and exact finite-domain descriptions are in
`research/physical_searches/` and `generalizer/search/`, with the latter
explained in `generalizer/SEARCH.md`. The C++ searches require a C++17
compiler; they are not needed to verify either frozen machine. The
physical searches were replayed and found no additional accepted fold.

## Package map and provenance

- `report/`: complete report source, generated tables, compiled PDF.
- `machine/`: PA194B dense/native tables and label bijection.
- `generalizer/`: complete PA194G source, table, proof and independent checks.
- `verification/`, `verification.json`: B certificate and construction
  outputs, startup accounting, and additional packaged replay receipts.
- `comparison/`: all-packet and all-graph ledgers, full census, novelty
  evidence, independent G command review, and portable audit tools.
- `references/`: inherited logical calibration and current project-status
  sources. `INHERITED_PROVENANCE.json` is an unchanged ancestral record;
  its older snapshot and member paths describe that earlier package.
- `PROVENANCE.json`: current pinned-source mapping, verified against Git
  blobs, including reconstruction of the exact primary native table.
- `vendor/`, `licenses/`: attributed imported compiler/runtime inputs and
  preserved upstream license notices. The new-material notice for this
  delivery is `licenses/NOTICE.PA194B-PA194G.txt`.
- `research/`: optional physical-reduction searches with reproducible logs.
- `RESULTS.json`, `SHA256SUMS`: concise outcome record and release integrity.

No search program or exploratory variant is a claimed sub-194 solution.
The two claimed constructions are exactly the two hashed tables above.
