# PA194 frontier audit and two new 194-state designs

Snapshot: VladimirReshetnikov/ProveIt commit
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2`.

## Result and exact proof status

The report constructs **PA194AX11G** and **PA194GH**, two new deterministic,
binary, one-tape, blank-start machines with **194 working states**, 388
transition rows, initial state 0 and separate halt label 194. Both have exact
source bindings, complete symbolic physical checks, whole-tape blank startup
certificates, and command-level refutation-search proofs. Both are new against
all 94 recognized 194-state graphs in the pinned repository, even under control
renaming, every spanning root, reflection, bit exchange and ignored terminal
write/move effects.

**No accepted sub-194 machine was obtained. No new unconditional iPRA
consistency equivalence is claimed.** The pinned repository itself leaves the
literal PA194 machine's two machine-specific iPRA reductions open. The new
constructions preserve the numerical calculus at the level of the displayed
command and physical interfaces and retain an explicit conditional arithmetic
calibration. The report carefully separates those results from the inherited
ordinary PA calibration and the unfinished internal iPRA endpoint.

| Quantity | PA194AX11G | PA194GH |
|---|---:|---:|
| Working states | 194 | 194 |
| Raw fixed controls + readers - folds | 134 + 67 - 7 | 134 + 67 - 7 |
| Primitive source sites | 3,672 | 3,653 |
| Universal branch-sensitive outcomes | 4,779 | 4,754 |
| Independent symbolic operations | 1,083,079 | 1,102,232 |
| Exact blank startup transitions | 58,154 | 57,922 |

The independent verifier derives four register-list lemmas from the literal
rows and uses two independent source resolvers. Its domain includes arbitrary
natural primary registers, both decrement branches, arbitrary nonempty finite
spare lists, arbitrary extra nonnegative gap and complete blank exteriors.
These are symbolic checks, not bounded register-value sampling, and are not
new Lean/Rocq kernel theorems.

## What changes mathematically

AX11G uses the explicit AX operand `c` to bind the saved generalization
`U(c,h)`. Its final AX push saves the guarded top, so the command generates
eleven stack entries including the old top and consumes a fourth operand `z`.
For all stores, its result is `(0,[q0,...,q9,t;w],z,0)`. The proof compiler
chooses `z=0`, while soundness covers every `z`. The combined generalization
word is `Push; Shift; AX(i,0,0,0); Shift^11` and needs no offset-setting command.

GH retains G's original three-field AX and combines it with cached-only Shift:
halting is tested at `h=1`. The corresponding `Pop` word halts exactly when the
visible top is one. Consequently the refutation compiler finishes with `Pop`;
finishing with a single Shift would be incorrect. Its generalization word is
`Push; Shift; AX(i,0,0); Shift^10`.

## Package contents

- `report/pa194_frontier_report.pdf`: complete typeset report, including both
  full transition tables and an index of all 94 historical frontier graphs.
- `report/main.tex` and its included `.tex` files: complete editable LaTeX.
- `machines/AX11G/` and `machines/GH/`: complete machines, builders, source
  graphs, proofs, independent physical checks, command checks, licenses and
  frozen verification receipts.
- `comparison/`: all 82 packet records, all 94 frontier records, full recognized
  table census, exact reference graphs, scanner and offline novelty comparator.
- `search/offset/`: fresh displaced-control merger synthesis on eight machines,
  with exact contexts, inputs and replay code.
- `search/startup/`: extended and corrected Runtime193 startup repair searches,
  including the nine-start first-write reduction and detector controls.
- `search/tags/`: new formula-tag searches, two completed shared-substring MILP
  runs, feasible dictionary verifiers, and the register reuse analysis.
- `proof_status/`: pinned repository status documents and independent audits.
- `RESULTS.json`: concise machine and evidence metadata.
- `SHA256SUMS`: integrity hashes for the final package.

## Reproduce the main constructions

Python 3.10+ and its standard library suffice. Run without `-O` and without
`PYTHONOPTIMIZE`. From the package root:

```sh
python3 -B verify.py --output /tmp/pa194-replay
```

This rebuilds both candidates, replays their physical and command checks,
checks their frozen artifact identities, compares them against the entire
pinned frontier, and verifies both MILP dictionary expansions. Fresh output
goes to the requested directory. It does not compile Lean or prove the missing
absolute iPRA calibration.

The individual candidate READMEs give separate construction and verification
commands. `comparison/check_frontier_novelty.py` accepts one or more candidate
tables and compares complete canonical tuples offline. Repeating the entire
repository census requires a checkout of the pinned Git commit; the complete
already collected census and all frontier representatives are included.

## Optional searches

The offset search needs a C++17 compiler:

```sh
python3 search/offset/replay.py --family all --output /tmp/pa194-offset
```

It regenerates symbolic contexts, repeats the searches, and compares exact
integer counters and candidate outputs with the recorded observations.
Elapsed times are intentionally excluded from comparisons. The startup and
tag folders provide their own replay commands and describe all limits.

For the two tag dictionaries, verification of the feasible result needs only
the standard library:

```sh
python3 search/tags/milp/verify_dictionaries.py
```

Optional MILP discovery requires NumPy and SciPy/HiGHS. Solver-reported
optimality in a dictionary objective is not a lower bound on Turing machines.
The time-limited anneals likewise do not prove that a better design cannot
exist. New research results distinguish certified outward rays, explicit
finite halts, and unresolved finite-limit exits.

## Rebuild the PDF

With a standard TeX Live installation:

```sh
cd report
python3 generate_tables.py
pdflatex -interaction=nonstopmode -halt-on-error -jobname=pa194_frontier_report main.tex
pdflatex -interaction=nonstopmode -halt-on-error -jobname=pa194_frontier_report main.tex
```

The generated table includes are already provided; the Python step is optional.
Bibliography URLs and all census records are pinned to the same repository
commit. Imported work and licenses are preserved and attributed in the
candidate and comparison directories.
