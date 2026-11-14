# PA consistency machines: comparison and new 194-state designs

**The requested result is not fully established.** This release does not
claim a machine below 194 states with the requested property, or a new
unconditional proof in iPRA of the PA-consistency equivalence.

It supplies two new, fully specified 194-state binary blank-start
implementations, independently replayed source/tape certificates, a new
command-level weak-arithmetic proof, an exhaustive recognized-table
comparison of the specified corpus, and an exact obstruction for a
particular 193-state bootstrap family. The distinction between these
results and the missing absolute arithmetic calibration is explicit in
`STATUS.json` and the report.

Read **`report.pdf`**. The editable source is **`report.tex`**, with included
fragments in `proof/`, `generated/`, `comparison/`, and `research/Runtime193/`.

## New literal machines

| Machine | Complete table | New behavior | Initialization |
|---|---|---|---:|
| AX11QH5 | `ax11qh5/AX11QH5/machine.tm` | Eleven-entry AX, four encoded operands, exchanged quantifier premises, coefficient-five formulas, no-push MP, cache-only Shift | 58,088 steps |
| PA194HX | `hx194/machine/pa194hx.tm` | Primary PA194 source with physical H/X register blocks exchanged | 56,134 steps |

Both have 194 working states, 388 rows, dense start 0, separate terminal
label 194, a two-way tape with alphabet `{0,1}`, an initially all-zero tape,
and initial head position zero. A row is `state read write L_or_R next`.
The halt label is excluded from the state count. Native tables and exact
dense/native label maps are also supplied.

Exact dense-table SHA-256:

```
AX11QH5  f7f52501055ff4fe47aab51acc6536adf3823afca4016a670c67b2c592ed4b02
PA194HX  3242a613d328d17c979ce3675a154733ea16a1949b4391cb824711b5aa46399a
```

## What is established here

AX11QH5's construction and independent literal checkers pass all **4,839**
source outcomes over arbitrary register values, a nonempty spare list,
and affine tape padding. PA194HX's independent checker passes **4,780**
such outcomes. Both rederive four generic list lemmas from literal rows
and check the entire blank-start tape, rather than just a control label.

The new AX11QH5 proof gives a paper-level I-Sigma-1 equivalence between its
explicit scheduler halting and refutability of the displayed numerical
calculus D5. Its compiler accounts for the fourth AX operand and uses
**Pop**, not a plain Shift, to detect a visible contradiction at the end.
The proof handles arbitrary carried stores, Cantor's zero-stack alias,
early halts, candidate/continuation encoding, and weak induction through
explicit tracked witnesses.

Both new tables differ from all **82** recognized spanning 194-state
reference classes under arbitrary state renaming, any spanning root,
global reflection, global symbol exchange, and ignored final halt actions.
The comparison uses full canonical tuples. The frontier also contains
one disconnected diagnostic, which cannot be isomorphic to these machines.

For the previously supplied Runtime193 core, a new exact nine-trace proof
shows that **all 9! = 362,880 physical register allocations**, with the
specified selector-only changes and native start 74, enter an outward
infinite ray after at most 93 transitions. The proof does not exclude other
bootstrap edits or other 193-state designs. Fresh pair/triple screens and
decoder searches found no qualifying smaller machine; their explicit
bounds and limited runs are retained.

## What remains open

The current repository itself distinguishes its ordinary PA calibration
manuscripts, standard finite-run results, and modeled-scheduler results
from the final literal-machine iPRA theorem. This release preserves that
distinction.

The new table's absolute endpoint still needs:

1. The uniform internal physical/source simulation in the required weak
   arithmetic, covering nonstandard coded frames and times.
2. The uniform equivalence of D5 refutation and PA refutation, proved in
   I-Sigma-1 or an appropriate PRA presentation.

The generic conservation and intuitionistic transfer are already present
in the repository. The new command proof does not supply those two
machine-specific premises by itself. No new end-to-end kernel theorem
or global state lower bound is claimed.

## Reproduce

Python 3.10+ and the standard library suffice. Keep assertions enabled;
do not use `-O` or set `PYTHONOPTIMIZE`.

```
python3 -B verify_all.py --receipt /tmp/pa194-fresh-verification.json
```

Default mode performs table reconstruction, exact source binding, command
identities, both independent literal symbolic replays, novelty checks,
and the nine exact Runtime193 startup proofs. It runs in temporary copies
and leaves the archive's recorded evidence unchanged. The observed full
run is recorded in `verification_full.json`.

```
python3 -B verify_all.py --quick --receipt /tmp/pa194-quick-verification.json
```

Quick mode skips the construction symbolic replay and the two independent
literal replays. It still reconstructs the tables, checks exact AX11QH5
initialization, source/command bindings, graph novelty, and the exact
obstruction. Its receipt records the omission. Recorded receipts are not
described as freshly rerun checks in quick mode.

The optional research searches require a C++17 compiler and are documented
in their own directories. A successful verifier does not assert the
missing iPRA calibration.

Rebuild the PDF with standard TeX Live:

```
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Corpus and artifacts

The comparison is pinned to ProveIt commit
`1c9524d8bf2e0a27b9a16ff622359927f536e663`: the PA research subtree,
61 placed packets, all 11 incoming archives, nested ZIPs, and recognized
explicit JSON tables. The audit verified 10,171 tracked files against Git
blob identities and inspected 15,220 direct/archive-member payloads.
It recognizes 3,422 complete table occurrences, 752 labeled normalized
tables, and 638 spanning one-halt graph classes. Six nonspanning tables
and incidental JSON fragments are recorded separately.

These counts describe the declared recognizers. They do not assert that
every arbitrary source-language or Lean-only encoding is a literal table.
The full packet ledger and source-level taxonomy cover the designs and
their attributed evidence categories, including rejected experiments.

| Directory/file | Contents |
|---|---|
| `report.tex`, `report.pdf` | Complete article, proofs, both tables, and comparison appendices |
| `ax11qh5/` | New construction, source graph, independent checks, input bindings, receipts |
| `hx194/` | H/X allocation, exact table, independent verifier, proof note |
| `comparison/` | All-packet/table ledgers, 193–196 representatives, novelty and rescan scripts |
| `proof/` | New command proof, proof-status audit, independent command-review receipt |
| `research/AX11QH5_grammar/` | New bounded grammar search and its actual log |
| `research/Runtime193/` | Exact allocation obstruction and fresh bounded pair/triple searches |
| `references/logical/` | Historical calibration dependencies, with explicit scope notice |
| `licenses/` and nested notices | Attribution and upstream license terms |
| `MANIFEST.json` | SHA-256 integrity manifest of all release files except itself |
| `STATUS.json` | Machine-readable limits of the result |

The full comparison can be rescanned from a pinned Git repository using
`comparison/audit_repository.py --repo PATH --output PATH`; read its
command help for exact options. It can read Git blobs without checking out
the entire large tree. No GitHub changes were published by this task.

Historical files retain their original terminology. The root report and
`STATUS.json` govern this release's claims. Supplied algorithms and
mathematics remain attributed to their original authors.
