# PA194ORMP and PA194ORMPLC3

**No justified machine below 194 working states was obtained.** This package
supplies two new 194-state designs, a complete comparison of the pinned
explicit-table corpus, written relative iPRA proofs, reproducible positive
certificates, and the unsuccessful reduction research.

Start with **report/report.pdf**. The complete LaTeX source and generated
appendices are in the same directory.

## Exact positive result

Both machines use one head, one two-way infinite binary tape, blank zero,
and only left/right moves. Every tape cell initially contains zero; the
head starts at coordinate zero. Working states are 0 through 193, initial
state is 0, and the distinct halt label is 194, excluded from the count.

| Quantity | PA194ORMP | PA194ORMPLC3 |
|---|---:|---:|
| Working states / transition rows | 194 / 388 | 194 / 388 |
| Resolved primitive source instructions | 3,671 | 3,671 |
| Changed source addresses versus revised AX11H | 154 | 449 |
| Universal source outcomes | 4,778 | 4,778 |
| Complete blank initialization transitions | 58,014 | 58,010 |
| Independent symbolic events | 1,101,819 | 1,100,304 |

The top-level tables PA194ORMP.tm and PA194ORMPLC3.tm are byte-identical to
their copies in construction/machine/ and construction/accelerated/.
Each row is: current_state read_bit write_bit L_or_R next_state.

Dense-table SHA-256:

~~~text
PA194ORMP
a0473681d6d5fb68e5fccfc473f35bc67aa48083d847e349ba3c52865f293629

PA194ORMPLC3
6d8a8cf2f5578ccdc28dd7025bc41a7c279dfbc09c5d3893cb965d70292d10f4
~~~

## What changes

PA194ORMP jointly changes the binary address trees of the operand routine
and the modus-ponens routine, repairing their shared backward-history use.
Its count is 135 fixed controls + 66 AX readers - 7 simultaneous folds.

PA194ORMPLC3 additionally changes the four-increment loop's association,
retags 61 counted continuations from depth two to depth three, changes a
second history selector, and incorporates three runtime shortcuts.
Every resolved instruction and successor still agrees with revised AX11H.

Both tables are new relative to all 548 spanning 194-state graph classes
in the pinned corpus, and distinct from each other, even allowing state
renaming, every possible root, reflection, symbol exchange, and ignored
final write/move decorations. Two nonspanning 194-control diagnostics are
excluded by the spanning invariant. Symbol exchange is used only for
structural comparison; the specified blank remains zero.

The individual OR, MP, LC, selector, and shortcut ideas are inherited and
credited. The new contribution is their exact joint implementation, its
fresh verification, relative proof, corpus reconciliation, and searches.

## Mathematical conclusion and proof boundary

The new written proof establishes in iPRA, for each delivered machine M:

~~~text
Halt_blank(M) <-> Halt_blank(PA194AX11H).
~~~

The direct parent is the exact revised AX11H table with SHA-256
c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a.
Composing with its identified inherited written calibration yields:

~~~text
iPRA proves: Con(PA) <-> not Halt_blank(M).
~~~

Con(PA) denotes the pinned Foundation nativePAConsistency predicate used
by that calibration. This archive binds and retains the imported proof,
and includes an independent review of the relevant interfaces. It does
not claim to complete the repository's end-to-end Lean or Rocq theorem,
or to reimplement the enormous inherited PA proof compiler.

The constructive source-to-physical witness bound is
startup(M) + 9*k^2 + 689*k for k source steps. A physical halt by t
reflects to a source halt by t+1. The common relative witness bound is
60000 + 9*(t+1)^2 + 689*(t+1). The proof handles halting inside segments;
it assumes neither Markov's principle nor that PA is consistent.

## Reproduction

Python 3.10+ and the standard library suffice. Assertions must be enabled.

~~~sh
python3 -B verify.py --output /tmp/pa194_joint_replay
~~~

The full replay checks release hashes; rebuilds both machines; independently
replays all 4,778 source outcomes for each new table and the parent; derives
the four list traversals from literal rows; checks every padded endpoint,
duration premise and premature-halt exclusion; and reruns novelty, incoming
startups, ordinary control-congruence checks, and the supplemental JSON
table inclusion check.

~~~sh
python3 -B verify.py --quick --output /tmp/pa194_joint_quick
~~~

Quick mode skips the complete construction/literal replay and must not be
described as a fresh universal runtime verification. All replay output goes
outside this frozen release.

Optional searches need a C++17 compiler. See the READMEs in research/.
To rebuild the report in a normal TeX installation:

~~~sh
python3 -B report/generate_tables.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
~~~

## Corpus scope

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Snapshot: 7c0bb454cf73c29ca1c385f9fec856ddd236a7cb.

The archive includes the complete 106-delivery ledger, an attributed
104-named-design ledger, thirteen freshly replayed incoming startups,
all 548 spanning 194-state classes, and 61 classes of 193-state research
tables. The final text/JSON/nested-ZIP scan recognizes 7,342 occurrences
and 1,381 normalized labelled identities. These are not counts of
independently proved consistency machines.

Unexecuted generators and prose-only encodings are outside the mechanical
census. Historical claims are attributed, not all independently reproved.
Exact scope, source bindings, the numeric-JSON supplement, and the full
transition index are retained.

## Artifact map

| Location | Contents |
|---|---|
| report/ | Main PDF, LaTeX, printed transitions and comparison appendices |
| PA194ORMP.tm, PA194ORMPLC3.tm | Definitive dense tables |
| construction/ | Portable builders, machines, literal checker, parent, clocks, proof, licenses |
| comparison/ | Complete ledgers, graph index, novelty, startup and congruence checks |
| review/ | Independent calibration/architecture review, TeX and PDF |
| research/ | Quotient and initializer searches, sources, inputs, receipts, bounds |
| verification/ | Release-level portable replay receipts |
| STATUS.json | Achieved/unachieved goals and proof boundaries |
| MANIFEST.sha256.json | Every release file's hash except the manifest itself |

The exact inherited calibration archive is construction/calibration_AX11H.zip,
SHA-256 93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075.
Original ProveIt, James Chang, and Wade notices remain in the license
directories. This delivery makes no modification to the upstream repository.
