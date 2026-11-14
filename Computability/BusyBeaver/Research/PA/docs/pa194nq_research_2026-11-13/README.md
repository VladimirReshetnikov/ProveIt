# PA194NQ: a new 194-state Con(PA) machine

This archive supplies the fallback requested in the research task: an explicit,
materially different **194-working-state**, binary, one-tape Turing machine.
No correct machine with fewer than 194 working states is claimed.

The ordinary mathematical argument in `report/pa194nq.pdf` establishes

    PA proves: not Halt(PA194NQ, blank) if and only if Con(PA).

It uses the identified, retained separate-head numerical-calculus calibration
from the supplied corpus, proves preservation under the new composition, and
connects the source program to the exact literal table. The proof is an
ordinary PA-formalizable argument with executable certificates. It is **not**
a newly compiled end-to-end Lean/Rocq proof or a theorem over iPRA.

## The accepted table

`machine/machine.tm` is the authoritative dense transition table. Every row is

    current_state  read_bit  write_bit  L_or_R  next_state

- Working states: 0 through 193 (194 states).
- Start state: 0. Halt label: 194, excluded from the working-state count.
- Alphabet: {0,1}; blank symbol: 0.
- Tape: two-way infinite, initially all zero; initial head position: 0.
- There are 388 transition rows; every step moves exactly one square left or right.
- Dense-table SHA-256:
  `d1cf0f6e7a3c8f999d045694efc107dd1f9a03d45dd6c15e3d197ff7754c7231`.

The PDF includes the complete transition table as an appendix.

## What changes

PA194NQ combines the visible-top, no-push MP controller of supplied PA194N
with the premise-exchanged quantifier-distribution emitter of supplied
PA194Q, while retaining the original Shift test. The two source edits commute
exactly. The construction has 134 fixed controls, 67 reader controls and seven
simultaneous folds: 134 + 67 - 7 = 194.

The emitter changes 79 resolved instructions relative to N and emits a
different numerical formula at a recurring axiom interface. MP has a different
store contract from Q's cached controller. A conservative complete action-graph
comparison finds no match among all 34 prior 194-state classes, allowing state
renaming, every graph-spanning root, reflection and global symbol exchange.
The new contribution is this verified composition, not the already supplied
no-push rule, premise-exchange theorem, compiler or physical proof engines.

## Comparison scope

The source snapshot is ProveIt commit
`3cc7fbf75ba111a0da696ef2f6001dd528891bd5`.
The comparison covers 51 deliveries: 47 filed packets and four fresh incoming
ZIPs. All packet contribution summaries were reviewed. The literal-table census
scans all 17,557 tracked blobs under the requested PA and incoming paths and
recursively inspects distinct ZIP payloads. It recognizes complete numeric
five-column tables in `.tm`, `.txt`, `.tsv` and `.csv`; it does not claim to
recognize arbitrary program/JSON/prose encodings. Historical proof checkers
were not all rerun.

The 34 prior 194-state graph classes include 21 with reported ordinary PA
arguments, nine auxiliary/search classes, and four rejected classes. The
packet ledger, individual frontier entries, duplicate findings, larger
ancestors and source-level prior-art discussion are in `comparison/`.

## Reproduce the accepted result

Use Python 3.10 or later, standard library only, with assertions enabled:

```sh
python3 -B reproduce.py
```

The runner checks `SHA256SUMS`, copies the release to a temporary directory,
rebuilds the exact accepted table, replays both physical checkers, checks the
emitter/command/exchange certificates, compares the frozen prior frontier,
and verifies the factor-three refutation. It leaves the original release
unchanged. No network, Git checkout, SAT/SMT solver, Lean or Rocq is needed.

Useful optional modes:

```sh
# Also replay the physically valid but logically rejected 193-state table:
python3 -B reproduce.py --with-rejected-physical

# Also repeat the bounded pair-quotient searches:
python3 -B reproduce.py --search

# Keep temporary copies and per-check logs:
python3 -B reproduce.py --keep-work

# A shorter check that explicitly omits the independent universal tape replay:
python3 -B reproduce.py --quick
```

`--quick` does not replace full verification. Do not set `PYTHONOPTIMIZE` or
use Python `-O`. Individual scripts regenerate their receipts in place; use
the temporary-copy runner to preserve the release manifest.

The construction and independent checkers each cover all 4,755 primitive
source outcomes over arbitrary nine-register values, both decrement branches,
arbitrary header padding, and arbitrary finite nonempty spare lists. The
independent checker rederives four list lemmas from literal rows. An exact
58,154-step startup establishes the whole initial source-frame tape. The
finite startup run is an initialization check, not an empirical inference
of nonhalting.

## The rejected 193-state shortcut

`search/rejected193/` contains a literal 193-state table whose physical
source simulation passes both checkers. Its coefficient-three formula
encoding, however, makes the unchanged logical interface inconsistent.
It is **not a solution** to the consistency-machine task.

The collision E3(1,0) = I3(0,1) = 6 yields a short derivation of code one.
The readable 14-line certificate is expanded into 73,393 primitive steps
checked without a K/S oracle. See `search/factor3_obstruction/`; the PDF
includes the proof. A valid coefficient-three approach would need a new
logical interface and calibration, rather than this unchanged shortcut.

The scoped negative searches do not establish a state-count lower bound.
`search/cross_command/` also preserves a 195-state research construction
sharing an AX decoder fragment with MP, a portable physical/source checker,
and a positive truth-sentinel proposal. Its consistency argument is explicitly
an outline; it is supplementary research, not another claimed 194-state result.

## Artifact map

| Path | Contents |
|---|---|
| `report/pa194nq.tex`, `.pdf` | Main comparison, construction, proof and transition appendix |
| `machine/` | Accepted dense/native/raw tables, labels, source graph and receipts |
| `construction/` | Deterministic builder, frozen grammars and attributed source inputs |
| `verification/` | Independent literal-tape refinement engine and driver |
| `mathematics/` | All-store command, emitter and premise-exchange certificates |
| `evidence/` | Fresh verification receipts and logs |
| `comparison/` | Full packet/frontier ledgers, frozen old tables and graph comparator |
| `references/logical/` | Retained ordinary logical calibration and propositional dependencies |
| `search/` | Bounded unsuccessful searches and the rejected 193-state construction |
| `NOTICE.txt`, `PROVENANCE.json`, `licenses/` | Attribution, exact source paths and retained licenses |
| `SHA256SUMS` | Release content hashes, excluding the manifest itself |

To compile the report with a normal TeX Live installation, run
`sh build_report.sh`. It requires standard LaTeX packages listed in the
source, and runs pdfLaTeX twice. The `.tex` fragment inputs are included.

The full corpus rescan requires the pinned ProveIt Git objects; instructions
are in `comparison/AUDIT.md`. The frozen 34-class novelty check is standalone.
