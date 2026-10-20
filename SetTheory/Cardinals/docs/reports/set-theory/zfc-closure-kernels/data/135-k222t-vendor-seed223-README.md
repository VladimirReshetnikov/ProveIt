# K223: an explicit 223-state Turing machine for Con(ZFC)

This packet constructs a deterministic **223-state, two-symbol, single-tape
Turing machine** whose non-halting on the blank tape is provably equivalent
in ZFC to `Con(ZFC)`. It improves the 224-state candidate in ProveIt commit
`49ee7cfdc8e0364c6db3614675d141d66f9350ed` by one working state.

The complete mathematical argument is in `report/main.pdf`, with editable
LaTeX sources beside it. The exact machine is `portable/machine/candidate223.tm`.
The report includes its entire transition table.

## Machine conventions and identity

| Property | Value |
| ---| ---|
| Working states | 223, numbered 0 through 222 |
| Start state | 0 |
| Separate terminal state | 223, excluded from the working-state count |
| Tape | One two-way infinite tape |
| Alphabet | 0 and 1 |
| Initial tape and head | All zeros; head at integer position 0 |
| Transitions | 446 rows; each writes a bit and moves one cell left or right |

A transition line has the format `state read write direction next_state`.
The initial-state directive is `#! start 0`. Every working-state/symbol pair has exactly
one row. The terminal state has none.

The canonical table SHA-256 is:

```text
c89d3f79ab12a3857092bb4b3d30bfc594079edc0f696b066ce4c386fd00f1b2
```

Inherited K and legacy labelings are also included, with explicit maps. All
446 canonical rows are independently checked as the conjugate of the
K-labelled table; the initial and terminal labels are checked too.

## The idea that saves the state

The emitted set-theoretic axiom changes from K's output-root presentation to
its witness-request, or seed, presentation. The request says that whenever a
matrix has an output for an input, the containing object supplies an output.
The identical request already occurs inside the hereditary closure clause.
Repeating it at the root creates useful compiled subtrees to share.

The source therefore becomes **longer**:4,962 primitive instructions instead
of 4,799. Its optimized binary grammar nevertheless has **209 distinct
subtrees instead of 210**. All 12 existing contextual decoder aliases and the
six-zero address limit are retained. There are 174 decoder states and 49 other
states, giving 223 in the literal transition table. In K labels the change
deletes K227 and changes 36 retained rows.

The seed reformulation and its consistency reductions already appear in
Elliot Glazer's pinned K230 development. The contribution here is choosing
that presentation as the actual emitted formula and compiling its repetition
into a smaller decoder. No priority claim is made for the seed theory, and
no minimality claim is made for 223 states.

## Proof and verification status

The ordinary mathematical proof establishes the equivalence in ZFC by
effective transformations of finite derivations. It handles the actual
native coupling `matrix code = private variable label`, the special codes
0 and 1, coincident input/output labels, and the inherited restricted equality
helper. The private code is chosen **after** translating equality into
membership indiscernibility.

The exact emitter is independently bound to the source by symbolic execution
of its 77-macro word, eight arbitrary-register macro comparisons and a complete
source bisimulation with 1,240 paired boundaries. The deterministic builder
additionally checks the push-one constituent, giving nine macro contracts,
and checks all 164 closed grammar units and both complete control-graph
resolvers.

Fresh independent runtime replays passed all **6,449 guarded source cases**
and covered all **446 transition rows**. These are unbounded induction proofs
over arbitrary natural register values, gap and first spare, and an arbitrary
finite remaining spare list. They use 1,566,562 symbolic rule applications;
the largest symbolic case has 400 applications. They do not sample bounded
register values or bound the concrete running time.

Exact blank execution reaches the complete intended initial register frame
after **409,835 steps**, with 351 one-cells at the recorded positions and
every other cell zero. Each simulated instruction takes positive finite time,
with minimum duration 13 steps.

**A new end-to-end Rocq or Lean theorem for these 223-state bytes has not been
compiled.** This contribution consists of the ordinary mathematical proof,
executable exact and inductive certificates, and explicitly pinned inherited
formal material. The report separates those layers. The runtime receipts
alone do not prove the theory calibration.

## Offline reproduction

Use Python 3.10 or newer with assertions enabled. From this extracted packet:

```sh
python3 -B portable/reproduce.py --output-dir /tmp/k223-replay
```

Choose an initially empty directory outside the packet. No network, external
Python package, optimization search or proof-assistant installation is needed.
The default:

1. Checks the complete portable manifest and extracts the unchanged pinned
   K224 archive.
2. Runs the predecessor's quick mathematical-certificate replay, including
   its logical and source checks.
3. Reconstructs the new source, all three table labelings and canonical map;
   compares their bytes with the published files.
4. Runs the independent emitter and uniform native-decoding audit.
5. Freshly derives all 6,449 K223 binary runtime cases, including the four
   list-induction schemas, complete startup and canonical row conjugacy.
6. Compares every fresh guarded-case summary with the frozen first replay
   and rechecks all input hashes.

Success prints `FULL_K223_REPLAY_PASS`. Reports and logs go only to the output
directory. The construction itself takes less than a second in the development
environment; a full default replay takes a few minutes. Do not use `-O`, `-OO`
or `PYTHONOPTIMIZE`.

To rederive the K224, K225 and K226 runtime cases too:

```sh
python3 -B portable/reproduce.py \
  --full-baseline --output-dir /tmp/k223-all-runtimes
```

A full predecessor replay and fresh K223 package replay were performed during
construction. Their receipts are in `verification/`. These are distinct from
any new proof-assistant build.

To regenerate the printed table and PDF:

```sh
python3 -B report/generate_table.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The LaTeX build uses standard mathematical, table, typography and hyperlink
packages. The generated PDF is already included.

## Packet map

| Path | Contents |
| ---| ---|
| `report/` | Complete LaTeX report, PDF, theory section and generated table |
| `portable/machine/` | Frozen source, grammar, transition tables and label maps |
| `portable/verification/` | Deterministic builder and independent emitter/runtime checkers |
| `portable/certificates/` | Source/table/emitter receipts, all guarded-case summaries and row delta |
| `portable/theory/` | Detailed native-code, ordinary-theory and runtime proof notes |
| `portable/vendor/` | Unchanged K224 archive, including its nested dependencies and notices |
| `research/` | Measured alternatives and explicitly scoped unsuccessful searches |
| `verification/` | Construction-session replay receipts, PDF checks and packaging checks |

The alternative-theory discussion considers the original, seed and conditional
K forms, request rewrites, equality-helper choices, NBG, reflection and
Ackermann routes. It identifies which alternatives were compiled or measured
and which remained conceptual. Search counts are exploratory history and are
not ingredients of the positive proof.

See `PROVENANCE.json`, `NOTICE.md`, `LICENSE` and `SHA256SUMS` for pins,
attribution, license scope and file integrity. The unchanged predecessor ZIP
has SHA-256
`cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887`.
