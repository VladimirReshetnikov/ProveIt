# PA194Q5 and PA194Q6

## Result

No verified machine below 194 working states was obtained. This archive
delivers two different 194-state binary Turing machines, PA194Q5 and PA194Q6,
with an ordinary mathematical proof of

\[
\mathrm{PA}\vdash
\bigl(\neg\operatorname{Halt}(M,\mathrm{blank})
\leftrightarrow\operatorname{Con}(\mathrm{PA})\bigr).
\]

They combine the premise-exchanged quantifier-distribution head with formula
coefficients 5 and 6, while keeping the original sum-testing Shift and
dummy-push MP controller. Both component ideas existed separately in the
supplied corpus. The claimed contribution is the new combination, its exact
source and physical implementation, and the accompanying calibration.

**Start with `report/pa194_qradix.pdf`.** The report includes the comparison,
proof, verification scope, unsuccessful searches, complete 194-state tables,
40-class frontier, and 54-packet ledger. Its editable source is
`report/pa194_qradix.tex`, with all required local includes retained.

## Machine convention

Both machines have one two-way infinite tape, alphabet `{0,1}`, and an
initially all-zero tape. The head starts at cell 0 in state 0. Each table row
has five fields:

```text
state  read_bit  write_bit  direction  next_state
```

`direction` is `L` or `R`. Working states are `0,...,193`; label `194` is the
halt target and has no transition rows. Each table contains all 388 required
rows. All 194 controls are graph reachable; this does not assert that the
particular blank run visits every control.

| Quantity | PA194Q5 | PA194Q6 |
|---|---:|---:|
| Working controls | 194 | 194 |
| Unfolded controls | 202 | 202 |
| Fixed controls + AX readers − folds | 135 + 67 − 8 | 135 + 67 − 8 |
| Primitive source sites | 3,734 | 3,795 |
| Primitive branch contracts | 4,841 | 4,902 |
| Exact blank startup moves | 58,320 | 58,320 |

SHA-256 of the complete dense tables:

```text
150041f819135fa32b4521154823f1b96e635e8141329a6e8fbf15988baa073a  machines/PA194Q5/machine.tm
7f53cacaa0533e601bad9685957a1ef5fede892533e0d62bd49684ef7cf984d4  machines/PA194Q6/machine.tm
```

## Deterministic reproduction

From this directory, with Python 3.10 or later and assertions enabled:

```sh
python3 -B reproduce.py
```

Only Python's standard library and the included files are needed. No network,
repository checkout, Lean installation, or stochastic search is required.
The run takes several minutes and writes separate results under `reproduced/`.
An alternative destination can be supplied with `--output /absolute/path`.

The driver checks the archive manifest and recorded census counts, replays
the finite K/S/MP premise-exchange proof, reconstructs both tables byte for
byte, runs complete source-step contracts and startup, runs the second
source parser and literal-tape verifier, and compares against all 40 stored
194-state representatives. It launches verifiers in separate Python
processes so their similarly named modules cannot interfere.

The stored verification receipts are under `machines/*/receipt.json` and
`verification/independent/results/{5,6}/`. The independent audit quantifies
over arbitrary natural register values, a nonempty arbitrary finite spare
list, an arbitrary nonnegative header gap, and full blank tape exteriors.
It does not infer a universal claim from finitely many register examples.
Its unary/list inductions are executable symbolic proof rules, not a newly
kernel-checked Lean or Rocq development.

## Contents and proof boundaries

| Directory | Contents |
|---|---|
| `report/` | Complete report, `.tex` sources, compiled PDF, generated tables. |
| `machines/` | Dense/native/raw tables, source trees, resolved instructions, source binding, fold traces, receipts, novelty checks. |
| `construction/` | Frozen grammar, deterministic builder, inherited compiler and symbolic runtime, required inputs. |
| `verification/` | Finite exchange proof and the independent source/literal-tape audit. |
| `calibration/` | Attributed inherited mathematical calibration manuscripts, restricted implication proof template, new integration review. |
| `comparison/` | All 54 packet records, all 40 frontier representatives, complete literal/JSON census, scanner and novelty scripts. |
| `search/` | Completed failed searches, frozen inputs, C++ programs, logical obstructions, and rejected experiments. |
| `licenses/` | Preserved upstream licenses. |

The theorem in the report is an ordinary mathematical PA-provability result
using explicit inherited proof templates and the new implementation
certificates. There is **no newly compiled end-to-end Lean, Rocq, or iPRA
equivalence theorem**. The comparison labels report the evidence supplied
for older machines; every historical consistency proof was not rerun.

The finite blank startup check is only the connection to the interpreter
frame. It is not evidence of nonhalting by itself. Likewise, the negative
searches are bounded investigations and do not establish a 194-state lower
bound. The physical reduction searches in `search/physical_invariants/`
target the previously supplied QN machine, not the delivered Q5/Q6 tables.

## Historical comparison and optional discovery

The source snapshot is ProveIt commit
`317b07268681b44ff352d173a162e2a8c241b2fe`.
The audit covers the requested PA and incoming areas, including nested ZIPs
and explicit JSON machine encodings. It also studies the ZFC compiler and
ConciseIPRA material for possible changes. See `comparison/README.md` for
the exact population, census limitations, and optional fresh-scan commands.

The novelty check allows arbitrary state renaming, all spanning roots,
tape reflection, global bit complementation, and ignores the final write
and move on halting transitions. Both candidates differ from every stored
194-state table under these transformations. This is a graph comparison,
not semantic inequivalence: their intended halting conditions agree.

The ten recorded emitter searches made 14,425,456 mutation iterations with
no accepted smaller machine. The additional invariant-based QN screens
test common-action merging, incoming-edge bypass, and predecessor-history
marking; every completed screen has zero candidates. Optional search
reproduction requires a C++17 compiler. The accepted machines' verification
does not depend on rediscovering a grammar within the same time limit.

## Rebuilding the PDF

With a normal TeX Live or MiKTeX installation containing the packages listed
in the preamble:

```sh
cd report
python3 generate_includes.py
pdflatex -interaction=nonstopmode -halt-on-error pa194_qradix.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194_qradix.tex
```

The PDF was rendered and visually inspected. The included calibration
manuscripts are supporting sources; the compiled main report is the
self-contained reading entry point.

See `PROVENANCE.json` and `NOTICE.md` for inherited material, original
authors, and the limits of the new contribution.
