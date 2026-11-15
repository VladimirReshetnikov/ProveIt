# Three new 194-state PA consistency machines

**Result:** no machine below 194 states was established. This packet supplies
a materially different source design with three distinct 194-state realizations,
their written iPRA equivalence
with `Con(PA)`, exact construction and independent operational certificates,
and the records of the additional unsuccessful reduction searches.

This directory is a self-contained, offline construction packet for **PA194GD**,
**PA194GDH**, and **PA194GDHS**. The supplied transition tables are deterministic,
single-tape, two-symbol machines. Each has exactly 194 nonhalting states, two
transitions per nonhalting state, blank symbol 0, initial state 0, initial head
position 0, and a separate halting state 194.

The common design uses the explicit AX operand `c` for theorem generalization
`U(c,h)` and the adjusted offset `D=d+x` for the diagonal axiom `Γ(D)`. These are
independent parameters. All three have the original order of the two premises
in universal distribution and the successful MP command that does not push a
dummy zero. GD tests `t+h=1`; GDH and GDHS test `h=1`, with different physical
implementations of that cached test.

The new contribution is this combination and its exact 194-state realizations.
The constituent binder change, offset diagonal head, no-push MP, and cached
Shift were present separately in the supplied corpus. The accompanying report
provides the mathematical calibration and the comparison with the complete
pinned corpus. This packet does not claim a completed Lean endpoint.

## Start here

- `report/report.pdf`: complete report, including all three transition tables.
- `report/report.tex` and its included `.tex` files: complete editable report
  source. See `report/README.md` for recompilation.
- `machines/GD`, `machines/GDH`, and `machines/GDHS`: exact tables, source trees,
  resolved instructions, label maps, and simultaneous fold certificates.
- `comparison/`: 93-delivery semantic ledger, the structural census, and all
  139 earlier spanning 194-state table classes used in the novelty comparison.
- `verification/independent/`: a separately implemented literal-row replay,
  whole-tape startup check, certificate closure audit, and structural comparison.
- `references/`: the exact inherited AX11H written calibration archive,
  ten reviewed TeX components, and the review's explicit scope.
- `research/`: bounded negative search inputs, code, logs, and replay instructions.
- `RESULTS.json` and `SHA256SUMS`: machine-readable results and file identities.

## Reproduce

Python 3.10 or later and the standard library are sufficient. Run without `-O`:

```sh
python3 verify.py --output verification/reproduced.json
```

The verifier builds fresh tables in a temporary directory, compares every table
and source artifact with the supplied version, proves the local folding
identities by exhaustive two-cell execution, checks complete blank-tape
startup, and replays every source-instruction outcome in the inherited symbolic
executor. It also checks the complete AX emitter in free terms and the derived
command words for both detectors. The separate `check_source.py` independently
generates the arithmetic templates, all instruction rows and outgoing edges,
and the complete AX expression including its freshness guard and free register
conditions. It also checks the declared exact clock equations on representative
inputs; their universal proofs use the inductions in the mathematical report.
`--quick` skips only the source-instruction
replay; it is intended for construction debugging.

To write a fresh construction into an explicitly chosen directory:

```sh
python3 build.py --output rebuilt
python3 check_commands.py --output verification/commands-reproduced.json
python3 check_source.py --output verification/source-reproduced
```

The separately packaged independent verifier replays literal transition rows
and checks symbolic unary-register loops without the construction executor's
arithmetic oracle. Its receipts provide an additional, independent check.
From `verification/independent/`, run:

```sh
python3 -B literal/check.py inputs/GD194sum inputs/GD194H inputs/GD194HS
python3 -B check_startups.py
python3 -B audit_closure.py
python3 -B check_novelty.py
```

The `GD194sum`, `GD194H`, and `GD194HS` names are frozen verifier aliases for
PA194GD, PA194GDH, and PA194GDHS. `delivery_names.json` binds them to the exact
table hashes. For preservation of the frozen receipts, replay in a copy of
the packet or use each checker's documented output option. Universal literal
replay may take several minutes.

To inspect a finite blank-tape trajectory with a plain scalar simulator:

```sh
python3 simulate.py --family GD --steps 58154
```

This simulation uses an unbounded set of one-cells and makes no inference about
non-halting from its finite run.

## Exact tables

| Machine | Directory | Fixed controls | AX readers | Removed by simultaneous folds | Final controls | Source sites | Source outcomes | Blank startup steps |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| PA194GD | `machines/GD` | 134 | 69 | 9 | 194 | 3654 | 4755 | 58154 |
| PA194GDH | `machines/GDH` | 134 | 69 | 9 | 194 | 3653 | 4754 | 57922 |
| PA194GDHS | `machines/GDHS` | 135 | 69 | 10 | 194 | 3650 | 4750 | 57768 |

Each `machine.tm` line has five whitespace-separated fields:

```text
state read_symbol write_symbol L_or_R next_state
```

The dense SHA-256 identities are:

```text
PA194GD   1362fe8f264656e5b6d3e88666c0c88a34883c4d3cc5e9f2b4da9f9f6e8e595e
PA194GDH  e11b587cdb7d620adc9ce086467931f2d9db453f56231c5829e9f8c71c04eed1
PA194GDHS 7b69655c9115d226f23be4cd70303650f894a97d195c53139f72e1c937cdda58
```

`machine.native.tm` uses inherited sparse names, initial state 74 and halt 254;
`labels.json` maps dense names back to those native names. `raw.native.tm` is
before folding. `folds.json` lists every removed state, its surviving state,
and the survivor's two new actions. `local_cases.json` records all four two-cell
contexts for each pair on the final simultaneous table, not on separate
hypothetical tables.

`nodes.json` is the exact modified source tree dictionary, `grammar.json` is the
AX grammar, `sites.json` lists every source leaf and path, and
`instructions.json` resolves every branch/jump to a numerical source address.
The builder compares the entire resolved graph against the changed word in the
primary source parenthesization. No source successor is accepted merely because
two flattened words coincide.

## Source provenance and construction choices

The upstream revision is
`8d31445d858761a8f6150c2e5012adae8895e932` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/8d31445d858761a8f6150c2e5012adae8895e932).
`PROVENANCE.json` gives source paths, exact Git blob identities, and SHA-256 for
every unmodified input. `build.py` verifies those identities before using them.
No repository checkout or network is needed for reproduction.

The original PA196 source tree and the primary PA194 raw native machine provide
the fixed machinery. The previously supplied D grammar provides an economical
association shape. Of its final token, `dec4`, this construction restores the
ordinary structural `breakTo1`. It also retains the ordinary `breakTo1` exit in
`node22`. Thus neither of the older D design's semantic zero-test substitutions
is assumed. Relative to the primary 190-token AX word, exactly four positions
change (zero-based): 1 changes `copyD` to `copyA`, and 121, 122, 123 change `copyA`
to `copyD`.

The modified guard/MP/Shift rows and source nodes are written explicitly in
`build.py`; the arithmetic-box rows are checked byte-for-byte against the
primary table. `construction/compiler.py` and `symbolic_runtime.py` are retained
verbatim for provenance. Their legacy disk loaders are replaced with local
input functions by `build.py`; no absent upstream directory is read.

## Proof scope

The finite executable evidence establishes exact transition-table identities,
local simulation, startup, universal source-instruction contracts, and symbolic
command laws. The ordinary mathematical proof that the resulting program's
non-halting is equivalent over iPRA to `Con(PA)` is supplied in the accompanying
report. The full source-instruction replay in this packet uses the inherited
arithmetic-box oracle, whose rows are checked unchanged. The additional
independent literal-row replay is packaged separately. These checks and the
written iPRA proof do not constitute a new completed Lean formalization.

The logical calibration is a written mathematical composition with the exact
inherited AX11H argument. The review found no concrete error in its ten TeX
components, but did not independently rebuild every cited finite proof recipe
or all transitive Lean dependencies. The report states the inherited negative
calibration separately from the positive machine/refutation equivalence; it
does not invoke Markov's principle or infer a positive existential equivalence
from a double negation.

See `COMMANDS.md` for the full semantic AX output and derived words, and
`NOTICE.md` plus `licenses/` for attribution and licenses.
