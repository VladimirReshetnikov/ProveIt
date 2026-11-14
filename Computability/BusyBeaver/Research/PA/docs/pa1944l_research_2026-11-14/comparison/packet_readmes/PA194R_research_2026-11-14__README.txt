# PA194R: a different 194-state PA consistency machine

**Result:** No machine below 194 states was verified. The primary fallback is
**PA194R**, a new decoder layout combined with a proved known-zero closing
decrement. It has 194 working states, two symbols, one two-way tape, an all-zero
initial tape, and only L/R moves. The halt state is excluded from the count.

The ordinary mathematical result is:

    PA proves: (PA194R never halts from blank) iff Con(PA).

This package supplies an ordinary mathematical proof and complete finite and
universal symbolic verification, with the inherited proof-producing logical
calibration explicitly retained. It does **not** claim a new end-to-end Lean or
Rocq theorem, or either missing machine-specific iPRA reduction in the upstream
project. Actual nonhalting in the standard model follows if PA is consistent.

## What is new

PA194R changes **1,111 of 3,646 source-address paths**, replacing 44 of the
67 axiom-reader subtree types while keeping 23. Its resolved instruction graph
is exactly that of the simpler new PA194F. Both replace the emitter's final
unconditional return with decrement X. A four-site invariant proves X is zero
there and gives exact equality with the supplied PA194CS source execution.

The 196-state research already contains the general zero-closing principle.
The new contribution is this verified 194-state composition and reassociated
decoder, its literal tables, the small proof and the independent physical
checks. The four new graphs are mutually distinct and absent from the eight
old 194-state classes in the recognized pinned corpus, even allowing state
renamings, root changes, reflection and global bit exchange.

| Directory | Change from supplied PA194CS | Clean startup |
|---|---|---:|
| `machines/PA194R` | New 67-reader grammar, seven AX folds, controller fold, final X decrement | 57,768 steps |
| `machines/PA194F` | Final emitter jump becomes decrement X; simple one-row intermediate | 57,768 steps |
| `machines/PA194A` | Entry jump at source 26 becomes decrement A | 57,978 steps |
| `machines/PA194X` | Entry jump at source 26 becomes decrement X | 58,014 steps |

Each has 194 controls, 388 rows, 3,646 source sites and 4,746 checked outcomes.
Both outcomes of every decrement are checked, including the new unreachable
positive branch.

## Read and use

- `report/main.pdf` is the report, including the complete PA194R transition
  table, ordinary proof, comparison, failures and 41-packet ledger.
- `report/main.tex` and its local TeX inputs are the complete report sources.
- `machines/PA194R/machine.tm` is the primary dense table.
- `machines/PA194R/machine.native.tm` is the same table in compiler labels.
- `machines/*/labels.json` gives dense label -> native label, including halt.
- `machines/*/instructions.json` and `sites.json` give complete source
  control-flow graphs and binary addresses.
- `machines/*/local_folds.json` records every simultaneous fold case.
- `verification/recorded/*/` contains independently produced tables, source
  graphs, all contracts, list-loop lemmas, whole startup and receipts.

Dense tables use start **0**, working states **0–193**, and halt **194**.
Rows have five columns:

    state read_symbol write_symbol L_or_R next_state

The head starts at coordinate 0 on an entirely zero tape. Halt has no outgoing
rows. Native tables instead use start 74 and halt 254.

Primary dense SHA-256:

    8a9a8a30773f73b638a7c51da1afca9c9921371aea819d6a21f02d742f673a4e

Primary native SHA-256:

    24539448def6e974d636052dbcb56eeb61d8e06ad0e9924d734c3bd4f0e01aa8

## Reproduce

Use Python 3.10 or later, standard library only; no network is needed.
Keep assertions enabled: do not set `PYTHONOPTIMIZE` or use `python -O`.
From this directory:

    python3 verify.py
    python3 verify.py --full

The default checks release hashes, rebuilds all four tables in a temporary
directory, reruns construction contracts and simultaneous fold checks,
checks zero invariants, compares released artifacts with independent outputs,
replays the rejected 1,361-step startup, and checks graph novelty. It does not
rerun the slower independent symbolic engine.

The `--full` run additionally rederives all four generic register-list lemmas
from each literal table and checks every outcome over arbitrary natural
registers and an arbitrary finite nonempty list of arbitrary natural spares.
It also rechecks whole blank startup. This takes several minutes. Fresh
outputs use temporary directories and preserve the release files.

Individual entry points:

    python3 construction/build.py --family all --output /tmp/pa194-rebuild
    python3 construction/build_reassociated.py --output /tmp/pa194-rebuild/PA194R
    python3 proofs/check_zero_cuts.py
    python3 verification/four_site_cut.py inputs/pa194CS.instructions.json machines/PA194F/instructions.json
    python3 verification/check_literal.py --output /tmp/pa194-independent
    python3 verification/check_companions.py --family both --output /tmp/pa194-independent
    python3 verification/check_reassociated.py --output /tmp/pa194-independent
    python3 verification/compare_recorded.py
    python3 comparison/compare_candidate.py machines/PA194R/machine.tm

The symbolic rules and their generic induction arguments remain in the trusted
verification base. Successful Python execution is not a proof-assistant theorem.
The ordinary PA proof explains finite calculations, unary-loop induction,
source induction and positive trace composition.

Compile twice from `report/`:

    pdflatex -interaction=nonstopmode -halt-on-error main.tex

The supplied PDF was rendered and visually inspected.
`report/generate_tables.py` regenerates the ledger, transition and validation
tables from released JSON/CSV artifacts.

## Comparison coverage

Source snapshot:

    VladimirReshetnikov/ProveIt
    17f92105e2bc4317feae6c219cb2143437b482ff

The audit covers 36 relocated reports and five newer incoming packets.
The current 26 incoming ZIPs overlap that inventory. Recursive literal-table
recognition finds 4,417 occurrences, 620 byte identities and 446 root-spanning
graph classes, including rejected candidates and synthetic controls. Two
disconnected synthetic controls are excluded from the last graph count.

The recognizer accepts complete numeric five-column `.tm`, `.txt`, `.tsv` and
`.csv` files with binary symbols, L/R moves and a unique undefined halt.
JSON-only and source-only encodings are outside this count; their reported
designs remain in the report ledger. Not every historical candidate was
independently reproved.

- `comparison/packet_ledger.csv`: all 41 reports and contributions.
- `comparison/frontier194.csv`: the eight existing 194-state graph classes,
  including the explicitly rejected scanner quotient.
- `comparison/census/`: old literal tables, byte/graph hashes, archive hashes
  and occurrence provenance.
- `comparison/novelty_*.json` and `new_family_graphs.json`: individual and
  pairwise graph comparisons.

The accepted separate-head 68/8 table is distinct from the rejected
diagonal191 seven-zero scanner table. Both have 194 controls; only the former
has the required supplied physical refinement.

## Search evidence and failures

`research/state_search/` contains portable bounded quotient synthesizers,
grammar searches, frozen inputs, logs and a positive control. Bounds and
limitations are recorded there. No valid reduction below 194 was found.
These are scoped unsuccessful searches, not an optimality proof.

The final parameter screen tested 373,248 assignments across four zero-closing
endpoints and two frontier shapes. The last three grammar runs made 16,903,868
proposals, all at least 194. The primary reassociation came from a saved
194 plateau and was then fully verified.

`research/rejected103/` is a negative control. Its source change and every
source contract pass, but the literal blank machine halts after 1,361 steps
before reaching the clean seed. This table is **rejected**. Its complete
trace can be replayed independently.

Other research JSON files are bounded experiment receipts; paths inside them
are historical provenance, not dependencies of the new verifiers. They do
not constitute accepted designs.

## Attribution and proof status

The work builds on ProveIt's PA research, the imported James Chang register
machine development and the attributed independent symbolic runtime. Licenses
and notices are retained in `licenses/` and beside imported code.
`PROVENANCE.md` identifies preserved inputs and proof texts.

The general known-zero closing, cached controller and symmetric comparison
are prior supplied ideas. The ordinary logical calibration is inherited and
audited explicitly; it is not replaced by external equiconsistency or by an
unfinished conditional iPRA endpoint.

`SHA256SUMS` identifies release files except itself. Runtime caches, LaTeX
auxiliary files and temporary outputs are excluded.
