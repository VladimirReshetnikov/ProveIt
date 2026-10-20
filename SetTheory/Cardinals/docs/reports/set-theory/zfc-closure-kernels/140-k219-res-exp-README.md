# Archived calculus and codec experiments

This directory contains the compact discovery drivers and original metric
receipts cited by the research appendix. It contains no failed candidate
transition tables. It is separate from the deterministic K219 construction
and its verification command.

## What the receipts establish

`receipts/<family>/summary.json` records the measured finite search family,
source metrics, and raw compiler outcomes. A `working_states` field describes
a raw table; it is **not** a correctness claim. Some raw tables failed actual
primitive interfaces, and many candidates failed decoder binding entirely.
The countermodel appendix is a separate mathematical result. None of these
finite source searches proves a global lower bound.

| Driver | Receipt family | Search scope |
|---|---|---|
| `additive_binder.py` | `additive` | Four implementations of the safe binder a+b+1 |
| `constructor_binders.py` | `constructors` | 16 existing-constructor binder choices |
| `pair_binders.py` | `pair_binders` | 120 scaled-Cantor/tag/order/shape choices |
| `h_fusion.py` | `h_fusion` | 72 exact existence/G fusions |
| `nested_fourth_parameter.py` | `nested_fourth_parameter` | Six nested-field register/role choices |
| `three_row_proposition.py` | `three_row_proposition` | 3,888 implementations of each of three complete bases |
| `tag_permutations.py` | `tag_permutations` | Six tag assignments times three edit policies times two increment shapes |
| `orientation_postfix.py` | `orientation_postfix` | All 16 constructor argument orientations |
| `orientation_repair.py` | `orientation_repair` | 20 seeded grammar parses per orientation in the recorded run |
| `nonlocal_reassociate.py` | `codec_reassociate_032`, `codec_reassociate_203` | Five greedy closed frontiers per node, all Catalan shapes through eight atoms |
| `protected_compile.py` | `protected_codec032` | Conservative helper-state protection; one larger table passed finite interfaces |

The `engine_protected.json` set was discovered from 6,167 finite primitive
frames. It is not a proof that every helper use has been identified.
Protected compilation is an exploratory debugging tool.

## Offline dependencies and invocation

Python 3 with the standard library suffices. Assertions must be enabled.
The drivers reuse the exact source-language and decoder utilities from the
pinned K220/K221 packets; they are not reimplementations of the final K219
runtime checker. `run_experiment.py` discovers the bundled K220 archive under
the K219 packet's `portable/vendor/`, extracts it into the requested work
directory, and extracts its bundled K221 parent. The archives and input
tables/source lists are checked against fixed SHA-256 values. No network
access is required.

From this directory, a small complete experiment is:

```sh
python3 run_experiment.py --work /tmp/k219-calculus-run nested_fourth_parameter.py
```

An existing extracted environment can be used explicitly:

```sh
python3 run_experiment.py \
  --work /tmp/k219-calculus-run \
  --k220-base /path/to/K220_Construction_2026-10-20 \
  --k221-base /path/to/K221_Construction_2026-10-20 \
  tag_permutations.py
```

If this directory is used outside the final K219 packet, pass
`--k220-archive /path/to/K220_Construction_2026-10-20.zip` instead.
Runner options precede the driver name. Remaining options are passed to the
driver. For example, the recorded orientation grammar family uses:

```sh
python3 run_experiment.py --work /tmp/k219-calculus-run \
  orientation_repair.py --trials 20
```

Outputs appear under `<work>/research_calculus/generated/` unless the driver
accepts and receives an explicit `--out` argument. Some experiments generate
many provisional tables and may take minutes; keep their output separate
from the release files. The runner records exact input identities, command,
Python version, and driver hash in `<work>/run_provenance.json`.

For the nonlocal codec receipts, first run `tag_permutations.py`. The two
source inputs are respectively
`I0Q3E2_last_right/sites.json` and `I2Q0E3_delta_right/sites.json` under its
generated directory. Use `nonlocal_reassociate.py --sites <input>
--max-atoms 8 --threshold 209 --retain 20 --out <directory>`.
The protected compiler may then be applied to the retained 209-node source
from the first of these searches. The archived finite runtime receipt is
provided as evidence of the original screen, not as a universal proof.

## Portability edits and provenance

The mathematical search bodies are preserved. `additive_binder.py` now
obtains paths from the runner's `K220_BASE`, `K221_BASE`, and
`CALCULUS_WORK_ROOT` environment variables. `search_general.py` is a small
dependency shim for the copied nonlocal DAG driver.
`orientation_repair.py` imports that local driver directly, and
`protected_compile.py` reads its recorded protection set from `receipts/`.
These replace discovery-workspace path assumptions. The nested-field
docstring was clarified: it preserves the axiom families and later-row
parameters, rather than literal identity of each original AX batch.

`PROVENANCE.json` lists the original discovery-driver identities and the
release-file identities. The original summaries are preserved byte for byte;
elapsed times and experimental raw allocation details should not be treated
as platform-independent performance guarantees.
