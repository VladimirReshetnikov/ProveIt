# Optional grammar and source-encoding research

The primary construction in the enclosing archive is the QT loop rotation, with **244 working states**. Its machine proof and source proof are packaged separately. This directory preserves the alternative source families, broader grammar moves, measured outcomes, and rejected source-to-table shortcuts explored while finding that construction. None of the alternative AX families below is claimed as a smaller certified machine.

The directory is self-contained for its finite source and grammar checks. Python 3.12 with the standard library is sufficient; C++17 is needed only to run optional heuristic searches. The thousands of generated seed directories are omitted. Six representative seed directories, one additional retained embedding witness, their inputs, and aggregate records are included.

## Replay the retained evidence

From this directory, run:

```bash
python3 verify_research.py
```

This checks all 528 conjunction sources and all 32 additional DNE sources against the pinned symbolic specification. It independently executes their RPN emitters, checks protected stack content and input events, replays their recorded tree/DNE transformations, and checks their fine words and hashes. It then independently audits every retained seed and search output, including all routing projections, terminal orientations, grammar closure, the 54 bootstrap locks, and source depth/zero-run bounds. The 128-rule normalized control is also replayed. Results are written to `results/package_verification.json`.

The exact symbolic source checks establish the stated emitter interfaces. Their logical calibration is explained in `grammar_report.tex` and in the companion formalism appendix. A grammar audit alone does not establish a full binary-machine simulation.

## Measured outcomes

All nominal totals in this table use the audited 117-role framework. The actual QT244 construction changes an open loop body and is outside this fixed-framework search space.

| Research family | Source variants | Best retained grammar roles | Nominal total | Evidence |
|---|---:|---:|---:|---|
| Conjunction permutations, associations, boundary DNE | 528 | 129 for a new source | 246 | 528 seed audits; 30 bounded searches |
| Additional DNE subsets on conjunction source 2002 | 32 | 129 | 246 | 32 seeds; 8 bounded searches |
| Equality/congruence row fusion | 1,368 | 133 | 250 | 1,368 seed audits; 10 bounded searches |
| K/B/Peirce basis | 1,296 | 135 | 252 | 1,296 seed audits; 6 bounded searches |
| K/B/Peirce relative to falsity | 648 | 136 | 253 | 648 seed audits |
| Long-word entry embedding, normalized control | 1 control | 128 | 245 | Retained grammar audit; 180-second search |

The conjunction family contains inherited controls, including source 2008 at 128 rules. The new source minimum is 129. The smallest rule counts are measured witnesses, not lower bounds on all possible grammars. Historical summaries preserve their original identifiers and paths as data; replay commands use the paths in this directory.

The raw C++ output retains an inherited `framework_states: 118` metadata field. Use the independent auditor's `framework_states` and `working_states` values: with the scanner deletion enabled by `short_scan=True`, the charged framework has 117 roles. The auditor reconstructs this count from the included table and validates the deletion conditions.

## Regenerate source families and grammar seeds

The two conjunction-family generators have portable paths to the included dependency snapshot:

```bash
python3 bundle_permutations.py
python3 deepen_bundle.py
python3 verify_research.py
```

They regenerate `bundle_variants.json` and `bundle2002_dne_variants.json`. The pinned specification, macro-to-fine dictionary, original DNE family, and prior Boolean controls are under `reference/theory_encoding/`.

To regenerate only the best new conjunction seed:

```bash
python3 seed_variants.py fine bundle_variants.json \
  reference/normalized245_grammar.json regenerated_bundle \
  --generic-edit --mask 2002
```

Omit `--mask 2002` to regenerate all 528 seed directories. The best seed has 129 rules. `seed_variants.py` accepts the same `variants[].fine_AX` JSON format as the companion formalism families. Those larger logical-family generators and JSON files are included once in the separate formalism package, rather than duplicated here:

- `formalism_fusions.py` and `formalism_fusions.json`;
- `formalism_kbp_sources.py` and `formalism_kbp_sources.json`;
- `formalism_kbp_sources.py --peirce-f` and `formalism_kbpf_sources.json`.

Pass the chosen companion JSON path as the second positional argument to `seed_variants.py`. Stable grammar-directory identifiers for these families are `1000 + variant index`; the symbolic source generators retain their own original identifiers. Their exact source interfaces and logical certificates belong to the companion formalism appendix.

## Optional broader searches

`anneal_cluster.cpp` extends the attributed search with atomic removal of one to four shared definitions and joint reparsing of their consumers. `anneal_embed.cpp` also permits a special entry to be embedded in an already charged source word beyond the inherited router constructor's length cap. `add_embedding.py` reproduces the latter extension from the former source.

Compile a search engine, then use the wrapper to preserve the source override and independently audit its output:

```bash
c++ -O2 -std=c++17 anneal_cluster.cpp -o anneal_cluster
python3 run_search.py selected/bundle_best new-search.json \
  --seconds 30 --seed 200233
```

For the embedding engine:

```bash
c++ -O2 -std=c++17 anneal_embed.cpp -o anneal_embed
python3 seed_variants.py fine \
  reference/theory_encoding/original_layout_dne_variants.json \
  reference/normalized245_grammar.json regenerated_dne --mask 32
python3 run_search.py regenerated_dne/mask32 embedding-search.json \
  --engine embed --seconds 30 --seed 777320
```

The search is bounded by elapsed time, and its discovery path can vary with compiler and machine. The included retained dictionaries are the reproducible witnesses; no replay needs to rediscover them. `run_search.py` writes an independent `.audit.json` alongside each output. A lower abstract count would still need its source-specific logical calibration, complete binary runtime proof, and blank bootstrap.

The minimal fine backend dependencies are included under `fine/runtime/`: the Python auditor, exact closed-source DAG, semantic vocabulary and orientations, lock file, and attributed 246-state ancestor table. `fine/fine-grammar.txt`, `fine/fine-constraints.txt`, and `fine/fine-lock54.txt` provide the seeder/search inputs. No full duplicate of the inherited machine-proof package is required for these optional grammar checks.

## Historical source reductions

`historical_source/source_reductions.tex` proves two useful source reductions at NIP and explains why their attempted direct table edits failed. These are separate from the successful QT rotation. In particular, a `PASS` in their source reports does **not** certify the rejected shared-state deletion.

Both source checks have portable defaults using their included dependency copies:

```bash
python3 historical_source/check_source_244.py
python3 historical_source/make_nip_specialization.py
```

The first replays the unbounded dirty-root invariant and the single-occurrence source weak bisimulation. The second independently checks the six-leaf NIP specialization and its complete source context. The first also regenerates a large admitted-guard list; that derived list is omitted from this focused packet. `rejected_boot.json` is historical finite bootstrap evidence for the rejected attempt, not the bootstrap of the actual QT244 machine. No rejected transition table is included here.

## Files, provenance, and licenses

`selected/selection.json` identifies the retained witnesses. `results/` contains all aggregate audits, rankings, bounded-search summaries, and compact search logs. `grammar_report.tex` is a body-only appendix for the enclosing report.

The inherited routing grammar, source-normalization helpers, and backend remain attributed to the ProveIt work and its cited upstream authors. Original notices and the ProveIt/Wade licenses are retained in `reference/`. The pinned specification is checked against SHA-256 by its symbolic loader. New portability changes only replace source-helper paths or add independent replay wrappers; they do not change the archived fine words or retained grammar witnesses.

`grammar_PACKAGE.json` in the enclosing workspace lists the focused files, sizes, groups, and SHA-256 hashes. The separately packaged primary QT244 verifier does not call any optional search or depend on these alternative AX families.
