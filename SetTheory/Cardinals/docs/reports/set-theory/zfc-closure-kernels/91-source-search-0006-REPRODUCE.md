# Reproduction

## 1. Verify the saved positive result

Use Python 3.11 or later with assertions enabled. The default checker needs only the standard library. Run from the archive's top directory:

```sh
python3 verify.py
```

The runner checks the archive hashes, extracts the unchanged reference packet into `build/`, and installs the new checker overlays into the recovered runtime. It performs these independent checks:

1. Reconstruct all 64 DNE formula templates from the pinned numerical specification, and check each exact AX stack, reads, rows, gate and fine word.
2. Check the six Boolean schemas, replay the seven-step full normalization and the 32 nearby source targets, and check their interfaces.
3. Prove all 19 original-macro/fine-expansion partial functions equal through the finite product construction and independent upstream path recheck.
4. Replay both exact six-zero scanner witnesses.
5. Check the selected grammar and all 63 retained nonidentity DNE breadth proposals from the immutable AST and exact source overrides.
6. Rebuild the explicitly modified source and literal table, check its register bisimulation, all 8,269 affine instruction guards, and sparse/dense blank execution.
7. Compare the canonical machine byte for byte with the supplied table.
8. Run a fresh independent frame, pointer, renumbering, and blank audit, linked to the archived full symbolic replay by exact table/site hashes.

The output is `build/reproduction-summary.json`; each subprocess log is in `build/logs/`. The expected canonical SHA-256 is:

```text
d193291ac92bc090a9b8a6e7d2c578928109633e12155cd0ce9fc1b5f66d2921
```

The default run was tested from the assembled packet. It **links to the archived full symbolic replay**; it does not silently claim to recompute that longer pass.

## 2. Recompute the full all-values tape proof

```sh
python3 verify.py --whole-frame
```

This also rederives actual-table macro inductions and replays every guarded source instruction for arbitrary extra gap, nine independent natural register values, and an arbitrary nonempty spare-list suffix. The original fresh replay took 393.55 seconds. Runtime depends on hardware; allow several minutes and keep Python assertions enabled. The expected report has 8,269 cases, 2,233,088 symbolic rules, all 490 transition rows, and `status: PASS`.

These scripts accompany explicit ordinary mathematical proofs. They are not a new Lean/Coq build. The final logical transfer and the inherited ZFC calibration are documented in the report and proof notes.

## 3. Rebuild the PDF

The PDF uses ordinary pdfLaTeX with `lmodern`, AMS mathematics, `booktabs`, `longtable`, `geometry`, `microtype`, `hyperref`, `xurl`, `fancyhdr`, and the other packages listed in its preamble. No generated images or network retrieval are required.

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The result is `report/main.pdf`; the delivered copy is `report.pdf`. The included `.tex` components are sufficient; Pandoc was used while authoring the appendices but is not needed to rebuild them.

## 4. Optional search and experiment reruns

First restore the historical relative layout:

```sh
python3 prepare_experiments.py
```

This only prepares local files. It recreates `work/machine_reduction/base/zfc245-proof-20261018`, fills `work/fine_grammar/runtime`, and decompresses the exact 8,385-case fixture. It does not start a search. Search reruns may overwrite their adjacent exploratory result files, so use a disposable extracted copy if preserving original manifests is important.

Compile the hardened fine search (g++ with C++17):

```sh
g++ -O3 -std=c++17 work/grammar_search/anneal_fine_compound_hardened.cpp -o build/anneal_fine
build/anneal_fine work/grammar_search/dne-seeds/mask32/grammar.txt work/grammar_search/dne-seeds/mask32/constraints.txt build/search.json 300 20261018 127 work/fine_grammar/fine-lock54.txt work/grammar_search/dne-seeds/mask32/resume.txt
```

The final positional argument, after the resume path, optionally specifies a deterministic proposal limit. For example, append `125000` and use a sufficiently generous time limit to reproduce a fixed number of proposals. Historical searches were time-budgeted. Their trajectories and proposal counts can differ across processor speeds and builds.

The raw C++ output does not retain the separate `source_override` proof metadata. Before compiling a source-changing result, restore it from its exact seed and verify its new word against the corresponding checked formula target. Use the already restored `final_search.json`, `final_compound.json`, or `machine/grammar.json` files for saved results. The independent grammar auditor and modified-source compiler must be applied before any new result is promoted.

The detailed search commands, masks, seeds, budgets and statuses are in `work/grammar_search/GRAMMAR_FINDINGS.md`, `grammar_lane_ledger.json`, `work/fine_grammar/dne-breadth/summary.json`, and neighboring logs. The mask49 initial discovery abort is preserved separately from the successful retry. Hardened discovery sources reject incomplete or nontransparent proposals; historical sources and measurements are retained unchanged.

The finite-dictionary MILP scripts additionally need NumPy and SciPy with `scipy.optimize.milp`/HiGHS. Their numerical infeasibility or time-limit statuses are search evidence for their specified dictionaries, not exact unrestricted lower bounds. Known seed assignments are checked with integer arithmetic outside the solver.

The optional matched-basis and coarse DNE searches use the included attributed fixture code:

```sh
python3 work/theory_encoding/basis_experiment.py
python3 work/theory_encoding/double_negation_experiment.py
```

The relevant K/S/Peirce control received 1,800 grammar trials; the coarse DNE sweep received 76,800. Their table counts and source-edge checks do not constitute new blank-start consistency theorems. The two additional unproved basis modes in the research script are marked exploratory and are excluded from the selected delivered machine tables.

## 5. Bounded predecessor-bypass studies

`work/machine_reduction/research-index.md` is the detailed index. After preparation, compile and run the C++ source in that directory against `candidate245-literal-cases.txt`. It embeds the baseline literal table in the fixture input. Every candidate execution uses 20,000 steps of fuel and tape interval `[-64,1983]`.

The one-entry family was exhausted under this filter. The multiple-entry searches retain only individually passing entry replacements, so they cover a separable family. The large retained products at old states 4 and 30 remain incomplete; the subsequent pruned and nogood runs each stopped at their stated time budget. No state-minimality theorem follows.

## Evidence conventions

* `PASS_FINE_GRAMMAR` means exact source spelling, closedness/orientation, routing, bootstrap projections and AST bounds. It does not alone prove logical calibration or tape simulation.
* `PASS_AFFINE_AND_BOOT` adds the explicit modified-source comparison, guarded affine instruction checks, and exact blank start. The full arbitrary-spare-list proof is a separate record.
* `certificates/normalized245/whole-frame.json` plus the independent linked audit are the full runtime evidence for the selected table.
* Formula length, grammar states, working states, and proof-assistant status are different quantities. No delivered result claims fewer than 245 working states.
