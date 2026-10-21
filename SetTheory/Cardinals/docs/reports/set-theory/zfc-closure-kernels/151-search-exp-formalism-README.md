# Formalism research checkpoint

**This checkpoint does not contain a justified machine with 217 or fewer working states.** It records a verified operational modification at 218 states, an ordinary proof of its modified proof-enumerator calibration, smaller source experiments whose allocation or logical calibration remains open, and three independently checkable finite countermodels to a proposed quantifier-stability lemma.

Baseline: ProveIt commit `9adcaff0a72486ecc81242e0eca86e428c74879e`, `Computability/BusyBeaver/Research/ZFC/candidate-k218`. Only its source, transition table, and decoder allocation are included under `baseline/`. The original repository is not copied.

## What is established

The selected omit-zero-push variant removes the successful modus-ponens dummy stack push. Its source has 205 DAG nodes and 4725 primitive occurrences. Its exact binary table still has **218 working states**.

- `code/generate_omit_source.py` exactly regenerates the selected source from the pinned baseline using Python's standard library.
- `code/check_omit_source.py` checks the exact closed-subtree deletion, the complete primitive-word deletion, independent arithmetic/interval control-flow graphs, and all6141 retained graph edges with the deleted block's entry redirected to its exit.
- `code/check_blank_omit.py` replays312909 exact blank-tape transitions and checks the entire resulting tape. It uses an unbounded finite-support representation and only Python's standard library.
- `code/check_runtime_omit.py` proves6142 guarded primitive interfaces with arbitrary natural register values and a complete endpoint-tape specification. The construction takes about110seconds here. A proof-search bound is not a runtime/value bound. It imports five pinned vendor files listed below.
- `reports/formalism-checkpoint.tex` gives the exact compiler repair: the successful-MP cleanup loses its last NIP because the dummy stack element was not pushed. This is an **ordinary mathematical proof**, not a new compiled Lean proof.

The mathematical symbolic runtime engine is not a proof-assistant kernel. Its corrected receipt is `runtime/runtime.json`, with all case summaries in `runtime/cases.json`. The current driver SHA-256 is `82808a32a1350a7070031aac752662681877d534abf4cfa206ce1f679a974ef9`.

The driver's inherited introductory phrase “source equivalence” refers to the external candidate-source semantics/calibration obligation. The variant is intentionally **not trace-equivalent to the old enumerator**. The corrected receipt and report state the precise obligation.

## Portable finite verification

Run from this directory with Python3.12 and assertions enabled:

```sh
python code/verify_checkpoint.py --output /path/to/finite-check-receipt.json
python code/generate_omit_source.py --output /path/to/regenerated.sites.json
python code/check_blank_omit.py sources/omit-zero-push.tm --output /path/to/blank-receipt.json
```

`verify_checkpoint.py` uses only Python's standard library and no vendor imports. It verifies the manifest, parses the selected source trees independently, recomputes their DAG/leaf/depth/zero-run metrics, verifies the exact omit-zero source transformation, checks table syntax/state count, checks consistency of the stored case census, and independently evaluates the finite Heyting countermodels. Its receipt consistency checks do **not** replace replaying the runtime engine.

The countermodels validate normality, preservation of finite meets and top, seriality `Q(0)=0`, and `¬Q¬QA≤A`. Both have stable inputs with unstable quantified outputs. The second additionally has `¬¬(A→QA)=top`. Neither is claimed to model the full native equality/membership/set calculus; consequently neither refutes K/S-only equiconsistency.

A third witness, `models/booleanized_commutation_countermodel.json`, has two modalities on the upsets of two disjoint two-world chains. The original modalities commute and each satisfies normality, seriality, and rho6. Applying double-negation closure to their outputs breaks commutation on a regular element. The standalone verifier checks every pairwise normality instance and every original commutation instance. This rules out another generic negative-translation shortcut, while leaving the full K/S-native equiconsistency question open.

## Central vendor dependency

The parent archive supplies this vendor once. Preserve these paths under a chosen `K221` directory:

```text
portable/build221.py
portable/source_language.py
portable/runtime/vendor/symbolic_runtime.py
portable/runtime/vendor/independent_runtime.py
portable/runtime/reference_results/legacy_mapping.json
```

The expected hashes are pinned in `code/check_runtime_omit.py`. All imports beyond these are from Python's standard library. No original K221 table is needed.

```sh
python code/check_omit_source.py --portable K221/portable --baseline baseline/sites218.json --candidate sources/omit-zero-push.snapshot.sites.json --output /path/to/source-receipt.json
python code/check_runtime_omit.py --baseline K221 --table sources/omit-zero-push.tm --sites sources/omit-zero-push.snapshot.sites.json --output /path/to/runtime-replay
```

## Source generators and selected research results

The source-search generators accept their paths through environment variables:

```sh
export FORMALISM_PORTABLE=/absolute/path/to/K221/portable
export FORMALISM_OUTPUT=/absolute/path/to/experiment-output
python code/optimize_ksp.py
python code/optimize_ksr.py
python code/optimize_khp.py
python code/optimize_formula.py
python code/complement_quantifier_local.py
python code/optimize_complement.py
python code/retag_constructors.py
```

`FORMALISM_BASELINE` optionally selects a different directory containing the same three pinned baseline files. `checkpoint_paths.py` checks both baseline and vendor hashes. Outputs default to a `generated/` directory. The optimizer sources were changed only to make paths/output locations configurable; the historical selected outputs are preserved under `sources/` with hashes. Search ties can depend on Python set iteration order, so the stored selected source bytes, not an unpinned rerun's tie choice, identify the reported objects.

The `measure.py` and `measure_protected.py` modules provide the shared helper and experimental allocation functions imported by the generators. Their historical command-line experiment is not the entry point for this checkpoint. No failed raw transition table is placed in `sources/`.

Selected source counts:

| Source | DAG nodes | Status |
|---|---:|---|
| Omit successful-MP dummy zero |205|218-state runtime/startup replay; ordinary compiler proof|
| K/S/Peirce |206|Source experiment; no selected valid217 table|
| K/S/DNE |207|Source experiment|
| K/S/Clavius |207|Source experiment|
| K/H/Peirce |207|Source experiment|
| K/S/quantifier stability |209|Source experiment|
| K/S only |204|Logical calibration open; origin allocation218 fails prefix binding|
| Complemented quantifier, selected association |218|Source nodes, not machine states; numerical calibration and zero-run issue open|

The complemented-quantifier section proves an ordinary schema-level equivalence after deriving ex falso without circular double-negation cancellation. It explicitly leaves the numerical private-binder/matrix calibration transfer open. Generic prefix coding conditions are proof obligations, not a certificate for an arbitrary junk-code implementation.

The three-command merged-NIP/DROP experiment reaches204 source nodes but223 allocated physical states and has an unresolved proof-compiler completeness problem. The K/S source likewise must not be advertised as a217-state consistency machine.

`MANIFEST.sha256.json` identifies the archived payload. Generated output directories, bytecode caches, and the manifest itself are excluded from the manifest. The report can be integrated into the parent TeX/PDF with paths adjusted to this directory layout.
