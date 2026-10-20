# Research navigation and verification boundaries

The requested 218-state blank-start construction was not obtained. Start with the main report and `STATUS.json` before using any table named `candidate` in the exploratory directories.

## Verified construction and initialized core

| Question | Primary artifact |
|---|---|
| What is the exact initialized218 table and its failure? | `machine/core218/construction.json`; `portable/core218_literal.py` |
| Where is its arbitrary-natural runtime proof? | `portable/check_runtime218.py`; `portable/core218_reference_results/`; `portable/audit_runtime218.py` |
| What configuration has the initialized calibration? | `machine/core218/example_initialized_configuration.json`; main report §4 |
| What is the complete alternative219 construction? | `machine/alternative219/`; `portable/reproduce_alternative219.py` |
| Were the current proofs regenerated? | `verification/fresh_release_replay.json`; `verification/fresh_core218/`; `verification/fresh_alternative219_runtime/` |
| Was the final wrapper checked? | `verification/final_quick_replay.json` and `verification/final_quick_logs/` |

## Formalism results

`research/theory218/formalism218_appendix.pdf` and its TeX source give the new fused-D certificate, the uniform fourth-slot obstruction, the terminal-cluster theorem, and the restricted emitter screens. The `research_summary.json` and `freeze_manifest.json` in that directory identify the associated evidence.

`research/theory_notes/formalism_research.pdf` contains the earlier full-model counterexamples and implicational alternatives. `encoding_family_research.pdf` treats bounded pairing, tag, binder, emitter, and related encoding families. The G/H derivation is checked by `certify_gh.py --verify-only`; its exact substitution certificate is included.

The full-model and structural-induction arguments are mathematical proofs. A finite truth-table certificate alone is not claimed to establish a model of the whole set theory. The new fused-D implication certificate is an exact derivation, but consistency calibration for the altered T-plus-explosion calculus remains open.

## Clean seeds, residue enumeration, and scheduler probes

- `research/source218/general_seed_lemma.tex` and `.md`: inherited finite-refutation argument extended to arbitrary initial candidate, additive parameter, and proof-list values with sound zero formula registers.
- `research/theory218_bootstrap/residue_scheduler.tex`: the all-powers-of-two residue/cofinality theorem, proof, sound fixed-stride scheduler, costs, and limits.
- `research/theory218_bootstrap/certify_residue_schedule.py`: checks the polynomial pairing identities and finite diagnostic consequences. The unbounded theorem is proved in the TeX text by valuation arithmetic.
- `research/theory218_bootstrap/FINALIZED_SCHEDULER_FILES.json`: exact frozen scheduler files, hashes, and claim boundary.
- `recheck_scheduler_artifacts.py` and `replay_loader_entry_screen.py` in that directory: development checkers for source shapes and failed startup/entry traces. They may expect extracted worktree baselines. None of the exploratory scheduler tables is accepted.

## Source transport and allocation

`research/source218/SOURCE218_REPORT.md` is the final source-side report. The corresponding `SOURCE218_CURATED_FILES.json` records the intended research selection; `DISCOVERY_FREEZE.json` records the end of discovery work.

`research/source218/transport_replay/` is a standalone compact experiment. It includes 16 literal input tables, direct-role descriptions, the C++ generator, pinned reference counts, and `reproduce.py`. Its full staged replay is in `verification/transport_full_replay.json`. It checks a finite startup family, without asserting a universal compiler-correctness theorem for every generated register transport.

The concrete logical-register-2/8 transport is retained under `research/source218/rename28/published/`: five selector-row changes, 32 representative arbitrary-natural primitive interfaces, and an explicit startup failure. Those representative interfaces do not replace a full 6,167-case proof for that exploratory table.

Source allocation and coordinated repair scripts outside the compact package retain development imports and original baseline-relative paths. Receipts distinguish completed pair families from two timeouts in the 124-result expanded batch.

## Machine synthesis and residue evidence

`research/machine218/SEARCH_REPORT218.md` and `final_local_synthesis_receipt.json` identify the final local-synthesis inputs, hashes, completed searches, and timeouts. The five completed radius-10 families fix old/new path bounds 50/128; the unrestricted eight-row search is incomplete. These are not arbitrary-machine lower bounds.

`research/root218/` retains the joint-residue invariant, its closure auditor and binary certificate, local reductions, comparator material, and bounded bootstrap searches. The joint abstraction is a sound overapproximation; it yields no additional dead branch beyond the retained product invariant. Interrupted two-row repair batches are explicitly partial.

Several proposed bootstrap row changes reach plausible clean frames on the blank run but corrupt ordinary primitive semantics. Their concrete counterexamples are retained. Such a startup success does not make a complete machine construction.

## File integrity

The top-level `MANIFEST.sha256` is the delivered inventory. Portable reconstruction also verifies its own exact `portable/manifest.json` and the unchanged nested K219 archive. Frozen research manifests may use original worktree-relative path names; their files are curated under `research/` in this archive.

No claim is made that every exploratory script is a polished standalone library, that every discovery search was exhaustive, or that this packet includes a new proof-assistant theorem for the final machine bytes.
