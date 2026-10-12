# Integration contract

## Target

Repository: `https://github.com/VladimirReshetnikov/ProveIt`

Pinned base: `8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`.

Apply `integration/proveit-relative-top-handles.patch` from the repository root after `git apply --check` succeeds. The overlay is an alternative containing the exact final versions. No external incoming patch is required. No remote commit or push is part of this delivery.

## Change inventory

| Files under `Topology/UnknotRecognition/fast/` | Purpose |
|---|---|
| `fastunknot/normal_cut_handlebodies.py` | Invoke top reduction when the source core has three-handles; wrap the terminal proof as version 6 |
| `fastunknot/normal_cut_handlebodies_verify.py` | Authenticate the original source packet, replay top reduction independently, and compose with the prior terminal verifier |
| `fastunknot/core_top_reduction.py` | Exact cap packet, rooted linear queue, reduced geometry and trace |
| `fastunknot/core_top_reduction_verify.py` | Independent source orientation/inventory reconstruction and trace replay |
| `fastunknot/core_top_template.py` | Compile, verify, and specialize one source tree for all normal vectors |
| `fastunknot/core_forest_exchange.py`, `core_forest_exchange_verify.py` | Separate abstract graph optimization and independently checked certificates |
| Three new `tests/test_core_*.py` modules | Top adapter, universal template, and forest prototype regression/adversarial tests |
| Seven `core_top_research/*.py` files | Corpus, timing, template, forest, chain, and exceptional-kernel research reproduction |

Only the first two files existed at the baseline. The patch contains 17 files in total. Generated research JSON is supplied under the package's `evidence/`, not mixed into the source patch.

## Producer and verifier order

The producer constructs the original parallelity geometry, then reduces top handles if needed. It subsequently constructs marked boundary words from the original source packet. Existing terminal paths receive the reduced core while the original interfaces remain available.

The verifier authenticates both original source proofs before applying the top trace. It then presents the reduced geometry to the existing terminal checker. This ordering must remain explicit: the original source checker must never be asked to authenticate a modified geometry as though it were the original source output.

The strict top schema has four fields: `schema`, `input_sha256`, `moves`, and `surviving_two_handles`. Moves use original source IDs. A loop has two endpoint occurrences. Each accepted move must meet exactly one live three-handle end, and the final survivor inventory must be exact.

The whole-cut schema `normal-cut-handlebodies-v6` has the original `parallelity` and `boundary` proofs, `top_reduction`, a `terminal` payload using version 1 through 5, and the final `census`. The terminal payload has no duplicate source proofs or census and cannot recursively be version 6. No-three-handle inputs retain the prior schemas.

The original `max_operations` gate continues to refer to the existing six orbit-proof operation counts. The top stage has a separate linear source bound and uses the same interruption callback. Callback exceptions propagate. The independent top checker imports neither the cap producer nor the queue.

## Geometry and API restrictions

The current source validator accepts the one-torus-boundary entry setting. The native relative theorem protects the recorded parallelity rectangles with their full charts and collars. It does not automatically protect arbitrary inherited pattern curves crossing the cancellation support.

The homeomorphism is fixed on the protected interface. It is not claimed to fix the entire undeleted lower-handle skeleton pointwise: the attaching-disk collar moves. The surviving attaching records are nevertheless retained literally in the reduced presentation.

The default queue is retained even though the universal source template is available. Replacing one valid top policy with another can change the surviving long rows; its effect on raw completion remains to be determined on genuine geometric inputs. Benchmark any such policy change through the complete terminal consumer. The abstract matroid planner is not a proven improvement for the native short-row class; homology eliminates the apparent freedom there.

`core_top_research/residual_kernel.py` is a fixed-forest research prototype. It returns an exact source peeling prefix and residual in the forest case, with quotient/signature data. Its cycle branch is a complete-peeling obstruction certificate, not an assertion that the displayed cycle is the full canonical stopping core. Do not import it into recognition dispatch without an authenticated source-matrix and relative-geometry contract.

## Required release checks

The supplied test runner selects 67 methods in eight modules. It needs the unchanged baseline source corpus and the three fixtures listed in the main README. It also sets the working directory needed by an existing subprocess CLI test. The clean application and fixture hashes are retained in `evidence/clean_patch_apply.json` and `evidence/clean_release_fixtures.json`; successful counts are in `evidence/clean_release_check/targeted_tests.json`.

Replay the seven new whole-cut certificates with `tools/replay_saved_certificates.py`. For a full source audit, use `core_top_research/audit.py` with the pinned `synthesis/data/boundary-kernel-audit.json`. Optional `--oracle-top` makes fresh explicit Regina checks of the ten former exclusions. The audit can target an unmodified checkout through `--fast-dir` to reproduce the baseline without needing to modify that checkout.

Regina is needed for fresh subdivisions and explicit oracles. The package follows the repository's Python version requirement of 3.10 or later; recorded runs used Python 3.12.14. Research assertions require Python optimization to be disabled. Recorded exact source fixtures allow the chain/kernel experiments to be replayed without regenerating triangulations.

## Downstream reporting

Keep `COMPLETE`, `INCONCLUSIVE`, unmarked cut census, and knot verdict distinct. Report whole-query performance separately from the isolated queue. Preserve raw timings, exact work counts, source/corpus hashes, and the independent proof traces. If source-context caching is introduced later, bound cache construction and retained memory and continue to reject mutated or unauthenticated source objects.

The article, source audit, claim ledger, and research questions can be imported alongside the patch as repository documentation. Their full LaTeX sources and evidence are self-contained in this archive apart from the deliberately referenced pinned repository and third-party literature.
