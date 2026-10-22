# Thirteenth K215 proof-simplification checkpoint

The [phase-fourteen successor](../phase14/README.md) now supplies the current
shared derived/profile proofs. This page and its execution packet remain an exact
historical checkpoint. The packet's optional `--repo` check requires these frozen
phase-thirteen sources; use its historical-source mode after later adoptions.

One implication derivation now serves both the numerical and unrestricted calculi. `DominatedImplication` exports K, Peirce and S alongside its existing unrestricted-row, composition and lifting theorems. `Lukasiewicz` instantiates the same proof with domination always true, preserving its old public types and the complete Tarski bridge. The exact machine and both endpoint statements are unchanged.

The generic core and Lukasiewicz module shrink together from **42,454 bytes / 811 lines to 18,243 bytes / 401 lines**: **24,211 bytes and 410 lines fewer**. The 179-module endpoint's selected sources shrink from **2,129,439 to 2,105,228 bytes**. Its module count and the five additional decoder-prefix modules remain unchanged. The generic core itself grows by 423 bytes; core plus unchanged numerical adapter is now **16,826 bytes**, against 16,403 before this change. The saving comes from sharing the formerly separate unrestricted derivation.

The source follows the [attributed upstream `3a7a61ee97` / `49e99c5b7c` development](../phase12/upstream-merge/README.md), with [independent mathematical/API review](source-peer/review.md). Its changed suffix derives composition, exchange, prefixing and S within the same 58 MP steps. Two single-use conclusions are inlined, leaving 56 private proof lemmas and six public conclusions. The proof uses only the stated implication, derivability, MP and domination fields; it adds no bottom, truth, injectivity or stronger order assumption. The six generic theorem reports are axiom-free.

This realizes the shared-basis idea from [Sources 185 and 187](../../../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-213.md). The selected two-module layout is 164 bytes and 17 lines smaller than the held three-module adaptation, and introduces no new module. These are alternative implementations; their savings do not add together.

Two incremental Lean checks pass, each with an observed outer exit of zero:

| Scope | Fresh providers | Reused providers | Typed checks |
| --- | ---: | --- | --- |
| Primary: 184 project modules plus three API clients | 36, including 33 project modules | 151 exact phase-twelve providers | 20 API reports; two additional endpoint clients with ten reports |
| Compatibility: 68 project modules plus two old clients | 16 | 53 current-primary providers and one phase-twelve `Dag254` | Ten old-client reports and five existing `WFTheory` reports |

The scopes contain **199 distinct project modules**, not a fresh 199-module build. Changed-source descendants were recompiled even when a direct dependency's object bytes were unchanged. Every reused source, import, dependency object and raw compiler log was checked; all nine physical site batches retain their exact accepted bindings and all 6,176 outcomes.

The API reports distinguish their assumptions precisely: the generic client's seven reports have no axioms; the numerical client's five reports use exactly `propext` and `Quot.sound`; the Lukasiewicz client's first seven reports have no axioms, while completeness retains exactly `propext`, `Classical.choice` and `Quot.sound`. Both unchanged endpoint clients retain their ten exact standard-axiom profiles. The old compatibility clients retain all ten prior profiles. Every API and endpoint audit has zero warnings. Primary project logs contain 20 preexisting warning occurrences (six in freshly compiled unchanged sources and fourteen reused); compatibility logs contain seven (one fresh and six reused). There were no proof-compiler failures.

The maintained [producer successor](source-proposal/production/generate_dominated_implication_lean.py) reads pinned raw proof text and ancestry data without executing the supplied renderer. Its inference controls, four CLI modes and post-adoption default check pass; the numerical adapter remains byte-identical. [Adoption](integration/adoption.json) records the two compiled source writes, synchronized producer and derivation input, and the upstream research renderer retained as unexecuted data. Exact before-bytes remain alongside it, including the old producer/input pair. The two retired templates remain absent.

[Root's actual review](integration/root-actual-review.json), [current-source binding](integration/current-review.json), [producer execution review](integration/producer-actual-review.json) and [canonical producer check](integration/canonical-producer-actual.json) bind the adopted bytes. The compact [Lean execution packet](lean/README.md) preserves both accepted runs and their saved reviews. It retains an initial reader failure caused by expecting `Classical.choice` in the compatibility model report, the exact two-axiom correction and the successful rechecks. The proof sources and compiler records were unchanged by that correction. The source proposal and ordinary review keep their original historical statuses.

The [previous checkpoint](../phase12/README.md) remains an exact historical record. This checkpoint changes no machine, endpoint statement or Rocq production source and adds no axiom. It supplies neither an internal PA proof nor a minimum-proof-size claim. Semantic site-contract integration and primitive/return factoring remain separate work.
