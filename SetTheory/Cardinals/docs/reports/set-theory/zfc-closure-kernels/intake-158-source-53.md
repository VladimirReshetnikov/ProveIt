# Intake 158, source 53: permutation252-reduction-study

Reviewed 17 October 2026 against current working tree at HEAD `80e26b89e905bf3e5dfc322befdc1c6eaf25a109`. Delivered root: `/tmp/zfc-intake-158/permutation252-reduction-study/permutation252-reduction-study`. Manuscript pin: ProveIt `43026ff42f0939f09b9e95495248cfadcad38e38`; original Mira/Jeff/Wade snapshot `297ab8df7e5de329605c3875b4934643b371a5e3`; mira-emmy PR20 head `0d544f2a2e3c18f12278441a74b7879f31cbe856`.

**Disposition:** useful research evidence, without a smaller consistency machine. The completed two-incoming full-action search and three-incoming target search extend current recorded partial/limited searches. The ordinary affine-coding and first-falsity-production arguments are mathematically useful under their stated hypotheses. Their costs are measured against a 281-state complete Wade-backend control, not against the separately optimized 252-state table. The report repeatedly preserves that distinction. Its 254-state tag-swapped runtime is a conditional control, not a new initialized consistency endpoint.

## What was read and checked

Read the complete `report.tex`, all substantive included sections (`results`, `higher_degree`, `codec_mapping`, `semantic_proposal`, and reproduction), README and attribution; inspected the portable wrapper and complete selected phase/affine/semantic drivers plus their relevant imported Python paths before execution. Source identity of `report.tex`: `259ae900fc7e14a3502bfb69978b8656ab0d57d2a4ab4c9a85f9eff6ad9c76a8`; wrapper: `27a25621730d8124f158f994d22850e2a9f84c984c725658f0a386fa878733ba`.

Executed only bounded Python experiments on a fresh separate copy `/tmp/zfc-intake-158/run-53`; outputs are `/tmp/zfc-intake-158/replay-53`. No delivered files were changed. No Lean, Coq, Lake, compiler version, dependency build, C++ build, manifest verification or large search was run. The Python Wade routine generates finite transition tables in memory; it does not launch a compiler executable. The proofs and search-completion claims not listed as replayed below remain source/evidence review, not fresh execution.

## Model and mathematical contents

The target is a deterministic one-tape, two-symbol, two-way-infinite-tape machine with L/R moves and entirely blank input. Working-state counts exclude halt. The baseline is the maintained canonical 252-state/504-row table (`8dae0c…0797`), not the rejected historical raw equality-free candidate. Original labels omit5 and8, start64, dispatch96, halt254. Canonical start/halt are0/252. The logical-to-physical permutation is `(6,2,0,4,3,7,8,5,1)`. The reported literal 82,552-step blank prefix, full tape and protected55 rows agree with the maintained benchmark description; this review did not repeat that baseline suite.

The deterministic search-prefix pruning argument is correct for the stated diagnostic: before reading an unassigned row, every completion has the identical trace. A completed diagnostic failure therefore removes a whole subtree of assignments; weights and frontier can be audited separately. This does **not** turn fuel exhaustion, unsupported box operations or unknown run length into semantic counterexamples. Reusing already completed cases is justified only when their exact traces did not read unassigned rows; interrupted cases are restarted.

Formula constructors use affine progressions `m*P+t`. Pairwise disjointness is exactly `gcd(m,n) ∤ (t-u)`. A total decoder can send holes to truth, but then an encode/decode inverse cannot be asserted on arbitrary numeric holes: soundness on all numeric inputs and completeness on genuine codes remain separate obligations. The additive proxy lower bound is sound: four disjoint progressions have sum reciprocal moduli at most1, hence sum moduli at least16 by Cauchy; distinct nonnegative offsets sum to at least6, so total at least22. Equality gives the uniform four residues. This is a lower bound on that proxy, not on shared DAGs, total TM states, runtime or every conceivable coding.

The MP first-production theorem requires falsity-free derivable initial entries; non-MP/failed-MP transitions preserve derivability and cannot introduce first falsity; successful MP derives its output; old acceptance observes falsity and is complete for derivability; changed commands agree until first successful production. Under these explicit hypotheses, moving acceptance to the first successful MP production preserves halting. Intermediate arithmetic values may equal1, so detection belongs at command boundaries. Falsity cannot simply move to0 because the retained machine uses0 as default/truth. The deterministic-MP control unpairs H/4, checks H mod4=0 and antecedent=T, returns consequent or0, clears the named scratch fields and preserves W/D. The H=T=0 truth-alias case is accounted for.

The 25 refined natural-value domains are finite products of exact0…K−1 plus periodic tails. The decrement transfer includes K−1 when crossing the tail boundary and otherwise safely overapproximates; initial inclusion and every enabled edge are checked after convergence. All domains retain the known six exclusions only. Possible guards are not claimed concretely reachable.

## Results and novelty boundaries

- Two-incoming targets:46×251²=2,898,046 assignments,185,033 partial nodes, empty frontier, no survivor. The Python/C++ node comparison covers all those nodes in the supplied evidence. This is the same completion separately delivered in source55; count it once in intake158.
- Two-incoming complete actions:46×1008²=46,738,944 assignments,2,995,822 nodes,5,891,454 attempts including2,972 interrupted attempts; complete with no survivor. Current source50 had only partial evidence for this same recipe family, so this is a completion, not an additional disjoint family.
- Three-incoming targets:19×251³=300,451,769 assignments,1,959,576 nodes,2,544,094 attempts; complete with no survivor.
- The1,472 independent Python failure replays sample32 entries per deletion label. They are a sample, not exhaustive semantic replay; support/write/direction/target categories can overlap.
- Larger searches remain partial: three-incoming actions leave15,283,724,115 of19,459,657,728 assignments, frontier1,755; target-only degrees4–9 leave4,001,507,399,054,136,275,604 of4,001,507,403,120,269,470,525, frontier854. Their enormous assignment weights are not executed candidate counts. All degree4 groups and four degree5 groups finish; higher groups remain. Families overlap and must not be added.
- The packed event ledgers represent114,517,735 events/3,928,283,950 uncompressed bytes. These `.ledger.gz` files are a special packed DFS encoding, not ordinary gzipped TSV. This review did not rebuild the native unpacker or replay these ledgers.
- The affine census examines5,432 allowed assignments through modulus12. Minimum complete Wade-backend count281; baseline and All/Eq tag exchange are tied. Six four-tag permutations cost281,281,282,282,283,283. Most assignments use a justified exact DAG/depth cost formula; actual table generation/reextraction checks representatives of each depth and selected winners, not all5,432 literal generations. Raw561 rows are totalized to562 without a new state by adding the documented unreachable row.
- Optimized All/Eq exchange maps4,533 unfolded leaves,115 Imp/17 Rel/24 of25 All subtrees and no whole Eq subtree. The modified optimized program has205 versus203 nodes; a3-state addition and deletion of unreachable old233 yields254 working states/508 rows. Its8,408 conditional guards and56,419 uniform-fold screen are reported supplied evidence, not rerun here. Two cheaper reassociations fail context/guards. No new blank bootstrap or consistency calibration is claimed.
- Five MP-birth controls cost281/284/285/284/285, and deterministic MP costs302/305. The latter has2,178 finite controls per variant. These negative costs do not authorize subtracting a backend delta from252. Dual/primitive-bottom controls similarly provide no new calibrated machine.

## Fresh functional replay

Commands executed from `/tmp/zfc-intake-158/run-53`, with assertions enabled:

```sh
python3 -B reproduce.py phase --out /tmp/zfc-intake-158/replay-53
python3 -B reproduce.py semantics --out /tmp/zfc-intake-158/replay-53
python3 -B codecs/affine_codec_search.py --max-modulus 12 --output /tmp/zfc-intake-158/replay-53/affine-codecs.json
```

All exited0. Phase took23.444s and matched the complete supplied JSON except elapsed time:25 certificates, each with6,456 possible leaves,8,384 enabled nonhalting edges and the same six exclusions. Semantic jobs took11.794s and5.008s;17 comparisons passed, covering the regenerated semantic records, DAGs and transition tables, with only relocated source-path normalization. The complete affine census took64.595s; a separate comparison matched every JSON field except seconds and exact generated table bytes. Its selected table has281 states and SHA `c65761a61b35598945e47a9902137d882ba70c1e5bde34e72b6069ba60d5316e`.

Receipts: `replay-53/phase/reproduction.json`, `replay-53/semantics/reproduction.json`, `replay-53/affine-comparison.json`; child logs are under each wrapper output directory. The manifest-only `verify` command was deliberately bypassed as required by intake procedure.

## Current-tree reconciliation

Paths below are relative to the reviewed repository root `/home/codex/.codex/worktrees/ec20/Proofs`; line numbers refer to the current source read during review.

1. `Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md:7` and `:134` identify the already closed external endpoint; `:156` distinguishes remaining arithmetic translation. `choice_calibration254.md:3` and `:16` close the external ZFC comparison without an outstanding Choice/V=L/model premise. The report correctly treats those as completed prior work, not a theorem newly furnished by Python.
2. `Computability/BusyBeaver/Research/ZFC/pa_internalization.md:9` explicitly says the active user goal is **PA**. Both this report and source55 state a ZFC-provability goal instead. Their weaker target must not replace the user's requirement. `pa_internalization.md:95` retains reverse proof translation, internal L-schema and full interpreter-to-Enum as major open steps. An ordinary ZFC-formalizability argument is not the requested PA derivation.
3. `permutation252_lazy_context_search.md:37`–`:42` records the old989,497-assignment/247-frontier partial target2 run; the supplied completion extends that record. Current corpus `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-157-source-50.md:27` records10,845,350 of46,738,944 full-action assignments pruned with1,093 frontier nodes; `:31` records a second timed prefix. Source53 completion supersedes this partial coverage for the matching family, rather than adding a new46-million-family count.
4. `permutation252_phase_analysis.md:36`–`:60` already has the same six exclusions and the ordinary unbounded source-invariant argument. Richer domains are new analysis, six exclusions are not new discoveries.
5. The internalization route has advanced beyond the report pin: `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentAlpha254.lean:296` supplies all-internal formula alpha transport; `ValidatorEnvironmentStreams254.lean:114` and `:132` now give concrete arbitrary-start and next-stream transport. `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticControlMP254.lean:510`, `:543` and `:579` now supply the exact complete MP endpoint and dispatcher contract. The roadmap text at `pa_internalization.md:65` and `:92` still describes these two recently completed local obligations as open; use the maintained declarations for those precise interfaces. None completes full reverse proof compilation, AX, hSchema or PA machine equivalence.

## Useful next work

Prioritize semantic certificate improvements over repeating covered local-action families. Source55's matrix-valued binary countdowns directly address the constant-offset limitation left by source53; combine their specific remaining-case records with this larger search coverage. For coding research, choose a joint operation change whose complete engine, register lifetime, delimiter and blank initializer can all be measured together. The independent modulus/first-production arguments are useful filters, but isolated formula lengths or local DAG savings cannot support a state bound. A command-boundary simulation with exact live fields, valid existential spare suffixes, positive progress and a complete initializer remains the appropriate acceptance test. Preserve the active PA target alongside the external consistency endpoint.

Attribution/licence boundaries are correctly retained in `THIRD_PARTY.md`: no repository-wide licence is asserted for the inherited busy-beaver snapshot; Wade's separately licensed backend and ProveIt's new contributions remain distinguished. No claims of sub252 success, whole-program semantic lower bounds, newly checked Lean proof, or exported internal ZFC/PA proof are warranted by this intake.

Publication note: the countdown cross-reference is corrected to source55; the [numbering erratum](intake-158-source-53-erratum.md) preserves the original review correction.
