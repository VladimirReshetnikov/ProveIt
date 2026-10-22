# ProveIt current-source review, round 13

Pinned repository: `VladimirReshetnikov/ProveIt` at `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`, compared with `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`; inspected 2026-10-22 UTC. There are 26 intervening commits. No repository change, push, received script execution or proof-assistant execution was performed.

## Main finding

Two substantial K215 refactorings are now maintained, not merely proposals. The accepted project scope has nine modified Lean sources and one retired source (`KProfileTC`), totaling **36,327 fewer bytes and 653 fewer lines** than round 12. The endpoint closure falls from **179 to 178 project modules**. Separately, the latest two commits simplify K217, not K215. Do not aggregate K217 savings into the K215 endpoint total.

1. **Phase 13: one implication derivation for both calculi.** `DominatedImplication` exports K, Peirce and S in addition to unrestricted rho8, composition and lifting. `Lukasiewicz` instantiates the domination relation with `True`; it preserves the Tarski bridge. The two modules shrink from 42,454 bytes / 811 lines to 18,243 bytes / 401 lines. The generic core grows from 287 to 300 lines; unrestricted `Lukasiewicz` falls from 524 to 101. These are net pair savings, not independent additive reductions. The six public generic conclusions are reported axiom-free. The canonical producer and derivation input were synchronized, while the supplied research renderer remained inert.

2. **Phase 14: shared derived rules and transitive-container profiles.** `TarskiDerived.Rows` supplies the quantifier and atomic rewriting interface for both `Thm` and `ThmK`, with propositional support explicit as `hC`. Equality-free, quantifier-free, binder and freshness premises are retained. Six profile contracts use `TransContainers` directly; stronger `Containers` specialization remains. Seven source replacements and retiring `KProfileTC.lean` save 12,116 bytes / 243 lines; the retired generator adds a separate 3,067 bytes / 71 lines. This is the adopted implementation, not the later quotient/dense proposals.

3. **K217 AX macro word (`ab6ceabe32ee`).** `L2AxiomsDom` now uses the checked-word template already used by K215's Perm lane: 1,196 to 161 lines. Its generator falls from 487 to 215 lines; Perm output is reported byte-identical. Public `f236`, `l236`, `c236`, `ax_eval` statements are preserved. The commit reports serial checks of 18 stale modules ending at `L2RootDom`, explicitly not `SeedDom` or `KEndpoint217` at that stage.

4. **K217 generalized enumerator (`6d9800d1ca67`).** `EnumDom.halts_iff` starts from any between-candidate state satisfying `Inv`; `SeedDom.seed_iff` is its instance. EnumDom grows 699 to 711 lines, SeedDom shrinks 108 to 44, and L2RootDom shrinks 250 to 208, a net 94-line saving. The obsolete zero-state route and 209-line EnumDom generator are removed. The commit reports checks of EnumDom, L2AxiomsDom, L2RootDom and SeedDom, explicitly not the stale machine-specific `KEndpoint217`. These two commits contain no new raw compiler receipt files; their local-check claims should not be described as an independently archived final endpoint rebuild.

## Exact receipt scope

Phase 13 selected 187 primary providers (184 project modules plus three API clients): 36 fresh and 151 exact phase-12 providers. Its separate compatibility scope has 70 providers: 16 fresh, 53 primary reuses and one phase-12 reuse. The union is 199 project modules, not a fresh 199-module build.

The current phase-14 primary has **190 providers**: 178 endpoint project modules, five extra decoder-prefix modules and seven API clients. Its **66 selected fresh records** comprise 65 successes from the first attempt and one corrected client from the retry; 124 records are exact phase-13 reuse. Both unchanged endpoint clients were freshly compiled separately, with ten named axiom reports. Compatibility has **70 providers**: 68 project modules plus two clients, with 16 fresh, 53 current-primary reuses and one phase-13 reuse. Their union is **198 project modules**, not a fresh 198-module compilation.

The first primary attempt failed in `ProfileTC14Api` because three implicit binders were missing in a structure-field implementation. Its failed record has exit 1, no object hash and `sorryAx` in two reports. The accepted retry uses different client source bytes, exits 0 and excludes those failed reports. No production theorem/source changed to fix this client. Do not mistake the retained failed log for an accepted admission, or relabel the failed attempt as successful.

The seven API clients supply 34 reports: 20 prior profiles and 14 new profiles (one axiom-free, five using only `propext`, eight using `propext`, `Classical.choice`, `Quot.sound`). The two endpoint clients retain ten reports; compatibility clients ten more, with five WFTheory facade reports separately. Accepted endpoint/API clients have no warnings. Project logs contain 20 primary and seven compatibility warning occurrences, explicitly preexisting rather than new proof failures.

All nine physical-site batches and their 6,176 outcomes retain exact inherited evidence. They were **not rerun** in phases 13 or 14. No Rocq production compilation accompanies these checkpoints.

## Independent byte and record checks performed here

`CURRENT_BINDING.json` binds **all 198 current project sources** to the exact phase-14 source hashes, with no mismatch. Phase-13 archive **270/270** indexed members and phase-14 archive **309/309** indexed members match their saved hashes and lengths. Archive hashes also match the result records.

`OWNED_REPLAY.json` additionally checks selected ledger PASS statuses and origin counts, separation of the failed and corrected profile client, and both raw endpoint audit logs against their recorded hashes. The logs have ten named reports, successful recorded exits, no warning and no `sorryAx`. These are independent data-integrity and receipt-scope checks. They are **not** local Lean compilation, proof verification, validation of live object bytes, or a fresh replay of all inherited provenance.

Offline owned replay: `python research215_round13_review/replay_bytes.py`. It resolves paths relative to its own file, rejects Python optimization, reads only saved data, and executes no received scripts. It reconstructs the comparison against `phase14/integration/current-review.json` rather than trusting only the derived summary. The earlier fetching/audit scripts are acquisition provenance, not required by this replay.

## Maintained versus proposal-only

`SOURCE_DELTA.json` confirms these current Lean sources are byte-identical to round 12: KSim, KRuntimeCore, KDecoderPrefix215, KSeed222, KSeedModel222 and KDenseBridge. Accordingly:

- Semantic residual coverage, even if a separate component covers all 6,176 guards, is not yet the maintained KSim/KSites endpoint route.
- Direct full-seed calibration is not yet adopted in KSeed222/KSeedModel222.
- The stronger absorbing KDenseBridge invariant remains a proposal, despite an intermediate commit presenting it as an adoption. The later merge expressly holds it outside the checked production sources.
- The quotient syntax and QHyp unification development also remains separate. The phase-14 later-406c merge states that maintained Lean sources and generate_kq1.py are preserved pending a separate kernel check. The current proposals catalogue names the later 25-module QHyp proposal; that component check does not extend the exact K215 endpoint receipt.

Maintained Rocq `Source215.v`, `EnumPerm.v`, `DomRho8.v` are likewise byte-identical to the prior review. Source215 remains SHA256 `2c4dbd46509125bdbd0caa38a9820d6fe4e91f551f3b0bae182a28c7daf36ec5`. Historical normalized-91 / Coq 8.18 checks and newly placed generic-core/scheduler components must not be presented as a current full Rocq 9.1 endpoint rebuild.

For further shortening, do not propose the now-adopted common implication core or common named-calculus derived rules as new work. The next useful milestone is to select one already checked component, integrate its exact adapter into the maintained lane, and recheck the affected endpoint closure. The most material open gates are the full semantic residual endpoint adapter, current-source Rocq shared-core/source-proof adoption, and calibration/quotient dependency consolidation. A small dense-invariant adoption is a distinct low-scope option, not a global runtime-proof replacement.

## Source scope and limitations

`COMPARE.json` is a GitHub comparison capped at 300 changed-file entries; it is **not an exhaustive changed-file inventory**. The scoped verification tree has 6,957 entries and `truncated=false`. The complete Lean ZFC Git tree has 2,205 entries and `truncated=false`; it confirms KProfileTC is absent. The formal directory confirms both retired generators are absent. Its separate Lean Contents listing was capped at 1,000 and is not used to infer absence. Source binding covers the precise 198-module accepted project scope; selected current files and proposal/merge READMEs were inspected. This is not an exhaustive global novelty search.

Several guessed top-level Rocq/QHyp/PowerSets paths returned 404; actual Rocq paths were recovered from the previous pinned source inventory and read successfully. No action was denied. No smaller machine, lower endpoint axiom set, internal PA proof, minimal proof, or measured global speedup is established.

Primary links:
- [Pinned phase 14 checkpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase14/README.md)
- [Pinned phase 13 checkpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase13/README.md)
- [K217 AX change](https://github.com/VladimirReshetnikov/ProveIt/commit/ab6ceabe32ee)
- [K217 enumerator change](https://github.com/VladimirReshetnikov/ProveIt/commit/6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95)
