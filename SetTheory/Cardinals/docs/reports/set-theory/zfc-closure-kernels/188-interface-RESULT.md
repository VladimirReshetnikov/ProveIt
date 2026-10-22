# Current ProveIt review, round 12

Pin: `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`, inspected 2026-10-22 UTC; 26 commits after `6f0d42d368506bc29c70ace1c992ed88b2651346`. Read-only upstream inspection and owned data-only checks; no downloaded script or proof-assistant source was executed.

## Maintained advances

- Phase11 shortens the generic dominated-implication core to 13,723 bytes / 287 lines, with 56 private steps and three public MP bodies. It retains the existing API and axiom-free generic statements. The larger six-goal shared-basis adapter is a separately placed proposal, not current adoption. Current Lukasiewicz is 524 lines / 28,731 bytes.
- Phase12 splits semantic imports into ZFModels and WFModelCore and preserves legacy WFModel/ZFNative wrappers. The exact endpoint closure drops from 192 to179 modules and selected source bytes by233,503. This is a dependency reduction, not a measured speedup or deletion of compatibility code.
- The accepted primary execution has184 providers:179 endpoint plus5 prefix modules.15 were fresh and169 source/import/object-bound reused; both unchanged endpoint clients were fresh, with10 named standard-axiom reports and no audit warnings. Compatibility separately covers67 project modules plus2 clients, with5 fresh compilations. Union199 project modules is NOT a fresh199-module build.
- Nine site batches retain checked evidence for6176 guarded outcomes; none was recompiled in phase12. No new Rocq check accompanies phase11/12.

## Independent current-byte binding

`CURRENT_BINDING.json` verifies all199 current project source bytes against phase12 current-review source hashes, and all167 archive members against its index. No mismatches. This confirms source identity with the recorded accepted run, not independent local compilation, live object validity, or a fresh replay of inherited provenance. Raw execution archive and current source files are saved under `current/` with their repository paths.

`LEAN_DELTA.json`: KSim, KRuntimeCore, KDecoderPrefix215, KSeed222 and KSeedModel222 unchanged from the prior pinned inspection. Thus semantic site-contract and direct full-seed adoption remain open.

`ROCQ_DELTA.json`: Source215.v, EnumPerm.v and DomRho8.v byte-identical to prior6f0d42d inspection. In particular Source215 still has SHA256 `2c4dbd46509125bdbd0caa38a9820d6fe4e91f551f3b0bae182a28c7daf36ec5`, not the historical normalized-91 endpoint input. Historical normalized/coqchk success must not be represented as compiling current Rocq bytes.

## Newly placed proposals and remaining opportunities

The nine batch212 packets are proposal placement, not maintained endpoint adoption. Proof Contracts is especially concrete: its29-module Lean component checks semantic KSim compatibility, prefix/suffix composition, and both branches of literal word000/decnz8. This is2 of6176 outcomes, not global suffix coverage; CheckedLeafSuffixes and source-shape obligations remain explicit. Its generic Rocq core/adapter and unchanged ThmDom client were checked with Coq8.18 namespace shims and recursive coqchk, not a full production Rocq9.1 endpoint rebuild.

Shared Proof Core and shared-implication already propose reusing the generic implication derivation for the unrestricted calculus. Do not claim that basic idea as new. Similarly semantic contracts, direct full-seed, and generic semantic bisimulation are existing proposals. Useful next work should close missing whole-family suffix obligations, consolidate duplicate model-calibration forks, or integrate a previously checked component with an exact current endpoint rebuild rather than add another unbound certificate.

## Evidence and limits

Upstream phase12 README, lean/result.json, integration/current-review.json, lean/index.json and lean/execution.tar.gz are saved. The archive records successful outer processes,20 primary warning occurrences (4 fresh preexisting linters,16 reused), and compatibility fresh logs without warnings. Collector metadata corrections and predecessor reuse are explicitly disclosed in README. The inspection does not claim a new smaller machine, lower final axiom set, internal PA proof, or performance improvement.

Scoped verification tree is complete (`truncated=false`). A missing guessed `further-interface/README.md` returned404; other inputs were obtained and no action was denied. Review scope is this pinned main and selected proposal artifacts, not exhaustive global novelty.
