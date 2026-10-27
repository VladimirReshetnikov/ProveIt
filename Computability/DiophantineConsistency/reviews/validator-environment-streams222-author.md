# Actual C222 stream selection and relabelling checkpoint

Author: `controller_certificate`, 26 October 2026. This records author implementation, full source review and private fresh leaf compilation. Independent review is separate. The approved scope is the stream-selection leaf only; accepted Substitution222, Alpha222 and every prerequisite source/object remain untouched.

## Frozen sources and results

- `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentStreams222.lean`: 140 lines, SHA256 `098224c05370ebcf8e66210278efde2cd1199d15124daddf2ecdfc1863f33194`.
- `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentStreams222Checks.lean`: 65 lines, SHA256 `925802d739555aac31e5516e66bce191befacca1c5299a1c098caabc34edcafc`.
- Detailed replay record: `reviews/validator-environment-streams222-replay.json`, SHA256 `dac381de7ae9c8f6ee9528b5314ee714931cb8f2d5169a412001169fc71c4208`.
- Final main object: `/tmp/environment-streams222-controller-k4fgo2l2/lib/ZFCinPA/ValidatorEnvironmentStreams222.olean`, SHA256 `7761dd66700da8bc578bb73a9b7e8e58aa68b8317c85ee4e852edb996b560d89`.
- Final checks object: same private directory, `ValidatorEnvironmentStreams222Checks.olean`, SHA256 `09caad632d416220a53c245d99c6c82b023e45406d0f60ca914e41deae055f79`.

Final main/check compilation PASS in 5.563 / 2.641 seconds, with peak resident memory 1,878,456 KiB. Main diagnostics are empty. All 15 focused axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The reserve of 512 MiB was checked before both compiler invocations; final recording observed 613,343,232 bytes free before writing the 437,584-byte record.

## Exact mathematical scope

The sole import is accepted `ValidatorEnvironmentAlpha222`. The previous Streams254 source was fully read and used as a guide to the parity-selector arithmetic and composition structure. It is not imported, and no CProv254 or Alpha254 semantic theorem is used.

`alternateStartDef` is fixed before model parameters, with argument order output, coarse bound, seed. It is an actual Σ0 formula whose bounded remainder witness determines the opposite-parity value `2*(bound+2)+1` when `seed%2=0`, and `2*(bound+2)` otherwise. `alternateStart_defined` proves the graph equivalence in every internal IΣ1 model; `alternateStart_sigma1` exports its definability. This is an explicit arithmetic selector, not an assumed fresh-label oracle.

`streamEnv_of_lt` bounds every stored label by its numeric vector code using `nth_le`. `streamFree_of_bounds` separately excludes fallback label1. Nonnegativity preserves these inequalities along every internal `s+2*k`. `apart_of_mod_ne` reduces any alleged shared element modulo2. `alternateStart_resources F B B' seed` supplies a new stream above `F+B+B'`, avoiding the free environment, both stacks and fallback1, and disjoint from the original seed stream. Original-stream safety is not inferred. Repeated labels, zero labels and seed0 are legal; no positivity or distinctness assumption is added.

`encode_formula_relabel` assumes a typed depth-zero source formula and explicitly assumes both original streams are free-safe. Under IΣ2, different parities use actual Alpha222 directly. Equal parities use an intermediate opposite-parity stream above F, then compose the two actual CProv222 implications in the correct directions. `encode_formula_next` applies this to s and s+2 using accepted `streamFree_next`. The focused negative check proves `¬Apart s (s+2)` from the shared element at indices1 and0; no impossible disjointness premise is supplied. `next_actual_witnesses` exposes both resulting internal History222 proof-code witnesses directly.

Checks cover seed0 and seed1 branches, repeated stored zero labels, fallback1 avoidance, equal-seed relabelling, overlapping next streams and both actual numeric proof witnesses. Neither a formula being vacuous in itself nor freshness of an Eind auxiliary label is assumed.

This packet does not establish semantic quantifier inference, arbitrary source-proof translation, CP/GIC, seed validity, consistency calibration or a proof in HA. IΣ1 suffices for the selector/resource arithmetic; the relabelling clients explicitly require IΣ2 because they use the accepted uniform Alpha222 theorem. Lean's metatheoretic standard axioms are not presented as an internal HA derivation.

## Authenticated private replay boundary

The approved source/cache proposal is `research/c222-streams222-proposal-20261026.md`, SHA256 `74c9667f235a98bb9bd8d20f23e47cd53b7b30b00e9b012e24f35db19a2600ec`. The exact closure is the `plans.streams` entry in `research/c222-substitution-opening-cache-plan-20261026.json`, SHA256 `16d3cbc7ac69f4386b9dd02cba242c98de51e79a6d0fc6cff4d029e7b9bb0c19`.

The private inventory contains **156 current-source cached prerequisites, 117 Foundation modules, 507 prerequisite artifacts and 40 explicit external primary boundaries**, including Init and Aesop. Every current import list was reconstructed with support for repeated public/private/meta import modifiers. No dependency was compiled. The accepted root Alpha222 object is `/tmp/validator-environment-alpha222-root-peer-sduorx47/lib/ZFCinPA/ValidatorEnvironmentAlpha222.olean`, SHA256 `0e905fe0fb08c3052ecfa8c46ccfc4d881e7590b677b36b5eebd8777823280e1`, bound by root record `5f2bdbc02ef0c245670402c50c0c5035ad910fccb884c02f7aa7f353c301d50b` through the pinned parent inventory.

The inherited provenance distinction remains: of the earlier 22 added Foundation modules, 20 have trace-authenticated source/four-companion evidence; two have historical successful primary-object evidence with separately recorded later companion observations. This leaf does not reclassify them or claim a fresh Foundation closure.

Private input inventory `/tmp/environment-streams222-controller-k4fgo2l2/inputs.json` has SHA256 `4ed8a9b6f2518b01ed0c8d5d029d2910f30eb3bb0ba0777ccb929426be1e81e2`. Preparation records checkout snapshot `867b3c5a24d0b7d3b09eaafbc702a658930e7d2a`; current selected source pins were checked independently of unrelated concurrent commits. All 718 final source/artifact/compiler/manifest/parent/leaf observations matched.

Compiler is `/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`, SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Lake manifest SHA256 is `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`. Each leaf used `-M6000 -j1 -DElab.async=false -o <private object> <source>`, with the exact full command, timing, log and source snapshot in the replay record. LEAN_PATH contains only the private symlink overlay followed by the explicitly recorded package roots; the shared project cache is excluded.

All new source/check lines and all adapted prepare/compile/record drivers were read before execution. Both initial leaves passed; the initial main emitted four simp-linter diagnostics. One arithmetic proof and one redundant simp argument were simplified, with no statement/check changes. The final pair passed cleanly. No compiler failure occurred. Both attempts, source snapshots, logs, timings and initial objects are preserved in the private logs and pinned in the replay record. No accepted source, shared object, shared documentation or Git state was changed.
