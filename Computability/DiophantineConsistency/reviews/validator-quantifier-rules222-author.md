# Actual C222 finite quantifier rules

Author: `controller_certificate`, 26 October 2026. This records implementation, complete source review and two private fresh compilations. Independent review is separate. The accepted encoder, substitution, streams, alpha and other prerequisite sources and objects remain unchanged.

## Frozen results

- `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorQuantifierRules222.lean`: 123 lines, SHA256 `6f1ad9c1d95546d712311a39bd8f4c35ea9f28d8d2d27738320573576e46ae81`.
- `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorQuantifierRules222Checks.lean`: 62 lines, SHA256 `92e2c937dc04632b7edf495a24c6f6bee6875b66af6d8e1a32f9213cd8ab73bd`.
- Replay: `reviews/validator-quantifier-rules222-replay.json`, SHA256 `077b0f60acb44678f7dc51f87d3073c95703d6750e3ebce847fa0f393b91667f`.
- Main primary: `/tmp/quantifier-rules222-controller-ixe8gflf/lib/ZFCinPA/ValidatorQuantifierRules222.olean`, SHA256 `225dc6df8a8b725cf8faba8b562acdd4191e3e0057be23fae30b04828c88f32f`.
- Checks primary: same directory, `ValidatorQuantifierRules222Checks.olean`, SHA256 `1e73a67ccad0524a27ef9030869768ac2a44afef18ef0b4eef2cc6ecad74f51e`.

Both leaves passed their first compilation, in 3.536 / 2.457 seconds. Main diagnostics are empty. All 13 focused axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. Peak resident memory was 1,874,196 KiB. The 512 MiB free-disk guard passed before each invocation; final recording observed 606,932,992 bytes free. No failed preflight or compiler attempt occurred.

## Exact finite inference

The only direct imports are actual `ValidatorEnvironmentStreams222` and `ValidatorEnvironmentSubstitution222`. Let `x = alternateStart F s`, let `P` be the actual encoding of `free p` at free environment `x∷F`, empty bound stack and stream `s`, and let `A` be the encoding of `∀p` at `F`, empty bound stack and stream `s`.

Under IΣ1, `fresh_resources` constructs the resources for this particular x. It retains the explicit original assumption `StreamFree s F`. Opposite parity gives x's avoidance of the whole original stream, while x exceeds all stored free labels and fallback1. Exact cons lookup reasoning proves `StreamFree s (x∷F)`. For the new stream x+2, accepted stream advancement handles old labels and the inequality x<x+2 proves avoidance of the newly stored head. No bound of the form `x∷F < x+2` is asserted. Repeated or zero stored labels and original seed0 remain legal when the stated original-stream safety holds.

Under explicitly stated IΣ2, `opened_body_equiv` transports the typed depth-zero source opening between streams s and x+2 with the same extended free environment. The actual numerical `encode_all_opened` identity binds the latter body under `wal x` to encoding the original ALL at stream x. Formula relabelling then returns to stream s. `all_opened_equiv` therefore constructs actual CProv222 witnesses for both `wal x P → A` and `A → wal x P`.

`ex_opened_equiv` makes the analogous two object-level implications for the existentially quantified body. It uses the actual encoded existential operation, its monotonicity, and the exact source-opening identity. It does not claim instantiation at an arbitrary source term.

`all_rule` obtains `A` from an actual proof of P using actual C222 generalization followed by the forward implication. It never asserts the generally invalid object implication `P → wal x P`.

`all_rule_under` retains a hypothesis H only with its actual `Vac x H` certificate. Its finite deduction is `H → wal x H → wal x P → A`. The guarded single negative source-hypothesis client uses the exact numerical source shift identity to replace `encode (x∷F) 0 s (shift A)` by `encode F 0 s A`; actual typed environment vacuity and `vac_neg` then discharge the guard. Its input remains a proof of the displayed implication, not a premise claiming the desired conclusion or unrestricted hypothesis generalization.

The focused checks expose actual internal `ArithmeticHistory222.value` proof-code witnesses, a truth context, fallback1 avoidance, zero original seed and the shifted negative source-hypothesis client. All formula transport uses actual CProv222 and the accepted Eind-based encoder. No implication from Eind back to primitive equality is used, nor any primitive-equality vacuity oracle or self-vacuity premise.

The complete old R2Quant/R2Main and relevant opening/instantiation source contracts were inspected as guides to the source calculus. Their CProv254 semantic proofs are not imported into this new leaf. The inherited syntax-only Substitution254 dependency keeps its accepted historical provenance and is not represented as a new semantic result.

This packet does not prove the source EXS term rule, an arbitrary context fold, arbitrary source-proof translation, CP/GIC or seed validity, the full consistency calibration, or an HA derivation. The object calculus used here is the actual internal C222 checker. Lean's three standard metatheoretic axioms are reported rather than identified with a proof in HA.

## Replay and provenance

Approved outline: `research/c222-quantifier-rules222-proposal-20261026.md`, SHA256 `c88a1b0f7995caa16775d60f9a675972beedfba2e646fdde240f79caa8520528`. Approved cache plan: `research/c222-quantifier-rules222-cache-plan-20261026.json`, SHA256 `214674a0f44f8aec74f22ac6fc110862b9767572eaad994c36b487221aed3d1b`.

The private cache reauthenticates exactly **159 current-source cached prerequisites, including 117 Foundation modules, with 510 artifacts and 40 explicit external primary boundaries**. Every selected import list is reconstructed, including repeated public/private/meta import modifiers. The boundary includes Aesop. No prerequisite or Foundation module was rebuilt. The earlier distinction between 20 trace-authenticated added Foundation modules and two historical-primary/later-companion records is preserved; no broader fresh-closure claim is made.

The selected accepted root providers are:

- Streams222: `/tmp/validator-environment-streams222-root-peer-3wkkdg1f/lib/ZFCinPA/ValidatorEnvironmentStreams222.olean`, SHA256 `7761dd66700da8bc578bb73a9b7e8e58aa68b8317c85ee4e852edb996b560d89`, root record `8c92ebd1aaa4b4a960f1e74e349831d10351b38fe781b2d945a4db7bda32fbc1`.
- Substitution222: `/tmp/validator-environment-substitution222-root-peer-l0pz7nuu/lib/ZFCinPA/ValidatorEnvironmentSubstitution222.olean`, SHA256 `99f58288809049cc943f25f7d31b6755e8faec3aadca5732890896cf39a090fc`, root record `b025af75cdc63b67d75f0cefae28267ea809f554d3e30b72765dd06b2ea13af2`.

Private `inputs.json` has SHA256 `81e14436bce94aa9010e7feaa6fbe386a3aaec7e2b058e7742d637702efb5ebf` and records checkout snapshot `a3350ad0e6a2cf95bd6995d7c8e2e7e434a5a044`. Selected source hashes, rather than assumptions about concurrent unrelated commits, determine reuse. All **732** final source/artifact/compiler/manifest/parent/guide/leaf observations matched.

Compiler `/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean` has SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; Lake manifest SHA256 is `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`. Each command used `-M6000 -j1 -DElab.async=false -o <private object> <source>`. LEAN_PATH contains only the private symlink overlay plus recorded package roots, excludes the shared project cache, and LEAN_SRC_PATH is removed.

All new source/check lines and all prepare/compile/record drivers were read before execution. The replay embeds the drivers and exact run metadata, including source snapshots, commands, empty main log, complete check reports and timing files. No accepted source, shared object, shared documentation or Git state was changed.
