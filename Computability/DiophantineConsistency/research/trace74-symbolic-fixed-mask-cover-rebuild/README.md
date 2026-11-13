# Held structural symbolic fixed-mask cover check

The first one-stage author check was deliberately terminated after a proof gap was identified; no theorem was accepted. The [source-reviewed](../../reviews/trace74-symbolic-fixed-mask-cover-draft-independent/README.md) draft proposes `betaNat+1<=lowNat+highNat` both on naturals and in each IΣ₁ model, using bounded defect digits and a positive high digit rather than full 590,069-bit `decide`. It does not itself establish a 74-zero no-carry condition, fixed-port guard, graph equivalence or iPRA statement.

The [audited parent](../../reviews/trace74-conditional-saturation-guard-result-independent/README.md) provides 2035 project objects; preflight checks 81 outside objects and one stage, with prior captured closure guards. The four retained baseline source-ancestry limits, outside/package/dynamic and external-file boundaries remain. Two ordered named axiom reports are required; optional line-wrapped axiom lists may contain only `propext`, `Classical.choice`, `Quot.sound` and no duplicates. Any other stdout, stderr, warning, error or `sorryAx` fails.

- Runner SHA-256 `c369649eb30d2f35b00e47a6680253bed09d133e8f9530467462fdd70f11fc5a`.
- Outer supervisor SHA-256 `6e89185691ac0c2221f7da6fb03c59ff29d1e224672795bbbd94cae7ca62722a`.
- Read-only preflight terminal SHA-256 `7c5a0ec332e2e70028e941bc5d33eb8a305ee3dfebceb8a8e95d7f76bd83cd6b`.
- Twenty-five policy controls SHA-256 `2de0b7a8be528c41b9cf522b08a8e349a301e87b16e30356ea660a903b82eba8`.
- Six supervisor controls SHA-256 `14900d26ddf97dc0d69a9b6ffa04d3638e32485ce5aabc485f1fbe002000d6a8`.

The [prelaunch review](../../reviews/trace74-symbolic-fixed-mask-cover-prelaunch-independent/README.md) gave scoped GO. During attempt01, source inspection found `cover_nat` retained only `defect <= high`, whereas the low identity has an additional `+1` and requires `defect < high`. On the parent coordinator's instruction the Lean child received SIGTERM; the signal command exited 0, the runner recorded child exit −15 and no internal timeout/resource reason after about 363 seconds, and actual outer session 66554 exited 1. Child result SHA-256 `1494e1bb37bbeac854d7e3160a9cae4a91d1db45fa2f0de394c1a54243c0876a`; outer terminal SHA-256 `d07f58779a801a0ab0634e4563ea96177e7ad79afa56616e7b57f2b7d16880d4`; both stage logs were empty. The separately captured operator observation `observations/attempt01/manual-stop.json` SHA-256 `bd549e4735d23b5bc1b687c6046b3ea698e6359b9d150f0ca05e210388832a0d` records the signal and observed exits. No Lean theorem was accepted and no timing identifies a particular expensive lemma.

A separate [v2 source correction](../trace74-symbolic-fixed-mask-cover-draft-v2/Trace74SymbolicFixedMaskCover.lean) keeps the strict bound; a [non-expanding split plan](../trace74-symbolic-fixed-mask-cover-split-plan/README.md) isolates support, high-list, abstract arithmetic and casting. Neither has been Lean checked, and both require independent review and a fresh pinned runner.

The [independent factual audit](../../reviews/trace74-symbolic-mask-stop-v2-independent/README.md) verified the captured child/outer status and empty logs, distinguished the operator's signal observation, and reviewed the separate strict v2 correction. No Lean theorem was accepted.
