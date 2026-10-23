# Phase27: shared formula inductions and order proofs

The full Lean kernel check and independent actual readback pass. Five proof-only edits remove **118 lines / 4,635 bytes** against published phase26 commit `9583476366bdf2c6fd6415379bad4adfefed33bb`. Imports, computational definitions, public statements and attributes are unchanged. No helper declaration is added.

Six formula inductions share identical constructor cases. The order proofs reuse complete end-extension facts, existing fibres and tuple extensionality. Native ZF satisfaction uses its existing witnesses directly. One-use local aliases are inlined; unused local work and a redundant stage promotion are removed. See the [source review](source-review.md).

| Scope | Before | After | Reduction |
|---|---:|---:|---:|
| Five edited files, physical lines | 1,741 | 1,623 | 118 |
| Five edited files, source bytes | 73,361 | 68,726 | 4,635 |
| Primary closure, project modules | 172 | 172 | 0 |
| Primary source bytes | 1,720,244 | 1,715,762 | 4,482 |

These measures overlap. `ZFNative` contributes the remaining 153-byte saving outside the primary closure; do not add the primary and five-file measures. [Metrics](integration/metrics.json) bind the exact sources.

The full check covers **230 providers**: 215 project modules and fifteen unchanged typed clients, with **140 fresh / 90 exact phase26 reuses**, plus **two fresh endpoint audits**. Thirteen clients compile fresh. All selected logs have zero warnings and the exact 93 client / 5 WFTheory / 10 audit reports match. Nine site batches, thirteen boot chunks and sixteen source-forward batches retain exact phase26 bindings. See the [Lean evidence](lean/README.md) and [independent actual peer](integration/actual-peer.json).

The focused check passes 68 providers, with 56 fresh and twelve reuses, zero warnings and no audits. It remains diagnostic and supplies no full-run reuse basis. No focused or full kernel invocation failed in this phase.

The deterministic capture and [independent archive review](integration/capture-review.json) pass. The eight proposals in user commit `56b37bde8b064d852154ad8478d58ec9ab5375d6` retain their [batch219 review](../phase24/follow-ups/batch219/README.md). The decrement-prefix experiment remains unadopted research.

This succeeds [phase26](../phase26/README.md). The machine remains **215 states**; the internal PA endpoint and minimum-state theorem remain open. No supplied checker, generator or proof ran for this checkpoint.
