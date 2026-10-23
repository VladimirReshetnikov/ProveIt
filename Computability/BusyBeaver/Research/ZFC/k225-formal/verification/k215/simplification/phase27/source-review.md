# Phase27 source review

The selected changes reuse existing proofs and share repeated local arguments. They introduce no helper declarations. All imports, computational definitions, public statements and attributes remain byte-identical to published phase26 commit `9583476366bdf2c6fd6415379bad4adfefed33bb`.

* `FirstOrder.Fol`: six inductions group constructors whose tactic bodies were identical. Lean’s documented `case tag₁ | tag₂ => tac` syntax replays the same tactic in each constructor context. The atomic, binary and binder arguments remain explicit. `Sat_rename_ext` composes the two existing semantic equivalences; `Sat_rename_relOf` uses the definition of `relOf`. The pointwise environment agreement in `closeN_valid` is inlined at its only use. Formula encoding and decoding are unchanged.
* `OrderRec`: `stage_wos` proves each image’s complete end-extension into the limit before proving that the limit is a well-order. This only uses stage membership, image well-orders and comparability, so it does not assume the desired conclusion. Its restriction and above-field clauses then serve antisymmetry, transitivity, leastness and the final result. The old repeated comparisons disappear. `step_wos` uses constructive disjunction congruences for the same field guards. Unused and one-use local aliases are removed.
* `CodeOrder`: the existing field-membership and empty-field hypotheses simplify the two relation transports directly. `tag_cw` already has both components in a positive natural stage; pairing them requires one successor. The preliminary promotion was redundant.
* `TupleOrder`: the existing `fibre_exists` theorem on the union of selected tuples constructs the set of final values. Union membership gives the exact old predicate, replacing a custom separation formula and its triple-union bound. Existing `tup_ext` handles the zero-length case. Functionality projections replace a trivial adapter, and common-prefix agreement is proved at its sole use.
* `ZFNative`: pass the existing container and collection witnesses directly through the semantic equivalence instead of unpacking and rebuilding them.

The five files shrink from 1,741 to 1,623 physical lines and 73,361 to 68,726 bytes: 118 lines/4,635 bytes removed. These are maintained-source counts, not state-count or performance claims.

`InternalWO`, `NativeTheory254` and `PSCCalibration` were also read. Their useful abstractions are already concise; no changes are forced. The generic tuple-agreement and formula-fold frameworks were declined because they add abstractions without a clear reduction. Public one-use declarations retain their compatibility role.

The full kernel check passes 230 providers and two endpoint audits with zero warnings and the exact existing assumption reports. The focused 68-provider check is diagnostic and supplies no full-run reuse basis. These proof changes preserve the 215-state machine; the internal PA endpoint and a minimality theorem remain open.
