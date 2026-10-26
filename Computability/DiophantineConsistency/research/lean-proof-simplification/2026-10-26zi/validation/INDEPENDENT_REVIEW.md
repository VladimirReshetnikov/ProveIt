> FINAL NOVELTY OVERRIDE: H1/H2/B1 are superseded comparison evidence, not new proposals. See `../late_review/` and the final report. This original source-only review does not incorporate the late novelty screen.

# Independent semantic, novelty and source review

## Result

**All four narrow proposals retained, with no source-level mathematical defect found. All Lean remains uncompiled.** Four patches reproduce five full modules and reduce their physical total **784 → 758 (26 lines)**, including both new helper declarations/documentation. The all-applied baseline is semantic, not a compiled composite checkout; the numeric saving is the literal incremental patch against the pinned current source, not a measurement of that hypothetical checkout.

The independent suite passed **60 tests**; the candidate author's helical suite passed 10 tests; bridge author static/model checks passed. All **914 selected sources, 6 dependencies, and 11 comparison sources** match their recorded Git-blob and SHA-256 values before and after disposable replay. Active source coverage is **637 Lean files**, and the 39-file active delta replays exactly. Four patches compose without overlap; outputs equal the five supplied full modules. Three generators reproduce all 21 designated outputs byte-for-byte.

## Mathematical review

### H1: signed helical row-zero transport

The hypothesis is exactly `Periodic (fun p : ℤ × ℤ => T p.1 p.2) (w,-1)`. The pinned Mathlib `Periodic.zsmul` theorem accepts any integer multiple in an additive group. At `(x,t)`, the multiple `t` sends the point to `(x+t*w, t-t) = (x+w*t,0)`; symmetry has the original orientation. The public theorem keeps arbitrary signed `w`, `x`, and `t`, including zero and negative width/time. No finiteness, positivity, modulus, or actual-machine premise has been added. The existing source already uses another theorem from the same Periodic API; no new import is claimed.

Residual elaboration risks: product addition/scalar projections at `change`, integer normalization in restricted `simpa`, and elaborator inference. The bounded model explicitly tests signed/zero-width cases and detects wrong-sign, absolute-time, and wrong-vertical-direction variants. It is not a proof of the Lean text.

### H2: exact band quotient certificate

The helper's leading `let` is the **same literal quotient of the same extended band** as the unchanged `canonicalWord` definition. It proves matching and every original-band tile binding before either existential packaging or marker enrichment. The canonical caller uses definitional reduction and proof irrelevance for proof arguments; it does not change the word or introduce a different choice. The separate existing marker theorem remains responsible for unique-start information.

The original halt and three independent `T+2` lower bounds remain, as does `3≤H`. Height/modulus nonzero instances and positive width remain available; no square geometry, coprimality, injectivity of an arbitrary alternate word, or unique-marker premise is added. Every signed time is included. The half-open spatial range retains `-L` and excludes `R`, and the twist stays `(R-1,t) → (-L,t+1)`. Existing public statements and all executable definitions are preserved; `canonicalWord` is also compared byte-for-byte by the author test.

Residual elaboration risks: reduction of the leading `let`, metavariable inference for `quotientWord_marked` and the existential witness, and definitional conversion at the canonical consumer. Extra annotations, if necessary, must be charged in revised metrics. The geometric model tests independently varied margins/heights, signed times, the excluded right wall, and negative wrong-sign/twist cases; it does not prove actual tile membership, matching, or halting.

### B1: finite temporal wrap/nonwrap normalization

The two existing interface equations are sufficient. On wrap, reset's south is initializer's north. Off wrap, the successor is nonzero. At zero, `H≥3` permits the initializer-to-time-1 transition (including the finish row at minimal height 3). Otherwise both sides retain the identical conditional `if k+2=H then 438 else color (run (k+1)) x`; associativity aligns indices. Deleting the split does not discard the finish case.

The public signature retains `H≥3`, all `Fin H` indices and signed positions, and does not gain a halt premise. Chronology is tested using opaque run-color/time symbols over all 2,077 seams for heights 3 through 64. Negative controls expose failures at heights 1 and 2, and modulus zero is rejected. The author model separately checks 525 seams for heights 3 through 32. Neither model is a machine simulation. Restricted Lean simplification remains untested.

### B2: paired actual halted constructors

With `cfg.state=none`, `color cfg x` is either `432+b` at the head or `b` elsewhere, where the same actual tape bit supplies `b : Fin 2`. The actual pinned constructors are `Allowed.pass a b` and `Allowed.finish a b`, whose north codes are `432*a.val+b.val`. Choosing `a=1` or `a=0` constructs both desired literal tiles at once. The color set is exactly `{0,1,432,433}`; initializer operating-head color 4 is correctly excluded. This does not weaken the halt premise or impose a normalized tape representation.

Both old public statements and executable tile functions remain unchanged. The private conjunction helper is transitively audited by both public callers. Local `Fin 2` projection/bit-witness reduction and `split_ifs` behavior still require Lean elaboration. The model is anchored to the literal constructor text and tests its arithmetic; it does not enumerate/prove the full 942-tile language.

## Novelty review against all prior outcomes

The baseline agent's final `NOVELTY_DECISIONS` and 25-subsystem/168-overlapping-row ledger were reviewed. I agree with retaining precisely these narrowed residual obligations:

- H1 is unbounded two-coordinate signed period transport, not finite inverse-invariance or guarded translated-interval propagation; it reuses an existing library theorem rather than introducing another general action framework.
- H2 is concrete computation-band extension/descent with exact original-tile binding before marker enrichment, not generic source-window or existential-witness packaging.
- B1 is finite temporal wrap gluing, not the already assumed spatial pulse/live-configuration adapters, nor bounded first-exit selection.
- B2 constructs two actual closing tiles from a halted configuration, whereas prior boundary fibers classify already-allowed tiles and prior action reflection only identifies the halted state.

The rejected neighboring source-window, first-halt/prefix and runTile-law-bundle ideas are correctly excluded. Validation support is reused infrastructure, not a fifth simplification. Earlier adopted refactor savings are not included in the 26-line total.

## Replay and evidence limits

The planned replay composes **nine ordered modules in one overlay world**: five changed modules plus unchanged CycleBoundary, CycleMarker, HelicalExtension and HelicalMarker connectors. This avoids checking BandMarker against old CycleBand or reaching old HelicalQuotient/TraceCycle through stale intermediaries. The explicit plan validates direct overlay prerequisites and refuses empty or reordered plans.

All **96 public theorem audit commands** are fully qualified and appended outside measured candidate spans. They include the seven public changed/new endpoints. The private paired helper is reached transitively through both public closing proofs. The future axiom-log gate rejects empty/missing reports, malformed lines, compiler errors, sorry/native/unknown axioms; these rejection paths were exercised with synthetic logs, not purported Lean outputs.

Shell syntax and early refusal paths passed. Missing binaries produced exit 69 before any Lean/Lake invocation; fake toolchain sentinels in additional refusal tests were never executed. No Lean/Lake runtime, installation, repository build, actual axiom-log check, upstream write or performance measurement occurred. A future selected-probe pass would still not establish a complete project build or a compiled counterfactual all-prior-applied baseline.
