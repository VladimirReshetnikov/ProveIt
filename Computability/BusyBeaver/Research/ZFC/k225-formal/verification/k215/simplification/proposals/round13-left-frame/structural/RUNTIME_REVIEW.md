# Independent adversarial read-through: framed local traces

Reviewed `research215_round13_runtime/LeftFrameContract.lean.proposal`, its owned
checker/discovery/negative-test source, recorded JSON endpoints, and the pinned
`KRuntimeCore`, `KHome`, `KHomeReady`, `KSim` and residual-interface source.
No runtime-worker script was executed and the template census was not rerun.
This is a logical/source review, not a kernel acceptance result.

## Result

No semantic flaw found in the proposed contract. The important exclusions and
side conditions are present. The 35-template/1,422-guard count is the worker's
finite diagnostic result, not an independently kernel-checked count.

1. **Append-frame commutation is correctly guarded.** In KRuntimeCore.sstep
   lines 136-163, every successful nonempty-left or right-facing branch either
   leaves the left tail unchanged, pushes onto it, or removes its first segment.
   Appending F at the far end commutes with all of these. Table and oracle
   selection do not inspect that tail. peelLeft/peelRight have the same property.
   The left-box branch is impossible under the successful-step hypothesis.
   The one excluded case, `(q,true,[],r)`, fabricates a blank and does NOT commute:
   appending F=[bit true] makes the framed step read true, whereas append-after-
   step leaves F on the left and inserts false on the right. safeLeft excludes
   exactly this counterexample, including after peeling an empty run.

2. **No unframed left trimming is used.** Local stepping retains raw left
   segment lists. Equality checks normalize `reverse(l) ++ r` as a right word,
   using `norm` rather than `normL`. A trailing local zero is therefore never
   silently discarded just because its future frame is absent. In the new
   35-template family every stored pre_home endpoint is `(2,true,[],R')`, so
   the remaining right-word equality is particularly direct. This endpoint
   shape must remain an explicit formal equation for each template.

3. **Positive progress is supplied at the right point.** runLocal_sound
   intentionally concludes Reach, not Reach1. Reorientation, zero-length scans,
   and box macrosteps need not establish the Boolean progress flag. Existing
   KHome.home_word concludes Reach1 through its Boundary hypothesis. Composing
   local Reach with final Reach1 is valid even when the local trace has zero
   concrete steps. No inference from a zero-step endpoint match is required.

4. **Home is not asserted for arbitrary prefixes.** At the empty-local-left
   endpoint the appended frame is exactly `P.reverse.map bit ++ [bit true]`.
   The proposal requires `scanBound 0 (P.reverse.map bit)=some k` and uses the
   existing scanBound_sound. Appending the marker resets the resulting scan
   state to 2; home_word then returns to state 84. This is the correct weaker
   premise than 'P ends in one'. A prefix containing an eight-zero run remains
   inadmissible. The source checker explicitly checks the scanner premise per
   occurrence, not only per suffix template. Blank far-left exterior is stated,
   so there is no unsupported arbitrary-nonblank-frame Home claim.

5. **Source operations cannot leak into P.** Continue requires enough ones
   in S and the exact strip result E. Break requires enough zeros, the exact
   stripped suffix, and a nonoverflowing increment giving E. Those premises,
   not merely the observed concrete source endpoint, justify the universal
   `action(P++S)=P++E` statement. In particular, an increment carry into P and
   an exhausted strip are excluded. The remaining three controls stay literal.

6. **Gap arithmetic and interface boundary remain visible.** Each occurrence
   needs |pc|<=48 to instantiate local n with `n+48-|pc|`; then its gap is
   `n+64-|pc|`. The unchanged prefix cancels in the successor-length delta.
   The semantic residual interface is the correct target: a Reach1 proof is
   not automatically a proof that the old Boolean whole-site checker returns
   true. The proposal correctly retains this integration as future work.

## Unclosed formal obligations

The algebraic `sstep_addLeft` tactic script is only a sketch, and may require
elaboration/tactic repairs. So may the runLocal induction and Home specialization.
All 35 concrete local-run equations, the source strip/carry framing lemmas,
exact per-occurrence scanner/routing/gap proofs, and final semantic coverage
composition must be kernel checked. The existing whole endpoint must then be
rebuilt in each assistant. The finite model is not a substitute for these
obligations; no measured time/memory gain, source-size reduction or new endpoint proof
has been established here.

The worker subsequently added `LABEL_MAPPING.json` and `FORMAL_TEMPLATES.json`:
native label 302 must become formal label 120. This review did not independently
replay that later label-mapping audit. Formal integration must use the translated
templates, not substitute the native-state diagnostic JSON directly into the
Lean table. The generic append-frame argument is uniform in the table and does
not remove this concrete binding obligation.
