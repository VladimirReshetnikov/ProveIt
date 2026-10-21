# Runtime simplification: close the actual oracle boundary, not just row counts

## Useful finding
The maintained engine already has the desired row-footprint interface. `KTape.boxLemmas` takes agreement with `tm230` on 44 explicitly enumerated rows, plus a separate increment-tail contract. No new generic unary scanning/lens framework is needed for those four engine contracts. Existing proofs include arbitrary-left-context and arbitrary-right-context return lemmas (`ret_file_any`), so repeating that factoring would duplicate completed work.

However, the exact DR215 and ST215 inputs use **198/0 = 0 L 40**, while the maintained `IncTail` bypass is **1 L 40**. The maintained `KRuntimeCore.boxList` and `BoxLemmas.inc` explicitly append `[1]`. Consequently, unchanged protected rows alone do NOT instantiate the maintained engine theorem for ST/DR. Our earlier symbolic dependency report correctly left BoxLemmas assumed; it cannot be promoted to a concrete runtime proof by row-disjointness alone.

The owned `check_engine.py` parses the current KTape state list and compares all 44 protected rows against the certified K215 native table. All 44 match for ST and DR. Both fail the maintained bypass predicate. The only changed ST→DR rows, (199,1) and (206,0), are outside this protected set, and the zero-spare tail is identical between them.

## Minimal useful refactor
Parameterize concrete box interpretation by a fixed Boolean spare value `a`, interpreted as 0 or 1:
- `boxList a (.plain (.inc r)) vs = sepsR (incr r vs ++ [a.toNat])`.
- `BoxLemmas a M`: change only the increment postcondition; mark, dec0, decp stay literal copies.
- `IncTail a M`: the direct bypass `M 198 false = some (a, false, 40)`; retain the old multi-row branch only when a=true.
- Generalize `KTape.box_inc`'s final bypass segment once. Its preceding scan/carry proof is unchanged. `ret_file_any` already accepts arbitrary suffix Y, so this is a tail/local list-identity proof rather than another unary induction.
- Thread a through `conc`, `oracle_sound`, `sstep_sound`, and `exec_sound`. The syntactic interpreter `sstep`, `oracle`, target comparison, and site certificates are unchanged: their box tag records only an increment effect, not the appended spare's numerical value.
- In `KSim.sim_step`'s increment case replace the witness `ext ++ [1]` by `ext ++ [a.toNat]`. The extension remains nonempty; no positivity requirement exists for spare values. Decrement gap growth is unchanged.
- Instantiate a=true to preserve existing K215. Instantiate a=false for ST/DR.

This is a rigorous minimal design, NOT a compiled generalization. One must prove the new zero-tail segment and parameterized soundness before claiming the DR physical proof. Replacing `[1]` only in the endpoint witness is insufficient because `boxList` currently fixes the entire tape interpretation.

## Exact dependency transport
`DependencyTransport.lean.proposal` gives a generic trace transport theorem preserving the exact symbolic state and the progress Boolean. It is uncompiled. Its interpreter-specific locality premise is discharged by the following exact footprint definition (branch assumption is held fixed):
- left empty/bit reorientation: empty footprint;
- left/right run: {(q,b)}, even if peeling rather than scanning;
- right literal bit: {(q,b)};
- singleton box with successful table-independent oracle: empty direct footprint;
- singleton box with failed oracle: {(q,false)};
- malformed configuration: empty footprint.
The distinction between failed oracle and successful oracle matters. A scan uses arbitrarily many physical transitions but its symbolic decision reads only the one self-loop row. Missing rows are values too: the formal footprint compares Options, not just defined transitions.

Proof: case split on the symbolic configuration and oracle result gives identical sstep outputs from agreement on the listed rows. Induction over a supplied successful trace then gives identical states AND progress flags at every step. Thus target checks, normalization, fuel use and positive-progress qualification are preserved exactly. No first-dispatch boundary assumption is made. Combine with the newly parameterized BoxLemmas and existing exec_sound to obtain full-tape, all-natural endpoint transport. A supplied trace may contain intermediate dispatcher frames; they are not rejection criteria.

The owned access-logging audit independently rechecked all 6,151 ST guards. It records every actual table lookup (not an event-label approximation), all oracle interface uses, and checks old/new sstep outputs on every state of each unaffected trace. Result: 6,012 unchanged guards have exact step/progress equality; all 139 affected guards pass fresh DR symbolic checks. All 36 oracle interfaces (mark/inc/dec0/decp × 9 registers) occur. This remains a symbolic result until the zero-spare parameterized engine theorem is proved.

## What is actually saved
After that one engine generalization and one interpreter-dependency lemma, a family member changing only decoder rows needs proofs/checks only for affected guards plus finite footprint-disjointness checks for the rest. Existing baseline successful certificates still have to be available in the formal environment. This proposal does not erase baseline certification, source correctness, or startup obligations and does not claim a new end-to-end DR endpoint.

## Evidence and status
`KTape.reference.lean` is inspected current repository source from pinned aa66d0a33f1f8237a348899eb8095b045a502832. It was not executed. `ENGINE_FOOTPRINT.json` and `DEPENDENCIES.json` are owned checker outputs. All new Python entrypoints reject optimized assertion-disabled execution. No Lean compiler is installed in this workspace; no new compiled-formal claim is made. The newly received 281-template decoder formalization is already completed archived work and is not claimed as this round's contribution.

### The new tail is genuinely local
`check_tail.py` verifies the exact six-step framed segment starting at state0 on four blanks, with arbitrary tape outside that window. It reads no exterior cell, ends at state40/head0, and leaves window `[1,0,1,a]`. Both choices a=0 and a=1 pass for the pinned tables. The first bit joins the transformed register-file carry; the suffix is `[0,1,a]`. With blank continuation, a=0 represents `sepsR [0]`, while a=1 represents `sepsR [1]`. This isolates the needed local tail proof and avoids replaying any unbounded register scan. The integration still needs the exact carry/zipper equations in KTape and the spare-parameterized interpretation; this finite framed check alone is not BoxLemmas.
