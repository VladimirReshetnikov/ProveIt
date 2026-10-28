# ArithmeticHome215 — author construction and replay

27 October 2026. PASS. This records controller_certificate's author
self-review and capped private replay; independent acceptance is pending.
Only the new ArithmeticHome215 and ArithmeticHome215Checks Lean leaves and
this evidence were written. Their exact imports are the accepted
ArithmeticSymbolicCore215 and existing KHomeReady. No dependency source,
shared object, shared progress document or Git state was changed.

The final 234-line main and 65-line Checks were fully read before the final
pair, including every earlier proof delta. The complete executed 115-line
driver was read before execution and remained byte-identical throughout
all four attempts. Both inputs were snapshotted before each attempt's first
compiler call. Main bytes are unchanged from clean attempt 3; the last
Checks-only change explicitly unfolds flatValue [] in one exterior-zero
client. A preliminary status message estimated line counts incorrectly;
234 and 65 are the final mechanically checked counts.

## Actual arithmetic interfaces

All execution statements quantify over an arbitrary ORing model of IΣ1.
The affine gap, register tuple, spare count, left/right numeric tails and
execution clocks are internal elements, including nonstandard values.
The symbolic Seg list, scanner counter and checker fuel are finite syntax.
The finite list induction uses already accepted internal scan theorems;
no unbounded induction over an arbitrary Lean predicate is introduced.

reset_row and next_row kernel-check all 15 scanner rows of literal tm215.
Three further literal equalities give the 50/false and 75/false,true rows.
ready215 independently kernel-checks the actual closed ready table/window
certificate. This finite Boolean certificate is not used as an oracle for
internal Home execution: boundary_actual proves all eighteen steps from
the actual arithmetic step and scans. Seven safe zero steps and the eighth
boundary step reach state 75, nine right zero steps return to the marker,
and the last true/right step writes the true bit and reaches sparse84.
The exact result is runFrom 18 (leftFrame 2 0 (2*R+1))=frameSparse 84 1 R
for every internal R. The source/data Python trace is only a cross-check.

scanBound_actual retains an actual counter j bounded by the checker's i.
A false run is accepted only with zero affine coefficient and i+c<8.
A true run's internal length may be zero; in that case its constant is
proved zero and the actual counter is retained. A positive true run resets
the counter, even when the checker conservatively keeps its previous upper
bound. Neither gap>0 nor nonempty true-run syntax is assumed. Every box is
rejected before it could be swallowed by the left scan. The output is the
exact reversed numeric fold, preserving the arbitrary right tail.

stripBlank_actual discards only exterior false bits or false runs applied
to tail zero. Its stopping marker must be a literal true bit. It does not
silently discard a box or accept a true run as that marker. home_actual
combines this equality, scanBound_actual, the true/reset row and the fixed
18-step boundary. It needs no positive spare count or branch premise, and
proves a positive clock even when all preceding scans are empty.

stepper_actual handles the actual KHomeReady decision and supplies
home_actual on success, otherwise the accepted actual sstep_actual. The
fallback retains k>0 and BranchValid exactly where the register oracle
needs them. exec_flag_actual retains the exact moved flag; its positive
clock conclusion is conditional on initial moved=false. exec_actual and
exec_matches_actual use that false initial flag and discharge all semantic
stepper/Home premises. Initially true may succeed with zero steps, as a
focused check confirms. No unrestricted positive-clock claim is made.

Checks cover zero gap/empty true runs with a nonzero conservative counter,
arbitrary internal positive true-run length, box and unbounded false-run
rejection, literal marker versus true run, exterior zeros, a right register
box with arbitrary spare count, failed-Home fallback, exact target matching,
both moved-flag cases and the full boundary with arbitrary R and R=0.
The 14 reports use only propext, Classical.choice and Quot.sound: reset and
ready use propext alone, next uses propext/Quot.sound, and the eleven other
reports use all three. No sorry, native_decide, new axiom or cap raise occurs.

## Exact cache, providers and final commands

The approved plan is research/c222-home215-plan-20261027/cache-plan.json,
SHA a13475a1cb749a81800a1f7773df53b90582a4bba37badb128058371ec8a8137.
Its five-file manifest is
58609a5f5c7b1a78ac660f4e894fc0fbf02f0ebd50a377c4bcc02f1d838dcb20.
Exact scope: 153 cached custom modules, including 95 Foundation modules,
438 custom artifacts, 41 boundary primaries plus 123 companions, for
602 first artifact providers. There were zero dependency refreshes.
All source headers, reachable imports, current source/object pins,
package-only external LEAN_PATH and first providers were authenticated.

The accepted ROOT Symbolic provider is
/tmp/symbolic-core215-root-d4b0mp1m/lib, with ROOT packet
8102b4470b0f939c6f88ff551eb5a41d165be8113f3cc8c000b538c2059dce26.
The four added cached syntax modules KHome, FramedWindow, KZipTape and
KHomeReady retain the already authenticated NativeAdaptiveCurrent peer
route. One inherited alternate KZip object is source-identical but has
unequal object bytes: 1230b602... in that native route versus the selected
current 5fc974ab.... Both observations are explicitly recorded in the frozen
plan; this is not claimed to be a byte-identical overlap. The accepted
current selection is unchanged, and no Foundation rebuild was performed.

Final private provider:
/tmp/home215-controller-author-59p32b0a/lib.
The two fresh regular outputs used the pinned Lean 4.32 executable,
-M6000 -j1 -DElab.async=false, LEAN_NUM_THREADS=1 and a 512MiB free-disk
reserve before and after each invocation. Main passed in 4.540 s; Checks
passed in 2.380 s. The main log is empty and Checks has exactly the intended
14 reports, with no warning or error. Final driver authentication rehashed
2728 observations across 962 paths. Full command lines, compiler pins,
first providers, input snapshots, timings, logs and objects are retained.

Final source SHA256:

- Main: ce91849e1aa711e0e4b7446f8b9c1597095fa361ba51290f35051801ef1e3d98
- Checks: e7416425451a86cfff8a8f0ad84526464cbfffcf426182d3298025c9a8c0e53a

Final object SHA256:

- Main: 14fac69e31382b57f2f3b2686c04e126b6e361f27c5b56b5b28e4b774f48c796
- Checks: a07ba2bca9ff7d058a62ea2d3b885928aee462a55072a4413f7f9951f19ec664

## Preserved attempts and limits

All four attempts and six compiler invocations are retained. Attempt 1
failed on local state arithmetic, the Foundation subtraction lemma name,
bit-prefix/numeral simplification and state-expression elaboration.
Attempt 2 reduced to one initial state0=2 rewrite. Attempt 3 main passed
cleanly, while one Checks client needed the explicit empty flatValue
reduction. Attempt 4 is the final clean pair. All eight input snapshots,
every command/log/timing and every available output remain pinned. Historical
source records are checked against their snapshots, not incorrectly against
later source bytes. Only the final pair is compared to current source.

I also authored the lower Tape, Boxes and Symbolic packets and substantial
earlier runtime prerequisites; this is not an independent review of them
or of the present pair. Home supplies the actual successful checker clients
needed by later site proofs, but does not prove all 4751 sites, canonical
path correctness, physical/control calibration, full control-to-tape
simulation, source-ZFC interpretation, internal equation/Pell equivalence
or the existence of the final HA proof. Those remain separate obligations.

Evidence: [replay](arithmetic-home215-replay.json),
[complete manifest](arithmetic-home215-author-replay/FILES.json).
Replay SHA256: 8c1c7fe38b55129f57debee97130603d22d70f57e23388474c6e8c1dc49064bc.
