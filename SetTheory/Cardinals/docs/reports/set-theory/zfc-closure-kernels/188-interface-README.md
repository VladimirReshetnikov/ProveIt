# Round 12: opaque-prefix contracts for the control primitives

## What is already completed upstream
At revision57541fe0cfe3af62b4cb58747d8d1d7c16b338d5, the Proof Contracts contribution has a checked29-module Lean slice, semantic simulator compatibility, and a concrete word000/decnz8 example proving BOTH suffix branches for arbitrary valid register files and gap values using KTape.boxLemmas. It is not just an interface sketch. Complete CheckedLeafSuffixes/source-shape coverage and an endpoint rebuild with that replacement remain open. This report does not claim the existing interface or that example as new.

## New concrete result
Factor each PC as P++S, where P is opaque, ends in1, and has no run of eight zeros. Keep S literal. During residual execution, ordinary symbolic rules must never read any cell of P; the ONLY operation allowed to traverse P is the existing Home scanner, extended by one generic prefix lemma described below.

Owned symbolic discovery on the exact K215 table/source found:
-1421 of1425 control-primitive guards fit the contract:1325 continue guards and96 break guards.
-These need only76 distinct template checks:69 continue templates and7 break templates.
-Four control guards remain literal:001/CB1,010111/CC3,1000111/CC3,11011/CB1.
-The1900 increment guards,2850 decrement branches and one halt guard remain literal. No arithmetic family has been proved by this experiment.
-Total proof obligations would be4831 template/literal checks instead of6176, if the opaque-prefix semantic extension is formalized. That is1345 fewer,21.78%. This is NOT a claim of a compiled coverage theorem, measured compiler speedup, or97 universal leaf cases.

The discovery never silently assumes a prefix read is safe. An ordinary step that would inspect the opaque token is rejected. Failure to admit an abstraction is not a divergence or impossibility result; the original literal obligation is retained. All6176 guards are accounted for.

## Precise universally quantified contract
For each admitted template, fix its literal suffix S, exact native control state q, opcode/argument, branch, and exact target suffix S'. Quantify over all finite Boolean P satisfying last(P)=1 and no eight consecutive zeros, all gaps g>=16, and all valid register lists/spares. The entry is the standard zipper leaf port: left=reverse(P++init(S))++[1], head at last(S), and right=last(S)::0^g::1::sepsR(vs). Tape to the far left is blank as in the maintained dispatcher relation. Do NOT replace this with arbitrary nonblank left exterior: Home's boundary theorem needs the standard blank-left frame.

The endpoint is the exact standard dispatch frame with PC P++S', specified gap change, unchanged register file for these CB/CC templates, and identical entire tape outside the stated operation. The symbolic opaque token denotes P in the right list or reverse(P) in the left list; reversal changes orientation explicitly. Its contents are never approximated or erased. Every successful residual starts with moved=false and has positive progress; Home supplies Reach1, ordinary steps preserve the existing progress discipline.

This template language is strictly stronger than checking each particular source prefix but weaker than arbitrary PC strings. Source coverage must prove the P predicate and source routing separately. The current finite source checks establish those side conditions at every admitted occurrence.

## Why the Home boundary is sound, including crossing runs
Home scans left. Its explicit suffix is checked with the existing eight-state zero-run automaton. At the crossing into reverse(P), the first bit is1 because P ends in1. That resets the scanner to state2 regardless of its incoming zero count0..7. The internal no-eight-zero-run predicate ensures that the remaining reverse(P) never takes the forbidden eighth-zero transition. The left guard bit1 resets the final counter before the already-proved boundary return.

Thus there is no unchecked zero run spanning the S/P boundary: that boundary is broken by1. Merely checking that P has no eight zeros, without P ending in1, would NOT suffice. A generic proof is a short induction over the Boolean word using KHome.Rows.reset/next, followed by LeftWord.append and KHome.home_word. The new lemma is uncompiled here.

## Source-operation framing is independently checked
Finite endpoint equality is not enough to infer that the source operation ignores arbitrary P. Every one of the76 templates separately meets these sufficient syntactic conditions:
-CCk: S contains at least k ones, and stripPath true k S is exactly S'.
-CBk: S contains at least k zeros; stripping those zeros remains inside S; incrementing the stripped suffix does not overflow; the result is exactly S'.

Therefore stripping and incrementing act wholly within S for EVERY admissible P. The gap delta depends only on |S|-|S'|, so varying the length of P cannot change it. The symbolic checker uses initial gap n+16 rather than a fixed PC-dependent constant. Actual source paths have length<=48, hence their maintained n+64-|PC| gap instantiates this parameter with a nonnegative offset. Overflow/root-marker cases that do not meet this framing condition are left literal, never normalized away.

## Minimal formal implementation
1. Add an opaque-prefix segment to the symbolic representation, with a semantic interpretation parameter P and the stated invariant. Alternatively add a separate tiny templated executor; avoid changing existing source certificates until its soundness is proved.
2. Ordinary step rules may move/write explicit cells but cannot inspect the opaque segment. Extend normalization only by preserving opaque tokens literally; orientation is part of the token.
3. Prove the opaque-Home lemma using the existing scanner and boundary theorem. The checker accepts an opaque chunk only in the final position of its reversed Home scan; it does not assume arbitrary opaque placement works.
4. Lift execWith_sound to this extended interpreter using unchanged BoxLemmas and the new Home lemma. In fact the admitted control templates use no arithmetic oracle change, so BoxLemmas can remain an inherited interface rather than a new engine proof.
5. Certify the76 template runs once, plus the4755 remaining literal guards. Bind each source leaf to the exact current routed q and source action, and prove source P/S decomposition meets the invariant and syntactic frame conditions.
6. Feed these contracts into the now-checked semantic EdgeSpec/coverage interface. The000/decnz8 example demonstrates that last attachment route already works for a literal suffix.

Rocq can use the same finite template data and word invariant, but must prove its own opaque-segment soundness in its existing zipper semantics. There is no reason to add a cross-assistant tape representation bridge merely to share these76 data entries.

## Evidence and limitations
`check_templates.py` and `analyze_symbolic.py` are owned code, not executed downloaded scripts. `TEMPLATES.json` gives every source guard's template/literal assignment and cut, template keys, syntactic framing results, and explicit control exceptions. The table/source are pinned to certified9683d6ed…/17af2071…; the inherited exact source-path port map is pinned as well. Python optimization is rejected.

The finite audit is NOT a kernel proof of the new opaque-Home rule or interpreter. Those are the precise remaining unbounded obligations. This result is a concrete reduction target with a local inductive justification, not a claim that6176 formal proofs have already been replaced.

### Accounting and parameter details
4831 counts expensive symbolic template/literal obligations, not all proof checks: there are still6176 cheap source-coverage instantiations and the generic soundness lemmas. No net line-count or build-speed claim is made. The actual gap n+(64-|pc|) equals the template gap n'+16 at n'=n+48-|pc|; the source bound |pc|<=48 proves n'>=0. The target gap transforms by the identical fixed |S|-|S'| delta.

The Home implementation's k:=7 after the opaque chunk is only a conservative upper bound, NOT the actual trailing-zero count. The code demands that PR is the final chunk of the reversed scan, so no later literal can combine with an unknown trailing-zero count. The guard bit is handled by the generic Home proof. Allowing any following chunk without a stronger summary would be unsound.

`OpaquePrefixHome.lean.proposal` gives a concrete uncompiled crossing/whole-Home proof sketch using existing scanBound_sound, LeftWord.append, and home_word. It explicitly includes the guard and arbitrary right frame. The full extended-symbolic-interpreter theorem remains separate. `test_boundaries.py` rejects eight negative mutations, including an attempted opaque read, a missing boundary1, an eight-zero prefix, opaque placement followed by more scan data, strip underflow and suffix increment overflow.
