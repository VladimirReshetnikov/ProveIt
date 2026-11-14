# Independent mathematical review of PA194AX11

Reviewed table SHA-256:

`1a7defae031c322a5577a3f2cb77d4c3bbc3242c7246f35f073d4dcf12a191d0`

Reviewed source snapshot: `ProveIt@2337ce611a26e308697ccbddb2a1636f989f01c3`.

## Verdict and scope

I found no remaining mathematical error in the **corrected four-parameter AX11 construction and its ordinary PA argument**, after checking the command algebra, the two source splices, the all-store proof compiler, the extra-field scheduling change, and the physical proof boundary. The initial informal description “fall through to MP(0)” was incorrect as a description of arbitrary machine executions. The corrected proof explicitly reads an additional operand z, proves soundness for all z, and selects z=0 only in its completeness compiler. That correction is essential and is now reflected in the comparison prose.

This conclusion depends on the explicitly retained ordinary mathematical PA calibration of the unchanged coefficient-four separated-diagonal calculus. It is not a newly elaborated Lean/Rocq theorem. I inspected the physical checker's symbolic induction rules and completed receipt; I independently replayed the new source and command checks. I did not repeat the already completed million-operation physical pass merely to duplicate its receipt.

The new proof is more than a state-count or finite-run assertion. Its obligations are separated correctly: logical calibration, total command semantics, all-store derivation compilation, exhaustive scheduling, exact source binding, universal positive physical simulation, and full blank startup.

## 1. Actual source change and the fourth operand

The source transformation replaces the single terminal AX `breakTo 1` by the existing nineteen-instruction `node49` push macro and deletes the nineteen-instruction dummy push in successful MP. I independently reran `check_source.py`, which expands the old and new trees without importing the construction compiler and compares two independently implemented CFG resolvers.

The actual ordinal correspondence is:

| Item | Old sites | New sites |
|---|---|---|
| AX terminal return / replacement push | 3553 | 3553–3571 |
| Following full MP field-reader entry | 3554 | 3572 |
| Deleted successful-MP dummy push | 3634–3652 | deleted |
| Retained successful-MP copy block | 3653–3659 | **3652–3658** |

An earlier draft misstated the last new range as 3633–3639. The corrected range above follows directly from the relocation certificate and is now in the proof fragment. All 3,653 other sites and all their resolved successors agree under relocation. External edges enter splice blocks only at their first instruction.

I additionally normalized the nineteen inserted push instructions against the nineteen removed old push instructions, translating the old push exit 3653 to the new exit 3572. Every resolved instruction agrees. Thus using the old push lemma here is justified by the actual closed block, rather than by its macro name alone.

The new successor is the *full* MP block, beginning with `node75`, whose first part reads another continuation field. It does not enter after that reader. After the push, the old AX cleanup has left t=d=h=0. Reading z and executing MP therefore has two cases:

- z=0: `I(0,0)=0`, so MP succeeds and returns zero.
- z>0: `I(0,z)>0`, so comparison against cached zero fails and returns zero.

Both cases preserve the new stack, clear the top and cache, and leave offset z. The correct general command is

`A(c,x,y,z)(t,w,d,h) = (0,[q0,q1,...,q9,t;w],z,0)`.

Here D=d+x, H=h+y, and the heads are, in stack order, the guarded gate (or zero), Gamma(c), h6,…,h1, the restricted implication head with actual lower operand d, and U(d,h). The last head uses the *old* d,h; the six ordinary heads use D,H. This distinction is respected by the free-constructor emitter check.

The new source count is exactly `3673−1+19−19=3672`. The numerical axiom families themselves remain unchanged.

## 2. Arithmetic aliases and safe Shift counts

The proof correctly treats Cantor stacks as numerical encodings, not free lists:

`hd(0)=tl(0)=0`, `[0;0]=0`, and `I(0,0)=0`.

These identities do not invalidate nested push/pop equations because the total projection equations `hd(p(a,w))=a`, `tl(p(a,w))=w` hold even at a=w=0. No argument uses the apparent list length as an independent invariant after zero collapse.

Every generated q0,…,q8 is either zero or an implication code, hence has residue zero modulo four. The final q9=U(d,h) has residue two and is at least two. Consequently the first ten Shifts after AX cannot test a sum equal to one; the next two tests contain q9 and are safe even when the saved old top is one.

The exact identities are:

- `A;S^10 = (q8,[t;w],0,q9)` when AX's fourth argument is zero.
- `A;S^11 = (q9,w,0,t)`.
- `A0;S^12` sends `(t,[a;w],d,h)` to `(t,w,0,a)` without halting, including t=1.

The new Pop is therefore **not** a contradiction test. The proof correctly appends a plain Shift to a compiled refutation. The unchanged Shift guard is t+h=1; in particular, t=h=1 does not halt. The checker and manuscript explicitly retain this case.

Push uses `A0;S^10;MP(0)`. Its final MP comparison fails because the candidate implication has residue zero while q9 has residue two, and it produces `(0,[t;w],0,0)`.

Discard is `MP(0)` only under offset d=0. Its success and failure branches both return top zero, even when the old cached formula is arbitrary. The proof does not use it to clear an arbitrary offset without first arranging d=0.

## 3. Selectors, generalization, and restricted implication

For j=0,…,8, starting from `(t,w,0,0)`, the word

`Discard; A(A,D,H,0); S^(j+2); Pop^(9−j)`

returns `(qj,w,0,0)`. After the first Shifts, qj is the top, q(j+1) the cache, and the residual generated heads followed by the saved zero remain above w. Exactly 9−j Pops exhaust that suffix and install the saved zero as the cache. The equation also covers collapsed all-zero stack components.

The restricted implication head needs its actual parameter u≤D, not merely the special u=0 selected by the simple formula above. The separate word

`Discard; Offset(u); A(A,D−u,H,0); S^10; Pop`

first sets old offset u, then adds D−u in AX. Its emitted head has the intended parameter u and its actual inequality is justified. The zero fourth operand clears the offset afterward. This addresses a potentially serious completeness omission.

Generalization is

`Push; Offset(i); S; A(i,0,0,0); S^11`.

After Push/Offset/S, the old theorem a is in the cache and offset is i. The inherited AX head U(d,h) is therefore U(i,a). The final eleven Shifts select it with saved zero in the cache. The intermediate Shift sees top=cache=0. This works even at a=1 and i=0; there is no undocumented side condition that the theorem being generalized differs from contradiction.

## 4. Modus ponens and the all-store compiler

The compiler explicitly reserves a zero below the two premise values, since MP no longer supplies the dummy zero. Its MP suffix starts from

`(0,[a,I(a,b),0;w],0,0)`.

The first Shift places a in the cache. The second either halts if a=1 or puts a in the top and I(a,b) in the cache. MP(b) succeeds. Pop then consumes the reserved zero while preserving b, clears the offset, and returns `(b,w,0,0)`.

The two critical corner cases are handled:

- If b=1, Pop still returns the visible contradiction safely; the final plain Shift performs the halt.
- If a=b=w=0, both implication and all relevant stack pairs can collapse to zero, but the total projection identities give the same result.

Induction on the proof tree is therefore valid with the invariant: from every `(t,w,0,0)`, the compiled word either halts or returns `(conclusion,w,0,0)`. Subproofs preserve the entire protected old stack, including the reserved zero. An early halt is acceptable in the completeness direction and is not derived from any assumption of consistency.

A leading A0 clears arbitrary incoming top/cache/offset while leaving some finite stack. Hence `A0;W_e;S` halts from **every** incoming store when e proves contradiction. No reset between scheduler trials is silently assumed. Soundness, separately, begins with theorem-annotated reachable stores; the argument does not improperly claim that an arbitrary unannotated store is sound.

## 5. Four-parameter scheduling and cofinality

The extra MP reader changes the command's encoding. The corrected fresh command payload is

`b_A(c,x,y,z)(r) = p(c+2,p(y,p(x,p(z,r))))`.

It is not the old three-parameter payload. The field order y,x,z matches the source readers. The command checker explicitly demonstrates that using the old payload would consume `hd(r)` as z and replace the intended continuation by `tl(r)`.

A nonempty continuation is encoded by `1+b_command(e(tail))`, while a fresh candidate uses the raw command payload. That distinction is maintained in the proof. After decoding any nonempty continuation n, the next continuation is at most n−1, so an additional field cannot defeat termination. The unchanged arithmetic macros are total with primitive-recursive bounds; the new AX adds only a total push, one total field read, and a total MP fragment. Thus all earlier nonhalting trials finish.

For a universal halting suffix W, the candidate family

`p(k+2,p(0,p(0,p(0,e(W)))))`

is strictly increasing and unbounded in k. Its leading AX has fourth operand zero; its state changes are harmless because W works from every carried store. Fresh enumeration from two therefore reaches a member unless it halts earlier. The proof needs no uniform semantic truth predicate: PA can formalize the finite primitive-recursive construction and induction over the finitely many earlier trials.

## 6. Soundness and the inherited logical calibration

Soundness must quantify over arbitrary fourth operands z, because the real machine enumerates all numerical candidates. The manuscript does this. AX pushes only the valid inherited heads, a generalization of the annotated old cache, and the saved annotated old top. Both visible outputs are zero; its arbitrary final offset z is metadata and carries no proof annotation. This cannot manufacture a false theorem merely by changing an offset.

Successful MP combines annotated premises; failure returns the fixed theorem zero. Shift moves annotations. If t+h=1, one annotated value is exactly one. This argument correctly avoids the false assertion that top one always triggers the sum guard.

The inherited PA calibration is a syntactic proof translation. For the reverse interpretation, finite binary comprehension is supplied by substituting each arithmetic formula into a PA induction proof template. The claim is about a primitive-recursive supplier of **proof codes**, not a uniform truth evaluator or a reflection principle. No new calibration is needed because AX11 has not changed any numerical axiom family, constructor, guard, MP rule, or generalization rule.

The retained diagonal and finite-bit-calibration manuscripts remain a real dependency. Their ordinary PA proof status should be stated explicitly, as in the new fragment. The stronger unfinished iPRA/Lean endpoint must not be advertised as completed by this review.

## 7. Literal-tape proof boundary

The completed independent physical receipt records:

- 194 working states and 388 rows.
- 3,672 source sites and **4,779 universal source outcomes**.
- Four generic list lemmas rederived from the literal transition rows.
- **1,078,230 symbolic operations**, maximum 397 per outcome.
- Positive-duration constant at least **3**.
- Exact dense/native conjugacy.
- Complete blank startup after **58,154** physical steps.

I inspected the underlying symbolic rules. Run lengths and duration coefficients are required nonnegative, and every accepted primitive case has positive constant duration. Nonhalting primitive cases must reach the exact complete target tape; a premature halt cannot satisfy that test. List sweeps are justified by checked one-block identities plus ordinary finite-list induction. The first arbitrary spare block plus arbitrary finite tail gives a nonempty spare list, and increment appends the prescribed unit block. The argument is universal symbolic arithmetic, not a collection of bounded numerical register tests.

The source binding and command proof are necessary in addition to those physical contracts; the latter alone do not identify AX's fourth operand. The corrected package has both.

The proposed-halt-time argument is sound: if a literal first halt occurred at T while the source continued, concatenate T+1 positive source segments after initialization. Determinism gives the same physical run extending beyond T without a halt, a finite contradiction formalizable in PA. This avoids assuming an unproved inverse decoder for arbitrary intermediate tapes.

## Corrections and remaining limitations

The substantive corrections addressed during the review were:

1. AX falls into MP_z after reading a **fourth operand**, rather than automatically into MP_0.
2. The retained MP copy block relocates to **3652–3658**.
3. The terminal contradiction test is a **plain Shift**, since the new Pop is safe at visible one.

The current proof and fresh command receipt incorporate all three. I found no further obstruction to the ordinary PA argument, conditional on its explicitly retained mathematical calibration and the ordinary justification of the symbolic induction rules. The work still does not supply a newly kernel-checked end-to-end PA/iPRA theorem, and no unsuccessful search proves a 194-state lower bound.

Independent replay artifacts from this review are `ax11_commands_independent_replay.json`, `ax11_source_independent_replay.json`, and `ax11_push_splice_review.json`. Exact corpus novelty is recorded separately in `axfall_novelty.json`.
