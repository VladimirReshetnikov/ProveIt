# Continuation: universal straight-line certificates

> Historical handoff below. The subsequent research completed a reviewed
> **75=41M+34A** universal certificate with30 positive witnesses and19 equations.
> Start with [the current proof](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md) and
> [its consolidated checker](../../verification/explore_fixed_raw_universal_75.py).

This WIP snapshot is on ProveIt's branch `codex/diophantine-native-stream-wip`.
It preserves the unfinished end of the former Diophantine research session.
All paths and executable imports below are relative to this repository; no
access to the originating Windows machine or old repository is required.

Continue reducing the size of a complete straight-line arithmetic certificate
for universal Diophantine representation, starting from Jones's 1980 Theorem 5.
The original target was 129 operations. The established complete bound is now
**76 = 41 multiplications + 35 additions/subtractions**, with 30 positive
witnesses and 19 equations. This WIP branch does not claim a smaller complete
bound. Its new six/eight-operation results are conditional components.

## Contract and accounting

Fixed numerals have no cost. Each binary addition, subtraction or multiplication
costs one operation, including multiplication by a numeral. Register reuse and
equality comparisons are free. Exponentiation, divisibility, digit extraction
and radix conversion are not free primitives.

Preserve soundness and completeness for the full representation theorem.
Compiler/program numerals must be fixed independently of the varying ordinary
numerical input x. All existential coordinates must satisfy the stated strict
positivity convention. Do not replace ordinary input by a convenient coded
input without paying for the bridge. The established 76 construction treats
positive raw input; the queue components also cover zero, with explicit proofs.

Read applicable repository instructions and the nearest project README. Inspect
Git state and concurrent work. Continue in ProveIt, preserving unrelated work.
The old Diophantine repository has been merged into this one and is being
retired. Its historical `current/` directory is now
`Computability/HilbertTenthProblem/Papers/`.

## Reading order and preserved files

Start with the project README and these files under
`Computability/HilbertTenthProblem/Papers/`:

1. `1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` and
   `verification/explore_fixed_raw_universal_76.py/.json`.
2. `1980/ALTERNATIVE_UNIVERSAL_MACHINERY.md`, a large research map whose
   older paragraphs retain historical milestone counts.
3. `1980/EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md` and
   `1980/EXPLORATION_DYADIC_BALANCED_WRONG_INDEX.md`.
4. `1980/EXPLORATION_CONSTANT_LENGTH_RAW_QUEUE.md` and
   `1980/EXPLORATION_DELAYED_BLANK_RAW_QUEUE.md`.
5. The new `1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md` and
   `verification/explore_native_stream_raw_queue.py/.json`.

The original task started from `1980/jones1980_theorem5_operations.tex`.
At the previous research audit, the operation-count TeX/PDF still presented
89 and its corresponding Lean milestone was 90. The 76 result is a constructive
mathematical proof with symbolic, sparse and modular checks, not a completed
Lean formalization of that optimized count. Recheck those publication and
formalization statuses before reporting them as current.

This directory also preserves:
- `audit_queue_base_three_streams.py`: independent scalar and genuine-history audit.
- `audit_delayed_blank_loader.py`: independently implemented delayed loader.
- `native_ternary_controller_encoding.md`: a correct conditional controller
  baseline, carry counterexamples, and a narrowly scoped encoding limitation.
- `COMPLETE76_BRIDGE_REWRITES.md` and
  `explore_complete76_bridge_rewrites.py/.json`: exact full-schedule rewrites
  that tie 76 or cost 77. They found no saving and are not a lower bound.

The other 66 untracked research files from the old current/ tree are preserved
in legacy-untracked/ with a hash manifest. They retain their historical WIP
status. Unselected tmp/ build products and miscellaneous scratch data are not
part of this handoff.

## Established 76 and open 75

The 76 ledger is 19 outer-encoding operations, 43 Pell-kernel operations and
14 input-bridge operations. Its important recent idea reuses the already
computed Pell power X=2^(2r+1) for temporal rotation. A fixed helical compiler,
power-of-five padded dimensions, and ignored Boolean bits arrange the required
alignment congruence at the actual packed index. The represented machine
recognizes the doubled set {2x : x in S}, while the certificate still takes
the original ordinary parameter x. See the proof for all compiler hypotheses.

A 75-operation candidate replaces the auxiliary expression (i*c^2)^2 by i*c^2.
Its exact schedule and positive completeness map are established; its full
soundness is **open**. The weakened 42-operation kernel admits wrong-index
solutions. A latest family has q=16, r=269, actual main index329 instead of539,
X=2^329 and Y=2^91, escaping a residue restriction that excluded an earlier
family. The compiler, transport and raw-input equations have not been assigned
in those counterexamples. Thus the kernel is refuted, but the full75 candidate
is neither proved nor refuted. Do not claim otherwise.

## New machine and native stream component

The new finite-state queue has nine symbols, exactly all ordered pairs of
ternary digits. Every transition removes one symbol and appends one symbol;
physical length is constant. Existential padding supplies enough space for
an accepting computation. A fixed normalizer establishes the canonical input
independently of padding, and genuine acceptance erases every symbol to zero.

Published predecessors give a 14-operation initialization/transport component
and a 13-operation delayed-loader successor. The latter turns a verified high
padding zero into a genuine blank. Both have complete machine contracts, but
their controller arithmetic and geometry remain unpaid. The last corresponding
old-repository milestone was 7e72a44142c9b3116422e3fd0d121474a68f9742; its sources
are already migrated and need no old-repository access.

The new formulation records only removed and appended trits in native base3:
D_i=sum_j d_(i,j)*3^j and A_i=sum_j a_(i,j)*3^j. If W=3^m is the queue-length
power, I_i the initial coordinate and F_i the final coordinate after t steps,

    D_i + 3^t F_i = I_i + W A_i.

At a zero endpoint this is D_i=I_i+W A_i. Conversely, with bounded streams and
the correct powers, the identity forces exactly the queue's actual heads.
A single synchronized controller path on the paired trits therefore proves
the actual queue run.

For initial I0=x, I1=L, L=3^ell, the arithmetic source is

    W=3L
    x+alpha=L
    D0=x+W*A0
    D1=L+W*A1

with positive alpha. It costs **6=3M+3A**. Adding the positive common bound

    D0+D1+beta=q

costs two additions, giving **8=3M+5A**. Power geometry L=3^ell, q=3^t and
the synchronized controller remain external hypotheses. The appended-word
bounds follow from the equations and removed-word bounds. All four streams
have strictly positive witnesses on genuine accepting runs, including x=0.

The author checker verifies 31,980 arbitrary scalar tuples, 131,160 forward
FIFO runs, and 463 genuine accepting histories totaling43,665 transitions.
It handles t=0 and t<m, paired-controller replay, zero endpoints, positive
streams and the common bound. The last erased symbol is #(0,1), which already
makes the joint bound strict without an extra step. Accepting zero loops also
permit extensions without changing the stream integers.

Fresh default receipt replay passed during the handoff. Earlier independent
conceptual/scalar/history audits passed. The final artifact's independent
review status is recorded in the adjacent README; do not substitute executable
checks for a complete proof review.

## Immediate bottleneck

The controller must be certified at the SAME native base-three time positions.
A fixed-numeral convolution compiler operating on wider cells cannot consume
these integers without a proved, paid conversion. Removing content histories
does not make that conversion free.

A sound baseline uses Boolean transition-selector streams and trit planes for
state codes, with true one-hot typing. This is expensive. Naive sums can carry
between positions: four unit selectors equal the ternary repunit11. Likewise,
huge free scalar state codes do not provide injective encodings of arbitrary
state words at all lengths. These are scoped obstructions, not lower bounds
on every controller verifier. Specialized controllers, nonlinear checks,
redundancy or different representations remain open.

A useful unfinished local observation is that Boolean ternary streams satisfy
A+B+C=H, H=(q-1)/2, exactly when they are coefficientwise exactly-one: residual
digits lie in[-1,2], so the first nonzero residual cannot be divisible by3.
Booleanity and the common word geometry still need to be paid. This observation
has not produced a competitive complete compiler.

## Unverified five-operation successor

This is only a proposal, with no completed implementation, proof or receipt.
Move the initial marker to the units position, I0=x,I1=1, and attempt

    x+alpha=W
    D0=x+W*A0
    D1=1+W*A1.

These expressions cost five operations before bounds, power geometry and
controller certification. A loader delaying two cells might convert two high
padding zeros to a genuine blank and a delimiter without changing x:
emit provisional delimiters in its first two steps, retain two raw cells,
then emit held predecessors while reading raw trits; at the provisional
delimiter boundary require the final two held raw digits to be zero and
finish with blank and delimiter. This needs a complete finite transition
definition, short-queue analysis, normalization and positivity proofs.

In particular W=1 is not excluded by an assumed power alone. One possible
argument uses the initial read and first append second coordinates both
equal1: modulo3, D1=1+W*A1 would then imply W=0 modulo3. This argument is
conditional on the proposed controller actually having those first-step
properties. Do not treat it or the loader as verified.

## Promising directions

- Co-design the machine and its arithmetic verifier. Queue/lag systems, cyclic
  tags, cellular automata, counters and rewriting calculi are candidates.
  Few states or short rules do not automatically mean few arithmetic operations.
- Reduce or replace the43-operation Pell kernel, while testing weakened index
  claims against existing counterexample families and the full compiler.
- Share registers across input, geometry, masks, transport and acceptance;
  such cross-interface reuse produced the largest established savings.
- Improve the14-operation input bridge or design a machine that directly uses
  ordinary x. Avoid silently outsourcing variable input conversion.
- Settle full75 soundness, or build an actual false raw-input instance satisfying
  every equation. A kernel counterexample alone does not settle that question.
- Use the research overview to avoid repeating already refuted deletions, while
  respecting the exact scope of every negative result.

Work autonomously with independent review/counterexample lanes when useful.
Keep the objective a complete bound below76. For each achievement, preserve
the theorem, exact acyclic schedule, independently constructed source
polynomials, positive-witness maps and focused checks. Commit stable milestones,
update the nearest project documentation, and follow ProveIt's integration
workflow. Publish through the ProveIt remote, with no force pushes or unrelated
staging. This WIP snapshot itself is not a request to merge unfinished claims
into main or to change the maintained universal bound.
