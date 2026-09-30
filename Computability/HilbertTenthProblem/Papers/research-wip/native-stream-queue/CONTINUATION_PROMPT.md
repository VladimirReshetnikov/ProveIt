# Continuation: universal straight-line certificates

> Historical handoff below. The current comparison frontier is
> **75=41M+34A**: see [the complete proof](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
> and [consolidated checker](../../verification/explore_fixed_raw_universal_75.py).
> The original source has30 positive witnesses and19 equations; the
> [signed projection](complete75_signed_projection_elimination101.md) retains75
> with20 positive witnesses and nine equations.
>
> The current single-polynomial frontier is **89=48M+41A**, with19 positive
> witnesses and exact degree160: see [the reversed auxiliary proof](complete75_reversed_auxiliary89.md).
> It builds on the [bounded projection99](complete75_bounded_projection_elimination99.md),
> [norm product91](complete75_norm_product91.md), and
> [shifted transport90](complete75_norm_product90.md). The proofs recover
> auxiliary signs and the original positive quotient in a specific order;
> do not assume intermediate computed coordinates are positive off the zero set.
> The [retained-auxiliary partitions](complete75_auxiliary_degree_tradeoffs.md)
> improve the lower-degree alternatives to93/degree128 and92/degree136;
> the96/degree84 and94/degree96 options remain. Preserve the strong auxiliary
> norm and the exact linear root. The comparison bound75 and polynomial
> bound89 are separate measures.
>
> The README indexes the four-row queue simulator, binaryFIFO58 and
> ternaryFIFO66, row-local controller obstruction, residue-affine pumping,
> PCP/matrix continuations and rejected shortcuts. Controller arithmetic
> and ordinary-input loading remain unpaid for the coded queue simulator.
> In the nonabsorbing63 binary family, all read-only cases are decidable;
> width is bounded outside the cone and on the additional c=-b,a/b<1
> boundary. The [odd-controller orbit analysis](binary_odd_controller_orbit.md)
> gives exact guarded duration cutoffs at each fixed width. Other cases
> inside the cone remain open; nonzero terminal states forbid free padding.
> The [factored counter map](residue_affine_factored_counter_step.md) escapes
> unit-slope pumping and pays10B+8 scalar guards, but its prime-power input
> loading and history remain unpaid.
>
> The [two-stack substrate](two_stack_affine_input_step.md) has a two-operation
> ordinary-input prefix. [Factored selectors](two_stack_factored_selector_step.md)
> lower its exact scalar step to8B+18 for a full B=9K table, with eight
> positive witnesses and seven equations. A fixed-t polynomial costs
> (8B+39)t+1. The [typed-history audit](two_stack_polycyclic_history_obstruction.md)
> retains stack guards with prefix maps and identifies their loss in direct
> inverse-group products. Exact bounded-depth linear encodings need dimension
> N=2^(H+1)-1 and a paid2N positive basis loader. A
> [typed prefix merge](typed_prefix_normal_form_merge25.md) costs25 operations,
> four auxiliary witnesses and seven equations. Fixed trees cost25(t-1);
> output typing is proved. The [singleton extension](typed_prefix_singleton_merge31.md)
> costs31 and supplies exact binary empty tests plus a typed ordinary-input
> endpoint in two affine operations. Fixed flags admit cheaper schedules.
> Variable leaf selection, synchronized control and arbitrary duration
> remain unpaid.
>
> Next targets are below75 comparisons or below89 polynomial operations,
> with degree and positivity counted. These are reviewed mathematical
> proofs with exact source audits, not Lean formalizations.

The previous cone/singleton proposal is now implemented and proved in
merge31: positive flags avoid their two explicit decodings. Its root
condition V=1,U=kappa*x+lambda uses the root's already proved power typing.
Keep the fixed-word and uniform-history scopes separate. Precomputed
subtree flags are legitimate only when the leaf flags are source constants;
variable selected branches need a paid replacement. The next substantive
history task is a uniform synchronized selected-word/tree certificate,
rather than another unchecked input or empty-test conversion.

For algebraic work, the strong factor1+T^2-K cannot be-1 modulo4, so any
integer product zero forces T^2=K before substitutions. The one-gate
[degree162 reduction](complete75_strong_reduction89.md) preserves even the
full integer zero set. The degree160 successor also uses V=of-c and reverses
the linear unit; keeping the old orientation admits a formal kernel sign
collision. Preserve the strengthened R+2 bounds and the order of index
recovery when attempting further rewrites.

A separate **unverified group-membership lead** may provide an ordinary-input
matrix substrate. For an r.e. set S, investigate
`G_S=<a,b,c | [b^(-n)*a*b^n,c]=1 for n in S>`. A proposed exact converse
uses the semidirect product of the graph group on a_i,c_j with commutation
edges i-j in S, shifted simultaneously by b. For a missing edge, retract
onto the two corresponding free generators to keep their commutator
nontrivial. This still needs a complete presentation/isomorphism proof.

Then investigate a finite-presentation embedding and the diagonal fibre
subgroup M(H) in a product of free groups. Relevant primary starting points
are [Mikaelian's Higman proof](https://arxiv.org/abs/1908.10153) and
[Bogopolski--Ventura, Section1](https://arxiv.org/pdf/0810.0690): the former
states the recursively-presented embedding theorem, and the latter gives
M(H)={(u,v):u=v in H}, generated by diagonal generators and relator pairs.
Check effectivity and preserve named a,b,c by presentation changes.

The proposed matrix input is the commutator of B^(-x)*A*B^x with a fixed C,
where B is unipotent and the ambient free generators have a faithful fixed
integer-matrix representation. Its entries may then be fixed polynomials
of degree at most4 in ordinary x. Prove the free embedding with B among
the basis images and count this loader explicitly. A plain power B^x alone
cannot encode an arbitrary set by subgroup membership: its preimage is a
subgroup of the integers. Even if the commutator route works, certification
of an arbitrary product of the fixed subgroup generators remains unpaid.
No matrix universality theorem or new Diophantine bound is claimed here.

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
