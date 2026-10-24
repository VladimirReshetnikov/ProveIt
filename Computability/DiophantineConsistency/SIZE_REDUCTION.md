# Active equation-size research

The owner paused Lean formalization on 23 October 2026 and directed the
research toward reducing equation size and complexity. The goal remains
active. Existing proof checkpoints and incomplete experiments are preserved;
no further Lean development or compiler runs are part of this phase.

The required mathematical endpoint is unchanged: the equation's absence
of solutions must be provably equivalent in ZFC to syntactic `Con(ZFC)`.
A smaller formula must retain a complete ordinary proof chain, including
its coefficient tuple and witness domain. Local gadget counts alone do
not establish the size of a complete consistency equation.

## Current comparison points

| Domain | Variables | Operations | Degree | Use |
|---|---:|---:|---:|---|
| Positive integers | 15 | 66 | 157 | Short-operation baseline |
| Positive integers | 15 | 69 | 155 | Complete one-page specification, including every constant |
| Positive integers | 12 | 96 | 70 | Free positive J and an identical polarized norm tail |
| Positive integers | 13 | 88 | 51 | Free positive J; previous one-page90/51 version retained |
| Positive integers | 14 | 73 / 74 / 75 / 76 | 342 / 312 / 293 / 191 | Hilbert Tenth root transfer and scaled ordinate centers |
| Positive integers | 11 | 111 | 211 | Adaptive carrier combined with the double center |
| Positive integers | 10 | 123 | 816 | Scaled centered sixteen-fold norm with shared product |
| Positive integers | 9 | 419 / 427 | 1,472,168 / 1,626,248 | Position-zero normalization; original31 / smaller compact54 tuples |
| Positive integers | 9 | 475 | 1,379,730 | Shared-product reduction of package71 |
| Positive integers | 9 | 722 | 1,158,228 | Collected J,D radical evaluator and identical norm rewrite |
| Positive integers | 9 | 953 / 1,056 | 999,518 / 997,810 | Collected radical / position-zero complete radical; cost-degree tradeoff |
| Integers | 10 | 471 | 1,245,324 | Shorter source-aware approximation guard |
| Integers | 10 | 475 / 478 / 512 | 1,179,788 / 1,114,252 / 1,080,888 | Short guard combined with compact shears |
| Integers | 37 | not optimized | 4 | Reviewed joint-sign quartics |
| Integers | 22 | 119 | 14 | Centered joint-guard combination;118 operations at degree16 is retained |
| Integers | 19 | 109 | 88 | Reviewed joint projection; other tradeoffs retained |
| Integers | 17 | 110 | 88 | Root-fusion quotient companion;114-operation checkpoint retained |
| Integers | 16 | 134 / 135 | 192 / 184 | Separated rational-root norm tradeoff |
| Integers | 15 | 124 / 128 | 352 / 204 | Parity-separated three-root norm |
| Integers | 16 | 115 / 118 / 119 / 132 | 160 / 124 / 112 / 108 | Parity/residue and prime-separation two-root norms |
| Integers | 12 | 208 / 202 | 2,400 / 2,912 | Fixed-prime separation with identical shared norms |
| Integers | 13 | 184 | 1,072 | Trace recovery and identical shared-norm evaluator |
| Integers | 14 | 137 / 148 | 792 / 414 | Root fusion and CRT/valuation composition |
| Integers | 20 | not optimized | 18 | Coordinated polynomial projection |
| Nonnegative integers | 399 | not optimized | 4 | Projected source, summed factorial radix and rational SOS contraction;8,286 terms |
| Nonnegative integers | 402 / 403 / 453 / 667 | not optimized | 4 | Complete term/height alternatives;6,882 /8,229 /5,059 /3,632 terms |
| Integers | 891 | not optimized | 4 | Lower-height projection;6,797 terms, height63,905,891 |
| Integers | 862 / 863 / 865 | not optimized | 4 | Actual-row guards and signed projection;11,245 /9,909 /9,814 terms, height2,445,790,974,704 |
| Integers | 1,190 / 1,224 | not optimized | 4 | Preserved synchronized checkpoints, now dominated by917 |

Operations mean live binary `+`, `-`, and `*`, with squares and fixed-scalar
multiplications charged and fixed numeral leaves free. Variable counts
exclude named polynomial abbreviations. Positive, natural and unrestricted
integer domains are compared separately. These are useful points, not the
complete frontier or a global optimality claim.

The maintained [equation.pdf](equation.pdf) now displays the10-positive
123-operation degree816 equation in full, including every constant, with
standalone [TeX](equation.tex). It uses the same complete fixed recipe as
the preceding13-positive90/51 page, now preserved as the lower-degree/cost
alternative. This is a significant three-variable reduction; it increases
degree and operations. Minor evaluator changes in an identical polynomial
need not trigger another rendering.

## Work now underway

The arrivals in`c1a102936a` and`9a33342a03` have been reviewed;
[PROPOSAL_REVIEW_WAVE11.md](PROPOSAL_REVIEW_WAVE11.md) compares finished
endpoints, exact derived improvements and alternate source encodings.
It records which full releases and selected component stages were replayed.
No incoming archive or historical delivered tree was replaced.

The [latest continuation review](PROPOSAL_REVIEW_LATEST.md) includes
eae4f1952b,440dd03ab8,d42be5cd87 and43ac596e36. It records the saturated
nine-variable targets, adaptive eleven-positive form, centered Hilbert
Tenth transfers, integer shears and complete direct-C222 alternative.
The13-integer and shared-direct arrivals at751bc067e2 have now passed their
ordinary reviews and full finite replays. A stronger prime-supported CRT
construction yields the direct points above; its natural and integer
polynomials are fully collected. Reusing the literal beta-row majorant
reduces the natural points to3,603/6,179; its index bound uses an endpoint
row before the CRT interpretation. Both parity small-integer families
have now passed separate ordinary reviews and their scoped replays.
Prime separation adds16/108/132 after its full normal/optimized review.
Fixing every positive-power common bound to`W=n+k`, deleting both
redundant lower-bound slacks and composing the beta majorant gives
3,328/5,739 natural variables. Actual-row guards yield6,604 integers.
Those complete checkpoints remain preserved. The newer synchronized
shared-frame construction first superseded them with522-natural
and1,224-integer points; complete ordinary and exact finite reviews pass.
Signed monic projection then reaches1,190 integers, preserving every
guard through a complete reverse-restoration certificate. Its larger
26,411-term expansion is an explicit cost of the variable reduction.
The separate batched667-natural/1,690-integer proposal also passes its
scoped review. The projected source now improves these checkpoints to
407 naturals or888/917 integers through the table's new exact transformations.

The first completed reduction is
[`gap2082-shared-products`](candidates/gap2082-shared-products/README.md):
sharing `M*U` between `P,A`, sharing `C*D` between `E,Lambda`, and reusing
the already computed `R+1` saves three operations. Exact local integer
polynomial identities plus a complete structural gate remap prove that
the440/447 positive/natural circuits equal their443/450 parents.
Coefficients and named values are unchanged. Both normal and optimized
Python replays check the deterministic artifacts, topology, liveness,
actual-coefficient diagnostics and an identity-corruption control.

The identical three-gate saving also applies to the lower-degree package71
branch: [`order7-shared-products`](candidates/order7-shared-products/README.md)
has475/482 positive/natural operations and the unchanged degree1,379,730.
The complete original31 tuple is preserved on that branch.

A shorter complete page is also available:
[`merged-mask-base62/equation.pdf`](candidates/one-page-compression/merged-mask-base62/equation.pdf).
Its436-character numeral, complete alphabet, positional sum and decoder
reduce the coefficient recipe to2297 nonwhite characters,8.8% below the
preserved771-digit page's2518. The original recipe has2861 characters.
The decimal-only merged-mask variant uses2482, and an original-tuple
notation variant uses2424. Base62 changes printed notation rather than
the integer's information content; the full alphabet overhead is charged.
An explicit finite quotient/sum decoder replaces the old action packing.
It uses a bijective control-state renaming that fixes start and halt;
all430 transition conjugacies and all four coefficient reconstructions
are checked. The new `K` differs from the old one, so this is a separate
whole-tuple specification with an ordinary state-conjugacy argument.
See [SEED_COMPRESSION54.md](SEED_COMPRESSION54.md) and
[SEED_PREDICTORS54.md](SEED_PREDICTORS54.md) for scope and replay.

For the alternative direct-proof route,
[`direct-flow-large-carrier`](candidates/direct-flow-large-carrier/README.md)
removes the carrier's common-multiple block using the exact factor bound
`M=(m+1)^t`. Combining this with quadratic beta-digit constraints reduces
the specified source constructor from140,639,095,370 to47,439,839
representation witnesses. These are **before** the final quartic compiler;
no final polynomial count or new small-equation frontier point is claimed.
The universal ordinary proof and count-only finite checks are included.

The new short-equation research includes a literal
[`twelve-positive100/70`](research/ordinary-unit-products/README.md)
equation, materialized from the report-only manuscript arriving in
`c1a102936a`. An early carrier congruence proves the rank bound needed
to use the ordinary strong norm before eliminating its root. This removes
one multiplication and lowers degree78 to70. The two-way witness maps,
selected nonzero leading coefficient, independent circuit/algebra checks
and normal/optimized receipts are included. This subsumes our independently
reconstructed101/78 checkpoint, also present in the arriving round11 package.
[`short-unit-products`](research/short-unit-products/README.md) retains that
checkpoint and a separate thirteen-positive90/55 tradeoff.
The latter is now improved to
[ninety operations and degree51](research/ordinary-unit-products/ORDINARY13.md)
by the same early-rank theorem, with no added unknown or gate.

An earlier nine-positive degree reduction collected the arriving radical
majorant's1,753-operation evaluator into1,065 operations at the
same degree1,158,228. Reusing its existing D register collects654 terms
into312, and exact polynomial substitution/remap certificates preserve
the entire original polynomial. See
[`radical-d-shared`](candidates/radical-d-shared/README.md) and
[the nine-variable review](PROPOSAL_REVIEW_WAVE11_NINE.md).
Later whole-radical representations reach722/1,158,228 and953/999,518;
their distinct polynomials, sources and tuple costs are recorded in the
latest comparison rather than conflated with this identity checkpoint.

For unrestricted integers,
[`joint22-centered`](candidates/joint22-centered/README.md) combines two new
proposals by the invertible polynomial shear `y_old=y+f*o`. It needs only
one extra addition in the118-operation joint22 circuit, while cancellation
lowers degree16 to14. The result has22 integer unknowns and119 operations,
improving the delivered degree14 evaluator by four gates. Complete inverse
row maps, the whole fixed six-port tuple and an exact leading form are checked.

1. Further optimize the literal433-operation and953-operation circuits,
   preserving their exact polynomials. Search for shared powers and algebraic
   rearrangements that
   remove live gates, with local exact identities and independent modular
   evaluation/topology checks.
2. Simplify the short positive equations and new root/guard mergers.
   Seek an actual improvement over the existing variable/degree/operation
   choices, proving both directions of each witness transformation.
3. Reduce the printed constant recipes. The shortest inspected full page
   contains a436-character base62 action seed and a complete decoder.
   A shorter seed or arithmetic decoder is useful
   only if the complete definition remains printed and independently
   reconstructs the entire coherent tuple.
4. Explore alternate proof-certificate and flow encodings. Identify a
   complete global polynomial and its cost before comparing it with a
   finished endpoint; keep unbounded aggregation obligations explicit.

The [Hilbert Tenth transfer](candidates/fixed-root-elimination/README.md)
now supplies14-positive73/342 and75/293 equations. Its signed-positivity
obligation is closed by an ordinary fixed-blank proof and independent review;
literal circuits, exact degree witnesses and normal/optimized checks pass.
Frozen source emitters and arrays were read as inert metadata.
The [ordinate-centered extension](candidates/fixed-root-centers/README.md)
adds74/312 and76/191, with a separately reviewed balanced-unit integrality
argument before the ordinary signed-root reconstruction.

Python algebra, explicit circuits and manuscript derivations remain useful
validation tools. They do not replace the unbounded ordinary correctness
arguments. A successful reduction will be saved as a separate candidate,
with its source pins, precise metrics and verification receipt.

## Preserved formal checkpoint

Commit `d0f3481b96` and its predecessors passed the3913-job library build
and the dedicated checks recorded in their commit messages. The already
completed `OnePageDisplay54` source and13-API audit are also retained;
these checks finished before the pause. Remaining unfinished files under
`Lean/` are work in progress and are not evidence for a completed theorem.
The one-page PDF and both TeX sources are committed. The requested full
internal-ZFC consistency calibration remains a separate open obligation.


The [interpolation review](PROPOSAL_REVIEW_TWELVE_INTERPOLATION.md) and
[congruence review](reviews/congruence-certificates-peer.md) now pass their
ordinary proofs and normal/optimized finite release checks. The former
introduces12-integer equations and improves the13-integer1072-degree
point to190 operations. The latter gives14-integer148/414 and a free
positive J; an identical polarized tail composes with that positive
change to give12-positive96/70. Complete tuples remain separated. The
canonical13-positive90/51 page is retained for these minor circuit changes;
the ten-positive proposal is now reviewed and its identical shared-product
sibling reaches123/816.


The next checked wave improves several domains at once. The
[position-zero norm family](candidates/position-zero-norm-sharing/README.md)
reaches9-positive419/1472168 and compact427/1626248, with1056/997810 as
a lower-degree choice. The [scaled ten-positive sibling](candidates/ten-positive-scaled-norm-shared/README.md)
gives123/816 after full ordinary and normal/optimized parent review.
The [valuation twelve-integer review](PROPOSAL_REVIEW_VALUATION_INTEGER12.md)
accepts215/2400 and209/2912; the [trace shared norm](candidates/interpolation-shared-norms/README.md)
reaches13-integer184/1072. All keep their whole coefficient tuples.

The [projected direct review](PROPOSAL_REVIEW_QUARTICS407888.md) accepts
407-natural/888-integer quartics; the917-integer companion has lower
height63,906,036 and6,986 terms. The502-natural self-bounding-radius
sibling remains a verified checkpoint. Composing its radius with the
new radix and optimizing the valuation norms are active next steps.
The complete ten-positive page now passes the independent rebinding,
formula and layout review and has become the canonical display. The prior
thirteen-positive page is preserved. Lean remains paused.


The [valuation shared-norm packet](candidates/valuation-shared-norms/README.md)
now freezes12-integer208/2400 and202/2912. Seven exact cut identities and
an every-node proof preserve the entire polynomials. A separate graded-lex
calculation over all six formal ports certifies the actual child leading
terms and their nonzero beta-only specialization. Both full candidate
modes and root's independent review pass.

The [projected factorial-radius family](candidates/projected-factorial-radius/README.md)
now reaches399 naturals/317 rows/8286 terms/height83843274, with complete
402/403/453-variable alternatives. The summed radix bounds both factorial
binomials even when the proposed t! output is initially zero. The paired
factorial inequality supplies the strict remaining low-digit bound before
the product formula is used. All six literal quartics, raw exports and
rational SOS restorations pass normal/optimized checks and root review.
A new integer guard/projection family is being checked separately; its
unsealed counts are not yet table entries. Lean remains paused.


The [projected-radius integer companions](candidates/projected-radius-integers/README.md)
now freeze862/863/865-variable quartics at height2445790974704 and a
891-variable lower-height point at63905891. Fresh161-seed/506-derived
actual-row sign proofs precede arithmetic interpretation; reverse signed
restoration recovers every guard before natural semantics. All four complete
coefficient tables, both checker/build modes and root's ordinary review pass.
The prior888/917 and1190 checkpoints remain preserved. Further semantic
sign relaxations and lower-height retention are under separate research;
no unmaterialized count is promoted.
