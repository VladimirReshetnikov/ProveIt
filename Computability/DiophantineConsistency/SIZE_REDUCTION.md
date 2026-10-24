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
| Positive integers | 10 | 89 / 95 | 288 / 262 | Uncentered saturated b transport; fewer-operation tradeoff, canonical page retained |
| Positive integers | 10 | 91 / 92 / 97 / 98 | 283 / 278 / 258 / 254 | Existing b transport; one-operation minor checkpoint, canonical page retained |
| Positive integers | 10 | **92** | **283** | Coprime saturated Pell product; complete canonical page and indexed constants |
| Positive integers | 10 | 93 | 278 | Sharp saturated center; lower-degree tradeoff |
| Positive integers | 10 | 98 / 99 | 258 / 254 | Direct positive X and upper/sharp saturated centers |
| Positive integers | 10 | 97 | 368 | Existing-square transport weight; one-operation saving, higher degree |
| Positive integers | 10 | 102 | 344 | Existing-square transport and direct positive X; operation/degree tradeoff |
| Positive integers | 10 | 98 | 360 | Positive index weight, zero-offset base; preserved predecessor page |
| Positive integers | 10 | 103 | 332 | Positive index weight and direct positive X; degree tradeoff |
| Positive integers | 10 | 98 | 368 | Zero-offset scaled base, shared muY and expanded transport |
| Positive integers | 10 | 103 | 340 | Direct positive X, shared carrier and expanded transport |
| Positive integers | 9 | 405 / 413 | 1,191,570 / 1,316,546 | Tight main folding and unshifted carrier; original31 / smaller compact54 tuples |
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
| Integers | 12 | 145 / 141 | 1,200 / 1,456 | Scalar intersective carrier, main folding and four-root prime separation |
| Integers | 13 | 135 | 536 | Trace before signs, main-root folding and quadratic projection |
| Integers | 14 | 117 | 312 | Signed main-root recovery, quadratic projection and reduced guard |
| Integers | 20 | not optimized | 18 | Coordinated polynomial projection |
| Nonnegative integers | 399 | not optimized | 4 | Projected source, summed factorial radix and rational SOS contraction;8,286 terms |
| Nonnegative integers | 402 / 403 / 453 / 667 | not optimized | 4 | Complete term/height alternatives;6,882 /8,229 /5,059 /3,632 terms |
| Integers | **517** | not optimized | **4** | Round14 derived factorial carrier; 310 rows, 6,774 terms, height 3,904,267 |
| Integers | 519 | not optimized | 4 | Round14 lower-height alternative; 321 rows, 6,253 terms, height 411,060 |
| Integers | 554 | not optimized | 4 | Ten output squares, 55 guards; 362 rows, 6,927 terms, height 2,445,790,974,704; earlier source pipeline |
| Integers | 557 | not optimized | 4 | Ten output squares, 56 guards, CSE/default projection; 6,937 terms, height 2,445,790,974,704 |
| Integers | 577 / 576 | not optimized | 4 | Existing-square 63-guard CSE projections; 5,754 / 5,818 terms, heights 964,213 / 45,769,613 |
| Integers | 787 / 657 / 599 / 584 | not optimized | 4 | Existing-square 63-guard lower-height CSE projections; heights 4,750 / 737,653 / 737,653 / 938,261 |
| Integers | 575 | not optimized | 4 | Squared-output 64-guard CSE/default projection; 7,225 terms, height 2,445,790,974,704 |
| Integers | 580 / 579 | not optimized | 4 | Squared-output 64-guard CSE projections; 5,768 / 5,832 terms, heights 964,213 / 45,769,613 |
| Integers | 790 / 660 / 602 / 587 | not optimized | 4 | Squared-output 64-guard CSE low-height projections; heights 4,750 / 737,653 / 737,653 / 938,261 |
| Integers | 591 | not optimized | 4 | Common-radius72-guard CSE/default projection;9,657 terms, height2,445,790,974,704 |
| Integers | 596 / 595 | not optimized | 4 | Common-radius72-guard CSE projections;8,328 /8,232 terms, heights964,213 /45,769,613 |
| Integers | 822 / 684 / 618 / 603 | not optimized | 4 | Common-radius72-guard CSE low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 594 | not optimized | 4 | Squared-radius72-guard raw/default projection;9,588 terms, height2,445,790,974,704 |
| Integers | 598 / 597 | not optimized | 4 | Squared-radius72-guard raw projections;8,564 /8,504 terms, heights964,213 /45,769,495 |
| Integers | 824 / 683 / 619 / 605 | not optimized | 4 | Squared-radius72-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 595 | not optimized | 4 | Shifted-t72-guard raw/default projection;9,586 terms, height2,445,790,974,704 |
| Integers | 600 / 599 | not optimized | 4 | Shifted-t72-guard raw projections;8,770 /8,696 terms, heights964,213 /45,769,499 |
| Integers | 828 / 683 / 621 / 607 | not optimized | 4 | Shifted-t72-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 598 | not optimized | 4 | Power-output73-guard raw/default projection;9,600 terms, height2,445,790,974,704 |
| Integers | 603 / 602 | not optimized | 4 | Power-output73-guard raw projections;8,794 /8,710 terms, heights964,213 /45,769,499 |
| Integers | 831 / 686 / 624 / 610 | not optimized | 4 | Power-output73-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 601 | not optimized | 4 | Encoded-index74-guard raw/default projection;9,661 terms, height2,445,790,974,704 |
| Integers | 606 / 605 | not optimized | 4 | Encoded-index74-guard raw projections;8,808 /8,724 terms, heights964,213 /45,769,499 |
| Integers | 834 / 689 / 627 / 613 | not optimized | 4 | Encoded-index74-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 604 | not optimized | 4 | Output-sign75-guard raw/default-affine projection;9,676 terms, height2,445,790,974,704 |
| Integers | 609 / 608 | not optimized | 4 | Output-sign75-guard raw projections;8,823 /8,739 terms, heights964,213 /45,769,499 |
| Integers | 837 / 692 / 630 / 616 | not optimized | 4 | Output-sign75-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 607 / 608 / 610 | not optimized | 4 | Factorial-bound76-guard projections;10,042 /8,706 /8,611 terms, height2,445,790,974,704 |
| Integers | 612 / 611 | not optimized | 4 | Factorial-bound raw projections;8,849 /8,753 terms, heights964,213 /45,769,499 |
| Integers | 840 / 695 / 633 / 619 | not optimized | 4 | Factorial-bound raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 610 / 611 / 613 | not optimized | 4 | Paired77-guard projections;10,053 /8,717 /8,622 terms, height2,445,790,974,704 |
| Integers | 639 | not optimized | 4 | Paired77-guard lower-height projection;5,605 terms, height63,905,891 |
| Integers | 843 / 698 / 636 / 622 | not optimized | 4 | Paired77-guard raw projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 642 | not optimized | 4 | Comparison-base lift, lower-height projection;5,565 terms, height63,905,891 |
| Integers | 1,493 / 846 | not optimized | 4 | Retained-wire78-guard equations;4,981 /3,813 terms, heights427 /4,750 |
| Integers | 701 / 637 / 623 | not optimized | 4 | Retained-wire78-guard projections;5,575 /8,925 /8,889 terms, heights737,653 /737,653 /938,261 |
| Integers | 613 / 614 / 616 | not optimized | 4 | Signed comparison-base lift and private sign orbits;10,013 /8,677 /8,582 terms, height2,445,790,974,704 |
| Integers | 613 | not optimized | 4 | Raw/default-affine projection;9,661 terms, height2,445,790,974,704 |
| Integers | 1,190 / 1,224 | not optimized | 4 | Preserved synchronized checkpoints, now dominated by917 |

Operations mean live binary `+`, `-`, and `*`, with squares and fixed-scalar
multiplications charged and fixed numeral leaves free. Variable counts
exclude named polynomial abbreviations. Positive, natural and unrestricted
integer domains are compared separately. These are useful points, not the
complete frontier or a global optimality claim.

The maintained [equation.pdf](equation.pdf) now displays the10-positive
101-operation degree368 equation in full, including every constant, with
standalone [TeX](equation.tex). It retains the full fixed recipe and saves
one operation and degree20 against the preserved102/388 page. This combined
update includes a fixed root weight, I=ic² and the positive short projector,
with full positive witness proofs. The earlier13-positive90/51 page remains
a lower-degree/cost alternative with three more unknowns.

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
then-canonical13-positive90/51 page was retained for these minor circuit changes;
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


The [identical integer14 simplification](candidates/constructive-integer14-shared/README.md)
reduces147 to145 live operations at unchanged degree568. Two complete
`(1+x)-1=x` substitutions preserve the entire polynomial and all six
fixed coefficients. Root reviewed the literal checker, all node maps,
normal/optimized replays and all30 sealed files. The lower-degree
148/414 and lower-cost137/792 alternatives remain useful tradeoffs.
The then-current10-positive105/408 PDF and TeX are unchanged by this minor
integer-domain simplification; Lean remains paused.


The [mixed retained-wire family](candidates/projected-radius-mixed-retained/README.md)
now gives1,580/933/788/724/710 unrestricted integer variables, all at
exact degree4. It keeps all original raw rows and coefficients, proves
A and D nonnegative from four original-row bounds, and copies107 guard
triples into the literal reviewed994 equation, with six fresh Legendre
witnesses for its two remaining guards. The full592-wire map is over
integers. All five collected quartics and complete signed inverses pass
independent and deterministic checks in both Python modes. Heights remain
427/4,750/737,653/737,653/938,261; each matched159-guard sibling loses
156 coordinates,52 rows and780 terms. The smaller706-variable, larger-height
family remains a separate tradeoff. The canonical PDF/TeX and Lean are unchanged.


The [signed main-root reduction](candidates/constructive-integer14-quadratic/README.md)
now reaches14 unrestricted integer variables,121 operations and exact
degree312. Absolute-value Pell folding recovers the missing main norm
before the signed rank bootstrap; a whole-product absolute height bound
resolves the quadratic projection for both signs of H. Explicit integer
n maps preserve zero existence in both directions. The complete proof,
all six original coefficients, universal formula binding, literal35-term
norm, exact leading form and normal/optimized replays pass independent
and root review. This improves both cost and degree over14-integer
137/792,145/568 and148/414, which remain preserved checkpoints. It has
more variables and operations than the then-current10-positive105/408 page,
so that complete PDF/TeX remains the canonical display. Lean is paused.


The [contracted mixed-bound family](candidates/projected-radius-mixed-bounds/README.md)
now reaches988/729/703/701/700 unrestricted integer variables at degree4.
All585 original body rows are unchanged. Restoring592 raw wires over
integers licenses the four actual t,n,A,D row bounds;107 copied guard
triples plus six fresh A/D witnesses give the literal reviewed994 zero.
Every projection restores the entire988 parent first. Independent and
full deterministic normal/optimized checks pass all1177 row identities,
complete coefficients/inverses and15 corruption controls. The700-variable
polynomial has10,437 terms and height2,445,790,974,704;729 retains lower
height63,905,891. Each matched994/735/709/707/706 checkpoint loses six
variables, two rows and28 terms. The710-variable retained-wire option
has much smaller height938,261. Canonical PDF/TeX and Lean are unchanged.


Two [identical prefix rewrites](candidates/constructive-integer14-quadratic-shared/README.md)
reduce the new14-integer degree312 equation from121 to119 operations.
Reusing q² and factoring ell(ell+1)k²=(ell*k)(ell*k+k) preserve the entire
polynomial over every commutative ring. Complete148-to146 node coverage,
all removed private definitions, every named register, the full35-term
norm and all six payloads pass independent root review and both complete
checker/rebuild modes. All33 packet seals pass. The signed ordinary proof
and exact nonzero leading coefficient transfer unchanged. This is a minor
saving within the new signed degree312 route; the canonical10-positive
105/408 PDF/TeX remains the separate lower-variable/operation display.
Lean remains paused.


The [thirteen-integer quadratic trace equation](candidates/integer13-quadratic-trace/README.md)
now uses135 operations at exact degree536, down from184/1072. Normalized
trace gives both CRT congruences before signs, the unscaled guard gives
four-root separation, and signed Pell folding restores the main norm.
The whole-product height proof resolves its quadratic projection, then
explicit unrestricted n maps restore the frozen trace endpoint in both
directions. Root reviewed the entire ordinary proof and independent
literal checker; all four normal/optimized checker/rebuild commands pass,
including the full495-term norm, centered425-term degree calculation,
authentic six ports and all138 original archive members. This improves
both current13-integer cost and degree. At that checkpoint, the10-positive105/408 page remained
a separate lower-variable/operation display. Lean is paused.


The [five exact original-row sign consequences](research/guard-seed-consequences/README.md)
remove two factorial-output guards, the moduli-product and CRT quotient
guards, and one endpoint quotient guard before any arithmetic semantics.
The CRT numerator uses its independently proved defining sums, avoiding
a circular quotient dependency. The [complete102-guard family](candidates/projected-radius-mixed-signs/README.md)
now gives973/714/688/686/685 integer variables, all degree4. A literal
102-triple transfer plus15 new Legendre witnesses restores the full988
parent; all integer projections are reversed first. Root reviewed both
ordinary proofs and independent checkers. Full normal/optimized checks
and rebuilds pass every original-row identity, the975-step sign ledger,
all coefficients and inverses. Each matched988/729/703/701/700 parent loses
15 variables, five rows and73 collected terms at unchanged height. The
smaller-coefficient retained710 family and canonical PDF/TeX are preserved;
Lean remains paused.


The [scalar-carrier twelve-integer equations](candidates/scalar-carrier12/README.md)
now use145 operations/degree1200 and141/1456, improving208/2400 and202/2912
with the same twelve unrestricted variables and all six original constants.
A scalar intersective quintic enforces H|K and excludes zero strong scale;
prime-order separation leaves four roots, and signed folding recovers the
missing main norm before its whole-product projection. The completeness
proof keeps one strong witness fixed while selecting the translated
intersective residue. Direct nonodd step-down is proved from the auxiliary
index polynomial. Full independent ordinary review, separate all-register
ring binding, all495 norm coefficients, exact every-gate leading induction,
whole payloads/parent inventory and final normal/optimized checks pass.
Both degrees are halved; cost falls by63 and61 operations. Canonical
10-positive105/408 PDF/TeX remains the lower-variable/operation tradeoff;
Lean stays paused.


The [nine-positive folded-saturation equations](research/nine-folded-saturation/README.md)
now reach414 operations/degree1,355,142 on the full original31 tuple and
422/1,497,238 on compact54-sharp. Saturating the strong norm with the
first Pell radicand allows a two-root equation; coprimality recovers both
squares, then main-Pell folding recovers C=psi_A(B1). Positivity is proved
before extraction, and finite matrix periods construct positive i,j,n.
Both directions retain the exact source/binomial boundary and whole fixed
tuples. Root read the full ordinary proof/checker and verified every
retained source node, every local algebraic cut, centered identity and
actual-coefficient homogeneous witness in both Python modes; both complete
rebuilds pass and all packet seals are checked. Both cost and degree improve
the matched419/427 parents. Lower-degree higher-cost alternatives remain
separate, and canonical10-positive105/408 PDF/TeX is unchanged. Lean is paused.


Two [exact private sign orbits](research/guard-sign-orbits/README.md)
now replace the U and bootstrap-witness guards. Complete raw/contracted
row identities negate U and its sixteen quotient partners together, or
reflect Zminus1 with its two private wires. The independent A>=2 row
bound excludes Z=0 before reflection; U=0 uses the identity branch.
All100 remaining guard values and all643 semantic-prefix coordinates
stay fixed. The [whole100-guard family](candidates/projected-radius-mixed-orbits/README.md)
has967/708/682/680/679 integer variables at degree4. Normalize private
values first, then six fresh witnesses give the literal973 equation;
reverse all signed projections before that step. Root reviewed the full
proofs/checkers and all normal/optimized checks/rebuilds pass. The679
polynomial has397 rows and10,335 terms at unchanged height2,445,790,974,704.
Each matched973/714/688/686/685 checkpoint loses six variables and two
rows. The retained-wire low-height family and canonical PDF/TeX remain
separate tradeoffs. Lean stays paused.

## Tightened nine-positive folding accepted

The [tightened packet](research/nine-folded-saturation-tight/README.md)
now gives409 operations / degree1,191,572 on the whole original31 tuple
and417 /1,316,548 on the separate compact54-sharp tuple. It improves the
frozen414/422-operation equations in both operation count and degree.
The strong ordinate omits J, the auxiliary quotient uses positive j
without a shift, the carrier is Jn+Q, and the first norm shares its
majorant. A new strict-gap proof forces positive margin before root
extraction; two finite matrix periods and a strict carrier bound construct
all three changed positive witnesses. No tuple or domain is weakened.
The [root review](reviews/nine-folded-tight-root-peer.md) records the full
ordinary proof audit, exact degree argument, all four normal/optimized
checks and rebuilds, and closed artifact seals. This nine-variable result
is a separate tradeoff from the maintained ten-positive one-page equation.
Lean remains paused; no new internal-ZFC endpoint is claimed.

## Direct positive J in the ten-variable equation accepted

The [free-J ten-positive equation](candidates/ten-positive-free-j/README.md)
saves two operations, reaching103 at the same exact degree408 and ten
positive unknowns. The enlarged positive J domain is sound: odd main
index recovery gives p=R before q parity, then odd q would force even J
and even R. Coprimality is used only after this contradiction recovers
even q. The J=1 case constructs fresh positive source61 witnesses and
uses its actual unrestricted-positive-J soundness statement. The whole
original tuple and separately calibrated BFS tuple remain distinguished.
The [root review](reviews/ten-positive-free-j-root-peer.md) and
[independent ordinary review](reviews/ten-positive-free-j-ordinary-peer.md)
record the proof and full literal affine-map/degree checks. All four
normal/optimized checks and deterministic rebuilds passed. This minor
two-operation saving does not trigger a new canonical PDF/TeX rendering;
its complete105-operation page remains available pending a substantial
improvement. Lean remains paused.

## Raw100-guard low-height quartics accepted

The [retained-wire100-guard packet](candidates/retained-radius-mixed-orbits/README.md)
gives complete integer quartics in1559/912/767/703/689 unknowns, at
coefficient heights427/4750/737653/737653/938261. Each saves21 unknowns
and seven quadratic rows over its corresponding frozen107-guard raw
parent, without increasing height. All original raw coefficients remain.
An exact zero-set bijection restores592 triangular monic affine wires
and copies all100 guard triples to the actual frozen967 equation before
using its sign theorem; no fresh witness or sign premise is needed for
the bridge. Each signed projection first restores the whole raw parent.
The [root review](reviews/retained-orbits-root-peer.md) records all1277
row identities, complete coefficient collections, four successful
normal/optimized checks/rebuilds and closed seals. The contracted679
quartic remains a different coefficient-height tradeoff. No new Lean
endpoint is claimed and formalization remains paused.

## Smaller signed fourteen-variable guard accepted

The [guard-reduced equation](candidates/constructive-integer14-guard-reduced/README.md)
has14 unrestricted integer unknowns,117 operations and exact degree312.
It removes the explicit v-square factor from the guard. Its new proof
excludes v=0 by rationalizing the remaining two roots and deriving an
impossible CRT divisibility, before using any weak-scale estimate. Both
integer witness maps regenerate only the four private guard coordinates;
the entire degree256 norm and six fixed coefficients are unchanged.
The full output difference has degree at most304, so the complete
nonzero degree312 leading component survives. The
[root review](reviews/integer14-guard-root-peer.md) records all node/guard/
norm identities, four successful normal/optimized checks and rebuilds,
and closed seals. The [initial research note](reviews/signed14-guard-research.md)
also records why two tempting smaller positivity gadgets fail. Lean and
the canonical ten-positive page remain unchanged.

## Ten-positive102/388 accepted

The [shifted strong equation](candidates/ten-positive-shifted-strong/README.md)
now reaches102 operations and exact degree388 in ten positive unknowns.
It uses I=(i+q²)c² and the shorter transport L=HI+b. The shift preserves
the unconditional lower bound and square-ordinate divisibility; a new
rational-rho bound licenses the smaller transport before parity recovery.
Canonical completeness keeps the strong ordinate and constructs a fresh
positive final n, including zero transport quotient. The complete norm
has a nonzero selected coefficient2^28*beta^224 in degree388. The
[root review](reviews/shifted-strong10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-shifted-strong-ordinary-peer.md)
record the full proof, exact gate/degree/whole-tuple checks, four passing
normal/optimized replays and closed seals. A new complete one-page display
is being prepared for the combined gain over105/408; its predecessor
will be preserved. Lean remains paused.

## Canonical page updated to102/388

The maintained [equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) at that checkpoint printed the complete ten-positive102-operation,
exact-degree388 equation, including every fixed constant, on one Letter
page. This batches the direct-J, shifted-strong and shorter-transport
improvements into one update over the preserved105/408 page: three fewer
operations and degree20 lower. The complete436-character seed,62-character
alphabet,943 tiles and closed arithmetic coefficient recipe are unchanged.
The [new page packet](candidates/one-page-shifted10/README.md),
[independent root page review](reviews/shifted10-page-peer.md) and
[CURRENT_EQUATION.json](CURRENT_EQUATION.json) bind the displayed bytes.
Both independent peer modes, renderer replays and full coefficient
reconstruction modes pass; the page was visually reviewed. The previous
[105/408 PDF](candidates/one-page-quadratic10/equation.pdf) and its TeX
remain preserved. Lean formalization remains paused.

## Twenty-one pointwise guard consequences accepted

The [main-root/modulus proof](research/main-root-and-modulus-signs/README.md)
recovers15 main-root signs and six power-modulus signs from the unchanged
raw equations with79 retained guards. Its independent semantic-prefix
proof precedes a strict A>W^W bound, signed-index recovery and negative-root
residue contradiction. Only then does a positive-base power call establish
f0>0 and the final modulus sign. All15 actual exponents are proved positive.
The [root review](reviews/main-root-signs-root-peer.md) and
[independent peer](reviews/main-root-modulus-signs-peer.md) verify the
complete original-row, constructor and21-call ledger; all six root
normal/optimized checks, rebuilds and peer runs pass. At the same body
tuple,79 existing triples and63 fresh Legendre witnesses reach the literal
frozen967 equation. Complete new quartics and signed projections are being
materialized separately; no unverified projected count is added here.
Lean and the current canonical PDF/TeX remain unchanged.

## Fixed root weight lowers ten-positive degree to368

The [weighted-root equation](candidates/ten-positive-weighted-roots/README.md)
has ten positive unknowns,102 operations and exact degree368. It replaces
the full-mu strong shift by I=i*c² and weights only the first root by3.
All signed cancellations are excluded before root extraction: two pairs
would imply mu|8, the third would equate an integer to -1/Delta, and a
zero triple would imply mu|2025, then mu|25 despite mu>=1025. Main folding
then gives the strict bound needed for weighted transport. Canonical
completeness uses the explicit positive shifts i_new=i_old+q² and
n_new=n_old+2*tau. The [root review](reviews/weighted10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-weighted-roots-ordinary-peer.md)
record the full proof and exact circuit/degree/whole-tuple checks. All four
normal/optimized checks and rebuilds pass; the unique leading component
has a positive selected coefficient2^28*beta^184. The prior102/388 packet
is preserved; a complete new page is under review. Lean remains paused.

## Complete79-guard compact quartics accepted

The [materialized compact family](candidates/projected-radius-main-root-signs/README.md)
gives full integer quartics in904/645/619/617/616 variables. The smallest
has376 quadratic rows,10,028 collected terms and coefficient height
2,445,790,974,704; the645-variable point has5,580 terms and height63,905,891.
Every profile saves63 unknowns and21 rows over its matching100-guard
parent at unchanged height. Complete signed inverses first restore all79
guards, then592 raw affine wires. The ordered21-sign theorem supplies
63 fresh witnesses at unchanged body values into the literal967 equation.
The [root review](reviews/main-root-quartics-root-peer.md) records full
coefficient collections, every100 copied/fresh guard-row identity, all
four passing normal/optimized checker/rebuild replays and closed seals.
These are checked whole equations, not estimates from deleting guards.
Lean and the ten-positive display remain separate and unchanged.

## Retained-coefficient79-guard quartics accepted

The [new raw family](candidates/retained-radius-main-root-signs/README.md)
keeps all original coefficients and gives1496/849/704/640/626 integer
variables, with exact degree4 and heights427/4750/737653/737653/938261.
The smallest has386 rows and8,904 collected terms. Each profile saves
63 variables and21 rows at unchanged height against its100-guard parent.
The [root review](reviews/main-root-raw-quartics-root-peer.md) records
the complete1256-row integer bijection into904, all592 affine inverses,
and the composed79-copied/63-fresh-witness transfer into literal967.
All100 target guard rows and every full collected polynomial are checked.
All four root normal/optimized checker/rebuild replays and closed seals
pass. The616-variable compact quartic is a separate height tradeoff;
no new Lean or native calibration endpoint is claimed.

## Comparison-base positivity guard removed existentially

The [comparison-base proof](research/comparison-base-sign/README.md) permits
negative B and then lifts it to a positive comparison base while preserving
all78 other guard values. Its complete1177-row audit accounts for62 private
coordinates,141 unit gates and every46 affected nongate constraints. The
signed-index and21-sign proofs precede the lift; q4 positivity is supplied
at the new tuple, not asserted at the old tuple. Three fresh Legendre
witnesses reach the literal904 source. The [root review](reviews/comparison-base-sign-root-peer.md)
and [independent peer](reviews/comparison-base-sign-peer.md) record full
normal/optimized author and peer replays, all passing. New compact/raw
quartics are being materialized separately; this theorem alone supplies no
new projected coefficient count. Lean remains paused.

## Positive short projector reaches101 operations at degree368

The [short-projector equation](candidates/ten-positive-short-projection/README.md)
uses ten positive unknowns and101 live operations at exact degree368.
Kpos=X(3c-2X)+2 is positive after main folding and obeys
Kpos=H*X*c-2*Kquad. Only2 is cancelled modulo odd H; P is retained in
the whole-product argument. Every old positive zero maps to a new one
by the strictly positive shift n_new=n_old+3*(Kquad/H)-X*c. The
[root review](reviews/short10-root-peer.md) and [independent ordinary peer](reviews/ten-positive-short-projection-ordinary-peer.md)
check the full unbounded proof. All four root normal/optimized checker
and rebuild replays, complete53-entry seals and full coefficient binding
pass. The entire polynomial change has degree at most360, preserving the
degree368 leading component. A complete one-page specification is being
reviewed for the next canonical PDF/TeX update. Lean remains paused.

## Canonical complete page updated to101/368

[equation.pdf](equation.pdf) and committed standalone [equation.tex](equation.tex)
now print ten positive unknowns,101 operations and exact degree368. This
batches the fixed root weight and positive short projector: one operation
and20 degrees below the preceding canonical102/388 page, with the entire
constant recipe unchanged. The [complete new page](candidates/one-page-short10/README.md)
includes all436 seed characters,62-symbol alphabet and943 tiles. The
[independent root page review](reviews/short10-page-peer.md) binds all101
live gates universally, verifies all four full ports, and records passing
normal/optimized page peers, renderer replays, author reconstructions and
27 closed seals. The full rendered page was visually checked. All prior
pages remain preserved; [CURRENT_EQUATION.json](CURRENT_EQUATION.json)
binds the exact canonical PDF, TeX and polynomial. Lean remains paused.

## Complete78-guard compact quartics accepted

The [new compact family](candidates/projected-radius-comparison-base/README.md)
has901/642/616/614/613 integer unknowns, all at exact degree4. The613
profile has375 rows,10,013 terms and coefficient height2,445,790,974,704;
the642 profile has5,565 terms at height63,905,891. Each saves three
unknowns, one row and15 terms at unchanged height against its matching
79-guard predecessor. The [root review](reviews/comparison-base-quartics-root-peer.md)
checks every full coefficient collection and inverse. Complete projection
restoration precedes the signed-B theorem and62-coordinate comparison lift;
all78 guard values stay fixed, while three fresh witnesses guard NEWq4
in literal904. Its21-sign theorem then reaches967. All four root
normal/optimized checker/rebuild replays, nested complete source checks
and34 closed seals pass. The canonical101/368 page and Lean remain unchanged.

## Complete78-guard low-height quartics and independent family peer

The [retained-coefficient family](candidates/retained-radius-comparison-base/README.md)
has1493/846/701/637/623 integer variables at exact degree4, with
heights427/4750/737653/737653/938261. The623 profile has385 rows and
8,889 terms; it saves three variables and one row at unchanged height
against626. The [root review](reviews/comparison-base-raw-quartics-root-peer.md)
records every1255 raw/guard row and901 restriction identity in the exact
1493↔901 integer bijection. Only after complete restoration does the
nonpointwise comparison lift reach904 with fresh NEWq4 witnesses, then967.
All four root normal/optimized checker/rebuild runs and35 closed seals pass.
The [separate family peer](reviews/comparison-base-families-peer.md) independently
checks all ten compact/raw inverse certificates, all raw/guard identities
and62 snapshot recipes. Both focused root replays reproduce its final
receipts and reject nine corruptions. The compact613 family is a separate
height tradeoff. Canonical101/368 PDF/TeX and paused Lean remain unchanged.

## Literal constructor prose correction

The [constructor erratum](reviews/main-root-constructors-erratum.md) corrects
two aliases in the frozen21-sign note: raw36=y+1>=1, and
raw86=(t+x+y+M0+2)^(2^23)>=3. Root checked every cited original row.
The431-step constructor certificate already uses those correct literal
rows, so all exponent-positivity, guard and equation conclusions remain
unchanged. Neither constructor has fixed parity from these premises.
Frozen certificates and polynomials are preserved; subsequent proofs use
the corrected descriptions. Lean remains paused.

## Direct positive X and zero-offset research

The [direct-base research](research/ten-positive-direct-base/README.md)
replaces X=wq by X=q+x and adds a delayed divisibility carrier. Its
complete prototype has ten positive unknowns,107 operations and degree340.
The [ordinary peer](reviews/ten-positive-direct-base-ordinary-peer.md)
checks the unbounded proof and a separate complete free-ring center cut:
remove the H denominator after whole-product projection, then recover q|X,
then justify X/q⁴ as an integer. Full materialized-candidate verification
is underway; this research checkpoint alone adds no accepted frontier.
The [zero-offset draft](research/ten-positive-zero-offset/PROOF.md) proposes
removing the inner constant offset in the scaled main base. Its stronger
ratio estimate suggests one fewer operation at unchanged degree; independent
review and literal checks are pending. The canonical101/368 page and
paused Lean remain unchanged.

## Complete direct-base107/340 endpoint accepted

The [direct-base candidate](candidates/ten-positive-direct-base/README.md)
has ten positive unknowns,107 live operations and exact degree340. It
replaces X=wq by X=q+x and recovers q divisibility from a new carrier
after the whole-product projection removes H. The [root review](reviews/direct107-root-peer.md)
and [ordinary peer](reviews/ten-positive-direct-base-ordinary-peer.md)
verify the complete proof chronology and positive witness map. All four
root normal/optimized checks and rebuilds pass, with61 closed seals,
full four-port binding, universal center/norm identities and an attained
nonzero degree340 coefficient. This lowers degree by28 at six extra
operations relative to101/368. The cheaper complete canonical page stays
unchanged; no global optimum or new Lean endpoint is claimed.

## Bootstrap guard exchange accepted; coefficient benefit still being measured

The [guard-exchange proof](research/bootstrap-guard-exchange/README.md)
replaces base0.T's sign guard by the bootstrap Zminus1 guard, keeping78
guards. Signed-A/B index recovery and four actual source calls exclude
negative A without assuming raw86 even or interpreting a factorial early.
The converse changes one free bootstrap coordinate, six gates and one
constraint. The [root review](reviews/bootstrap-guard-exchange-root-peer.md)
and [independent peer](reviews/bootstrap-guard-exchange-peer.md) check
both whole-source existence maps. Both root author/peer normal/optimized
runs reproduce the final receipts, and all four research seals pass.
Actual coefficient profiling is separate; no new projected count follows
from the exchange alone. The [paired-index proposal](research/paired-index-guards/README.md)
is another unfinished lead, with its exact local factorial/binomial
obligation recorded. Canonical101/368 PDF/TeX and paused Lean are unchanged.

## Complete ten-positive99/368 endpoint accepted

The [zero-offset equation](candidates/ten-positive-zero-offset/README.md)
uses ten positive unknowns,99 live operations and exact degree368. The
stronger directly proved ratio bound permits A=mu*a+1; sharing the
already-needed muY product in A-1=(muY)(X+1) removes a second operation.
The [root review](reviews/zero99-root-peer.md) and [independent ordinary peer](reviews/ten-positive-zero-offset-ordinary-peer.md)
check full fresh canonical completeness, including positive auxiliary T
and final n, and every soundness license. All four root normal/optimized
literal checker/rebuild replays, both focused peer modes and62 closed
seals pass. Complete coefficient payloads, all99 live definitions and the
attained degree368 leading component are bound. This improves101/368 by
two operations. The complete canonical101/368 PDF/TeX is preserved while
minor presentation updates are batched, as requested. Lean stays paused.

## Guard-exchange profile finds no benefit in the tested configurations

The [paired coefficient profile](research/bootstrap-guard-exchange-profile/README.md)
tests both compact/raw sources at five support caps, keeping every setting
and source coefficient except the guarded value fixed within each pair.
All20 profiles in each root normal/optimized replay reproduce the complete
receipts. Integer substitutions verify and every quartic is independently
expanded. The [root review](reviews/bootstrap-profile-root-peer.md) records
unchanged variable/row/support/height metrics and one added term in each
projected exchange. The accepted guard placement is retained. An unrelated
raw baseline order gives a possible613-variable/9661-term point at the
same high coefficient height; a full separate package is under review.
No new accepted frontier follows from this research measurement alone.
Canonical101/368 PDF/TeX and paused Lean remain unchanged.

## Default-affine raw613 support improvement accepted

The complete [raw/default-affine613 quartic](candidates/retained-radius-default-affine/README.md)
reduces the expanded support from10,013 to9,661 monomials at the same
613 integer variables,375 quadratic rows, degree4 and coefficient height
2,445,790,974,704. The exact unchanged1493 input uses support8 for both
affine and quadratic restorations. All880 integer restorations and all
9,661 coefficients were independently replayed in normal and optimized
Python, along with both deterministic rebuilds; see the
[root review](reviews/default-affine613-root-peer.md). All78 original
guards remain. This is a new projection configuration, separate from the
bootstrap guard exchange. The canonical one-page equation remains unchanged.

## Combined direct/zero-offset105/340 accepted

The complete [ten-positive105/340 candidate](candidates/ten-positive-direct-zero-offset/README.md)
combines the direct coordinate X=q+x with A=mu*Y*(X+1)+1 and shared muY.
It improves107/340 to105/340; the accepted99/368 candidate retains the
lower operation count. All107 direct-parent and99 zero-offset-parent
definitions are bound to the same literal105 rows. The ordinary proof
retains delayed q-divisibility, and its positive completeness map uses the
same zero-offset kernels. Root replayed all four normal/optimized checks
and rebuilds, all complete payloads and degree340 certificates; see the
[root review](reviews/direct-zero105-root-peer.md). Lean remains paused.
The canonical101/368 PDF is unchanged while these small gains are batched.

## Paired index guard theorem accepted

The ordinary [paired-index proof](research/paired-index-guards/LOCAL_FACTORIAL.md)
replaces raw1214's sign with V>=1 and replaces the two t/k122 index-slack
guards with one guard on their product. The exact local factorial bridge
uses only calls1/5/6 at retained K/shifted-K pairs; call2 is used only
for parity. This gives77 predicates instead of78 before projection. Both
zero-existence directions and full source identities passed author,
independent peer and root review in normal/optimized Python; see the
[root acceptance](reviews/paired-index-guards-root-peer.md). Projected
equation sizes remain a separate task; no count is inferred from this theorem.

## Complete77-predicate quartic profiles accepted

The [paired-guard profile packet](research/paired-index-guard-profile/README.md)
contains20 complete equations, quartics and integer projection certificates.
Its compact support32/16/8 choices have610/611/613 variables and
10,053/8,717/8,622 terms, at common height2,445,790,974,704; the lower-height
639-variable choice has5,605 terms at height63,905,891. Raw projections
reach843/698/636/622 variables at heights4,750/737,653/737,653/938,261.
Every source row, guard predicate, integer inverse and full quartic was
checked before inheriting the77-guard proof. All four normal/optimized
checker/rebuild replays passed; see the
[root review](reviews/paired-guard-profile-root-peer.md). A product wire
produces the same projected quartics. No variable saving is inferred merely
from guard count. The canonical PDF and Lean sources remain unchanged.

## Reflected auxiliary parameter improves the nine-positive family

The complete [reflected-nine packet](research/nine-folded-reflected-parameter/README.md)
uses G=F(A+C+1)-A. It stays positive before margin recovery, is1 modulo C
and -A modulo F. Signed Pell folding gives the same soundness rank; the
actual odd completeness index removes the reflection sign. The original
and compact whole tuples now have408/1,191,570 and416/1,316,546
operations/degree, saving one operation and degree2. Root ordinary review
and all four normal/optimized checker/rebuild replays passed; see the
[root review](reviews/nine-reflected-root-peer.md). All source bindings and
the canonical page are preserved; Lean remains paused.

## One factorial bound replaces two more index guards

The ordinary [factorial-radius guard proof](research/factorial-radius-guard/PROOF.md)
replaces the retained K/shifted-K index slacks by f0>=2, reducing77 to76
source predicates. A seed without its bound is either at its true index
or has the exact collapsed coordinates X=A,Y=1. Literal digit/remainder
and ceiling equations exclude every collapsed branch before factorial
meaning is used. Both old slacks are then restored; conversely f0=K!>=6
supplies the new bound. An independent ordinary/source peer and both
normal/optimized root replays pass; see the
[acceptance record](reviews/factorial-radius-guard-root-record.md). Projected
counts remain separate. The canonical PDF and Lean sources are unchanged.

## Shared minimal reflection saves two more operations

The complete [minimal-reflection sibling](research/nine-folded-minimal-reflection/README.md)
reuses the stored product F-1 and sets G=A(F-1)+F. It preserves positivity
and both residue interfaces while using only two new operations. The nine-
positive whole-tuple circuits now have406/1,191,570 and414/1,316,546
operations/degree. Root reviewed the complete ordinary proof and all literal
checks, then replayed both checker/rebuild modes; see the
[root review](reviews/nine-minimal-reflection-root-peer.md). Full fixed
coefficients and source domains are retained. The canonical PDF is unchanged.

## Complete76-predicate quartics accepted

The [factorial-radius profile packet](research/factorial-radius-guard-profile/README.md)
contains15 complete equations and full quartics, including607 variables
with10,042 terms at height2,445,790,974,704. Fresh raw configurations give
612 variables/8,849 terms/height964,213 and611/8,753/45,769,499. Lower-height
choices reach840/695/633/619 variables at heights4,750/737,653/737,653/938,261.
All have exact degree4. The full source domain, every integer restoration
and every quartic coefficient passed both independent modes and both
deterministic root rebuilds; see the
[root review](reviews/factorial-radius-profile-root-peer.md). Only after
restoring the complete76-predicate parent is its ordinary theorem applied.
No projected count was inferred from guard count. Lean remains paused.

## Exact odd-rank sharing reaches405/413 operations

The complete [shared odd-rank sibling](research/nine-folded-shared-odd-rank/README.md)
reuses the literal source register RankPlusOne in B1=R+RankPlusOne, since
R=RankPlusOne-1. It deletes one private multiplication and preserves the
entire polynomial for every assignment. Both whole-tuple nine-positive
circuits now have405/1,191,570 and413/1,316,546 operations/degree. Full
node/operand inventories, coefficients, norms and attained-degree checks
passed both checker/rebuild modes under root replay; see the
[root review](reviews/nine-shared-odd-rank-root-peer.md). The canonical
page and Lean pause are unchanged.

## Early output-sign recovery reduces the source to75 predicates

The ordinary [output-sign extension](research/factorial-radius-output-sign/PROOF.md)
removes the raw93 guard. The exact unconditional eight-row ideal gives
N=f*r+(f-1)*s+f>=2 from the retained f>=2,r>=0,s>=0 predicates, before
the prefix proof or any power meaning. This restores the sole missing
early sign premise and reaches the actual76-predicate source; the reverse
map forgets that triple. Root reviewed all source coefficients and both
normal/optimized replays; see the
[root review](reviews/factorial-radius-output-sign-root-peer.md). There
are75 predicates before projection. Actual quartic sizes remain a separate
measurement; no new Lean or canonical-page change is made.

## Complete75-predicate quartics accepted

The [output-sign profile packet](research/factorial-radius-output-sign-profile/README.md)
contains17 complete degree4 equations with all integer inverse certificates
and full coefficients. Raw/default-affine support8/16 reaches604 variables
and9,676 terms at height2,445,790,974,704. Lower-height choices include
609 variables/8,823 terms/height964,213 and608/8,739/45,769,499; raw
low-height profiles reach837/692/630/616 variables at heights
4,750/737,653/737,653/938,261. The early missing sign is rederived from
actual source coefficients before prefix closure, then every domain row,
integer restoration and quartic coefficient is checked. Root replayed
both checker and rebuild modes; see the
[root review](reviews/factorial-radius-output-profile-root-peer.md). The
canonical one-page equation and Lean sources remain unchanged.

## Encoded-index sign is recovered:74 source predicates

The corrected [encoded-index proof](research/encoded-index-sign/PROOF.md)
removes raw59's explicit sign guard. Raw59 is not a power argument: its
only source use is E=raw59+1. Early direct signs give M>=1,E>=0 and a
modified642-coordinate prefix supplies the unchanged43-argument frame.
A weak-radix carry argument restores the factorial index bounds; then only
the first ten actual powers, exact binomial digits and the moduli-product
remainder prove M=product(1+fj)>1, hence raw59>=0. This reaches the actual
75-predicate source before using its semantic chain. Full author,
independent peer and root normal/optimized checks pass; see the
[root review](reviews/encoded-index-sign-root-peer.md). There are74
predicates before projection. No projected metric, Lean or page change is
claimed by this source theorem alone.

## Identical-polynomial transport contraction reaches98/103 operations

The complete [expanded-transport graphs](research/ten-positive-expanded-transport/README.md)
have ten positive inputs and98 operations at degree368, or103 operations
at degree340. Expanding W=1+gL moves L*B into the center, saving one
operation with the identical polynomial. The direct version also shares
q(q-1) in its carrier, saving a second. Full literal row maps, recursive
free-ring coefficient identities, whole payloads and all four normal/optimized
checker/rebuild root replays pass; see the
[root review](reviews/ten-expanded-transport-root-peer.md). Every parent
positive witness and ordinary proof step transfers by identity. Lean remains
paused; the canonical101/368 page is unchanged while minor gains are batched.

## Complete74-predicate quartics reach601 integer unknowns

The [encoded-index profile packet](research/encoded-index-sign-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches601
variables,9,661 terms and height2,445,790,974,704. Lower-height alternatives
reach606/8,808/964,213 and605/8,724/45,769,499 (variables/terms/height).
Every original domain row, both directions of the full raw/compact integer
bijection, every fresh signed inverse and every quartic coefficient passed
normal/optimized root replay, along with both deterministic rebuilds. The
modified prefix/frame and independent74-predicate source peer are checked
before semantic calibration; see the [root review](reviews/encoded-index-profile-root-peer.md).
No count was extrapolated from a deleted guard. Earlier families remain
preserved. Lean stays paused and the canonical one-page equation is unchanged.

## Actual power-output sign is recovered:73 source predicates

The [power-output proof](research/pow2-output-sign/PROOF.md) removes the
raw104 sign guard. Exact early rows give B=raw104>=-1 and D=B+2>=1;
the modified641-coordinate prefix and weak frame still bound every
positive base/index. Under B=-1, actual indices t and k122=t+1 are
consecutive. Sign-safe calls0/9 recover the paired seeds, then actual call2
forces a positive residue strictly below its divisor, a contradiction.
No local factorial semantics precede this sign recovery. Both existence
maps reach the actual74-predicate parent before inheriting its theorem.
Root read the full proof and checker and matched author/peer receipts in
both modes; see the [root review](reviews/pow2-output-sign-root-peer.md).
There are73 source predicates. Projected sizes require a separate complete
materialization; the measured601-variable family, canonical PDF and Lean
pause are unchanged.

## Six e13 proposal packages screened with reproducible inert checks

The [six-archive intake](research/incoming-e13c748234/README.md) records
complete hashes,2145 member pins, historical reuse and explicit domain
comparisons. Independent data checks reproduce33 full quartic expansions,
39 supported DAG censuses and54 coefficient bindings in both interpreter
modes. After the source76–110 placement, exact old inputs are read from
pinned Git blobs in memory. Root reviewed the report/checker and matched
both sealed receipts; see the [root review](reviews/incoming-e13-root-peer.md).
Squared/centered factorial and common modular Pell identities are useful
new research leads. The squared-radius transfer has an explicit missing-
K-bound obstruction, so no one-gate compiler improvement is assumed.
Natural395/394 and other advertised endpoint tradeoffs await their own full
ordinary/literal calibration review. The current measured601-integer family
and98/368 ten-positive evaluator are unchanged; Lean remains paused.

## Replaying sealed checks after incoming archive placement

The source76–110 placement removed old incoming ZIP paths. The separate
[compatibility runner](research/historical-archives-compat/README.md) supplies
35 exact hash-checked historical ZIPs temporarily from pinned Git objects,
runs an argv command, then removes only unchanged files it created. Existing
paths are preserved and concurrent wrapper lifetimes are serialized. This
keeps all sealed proof/checker bytes unchanged. For example:

```sh
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B Computability/DiophantineConsistency/research/encoded-index-sign-profile/check.py --output /tmp/encoded74-check.json
```

Root read the complete wrapper and replayed both modes of all10 integrity
controls; the frozen601 normal/optimized receipt bytes also match under the
runner. See the [root review](reviews/historical-archives-compat-root-peer.md).
This changes reproduction only, with no equation or Lean change.

## Complete73-predicate quartics reach598 integer unknowns

The [power-output profile packet](research/pow2-output-sign-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches598
variables,9,600 terms and height2,445,790,974,704. Lower-height alternatives
reach603/8,794/964,213 and602/8,710/45,769,499 (variables/terms/height).
Only raw104's guard is deleted. Every original domain row, both directions
of the592-coordinate raw/compact integer bijection, every fresh signed
inverse and every quartic coefficient passed normal/optimized root replay,
as did both deterministic rebuilds. The weak641-prefix/43-frame source
interface and branch-local sign proof precede inherited calibration; see
the [root review](reviews/pow2-output-profile-root-peer.md). All46 corruption
controls fail as expected. Earlier families remain preserved. Lean stays
paused and the canonical one-page equation is unchanged.

## Shifted-t index guard is recovered:72 source predicates

The [shifted-t proof](research/shifted-t-index-guard/PROOF.md) removes raw825's
explicit sign guard. Partial parent proofs first recover104 and the four
other required Pell pairs without using825. The actual choose-one row then
excludes the collapsed shifted-t pair: its numerator is at least b² for
t>=2, while the t=1 ceiling forces a digit at least2. Only after this
contradiction does the signed-index theorem recover825>0. No factorial1
meaning or premature call7 interpretation is assumed. A fresh triple reaches
the actual73-domain parent before using its complete theorem. Root read the
entire proof/checkers and matched author and independent peer receipts in
both modes; see the [root review](reviews/shifted-t-index-guard-root-peer.md).
There are72 predicates before projection. The measured598-variable family
remains current until fresh complete profiles pass. Lean and page unchanged.

## Complete72-predicate quartics reach595 integer unknowns

The [shifted-t profile packet](research/shifted-t-index-guard-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches595
variables,9,586 terms and height2,445,790,974,704. Lower-height alternatives
reach600/8,770/964,213 and599/8,696/45,769,499 (variables/terms/height).
Only raw825's guard is deleted. Every domain row, both directions of all592
raw/compact restorations, every fresh signed inverse and every quartic
coefficient passed normal/optimized root replay and both deterministic
rebuilds. Both the95-identity source checker and independent15-cut peer are
pinned and replayed, with exact call7/t=1 chronology and50 corruption
controls; see the [root review](reviews/shifted-t-index-profile-root-peer.md).
Earlier families remain preserved. This is the direct quartic lane; the
fewer-variable norm/display tradeoffs remain separate. Lean stays paused
and the canonical one-page equation is unchanged.

## Squared-radius RAW prototype: complete finite checks accepted

The [separate RAW prototype](research/squared-radius-source-prototype/README.md)
changes only radius row75 and exchanges f>=2 for f>=K at the same guard
triple. All12 complete equations, signed inverse certificates, quartics and
censuses passed root normal/optimized checks and both deterministic rebuilds.
The default prototype has594 variables and9,588 terms: one fewer variable
and two more terms than595/9,586. No new consistency endpoint is inferred
from that measurement. The complete ordinary source proof and fresh
canonical completeness remain separate review obligations; see the
[root finite review](reviews/squared-radius-prototype-root-peer.md).
The accepted595-variable family, canonical page and Lean pause are unchanged.


## Complete squared-radius equations:594 integer unknowns

The [complete ordinary source proof](research/factorial-square-guard-exchange/FULL_SOURCE.md)
and its independent audit are now accepted and exactly bound to the
[frozen RAW prototype](research/squared-radius-source-prototype/README.md).
All12 materialized quartics therefore inherit the ordinary Con(ZFC)
calibration. The first radius is f² and its one guard is f>=K; the second
radius remains g*t². Direct bounds justify all8 range graphs before product
semantics, and completeness recomputes every radix/frame/Pell witness.
Root replayed both complete source audits in normal and optimized Python;
all receipts match. See the [combined root review](reviews/factorial-square-calibration-root-peer.md).

The default complete degree4 equation has594 integer unknowns,9,588 terms
and height2,445,790,974,704. Lower-height alternatives are598/8,564/964,213
and597/8,504/45,769,495 (variables/terms/height). The595-variable predecessor
has two fewer terms and is preserved. This resolves the preceding prototype's
ordinary-proof obligation without changing its sealed finite-scope flags.
The canonical ten-positive page remains unchanged; Lean remains paused.


## Complete common-radius quartic:591 integer unknowns

The [common factorial-radius proof](research/common-factorial-square-radius/PROOF.md)
keeps72 predicates with both radii f² and the one joint guard f>=K+g.
It derives g>=0 before f, repairs the t=1 shifted-seed argument using g<=f,
and rebuilds every radix/frame/Pell witness for completeness. The exact
RAW binding and a separate invertible integer row operation sharing the
base moduli license all24 checked [RAW/CSE quartics](research/common-squared-radius-source-prototype/README.md).
Root's four ordinary replays, both finite checks and both deterministic
rebuilds all pass and match their seals; see the [combined review](reviews/common-squared-radius-root-peer.md).

CSE support16/default gives591 integer variables,9,657 terms and height
2,445,790,974,704 at degree4. Lower-height CSE choices include596/8,328/964,213
and595/8,232/45,769,613 (variables/terms/height). The594-variable predecessor
has69 fewer terms and is preserved. This is the direct quartic family;
other domains and compact norm equations remain separate tradeoffs.
The canonical ten-positive page is unchanged and Lean remains paused.


## Mixed-radix seed: complete-recipe comparison is negative

The [closed mixed-radix experiment](research/mixed-radix-bfs-seed/README.md)
saves221–233 seed bits and37–39 base62 symbols, while its complete printed
recipes grow by26–35 nonwhite characters after paying for the product and
halt decoder. Root read the full proof/renderer and matched both full
render/reconstruction receipts; every action, tile and coefficient byte
remains exact. See the [root review](reviews/mixed-radix-seed-root-review.md).
All three standalone PDF/TeX siblings are preserved. The canonical page
remains the better tested display; this does not rule out other decoders.


## Squared output bounds give 575 integer unknowns

The [64-predicate ordinary proof](research/range-output-square-frame/PROOF.md)
replaces eight range output bounds by their squares, then derives their
quotient signs after positive-power recovery. All earlier seed arguments
keep their required signs; a retained positive ordinate is essential to the
signed-output lemma. Fresh completeness rebuilds the entire new frame and
private Pell data. The exact binding licenses all 24 checked
[RAW/CSE quartics](research/squared-range-frame-source-prototype/README.md).
Root's six ordinary replays, both complete finite checks and both
rebuilds pass; see the [combined review](reviews/squared-range-frame-root-peer.md).

The complete CSE/default equation has 575 integer unknowns, 7,225 terms and
height 2,445,790,974,704 at degree 4: 16 fewer variables and 2,432 fewer terms
than 591/9,657. Lower-height alternatives give 580/5,768/964,213 and
579/5,832/45,769,613 (variables/terms/height). These improve the direct
quartic family; compact norm equations remain separate. All predecessors
are preserved, the canonical ten-positive page is unchanged and Lean is paused.


## An existing square reduces the direct quartic family to 572 integers

The [63-predicate ordinary proof](research/power0-output-square-frame/PROOF.md)
uses the existing square of the first power output in its frame and derives
that output's sign after a separate guarded output orients the t pair.
Both earlier pairing arguments use the replacement support. Fresh
completeness rebuilds the entire new frame and private Pell data.
The [complete RAW/CSE quartics](research/power0-square-frame-source-prototype/README.md)
are exactly bound to that proof; see the
[combined root review](reviews/power0-square-frame-root-peer.md).

The best equation has 572 integer unknowns, 7,211 terms, degree four and
coefficient height 2,445,790,974,704. It saves three variables, one residual
and fourteen terms against 575/7,225 at unchanged height. Lower-height
alternatives give 577/5,754/964,213 and 576/5,818/45,769,613
(variables/terms/height). All 24 full polynomial checks, both independent
checker modes and both root rebuilds pass. The compact canonical page
is unchanged by this quartic step; Lean remains paused.


## Canonical complete page: 98 operations and exact degree 360

The [updated equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) now print the complete ten-positive equation
at degree 360 in 98 operations, improving the preserved 101/368 page by
three operations and eight degrees. The full constant body remains on the
same Letter page in 9-point body type: all 436 seed characters, decoder,
943 tiles and four coefficient recipes are retained verbatim.

The [ordinary index-weight proof](research/ten-positive-index-weight/PROOF.md)
uses the pre-transport inequality k>H to replace HI by kI. Its positive
polynomial n shear proves completeness. A separate direct-base equation
has 103 operations and degree 332. All six root source audits, actual-TeX
parsing, both render modes and full tuple reconstructions pass; see the
[root review](reviews/ten-index-weight-root-peer.md) and
[page evidence](candidates/one-page-index-weight10/README.md).
The selected nonzero homogeneous component proves exact degree rather
than a sampled degree. Every earlier page, including its TeX, is preserved.
Lean remains paused; no global simplicity minimum is claimed.


## Existing-square transport: 97/368 and 102/344 alternatives

The [complete square-weight equations](research/ten-positive-square-weight-tradeoff/README.md)
reuse the existing I² gate in L and delete one multiplication. The ordinary
pre-transport inequality I>k>H preserves soundness; the positive polynomial
n shear proves completeness. Exact source, norm and leading-form checks
give 97 operations at degree 368, or 102 operations at degree 344.
These save one operation against 98/360 and 103/332 while raising degree.
All six fresh root normal/optimized replays pass, with 27 actual-artifact
corruptions rejected in each mode; see the
[root acceptance](reviews/ten-square-weight-root-peer.md).
The canonical 98/360 one-page PDF/TeX is retained, all predecessors are
preserved and Lean remains paused.

## A second signed output reduces the quartic family to 569 integers

The [62-predicate ordinary proof](research/power3-output-square-frame/PROOF.md)
appends the square of output106, uses it only in the frame, and removes
that output's scalar guard. Actual call3 keeps output106. Independent
supports orient its t pair before the signed residue recovers106=f^t>0.
The delayed bound for130 and its five related signs are restored before
later source semantics. Fresh completeness rebuilds the changed frame
and private Pell witnesses. Both common factorial radii remain unchanged.

The [complete equations and certificates](research/power3-square-frame-source-prototype/README.md)
include 24 RAW/CSE configurations. The best has **569 integer unknowns,
363 residuals, 7,197 monomials and exact degree four**, with coefficient
height 2,445,790,974,704. Its 885 signed restorations recover every parent
coordinate; none is unconstrained. Savings vary by configuration, as
recorded in the [combined root review](reviews/power3-square-frame-root-peer.md).
Lower-height CSE alternatives include 574/5740/964213, 573/5804/45769613,
581/5731/938261, 596/5521/737653, 654/4784/737653 and 783/3599/4750
(variables/terms/height). The retained parent is 1454/4791/428.

Both ordinary checker modes, both complete finite checker modes and both
full rebuilds pass fresh root review and match retained author receipts.
All prior packets remain preserved. This improves the direct quartic
family; the canonical ten-positive 98-operation/degree-360 page is unchanged.
Lean formalization remains paused, and equation-size research continues.

## Direct tile indices shorten the complete printed recipe

The [directly indexed standalone page](research/indexed-tile-enumeration/equation.pdf),
with [TeX](research/indexed-tile-enumeration/equation.tex), removes the
sorted-rank computation for the same 943-tile language. The complete
constant recipe falls from 2,393 to 2,343 nonwhite printed characters;
the whole page falls from 3,217 to 3,167. All index explanations, the full
436-character seed and its 62-character alphabet are counted. The page
retains ten positive unknowns, 98 operations, exact degree 360 and the
same one-Letter-page layout.

The new selector order changes K. Its [ordinary proof and root review](research/indexed-tile-enumeration/PEER_REVIEW.md)
rebuild the entire native witness and cofinal rank controller for the new
coherent tuple; they do not transfer old packed words pointwise. All 430
transitions, 943 tile conjugacies, 66,062 native basis identities, four
complete integers and controller unit/order/lift facts pass independent
checks. Eight fresh root normal/optimized build, render, checker and
artifact runs match the author records; each artifact run rejects 40
actual corruptions and passes two complete controls.

This 50-character gain is retained as a research alternative. The canonical
98/360 PDF and TeX stay unchanged until a larger improvement is ready.
Lean remains paused and the reduction goal continues.

## Six shared sums permit six product guards

The [anchored product-guard proof](research/shared-remainder-product-guards/PROOF.md)
replaces twelve scalar sign guards by six quadratic product guards. It
uses only ten exact source row sums and four retained anchor pairs:
r+s=a+b>=0 together with rs>=0 forces both removed signs. The signs are
restored before any existing Pell or source interpretation is invoked.
Every raw arithmetic coordinate, including the complete W/A/Pell data,
stays fixed; only guard witnesses are rebuilt.

The full parent drops from 1,454 coordinates and 1,248 residuals to
**1,436 coordinates and 1,242 residuals**, with 56 predicate graphs.
Fresh root normal/optimized checks and rebuilds pass, as does the
independent peer review; see the [root acceptance](reviews/shared-remainder-product-guards-root-peer.md).
The literal checker verifies 16 source identities and rejects 23 actual
corruptions. A separate audit checks all 118 old/new graphs and the
32 possible abstract anchor selections, with 192 difference identities.
Only the fixed six replacements are materialized.

Projected quartic savings remain to be measured from complete equations
and certificates. The current best checked direct quartic still has
569 integer unknowns. The canonical compact page is unchanged and Lean
remains paused.

## Eight new proposal archives at 45b399ec51

The [static intake](research/intake-45b399ec51/TRIAGE.md) authenticates all
eight archives, 1,693 members and 237 statically indexed Python files.
It records exact read scopes and distinguishes delivered claims from
accepted results. No incoming program was executed for this checkpoint.
An independent root replay verifies every member hash and the AST index.

The most promising new claims are ten-positive 92/283 and 93/278 saturated
Pell equations, a ten-positive 96/266 coprime-fusion equation, and direct
quartics with 517 or 519 integer variables. Complete mathematical and
code reviews are in progress. The current page and accepted comparison
frontier are unchanged by intake alone. New shared-sum, quotient-frame
and transport-majorant mechanisms are recorded as separate research leads.
Lean remains paused; successful substantial compact improvements will
replace the canonical PDF and its standalone TeX after full verification.

## Complete shared-remainder compiler reaches 557 integer variables

The [new complete finite family](research/shared-remainder-product-source-prototype/README.md)
now realizes the separately approved 56-guard source theorem. Its best
checked default has **557 unrestricted integer variables, 363 rows,
6,937 quartic terms and height 2,445,790,974,704**. This saves twelve
variables and 260 terms against the preserved 569-variable equation,
at the same row count and height. All 24 RAW/CSE profiles, complete
coefficient maps, inverse restorations and exact censuses pass fresh
normal/optimized rebuilds and independent checks; 89 corruption controls
are rejected. The default has 879 signed restorations and no unconstrained
deletion. Actual deltas for every configuration are retained in the packet.

The [root acceptance](reviews/shared-remainder-product-source-root-peer.md)
composes these finite results with the exact complete ordinary source
theorem and native calibration. A finite polynomial check alone does not
supply that interpretation. Earlier packets remain preserved. The
compact ten-positive page and paused Lean work are unchanged by this result.

## Significant compact-page improvement: 92 operations, degree 283

The canonical [PDF](equation.pdf) and standalone [TeX](equation.tex) now
print the [complete saturated Pell equation](candidates/one-page-saturated10/README.md):
**ten strictly positive unknowns, 92 operations and exact degree 283**.
This saves six operations and lowers degree by 77 from the preserved
98/360 page. All constants, tiles, the decoder and complete 436-character
numeral fit on the same Letter page in 9-point body type.

The [ordinary proof](research/ten-positive-saturated-pell/PROOF.md)
establishes both directions with fresh positive witnesses, coprime root
recovery and a global attained degree proof. Its whole indexed native
composition licenses the shorter fixed recipe jointly at all four ports.
Independent actual-TeX parsing binds every displayed definition and the
complete boxed equation to all 92 live gates, and verifies every rendered
front glyph and the whole PDF constant body. Normal/optimized source,
renderer, parser and artifact checks pass. See the
[root promotion review](reviews/ten-saturated-pell-root-peer.md).

Separate complete tradeoffs use 93 operations at degree 278 and direct
positive X charts with 98/258 and 99/254. Earlier pages and complete source
packets remain preserved. No global optimum or new Lean endpoint is claimed.

## A derived anchor permits a seventh product-guard exchange

The [new ordinary source proof](research/shared-binomial-digit-product-guard/PROOF.md)
replaces scalar guards on raw123 and raw564 by one product guard. Retained
raw94/raw95 signs and literal rows derive raw91>=1; with retained raw537,
the exact source identity gives raw123+raw564>=1. The product then restores
both removed signs before any inherited source interpretation. Each
direction fixes the whole raw body and rebuilds only guard auxiliaries.

The complete literal parent has **55 guards, 1,433 variables and 1,241 rows**.
Four exact source ideals, every guard graph, full maps and whole inherited
seals pass independent normal/optimized checks with 27 corruption controls.
See the [root acceptance](reviews/shared-binomial-digit-product-root-peer.md).
No projected improvement is predicted: the measured default remains the
557-variable quartic pending a separate full compiler packet. The canonical
92/283 page and paused Lean work are unchanged.

## Reviewed Round14 direct quartics: 517 and 519 integer variables

The [ordinary review](research/intake-45b399ec51/ROUND14_REVIEW.md)
approves the new factorial/carrier architecture and signed-Pell proof
relative to the named inherited C222/refutation contracts. Complete
[scoped reproduction](research/round14-direct-reproduction/README.md)
and fresh root normal/optimized runs rebuild all 34 distinct endpoint
artifacts exactly, including full quartics, signed inverses and integral
translations. The independent static collector rejects twelve actual
data corruptions. See the [root acceptance](reviews/round14-direct-root-peer.md).

The new points are **517 unrestricted integer unknowns, 310 rows, 6,774
quartic terms, height 3,904,267**, and **519 unknowns, 321 rows, 6,253
terms, height 411,060**. Both have exact degree four. All earlier complete
families are preserved. The architecture generators themselves were not
replayed; their frozen raw interfaces and ordinary semantics were reviewed
separately. The unrelated norm branch and Lean were not executed.

The eight newly unpacked manuscript releases now occupy111 through118
under con-zfc-diophantine-forms. Exact historical ZIPs remain readable
from the pinned Git arrival commit; selected adapters authenticate their
whole bytes without restoring them into docs/incoming. This relocation
does not itself approve any other incoming mathematical claims. The
canonical ten-positive92/283 PDF and TeX remain unchanged.

## Reusing the existing b saves one more multiplication

The [complete reused-b extension](research/ten-positive-reused-b-weight/README.md)
gives **91/283, 92/278, 97/258 and 98/254** operation/degree profiles
with ten strictly positive unknowns. It replaces L=k(T+alpha) by the
already evaluated b=c(T+alpha)-R. The ordinary proof bounds b before
transport and constructs a fresh positive n. The changed remainder has
degree six, below all existing center defects, so every exact degree
and nonzero global leading form is preserved.

Independent full proof/code review and six normal/optimized replays pass;
all 152 interfaces and 378 gates, complete parent-row maps and both whole
native tuples are bound. Twenty graph corruptions and 31 malformed
artifacts are rejected. See the [root acceptance](reviews/ten-reused-b-root-peer.md).
This one-operation gain is recorded separately while further changes are
batched; the canonical complete92/283 PDF and TeX remain unchanged.
Lean work remains paused.

## The complete 55-guard source family reaches 554 variables

The [new finite packet](research/shared-binomial-digit-product-source-prototype/README.md)
materializes every RAW/CSE profile of the separately accepted seventh guard
exchange. Its best default has **554 integer variables, 362 rows, 6,927
quartic terms and height 2,445,790,974,704**. Against the preserved557
family it saves three variables, one row and ten terms. Both root checker
JSONs and all four normal/optimized full replay transcripts match the
author exactly; every coefficient, signed inverse and census passes, and
90 actual corruptions are rejected. An independent retained-set audit
checks all24 old/new profiles and their actual three delta classes.

The [root acceptance](reviews/shared-binomial-digit-product-source-root-peer.md)
composes those finite results with the exact complete ordinary source
theorem. All coefficient/term alternatives and earlier equations remain
preserved. The separate Round14 family reaches517/519 variables; this
554 result is progress within the older source pipeline. The canonical
92/283 PDF and TeX and paused Lean work are unchanged.

## Removing the center gives 89/288 and 95/262 tradeoffs

The [complete uncentered packet](research/ten-positive-uncentered-b-weight/README.md)
uses **89 operations at exact degree288**, or95 at degree262 on the
direct chart, with ten strictly positive unknowns. The already folded
odd Pell index excludes the first two auxiliary possibilities; the fifth
index forces a strong enough transport bound to omit Cg altogether.
Positive completeness follows from the exact forward n_new=n_old+Cg
shear; positivity of a reverse shear is not assumed.

The global degree proof is a polynomial cancellation argument with a
uniquely dominant final term and explicit nonzero highest coefficients.
Independent full proof/code review and all six normal/optimized replays
pass, covering every live gate, all four parent routes, both whole native
tuples,10 source corruptions and28 malformed artifacts. See the
[root acceptance](reviews/ten-uncentered-b-root-peer.md).
These save operations with slightly higher degree than their centered
parents. The canonical complete92/283 PDF and standalone TeX remain
stable while further changes are batched. Lean remains paused.

## Pointwise guard compression for both Round14 sources

The [new ordinary theorem](research/round14-pair-guard-compression/PROOF.md)
licenses nine individual pair exchanges in the517 ancestry and eight
in519. Exact common-numerator and factorial/digit identities restore all
removed signs over every unrestricted integer body zero, before source
semantics. Both directions fix the entire body tuple and choose fresh
Legendre witnesses. Mixed and factored source views are proved separately.

Independent normal/optimized checks bind19 exact identities,123 old guard
graphs and complete noncontiguous body maps, and reject28 actual corruptions.
Every old guard auxiliary is checked to occur only in its own guard row;
the appended private Horn body coordinate is retained. See the
[root acceptance](reviews/round14-pair-guard-root-peer.md).
This is an ordinary guard-domain result, with no new materialized equation
or projected count. Existing517/519 quartics and the complete92/283 PDF
and TeX remain unchanged until separate complete candidate checks pass.
Lean remains paused.
