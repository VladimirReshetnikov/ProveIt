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
| Positive integers | 10 | 102 | 388 | Shifted strong multiplier, shorter transport and quadratic main-Pell projection |
| Positive integers | 9 | 409 / 417 | 1,191,572 / 1,316,548 | Tight main folding and unshifted carrier; original31 / smaller compact54 tuples |
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
| Integers | 708 | not optimized | 4 | Mixed-domain lower-height projection;5,887 terms, height63,905,891 |
| Integers | 1,559 / 912 | not optimized | 4 | Retained-wire mixed guards;5,289 /4,134 terms, heights427 /4,750 |
| Integers | 767 / 703 / 689 | not optimized | 4 | Retained-wire mixed projections;5,897 /9,247 /9,211 terms, heights737,653 /737,653 /938,261 |
| Integers | 679 / 680 / 682 | not optimized | 4 | Signed comparisons, derived guards and private sign orbits;10,335 /8,999 /8,904 terms, height2,445,790,974,704 |
| Integers | 1,190 / 1,224 | not optimized | 4 | Preserved synchronized checkpoints, now dominated by917 |

Operations mean live binary `+`, `-`, and `*`, with squares and fixed-scalar
multiplications charged and fixed numeral leaves free. Variable counts
exclude named polynomial abbreviations. Positive, natural and unrestricted
integer domains are compared separately. These are useful points, not the
complete frontier or a global optimality claim.

The maintained [equation.pdf](equation.pdf) now displays the10-positive
102-operation degree388 equation in full, including every constant, with
standalone [TeX](equation.tex). It retains the full fixed recipe and saves
three operations and degree20 against the preserved105/408 page. This one
combined update includes direct J, shifted I and shorter transport, with
full positive witness proofs. The earlier13-positive90/51 page remains a
lower-degree/cost alternative with three more unknowns.

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
[equation.tex](equation.tex) now print the complete ten-positive102-operation,
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
