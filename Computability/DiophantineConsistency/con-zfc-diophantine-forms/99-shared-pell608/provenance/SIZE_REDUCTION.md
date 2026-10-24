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
| Positive integers | 12 | 99 / 100 | 164 / 70 | Ordinary-norm100/70 improves100/110 and102/82 |
| Positive integers | 13 | 90 | 51 | Ordinary strong norm improves the90/55 unit product |
| Positive integers | 14 | 73 / 74 / 75 / 76 | 342 / 312 / 293 / 191 | Hilbert Tenth root transfer and scaled ordinate centers |
| Positive integers | 11 | 111 | 211 | Adaptive carrier combined with the double center |
| Positive integers | 10 | 131 | 1,152 | Four-root radical/residue form |
| Positive integers | 9 | 433 | 1,628,768 | Saturated compact54 source and identical norm rewrite |
| Positive integers | 9 | 475 | 1,379,730 | Shared-product reduction of package71 |
| Positive integers | 9 | 722 | 1,158,228 | Collected J,D radical evaluator and identical norm rewrite |
| Positive integers | 9 | 953 | 999,518 | Saturated H1868 radical, D collection and identical norm rewrite |
| Integers | 10 | 471 | 1,245,324 | Shorter source-aware approximation guard |
| Integers | 10 | 475 / 478 / 512 | 1,179,788 / 1,114,252 / 1,080,888 | Short guard combined with compact shears |
| Integers | 37 | not optimized | 4 | Reviewed joint-sign quartics |
| Integers | 22 | 119 | 14 | Centered joint-guard combination;118 operations at degree16 is retained |
| Integers | 19 | 109 | 88 | Reviewed joint projection; other tradeoffs retained |
| Integers | 17 | 114 | 88 | Explicit counted saturated-certificate/congruence interface |
| Integers | 16 | 134 / 135 | 192 / 184 | Separated rational-root norm tradeoff |
| Nonnegative integers | 16,036 | not optimized | 4 | Complete direct C222 proof-certificate compiler |
| Integers | 27,916 | not optimized | 4 | Same direct compiler with three-square input guards |

Operations mean live binary `+`, `-`, and `*`, with squares and fixed-scalar
multiplications charged and fixed numeral leaves free. Variable counts
exclude named polynomial abbreviations. Positive, natural and unrestricted
integer domains are compared separately. These are useful points, not the
complete frontier or a global optimality claim.

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
The newer13-integer and shared-direct claims at751bc067e2 remain under
review; neither is silently added to the checked table.

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
reduce the coefficient recipe to2293 nonwhite characters,8.8% below the
preserved771-digit page's2514. The original recipe has2861 characters.
The decimal-only merged-mask variant uses2478, and an original-tuple
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

