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
| Positive integers | 12 | 99 / 100 / 102 | 164 / 110 / 82 | Current degree/cost tradeoffs from packages74/69 |
| Positive integers | 11 | 113 | 325 | Three-root transfer, package70 |
| Positive integers | 9 | 440 | 1,845,940 | Shared-product reduction of the443-operation target |
| Positive integers | 9 | 475 | 1,379,730 | Shared-product reduction of package71 |
| Integers | 10 | 481 | 1,576,864 | Free-Lucas finalizer, package68 |
| Integers | 38 | not optimized | 4 | Cone/determinant alternatives, packages69/71 |

Operations mean live binary `+`, `-`, and `*`, with squares and fixed-scalar
multiplications charged and fixed numeral leaves free. Variable counts
exclude named polynomial abbreviations. Positive, natural and unrestricted
integer domains are compared separately. These are useful points, not the
complete frontier or a global optimality claim.

## Work now underway

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
[`bfs-collected/equation.pdf`](candidates/one-page-compression/bfs-collected/equation.pdf).
Its literal seed has771 digits instead of1294, and the complete printed
coefficient recipe is12.1% shorter by extracted nonwhitespace characters.
An explicit finite quotient/sum decoder replaces the old action packing.
It uses a bijective control-state renaming that fixes start and halt;
all430 transition conjugacies and all four coefficient reconstructions
are checked. The new `K` differs from the old one, so this is a separate
whole-tuple specification with an ordinary state-conjugacy argument.
See [SEED_COMPRESSION54.md](SEED_COMPRESSION54.md) for its scope and replay.

1. Further optimize the literal440-operation circuit, preserving its exact
   polynomial. Search for shared powers and algebraic rearrangements that
   remove live gates, with local exact identities and independent modular
   evaluation/topology checks.
2. Simplify the short positive equations and new root/guard mergers.
   Seek an actual improvement over the existing variable/degree/operation
   choices, proving both directions of each witness transformation.
3. Reduce the printed constant recipes. The current full page contains
   a1294-digit action seed. A shorter seed or arithmetic decoder is useful
   only if the complete definition remains printed and independently
   reconstructs the entire coherent tuple.
4. Explore alternate proof-certificate and flow encodings. Identify a
   complete global polynomial and its cost before comparing it with a
   finished endpoint; keep unbounded aggregation obligations explicit.

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
