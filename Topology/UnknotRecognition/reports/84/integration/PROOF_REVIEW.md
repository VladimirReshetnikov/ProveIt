# Proof review and dependency map

These are conventional mathematical proofs with finite computational checks,
not Lean or other proof-assistant formalizations. The authoring process is
not an independent external peer review. Classical ingredients are credited
in the article; no exhaustive literature-priority claim is made.

## Integral condensation

The geometric input is a collared union of a core and disjoint interval
bundles, with intersections exactly over finite unions of boundary intervals
and complete boundary circles. This supplies Mayer–Vietoris. Bundle projection
identifies homology with that of its base. For an orientable total bundle the
restriction to each base boundary circle is an annulus.

The free `H_0`-kernel in Mayer–Vietoris is the cycle space of the attachment
multigraph, not merely a count of base components. Surface homology gives
`sum(d_j)=0` or `2 sum(x_j)+sum(d_j)=0`. When a boundary circle remains
unattached, eliminate it before substituting the attached circles: no core
relation remains. When all are attached, retain one sum relation. In the
nonorientable case `h=sum(x_j)` is primitive and can be included in a
unimodular basis. This gives the `2I` block and the binary bulk formulas.

Checks: closed and empty bases are separate cases; attached profile
multiplicity is one; the empty graph is allowed; `H_2` recovery uses the
actual orientable three-manifold/nonempty-boundary premise. The abstract
algebra validator alone does not establish that premise.

## Endpoint-port reconstruction

Each endpoint occurrence carries a distinct power of two. A quotient orbit
sum therefore has no repeated bit or carry. At most twice the number of
ports have nonzero endpoint-orbit masks. Correct one-manifold boundary
incidence makes the retained graph a union of paths and cycles. A cycle is
one complete boundary circle, independent of the number of arcs in it.

The supplied endpoint quotient must be source-authenticated, and orientable
base circles must share a coherent relative orientation. The implementation
checks the finite stage, not the origin of either piece of information.

## Twisted attachments and torsion

The map `G -> (G + Z^t)/<s_j+2h_j>` is injective because a relation lying in
`G` has zero coefficient in each independent `h_j`, forcing every integer
relation multiplier to vanish. The quotient is `(Z/2)^t`.

Odd-primary torsion is unchanged. If the torsion exponent of `G` is `e`,
then a torsion element of the larger group has its double in `Tor(G)` and
hence is annihilated by `2e`. This is a simultaneous bound, not `2^t e`.
When `G` is free, all torsion is elementary two-torsion; rational rank and
mod-two rank give its exact dimension. The invariant-factor-run algorithm
merges primary exponent lists without expanding the repeated twos or
factoring odd integers.

## Geometric restrictions on abstract stress tests

The incidence-sensitive bound uses Hadamard plus determinantal divisors.
A linear handle count does not prove a linear attaching-word bound. Moreover,
disjoint closed nonorientable surfaces in an orientable source yield
independent mod-two cohomology classes: a transverse closed curve can be
chosen to meet its own surface once and the others not at all. Thus their
count is bounded by the source mod-two first Betti number. Very large
unported nonorientable multiplicities in the stress test are algebraic
inputs, not normal cuts of a fixed small triangulation.

## S3 homology and the sphere terminal

Alexander duality for the boundary gives exactly `b` complementary
components. Apply duality to their compact collared closure to obtain
`H_2(X)=Z^(b-1)` and torsion-freeness of `H_1(X)`. The Euler characteristic
of the double then yields `rank H_1=G_boundary`. Schoenflies upgrades one
locally flat sphere boundary to a ball only with the S3 embedding premise.
The proof is not a general ball-recognition algorithm for arbitrary sources.

The core and the whole space have free homology under this premise. The
injection in the twisted theorem then forces the orientable quotient to be
free, proving lattice primitivity. The saturated nonorientable sum vectors
must be independent modulo two. Passing these necessary tests does not
prove embeddability.

## Complexity and implementation boundaries

Condensation and its finite interface replay take polynomial bit time in
explicit core/interface data and binary profile fields. A polynomial
integer-normal-form backend gives the stated polynomial group-isomorphism
query. The delivered Euclidean Smith producer is exact and terminating, but
its worst-case intermediate coefficient growth is not claimed polynomial.
Its independent verifier checks local unimodular operations and final
normal-form conditions within explicit resource allowances.

The symbolic cohomology theorem yields a compact functional in the condensed
basis. Pulling it back to source edges or constructing a cutting surface is
not implemented or proved by a dimension count. The global quasi-polynomial
criterion assumes a complete hierarchy with bounded intermediate encodings,
per-step cost, pattern complexity, and depth; it is not an existence proof
for those assumptions.

## Empirical evidence scope

The expanded oracle uses literal standard surface presentations and its own
core-forest logic. SymPy supplies an independent Smith comparison; selected
small matrices are checked via all minors. These are 4,800 finite seeded
checks plus deterministic regressions, not a proof for all inputs. No native
source cut, full repository regression suite, or Regina computation was run.
