# Independent audit: signed occurrence fusion

**Accepted as an ordinary zero-set bijection.** The full proof in
`report/height_one.tex` was reviewed; this note does not claim to duplicate the
separately replayed literal incidence/energy checker.

Pairing two equal logical monomials in distinct source rows with opposite
oriented signs into one prescribed edge preserves the signed boundary of
each row block. Therefore the sum of prescribed divergences in that block is
exactly its oriented normalized residual. Internal tree edges cancel in
that sum; the hub sum is the negative total of the row sums. No information
about an individual residual is lost by eliminating two separate hub edges.

The energy E=(1/2) sum d_v^2 is nonnegative, and a simple incidence graph has
formal diagonal edge coefficients one and cross coefficients zero or plus/minus
one. Initially private aliases prevent accidental product collisions; subsequent
alias identifications are licensed only by exact complete coefficient checking.

Every equality penalty is nonnegative and has precisely the asserted zero
set. In particular Q(a,b)=(a-b)^2(a^2+ab+b^2) vanishes only when a=b; the
second factor can vanish over the reals only at a=b=0. The no-prescribed-square
condition excludes energy collisions with all four quartic Q monomials:
an a^3 b product requires a prescribed a^2 factor, and similarly for ab^3.
The anchored unit chain forces every unit alias to one. Ordinary equality
classes and units are disjoint, as required by the certified construction.

At a polynomial zero, nonnegativity forces E and every equality/unit penalty
to vanish. Reading common alias values and summing divergences within each
block gives every oriented normalized row zero. The row signs are units;
the triangular monic constructors uniquely recover their intended integer
constant/scale/affine values. Projection consequently gives a source zero.

Conversely, evaluate those constructors and aliases at any source zero.
For a rooted internal tree the explicit edge flow minus the child's incidence
sign times its subtree prescribed-divergence sum cancels each nonroot
divergence. The root divergence is the block total, hence zero. This is an
integer polynomial lift. Leaf elimination also proves uniqueness of all tree
flows. Together with unique constructors, aliases, units and dummy values,
this gives the claimed inverse bijections of integer zero sets.

The universal lift identity must include the hub term:

    P(L(x)) = (sum_r R_r(x)^2 + (sum_r delta_r R_r(x))^2)/2.

The reviewed proof correctly states it, rather than incorrectly claiming the
bare sum of source squares. Constructor rows vanish under their canonical
substitution. This identity and the zero-set bijection do not rely on a
minimal alias count or optimal row-sign search. Degree-four/height-one claims
for particular artifacts still require the independently checked complete
coefficient files. The inherited consistency-calibration boundary remains
unchanged.
