# A derived anchor permits the seventh product guard

Fix the complete1268-coordinate,1186-row raw integer body in the accepted
56-predicate source. This packet changes only two scalar guard graphs:
raw123>=0 and raw564>=0 are replaced by raw123*raw564>=0. The body,
all power/seed requests, all ten frame squares, W,A, native ports, radius
laws and private Pell coordinates are unchanged. The full literal parent
has55 guards,1433 coordinates and1241 quadratic residuals. These dimensions
are not a projected quartic census.

For EVERY unrestricted integer body tuple z satisfying all1186 residuals,
we prove

    there exist old56 guard auxiliaries over z
        iff there exist new55 guard auxiliaries over the SAME z.

Only guard auxiliaries are reconstructed. No full guarded-tuple bijection
or identity between the two sums of squared residuals is asserted.

## 1. The existing guard graph

For integers u,a,b,c let G(u;a,b,c)=u-a²-b²-c²-c. Then

    there exist integer a,b,c with G(u;a,b,c)=0 iff u>=0.

Forward, both squares and c(c+1) are nonnegative for every integer c.
Conversely, for u>=0 the integer4u+1 is1 or5 modulo8, so is not of the
excluded form4^j(8m+7). The existing Legendre three-square theorem gives
4u+1 as three squares. Modulo4 exactly one root is odd; permute it to the
last position and write the roots as2a,2b,2c+1. Subtract1 and divide4 to
obtain u=a²+b²+c²+c. The endpoint u=0 also has a=b=c=0.

The new guard is precisely G(raw123*raw564;a,b,c)=0. Its residual remains
quadratic with three auxiliaries and no new body gate.

## 2. The anchor is derived from retained signs

Write R_j for actual zero-based body residual j, and z_i for raw coordinate i.
The following four identities are universal integer polynomial identities.
CERTIFICATE.json contains every row multiplier and every polynomial
coefficient; the stdlib checker collects them from the actual full body.

| Identity | Exact source-row combination |
| --- | --- |
| z91-z94-z95-1 | R83+R84+R85 |
| z530-z91-z537-1 | R518+R519+R520 |
| z530-z123-z564-1 | R540+R541+R542 |
| z123+z564-z91-z537 | R518+R519+R520-R540-R541-R542 |

The guards on raw94,raw95,raw537 remain at old indices12,13,23. Section1
gives z94,z95,z537>=0. On every body zero the first identity therefore
gives z91=z94+z95+1>=1. There is no direct guard on raw91 in the old
source, and none is assumed or added here. The last identity then gives

    z123+z564=z91+z537>=1.

This uses no positivity or numerical meaning for raw530, no factorial,
binomial, power, Pell, rank, frame or native interpretation, and no sign
being recovered by the new product guard. It uses only three retained
scalar guards and literal vanishing body rows.

## 3. Product and sum recover both signs

For any integers r,s, if r+s>=0 and rs>=0 then r,s>=0. Indeed, if r<0,
then rs>=0 forces s<=0, whence r+s<0; similarly s<0 is impossible.
This general lemma includes the zero-sum case, where r=s=0. Here its sum
is at least1; its zero-product boundary is still needed, for example
r=0,s=1. Conversely two nonnegative factors always have nonnegative product.

Apply the lemma with r=z123 and s=z564, using Section2 and the new guard's
product sign. It restores both removed signs before any inherited source
proof is invoked. Thus the early sign/prefix chronology is unchanged.

## 4. Both parent directions on the fixed raw tuple

From an old guarded zero, the two scalar graph equations imply
z123,z564>=0 by Section1. Their product is nonnegative. Keep every
unaffected guard witness through the explicit old/new coordinate map,
and choose a fresh Legendre triple for the product. All new guard graphs
and all unchanged body rows vanish.

From a new guarded zero, the three retained anchor-source graphs give
z94,z95,z537>=0. The four body identities and Sections2-3 give
z123,z564>=0. Keep every unaffected triple under the inverse coordinate
map, and choose fresh old Legendre triples for the two recovered signs.
Every old body and guard row now vanishes over the same raw tuple.

All54 unaffected guard graphs keep their exact operands, labels and
auxiliary metadata under reindexing. In particular all six earlier
remainder-product graphs, the strict-common-V graph, paired-index-slack
product graph and joint-factorial graph survive. Six old auxiliary
coordinates are removed and three fresh product auxiliaries introduced.
Some numeric indices overlap across the two coordinate vectors; this
does not identify their witnesses. The construction need not undo the
choice of guard auxiliaries in either direction.

These two constructions prove the uniformly quantified theorem at the
start, including both ordinary soundness and completeness.

## 5. Exact composition and boundary

The accepted56 ordinary theorem is sealed at
research/shared-remainder-product-guards/MANIFEST.json with SHA256
8678f1226872f49759c6527cea7e8e0a334603a9b9a2b9d58776e432c11c8a6c.
Its complete literal arithmetic profiles are separately sealed at
research/shared-remainder-product-source-prototype/MANIFEST.json with
SHA25619fc65a27b18920d916922025fc07e80741ef255d59cf8a15edb6d33c29ba551.
All source and guard interfaces from those packets are authenticated here.

The reconstructed old56 zero has the IDENTICAL raw tuple. The inherited
ordinary theorem therefore retains its whole chronological sign, root,
rank, whole-product projection, coherent ports and positive completeness
arguments. Native constants, source ports and the fixed finite ZFC-refutation
endpoint remain unchanged. No new cofinal frame, private Pell witness or
radix witness construction is needed for this guard-only exchange.

The stdlib checker authenticates complete input seals, reconstructs every
new guard/row/name/map, checks every source-ideal coefficient and rejects
actual operand, anchor, source, graph and scope corruptions. These are
literal transcription controls, not a proof by sampling. No optimizer,
incoming program, parent checker or Lean command is run. Projected metrics,
CSE and complete expanded quartics belong to a separate later finite
packet. This proof makes no new Lean, internal object-ZFC, consistency or
unsolvability claim.
