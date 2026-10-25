# Affine consequences hidden in a quadratic residual basis

## Result and exact scope

This component gives fixed sum-of-squares quartics over unrestricted integers
in 278, 279, 284 and 306 coordinates (two coefficient/support profiles are
provided in dimension 279). Every residual and every collected coefficient
is supplied. The new step is to expose affine consequences by elementary
row operations and then remove their unit-coefficient coordinates. It does
not change the arithmetic or proof-theoretic meaning of the parent system.

The parents are the exact `strict_dimension_centered`,
`strict_grouped_centered` and `strict_sparse_centered` equations from the
incoming Cofinal Anchors/Height One round-17 archive in the pinned ProveIt
repository. Their ordinary theorem is that integer unsolvability is
equivalent in ZFC to Con(ZFC). We inherit that theorem and its identified
ordinary arithmetic and C222/ZF/ZFC calibration dependencies; this component
does not assert a newly kernel-checked end-to-end theorem. All claims below
are universal polynomial identities and apply to every integer tuple, not
merely tuples sampled in a finite test.

## 1. Three elementary equivalence lemmas

**Lemma 1 (row shear).** For residual polynomials R_0,...,R_{m-1}, replace
R_i by R_i+kR_j where i is different from j and k is an integer, leaving
all other residuals unchanged. The common zero set is unchanged.

**Proof.** A common zero remains a common zero by substitution. Conversely
the new R_j is still R_j, so its vanishing and the vanishing of R_i+kR_j
give R_i=0. The inverse row operation uses -k. In matrix language the
operation is unimodular with determinant one. No division or sign assumption
is used. The sum of the squares need not be the same polynomial; only its
integer zero set is the same. This distinction is essential. QED.

**Lemma 2 (coordinate shear).** Replacing one old coordinate x_t by
z_t+L(z), where L is an integral affine polynomial independent of z_t and
all other coordinates are unchanged, is a bijection of integer lattices.

**Proof.** The inverse replaces z_t by x_t-L(x). Because L does not contain
the changed coordinate, both compositions are the identity. Substitution
preserves degree at most two. A sequence is inverted in reverse order. QED.

**Lemma 3 (unit affine projection).** Suppose one residual is
epsilon*x_t+L(x)=0 with epsilon in {1,-1}, and L is integral affine and
independent of x_t. Delete that residual and substitute x_t=-epsilon*L in
every other residual. Restriction to the retained coordinates is a
bijection between the old and new common integer zero sets.

**Proof.** Every old zero has its x_t forced to the stated integral value,
so restriction satisfies the substituted equations. Every new zero extends
uniquely by that value; the deleted equation then vanishes identically and
the other equations vanish by substitution. Repeated projections are
restored in reverse order, so later-eliminated dependencies are available.
Affine substitution does not raise degree. QED.

Finally, for integer residual values, sum_i R_i^2=0 if and only if every
R_i=0. Thus all three lemmas transfer directly to the single sum-of-squares
equation. These arguments are elementary and formalizable in ZFC.

## 2. Credited coordinate preconditioning

The following six coordinate shears are prior ProveIt work, not claimed as
new here. Their exact upstream certificates and provenance are retained in
`sources/` and `SOURCE_PROVENANCE.json`. We transfer them to the three
incoming parents and independently verify each forward/inverse identity.
Indices below are zero-based source coordinates. Each line means old
target equals the expression in the new coordinates at that stage:

    x21 := x21 - 2*x10 - 2*x11
    x23 := x23 - 8*x22
    x38 := x38 - 8*x37
    x35 := x35 - 4*x10 - 5*x12 - 2*x25 - x27
    x27 := x27 - x10 - x12
    x25 := x25 - x11 - x12

The target names are respectively mul.40, mul.53, mul.148, mul.137, mul.75
and mul.64. The six operations are performed in exactly this order. They
are not treated as simultaneous assignments. There is no reliance on an
upstream acceptance claim for a semantic V-R1 endpoint: only these explicit
bijective substitutions are used and rechecked here.

Write Q_i for the source residuals after these six substitutions. Source
variable names and indices through the displayed range agree in all three
parents; the checker binds names explicitly.

## 3. The three newly exposed affine identities

Exact expansion in all three parents gives:

    Q21 - Q6
      = 4 + 4*x10 + 8*x11 + 4*x21 - x22 + x37;

    Q73 - Q71 - 4*Q70 - 8*Q68
      = 12 - 6*x3 - 8*x84 - 4*x85 - x86 + x89;

    Q122 - Q120
      = 3 - 2*x107 + 2*x151 - x167 + x169.

These are literal identities of integral polynomials, not identities only
modulo the solution set. They can be verified by collecting the supplied
quadratic coefficients. The first replaces row 21 by row 21 minus row 6.
The second uses three elementary operations on row 73, subtracting rows 71,
70 and 68 with multipliers 1,4,8. The third subtracts row 120 from row 122.
None of the donor rows is changed by another listed operation.

Lemma 1 therefore permits replacing those three residuals by the displayed
affine rows. Lemma 3 then gives the unique restorations

    x37  = x22 - 4 - 4*x10 - 8*x11 - 4*x21,
    x89  = x86 - 12 + 6*x3 + 8*x84 + 4*x85,
    x169 = x167 - 3 + 2*x107 - 2*x151.

The eliminated names are add.145, mul.346 and base4.T. Thus the three
parents drop from 282,287,309 coordinates to 279,284,306, and from
192,197,219 rows to 189,194,216. The remaining residuals stay quadratic.
This is the dimension improvement; numerical row-basis optimization later
changes neither count.

## 4. The 278-coordinate tradeoff

There is also an already affine source row Q90. In addition to the three
newly exposed equations, remove Q90 by restoring its unit coordinate as

    x105 = x10 + x11 + 4*x21 + 2*x24 + 4*x26 + 2*x29
         + 2*x31 + 4*x32 + 2*x34 + 2*x36 + 4*x39 + 2*x40
         + 2*x43 + 2*x47 + 4*x68 + 2*x69.

The name x105 is add.380. This gives 278 coordinates and 188 residuals
from the 282-coordinate parent. The dense replacement increases support,
so this is explicitly a variable/support tradeoff rather than domination
of the other selected endpoints. This already affine row is not claimed
as one of the newly discovered identities.

## 5. Finite residual-basis optimization and exact construction

Each endpoint certificate records, in order: the six coordinate shears,
five affine-exposure row shears, three or four affine projections, and a
finite final list of elementary integral row shears. The last list was
selected by a bounded sparse-coefficient search. Its proof is simply
Lemma 1 for each displayed operation; its search heuristic is not a
mathematical premise. No global or local optimality is claimed for the
frozen endpoints.

`build.py` deterministically executes only this frozen finite certificate,
not the search. It produces the complete quadratic residual list, complete
collected quartic coefficients and metrics. The exact degree is four,
verified by a nonzero quartic coefficient, and every declared coordinate
occurs in the collected polynomial. Integer domains are unchanged.

To restore a zero of a final equation, first use the inverse final row
shears to infer that the projected residuals vanish. Restore the eliminated
coordinates in reverse projection order, then apply the inverse
affine-exposure row operations to infer all Q_i vanish. Finally evaluate
the coordinate shear maps in reverse execution order to obtain a zero of
the original parent. Conversely, apply the inverse coordinate bijection
to an old zero, restrict by the affine equalities, and use the final row
shears. This proves a bijection of common integer zero sets. Composing
with the parent ordinary calibration proves the same Con(ZFC)
unsolvability equivalence for every supplied new quartic.

## 6. Independent verification and the finite obstruction

The checker imports no producer. It verifies every coordinate inverse,
every row inverse, every unit affine equation before deletion, the zero
of every deleted row, absence of each deleted coordinate, exact coordinate
renumbering and liveness, every final quartic coefficient and all metrics.
More strongly, it constructs every original coordinate as an affine
polynomial in the final coordinates and compares every original residual
pullback with the inverse-row certificate, as a universal polynomial
identity. Five deliberately corrupted certificates/artifacts must be
rejected. A fresh rebuild must be byte-identical. Checks are run normally
and with Python -O; none depends on Python assert statements.

The optional `affine_rank.py` supplies an exact finite obstruction to
repeating this particular step on the 278-coordinate endpoint: its 188
quadratic parts have rank 188 modulo the prime 1000003. A nonzero minor
modulo a prime is nonzero over Q, so no nonzero rational linear combination
of these 188 residuals can be affine. The parent rank is also 188, while
the four explicitly independent affine combinations above give its
four-dimensional quadratic-part kernel. This rules out further affine
row-span consequences at this stage only. It does not rule out nonlinear
ideal consequences, new arithmetic encodings, non-affine projections or
smaller quartics by other means.

No part of the finite verification searches for a consistency witness,
proves Con(ZFC), proves global variable minimality, or substitutes finite
sampling for the unbounded parent arithmetic proof.
