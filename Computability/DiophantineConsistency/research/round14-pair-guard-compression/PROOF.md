# Pointwise pair guards for the Round14 sources

This packet proves a guard exchange for the two accepted Round14 signed
sources and, separately, for their exact factored sources. Every coordinate
of the selected source body remains fixed. It constructs no projected
equation and claims no new variable count, term count or height. The labels
517 and519 below name the accepted ancestry, not a newly measured endpoint.

The exact inputs, rows, variable names, old auxiliary coordinates, retained
guards and individual replacement predicates are in CERTIFICATE.json.
SOURCE_PINS.json authenticates the complete literal files. No incoming
program, compiler, optimizer or Lean code is needed for this proof/checker.

## 1. The integer lemma

For integers r,s with r+s>=0,

    r>=0 and s>=0  if and only if  r*s>=0.

The forward implication is immediate. If r<0, the sum condition gives
s>=-r>0 and hence r*s<0. The argument with r,s interchanged excludes s<0.
There is no restriction on the size of either coordinate. The case r+s=0
is included: the product condition then forces r=s=0.

In particular, if fixed body rows imply r+s=a+b and the retained predicates
give a,b>=0, the two scalar predicates r>=0,s>=0 can be replaced by the
single predicate r*s>=0. This statement holds for each fixed integer body
tuple. It uses no interpretation of its variables as natural numbers,
powers, factorials, quotients or proof codes.

Each replacement is individual. A product of the products is insufficient:
two pairs (-1,2),(-1,2) both have nonnegative sum, but their combined product
is positive despite both pairs violating the original scalar guards.

## 2. The common-numerator groups

Each relevant remainder row is literally

    F_i = N - r_i - s_i - 1 = 0.

For its group's retained anchor row F_a, coefficient collection gives

    r_i+s_i-a-b = F_a-F_i.

Thus a,b>=0 supplies the required sum condition before N is identified as
any power. All groups below use an actual common variable N, not merely
equal intended exponents.

| Source ancestry | Retained pair | Other pairs replaced individually |
| --- | --- | --- |
| 517 | range0 remainder/slack | range1, range2, range3, range9 |
| 517 | range4 remainder/slack | range5 |
| 517 | range6 remainder/slack | range7 |
| 517 | choose0 remainder/rslack | choose1 remainder/rslack; range8 |
| 519 | range0 remainder/slack | range1, range2, range3 |
| 519 | range4 remainder/slack | range5 |
| 519 | range6 remainder/slack | range7 |
| 519 | choose0 remainder/rslack | choose1 remainder/rslack; range8 |

The corresponding N variables in the mixed517 source are200,222,234,185;
in the mixed519 source they are218,240,252,203. Their intended meanings are
q^(t+1), q^(y+1), q^(x+1), q^t, respectively. Those meanings are recorded
only to identify the interfaces; the argument uses the displayed rows.
The original guards retain every member of all four anchor pairs.

## 3. The two digit outputs

Write D for choose0.output, B for choose1.output, a for choose0.oslack and
s for choose1.oslack. The two actual digit-bound rows are

    G_D = Q-D-a-1 = 0,
    G_B = Q-B-s-1 = 0.

Here Q is mixed coordinate183 in517 and201 in519. Hence

    B+s-D-a = G_D-G_B.

D itself is not a retained scalar guard. The retained factorial remainder
and slack give it a stronger bound, without factorial meaning: the exact
factorial remainder row is D-u-v-1=0, where u,v remain guarded. Therefore
D=u+v+1>=1. The retained a>=0 implies B+s=D+a>=1. The integer lemma now
replaces the original B>=0,s>=0 by B*s>=0. No use is made of the reciprocal
index congruence, nonzero B, positive radix, a power output, or the order of
the accepted source's later semantic recovery.

For517, (D,u,v,a,B,s)=(6,8,9,189,28,196). For519 it is
(46,48,49,207,52,214). In both cases u,v,a remain scalar predicates.

## 4. Complete fixed-tuple equivalence

Let S be the complete list of original scalar guard targets. Let P be the
list of disjoint exchanged pairs in CERTIFICATE.json and let R be S with
all members of P removed. For every integer assignment z to the complete
mixed body coordinates satisfying every mixed residual,

    (all z_j>=0 for j in S)
      iff
    (all z_j>=0 for j in R and all z_r*z_s>=0 for (r,s) in P).

Here the mixed-source residual list is evaluated over the integers. Its
nonnegative domain metadata is not an additional premise: the old selected
guard predicates, and the already accepted signed-source argument, determine
which coordinate signs are required.

Left-to-right follows from nonnegative products. Right-to-left first uses
the four retained anchors and their row differences to restore every
exchanged remainder/slack sign, then the retained factorial pair and
choose0.oslack to restore B and its digit slack. All remaining old signs
are members of R. These are all original predicates, as checked against
the entire actual guard list; none is silently discarded or substituted.

There are nine exchanged pairs in the517 ancestry and eight in519. These
are predicate counts only. No optimizer or projected metric is inferred.
The original predicate list is read in full: the actual files contain63
guards for517 and60 for519, and the certificate/checker binds
each original guard, including its complete Legendre graph and name.

The same theorem holds independently on the factored bodies after deleting
their nonnegative rows. Every selected row is literally unchanged there,
though its row number can differ. The selected coordinate metadata is
unchanged. The checker compares every old guard graph as well. This does
not assert pointwise equality of the mixed and factored bodies: the parent's
Horn factorization changes private coordinates. It shows the present guard
exchange applies on either side, on that side's own fixed integer tuple.
The factored517 body has coordinates0..549 together with739 and468 rows;
the factored519 body has coordinates0..553 together with734 and475 rows.
The appended Horn coordinate is part of the fixed body. Old guard auxiliaries
lie between these blocks. Their triples are pairwise disjoint, avoid every
guard target and occur only in their own nonnegative graphs in both views.
In particular, none occurs in a body residual. CERTIFICATE.json
records both complete, noncontiguous coordinate maps and all body row indices.

## 5. Polynomial realization and calibration boundary

The existing nonnegative graph is

    x = A^2+B^2+C(C+1),  A,B,C integers.

Its right side is nonnegative for every integer triple. Conversely every
integer x>=0 has such a representation: Legendre's three-square theorem
applied to 4x+1 gives two even squares and one odd square, because the
square residues modulo4 sum to1. Writing the even roots as2A,2B and the
odd root as2C+1 gives the graph. The number4x+1 is not an excluded
4^a(8b+7): it is odd and congruent to1 or5 modulo8.

A pair product predicate therefore has the quadratic graph

    r*s - A^2 - B^2 - C - C^2 = 0.

It requires no altered source-body coordinate. For a fixed old body tuple,
existence of all old guard triples is equivalent to existence of all retained
triples and the new individual product triples. Completeness chooses fresh
guard witnesses; old triples are not identified with the new ones. This is
an existence equivalence over the guard auxiliaries, with the body tuple
fixed in both directions. Sums of squares vanish exactly when every row
vanishes, so the same equivalence holds for the corresponding full sums of
squares whenever that realization is materialized and checked.

Restoring all original guards licenses the accepted source theorem in its
original chronology and with its original named C222/Pell contracts. No new
arithmetic interpretation or native logical theorem is required. This packet
does not generate a new guard layout, rerun monic elimination, transfer the
old final517/519 coefficients, or assert a new complete calibrated endpoint.
The existing final equations and every frozen parent remain unchanged.

The checker verifies the finite literal premises and tests counterexamples
to weakened variants. The argument above, rather than a finite test range,
proves the unbounded fixed-tuple statement.
