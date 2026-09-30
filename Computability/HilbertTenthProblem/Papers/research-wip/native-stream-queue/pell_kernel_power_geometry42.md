# Strong power geometry in 42 operations

The exact binary and ternary power predicates each cost **42=25M+17A**
after replacing the first-index equation by `k=hq`. Both keep the full
strong auxiliary square. Their positive projections are respectively
`q=2^t` and `q=3^t`, with integer t>=1.

This saves one addition in the power43 components and lowers their paired
FIFO compositions to **51** in binary and **49** in ternary. The complete
universal bound remains76: these are exact geometry and FIFO components,
without a universal arithmetic controller or acceptance compiler.

This is a different change from the
[false single-product42 source](pell_kernel_power_geometry_weak42.md).
That source saves a multiplication by weakening the auxiliary norm; the
present source retains that norm and simplifies the first-index congruence.

## 1. Exact source change

Start from [binary43](pell_kernel_power_two43.md) or
[ternary43](pell_kernel_power_three43.md). Retain `r+1=q`, scale `X=wq`,
`Y=sq`, and every equation except

    k=r+1+hXY.

Replace it by

    k=hq.                                               (1)

The old product `h*XY` and following addition become the single product
`h*q`. The already computed `r+1` remains available for its free comparison
with q and for computing `2r+1`. Thus the total is42=25M+17A, with the
same eleven equations and seventeen positive auxiliary coordinates apart
from q. No divisibility predicate is treated as a free operation: the
product in(1) pays for it.

The [checker](pell_kernel_power_geometry42.py) constructs both literal
DAGs, expands every independent polynomial, and verifies the auxiliary
norm correction. In particular the source still contains

    (i*c^2)^2=Delta*(f^2-1).

## 2. A smaller congruence is sufficient here

For q>=5, use exactly the preliminary inequalities proved in power43.
In either branch set `A=a+b`, where b is2 or3, and

    P=2XY^2+1, J=2r+1=2q-1.

The first norm and the main norm give

    k=psi_P(n), c=psi_A(p), d=chi_A(p), n,p>=1.

Before any power recovery, q divides X and Y, so `P=1 mod q`. Reduction
of the Pell recurrence gives `psi_P(n)=n mod q`. Equation(1) therefore
forces q to divide n, and hence **n>=q=r+1**.

Since P>A and the strict ratio interval gives c>k, index monotonicity
implies `p>=n+1>=q+1>=6`. Consequently

    c>=(2A-1)^(p-1)>A^5>A*(A^2-1)^2,
    c>J, 2p<=c.

These are the same relaxed-rank and half-parameter hypotheses used by
power43. They use the strong auxiliary norm and recover `p=J=2q-1`.
The first index now satisfies

    q divides n, q<=n<=p-1=2q-2.

The only possible multiple is **n=q**. No modulus XY or congruence class
`q mod XY` is required to obtain this conclusion.

The retained lower-ratio-first proof now applies at exactly the same
two indices as in power43. It yields `Y>=X^r`, bounds the exponent
representatives, and gives `X=b^(2r+1)`. Since q divides X, q is a power
of b. The ternary proof still handles X=5 and X=7 by its explicit small
representative bounds.

The small q cases are unchanged. Positivity of r excludes q=1. For the
binary source q=2 and q=4 already have the required geometry, while q=3
is impossible modulo3 in the main norm and exponent equation. For the
ternary source every even q is impossible modulo2, q=3 already has the
required geometry, and all remaining q are covered above. These small
cases do not require classifying every possible kernel witness.

## 3. Strictly positive converse

For every power q=b^t, take the canonical positive power43 witness at

    r=q-1, X=b^(2r+1), Y=floor((X+1)^(2r)/X^r),
    P=2XY^2+1, k=psi_P(q).

Keep every coordinate except h and set

    h=k/q.

This is integral because `P=1 mod q` and `psi_P(q)=0 mod q`; it is
strictly positive. Equation(1) holds and no other equation uses h.
Thus both complete positive converse maps are preserved.

For example the smallest binary case has q=2, k=3202 and new h=1601.
The checker materializes all seventeen auxiliary coordinates at that
case and verifies all eleven equalities in the new DAG. Its largest
coordinates have over three million bits. It also checks the exact eight
main equalities and positive new h for binary q=2,4,8,16,32 and ternary
q=3,9,27. Larger final auxiliary tuples remain parametric, as in power43.

## 4. Exact paired FIFO compositions

The stream equations and their semantics in the two earlier components
are unchanged. Replacing only the geometry source gives:

| Interface | Operations | Multiplications | Additions/subtractions | Equations | Positive witnesses besides x |
| --- | ---: | ---: | ---: | ---: | ---: |
| Binary FIFO with high marker | 51 | 29 | 22 | 18 | 28 |
| Ternary FIFO from(x,0), separate bounds | 49 | 28 | 21 | 17 | 27 |
| Ternary FIFO from(x,0), joint bound | 49 | 28 | 21 | 16 | 26 |

The binary projection is exactly the one proved in
[the52 reference](native_binary_pair_fifo52.md). The ternary projections,
strictly positive append streams, and delayed finite loader are exactly
those in [the50 reference](native_ternary_pair_fifo50.md). These statements
follow from the same exact power projections, not an assumption about
unchanged internal Pell coordinates. The converse uses the new h above.

The checker audits all equations of all three combined DAGs. It also
appends the existing nine-operation general affine-controller schedules,
giving binary60=34M+26A and ternary58=33M+25A. Their scope remains the
entire unfiltered affine graph. The delayed loader and the universal
machine's finite control are not certified by those schedules; the
previous absorbing-endpoint decidability obstruction still applies.

## 5. Evidence boundary

The argument for the new index congruence is a proof for arbitrary q.
The finite first-index audit tests its recurrence and interval consequence
for q through50. Every operation, source equality and coordinate count
is checked symbolically; positive witnesses are exact materializations
where stated and parametric constructions otherwise.

Default execution compares [the saved receipt](pell_kernel_power_geometry42.json).
Independent full proof, source, and default-replay review passed. No Lean formalization or complete
universal bound below76 is claimed.
