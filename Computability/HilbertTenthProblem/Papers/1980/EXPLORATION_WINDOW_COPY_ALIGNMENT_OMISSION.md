# A full false input after deleting window-copy period alignment

From the [80-operation window-copy certificate](FIXED_RAW_UNIVERSAL_80_PROOF.md),
delete the equation `(B-1)*align=P-1`, its positive coordinate `align`,
and the two instructions constructing its sides. The resulting system
has **78 operations: 42 multiplications and 36 additions/subtractions**,
with **32 positive existential coordinates and 20 equations**.
It retains `P*v=q`, the complete raw-input bridge, both masks, and the
original scale q^3. Nevertheless this proposed reduction is **unsound**.

There is a fixed normalized machine accepting the empty set for which
the deleted system accepts raw input x=1 with all supplied coordinates
strictly positive. Its false successor parameter is the within-cell
shift

    P=R^(3a_tiles),          1<P<B.                         (1)

This makes every vertical copy test compare a bit with itself. It does
not represent a shift by a whole window. The counterexample uses genuine
allowed window states with all their copy bits correct; dummy bits may
be zero. The positive divisibility equation `P*v=q` does not prevent it.

The [complete checker](../verification/explore_window_copy_alignment_omission.py)
and [receipt](../verification/explore_window_copy_alignment_omission.json)
verify the modified source, exact positive outer tuples, and their actual
mask valuations. The full fixed machine compiler and astronomical Pell
extension are specified mathematically below. The proved 80-operation
certificate and its files remain unchanged.

## 1. The precise deleted source

Delete only these two instructions from the 80 schedule:

    Pm1=P-1,
    alignment=(B-1)*align,

together with the free equality `alignment=Pm1` and the supplied
positive unknown `align`. The other source equations are unchanged.
In particular the six remaining outer equations are

    (B-1)J=q-1,                       P*v=q,
    C+alpha+d*x=q,
    (DC+B*DR+P)C=F+z*(q-1),
    r=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J,
    C=CS+Z+W.                                             (2)

Here d is the fixed cell bit width, and CS=R. All ten fixed-minus
Pell equations and all four fixed-base input equations remain exactly
as in the 80 proof. Their scale is still D0=q^3.

| Part | M | A | Total |
|---|---:|---:|---:|
| Remaining outer schedule |10|11|21|
| Retained fixed-minus Pell kernel |25|18|43|
| Retained raw-input bridge |7|7|14|
| **Rejected source** |**42**|**36**|**78**|

The checker expands all 20 residuals, with the auxiliary norm correction
reindexed after the deletion. There is no replacement alignment test or
free inequality in the modified source.

## 2. Why the within-cell shift defeats the vertical tests

Use precisely the native compiler of the 80 proof, for its full fixed
alphabet of allowed three-by-three windows. Write a_tiles for the number
of underlying tile symbols, avoiding confusion with the Pell parameter.
The compiler's copy positions and coefficient are

    e(row,col,s)=T0+(2-row)*3a_tiles+(2-col)*a_tiles+s,
    DC=R^(3a_tiles)+R^(H+a_tiles)+sum_e c_e R^(T-e),
    DR=R^H.

Its layout has Emax+3a_tiles<H and
T-Emax>H+Emax+a_tiles. All genuine copy positions, selectors and ignored
dummy positions are included in Emax. Let C_i and R_i be arbitrary
native typed center and right cells and replace the intended successor
cell by the shifted integer `P*C_i`, with P as in (1). Define

    F_i=(DC+P)*C_i+DR*R_i.                                (3)

At each tested vertical degree e(row,col,s), row=0 or1, the coefficient
of (3) is exactly

    2 * center_copy(row+1,col,s).                          (4)

One contribution comes from DC's original R^(3a_tiles) term, the other
from P. A coefficient 0 or2 passes the mask1 parity test. The same
selector and dummy separation proof as in the 80 compiler applies:
shifted selectors lie below all copy masks, while shifted dummies lie
above them. The whole new successor band has degree at most
Emax+3a_tiles<H. Thus it meets neither the horizontal mask nor the
center-clause mask.

At degree T, the coefficient is still the center's exact occupancy and
copy-link expression. At a horizontal tested degree it is still the
sum of the center's right copy and the right cell's left copy. Therefore
every horizontally consistent cyclic row of genuine allowed windows
passes all the local masks under (3), regardless of whether those
windows extend to any accepting periodic computation.

Although P*C_i need not itself be a native typed cell, the needed
no-carry estimate remains valid. It has at most K native input bits,
shifted together without overlap. The total polynomial coefficient
mass of (3) is still bounded by

    K*(sum_e c_e+4) <= R-2.

Its highest degree is no greater than T+Emax, below the exponent defining
B. Consequently `0<=F_i<=B-2`. Also `P*C_i<B`, because its degree is
at most Emax+3a_tiles<H and its radix-R coefficients are Boolean.
This is an explicit extension of the raw coefficient estimate, not an
assumption that the false successor field was properly typed.

## 3. An actual nonhalting machine and a genuine initial slab

Use the fixed machine with tape alphabet {0,1,2}, start q0, nonhalting
q1 and absorbing halt Hhalt. On symbol1, q0 writes2, stays, and enters
q1. Its other transitions also stay and enter q1. Every q1 transition
preserves its tape symbol and stays in q1. Thus no input halts, and the
stationary first step is exactly the normalization required by the
80/81 semantic interface. This fixed compiler represents the empty set
before the proposed deletion.

For x=1, take a cyclic strip of width N=8. Its initial row is

    V  L  L  I  I  Q  R  R.

Here V is the uniform vertical boundary, L and R are blank headless
initialization phases, I is headless1, and Q is symbol1 with head q0.
The row above has V in its boundary column and horizontal-boundary
tiles elsewhere. The row below is the genuine first successor: all
non-head cells are unchanged and the Q cell contains symbol2 with head
q1; interior phases are now absent. The V column remains uniform.

Every three-by-three window centered on the middle row satisfies the
unchanged helical local predicate. Initialization phases are correct,
the two exterior margins are blank, and the transition to the lower row
is exact. The predicate does not demand a halt in this middle row: there
is no next horizontal boundary here. This is a finite slab of a genuine
nonhalting computation, not a claimed accepting periodic tableau.

Center the cyclic window word at the last I and enumerate physical
columns leftward. Then

    word[0]=Start, word[1]=End,

each marker occurs exactly once, and word[i] overlaps horizontally with
word[i-1] for every i modulo8, including across V. These are the exact
Start/End windows of the 81 proof. All eight windows belong to the
full fixed alphabet used by the 80 compiler.

The same construction works with initial row `V L^l I^(x+1) Q R^b`,
for x>=1 and l,b>=2. Only x=1 is needed for the false-input theorem.
The checker also uses two larger examples to vary the marker separation
and boundary margins.

## 4. Every remaining outer coordinate is positive

Use the **full** fixed compiler constants, enumerate End as state0 and
Start as state1, and give each window in the preceding cyclic word its
genuine selector and nine tile-copy bits. Set dummy bits zero. Let C_i
be these cells and define

    C=sum_i C_i B^i,
    Rword=sum_i C_(i-1 mod N) B^i,
    F=sum_i ((DC+P)*C_i+DR*C_(i-1 mod N)) B^i,
    q=B^N, P=R^(3a_tiles), W=B^x,
    J=(q-1)/(B-1), v=q/P,
    Z=C-R-W, alpha=q-C-d*x,
    kR=(B*C-Rword)/(q-1), z=DR*kR,
    r=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J.                       (5)

Since B is a power of R with exponent larger than 3a_tiles, v is a
positive integer. In fact 1<P<B<=q, so P is visibly not aligned to a
whole cell. No positive align can satisfy the deleted equation.

Every C_i is positive; the cyclic wrap quotient kR is its positive
last cell C_(N-1), making z>0. The estimate in Section 2 gives
P*C<q and F<q-1. Equation (3) and the exact horizontal wrap give

    (DC+B*DR+P)C=F+DR*kR*(q-1),

so the retained transport equation holds with the positive z in (5).
The fake vertical shift has no outer wrap; it requires no zero-valued
supplied quotient.

The two marker selectors are removed disjointly in Z. All genuine copy
bits of the marked cells remain, hence Z>0, Z<C<q and Z is even. The
native low mask gives `Z AND MC*J=0`; Sections 2--3 give
`F AND MF*J=0`. Every cell obeys C_i<=B-2, and the same raw-bound
estimate as in the complete proof applies:

    q-C>=J+1,       J>=B^x=2^(d*x)>d*x.

Thus alpha>0. All eleven supplied outer coordinates
q,P,C,v,J,F,alpha,z,Z,r,W are positive, and every equation in (2) is
exact.

The masks still have total population dN. Their vanishing therefore
gives the unchanged exact population identity

    popcount(r)=3dN,        q^2<=r<q^4,       r odd.        (6)

The odd parity follows from even Z and qF and odd MC,J. Consequently
q^3 divides binom(2r,r). The counterexample has preserved the entire
original mask threshold, unlike the separate rejected scale deletion.

## 5. The full positive kernel and input extension

Here the retained kernel and raw-input equations are literally
unchanged. They see the actual r from (5), the same power-of-two scale
D0=q^3, and the same endpoint W=B^x. Their positive converse requires
no equation relating P to a whole-cell shift. For clarity the fresh
witness construction is explicit below.

Write J0=2r+1 and define

    X=2^J0,
    Y=sum_(j=0)^r binom(2r,r+j)*X^j,
    w=X/D0, s=Y/D0,
    a=Y*(X+1), A=a+2, Delta=A^2-1,
    Q0=X*Y^2, P0=2Q0+1,
    c=psi_A(J0), dmain=chi_A(J0), k0=psi_P0(r+1),
    tau=(chi_P0(r+1)-1)/2,
    h0=(k0-r-1)/(X*Y),
    eta=c-k0*Y, zeta=k0-eta,
    gamma=(dmain-X-a*c)/(4a+3).                            (7)

Equation (6) gives the binomial divisibility. Also D0=q^3<=r^2,
so D0 divides X and Y. The direct positive converse in Section 5 of
[the scale-deletion analysis](EXPLORATION_FIXED_RAW_SCALE_Q2.md) applies
to any power-of-two D0<=r^2 dividing binom(2r,r), at odd r>=64.
All those hypotheses hold here. Its ratio estimate

    Y < c/k0 < Y+3/4

makes eta and zeta strictly positive, and its congruence and growth
arguments give positive integral tau,h0,gamma. These are the same
first-Pell formulas used in the retained complete proof.

At this new c,A,J0 choose

    maux=2cJ0, f=chi_A(maux), Raux=Delta*psi_A(maux),
    i=Raux/c^2, yaux=psi_Raux(J0), Uaux=chi_Raux(J0)/Raux,
    j=(Uaux+J0)/c, o=(Uaux+c)/f.                           (8)

The [fixed-minus odd-index construction](EXPLORATION_ODD_INDEX_PELL_SIGNS.md)
proves that these are positive integers satisfying the retained
auxiliary norms and both equations
`Uaux=j*c-J0=o*f-c`. This supplies all sixteen additional kernel
coordinates beyond the already supplied r.

Finally, putting u=d*x, choose

    kappa=psi_A(u), muP=chi_A(u),
    delta=(kappa-u)/(a+1), phiP=c-kappa,
    rho=(muP-a*kappa-W)/(4a+3).                            (9)

We have 4<=u<q<J0, W=2^u<q<X<a. The unchanged input-bridge congruences
give integrality. Strict Pell growth gives delta>0 and phiP>0, and
`muP-a*kappa>kappa>=2A>W` gives rho>0. Thus (5), (7), (8) and (9)
specify all **32** positive existential coordinates of the deleted
system and satisfy its **20** equations.

The fixed machine never accepts x=1, proving a complete false input.
No astronomical tuple from another packed index is reused.

## 6. What is numerically checked

The checker verifies the complete78 source and unchanged norm
correction. It constructs the actual three-row slabs and checks every
window against the original machine predicate, both unique markers,
and every cyclic horizontal overlap. For manageable exact arithmetic
it compiles each slab's finite subalphabet of actual allowed windows,
and verifies six complete positive outer tuples, including both zero
and all-one dummy fills. The proof above applies to the full fixed
machine alphabet, independently of these finite numerical subalphabets.

Every tested vertical coefficient is checked to be exactly twice its
center copy bit. Every horizontal coefficient and center-clause
coefficient is checked separately. All six retained outer equations,
the positive raw bound, `P*v=q`, `1<P<B`, the two masks, the odd index
and the full 3dN valuation are checked with exact integers.

The full fixed alphabet and the enormous complete Pell tuple are not
numerically materialized. Their existence and every positivity
obligation are supplied by Sections 3--5. This rejected optimization
does not provide a smaller universal certificate. It concerns the
unchanged native compiler of80; a different compiler may enforce
alignment through its encoded local conditions.
