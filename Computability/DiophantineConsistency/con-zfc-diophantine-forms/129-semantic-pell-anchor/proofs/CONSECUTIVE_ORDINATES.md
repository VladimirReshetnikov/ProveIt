# Consecutive Pell ordinates with orientation supplied by the output row

This note is an independently derived optional compiler transformation for
natural-domain Pell power and modular-residue requests. It does not by itself
claim a lower final variable count.

## Exact lemma

Let A,n,y,z,R be nonnegative integers with A>=2 and 1<=n<A. Suppose

    y^2+z^2-2Ayz=1,       n*y-z=R.

Then 0<=z<y, and X=A*y-z is positive and satisfies

    X^2-(A^2-1)y^2=1.

Consequently there is a unique j>=1 with

    y=Y_j(A), z=Y_{j-1}(A), X=X_j(A),

where X_0=1,Y_0=0 and the standard Pell recurrences use base A.

Proof. If y=0, the conic gives z=1 and the output row gives R=-1,
contradicting R>=0. Thus y>=1. If z>=y, the output row gives
z<=n*y<Ay. For fixed y the function f(z)=z(2Ay-z) is increasing on
[0,Ay], so

    z(2Ay-z)>=y(2Ay-y)=(2A-1)y^2>y^2.

This contradicts y^2-z(2Ay-z)=1. Therefore z<y and
X=Ay-z>=(A-1)y+1>0. Expanding the displayed norm gives exactly the
conic. The standard classification of positive Pell solutions gives a
unique j>=1. The backward recurrence yields
z=Ay-X=Y_{j-1}(A).

Conversely, for every j>=1 take y=Y_j(A),z=Y_{j-1}(A). The conic
holds identically, and

    n*y-z=X_j(A)+(n-A)Y_j(A)>0

for every n>=1. Thus any existing exact or modular output equality is
preserved by this replacement. The forward and reverse changes preserve
all semantic data and all quotients/remainders of the output row.

The condition n<A is used only to derive orientation in soundness. It
cannot be silently omitted: for A=2, y=1,z=4, the conic holds, and n=4
gives n*y-z=0 although z>y.

## Application to a shared cap

The pooled-cap certificate bounds the principal ordinate y and uses the
squares (y-k)^2. It is unchanged. After restoring X as above, its theorem
identifies j=k. Every independent pair must occur in at least one output
row satisfying the hypotheses; this needs an explicit incidence check.

For an exact-power request, n is an actual semantic base, so the shared
frame W>n and A>W^W guarantee n<A. A modulus row excludes n=0.
For a modular binomial request, the supporting base is n=q+1. The actual
radix q occurs as a semantic power output, so q<W and hence q+1<=W<A.
The right side is a sum of products of natural coordinates, so R>=0.
All requested indices in the combined source are positive before any
power interpretation. There are no additive derived pairs in its current
15-seed architecture.

## Quadratic implementation

Introduce u=y*z and use two quadratic rows

    u-y*z=0,
    y^2+z^2-2A*u-1=0.

Replace X+n*y=A*y+R by n*y=z+R. The restored X is an integer
polynomial, but it is not a new quantified coordinate.

A direct graph with X,y,w=A*y already uses the same three coordinates
and two quadratic rows. Thus no raw per-seed variable improvement is
claimed over that centered-square implementation. The new form may alter
the success of subsequent monic/nonnegative projections; any final
saving must be measured after actual exact projection. Both forms have
fully explicit integer coefficients and exact degree at most four after
summing row squares.
