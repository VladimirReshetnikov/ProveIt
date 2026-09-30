# Exact odd-controller orbits and a stronger nonabsorbing boundary obstruction

Consider the paid [binary63 component](native_binary_three_row_fifo58.md),
with fixed signed integer coefficients a,b,c,g and ordinary input x>0:

    aA+bD+cq=g,
    I=2x, W=2^m>I, q=2^t, D=I+WA.                    (1)

Its read and append words D,A use only00,01,10, start with00, use all
three rows, and end with zero queue. All26 existential coordinates of the
arithmetic source remain strictly positive; intermediate queue and carry
states below are mathematical states, not additional witnesses.

For odd a, this note gives an exact scalar-orbit decision at each fixed
width, an explicit duration bound in terms of a multiplicative order,
and a uniform bound on the orbit's transient. Every test retains the11
prohibition. Independently of oddness, it proves that the boundary
c=-b with a/b<1 has a finite input language. The already classified
case a/b=1 is the [fixed-idle57 family](binary_fixed_idle_controller.md).
These results do not decide every remaining coefficient choice or lower
the complete universal bound75.

## 1. The scalar orbit determines the append stream when a is odd

Let N_j be the queue value and k_j the affine carry. For read bit d_j
and append bit e_j,

    2N_(j+1)=N_j-d_j+W e_j,
    2k_(j+1)=k_j+a e_j+b d_j,
    N_0=I, k_0=-g, N_t=0, k_t=-c.                    (2)

Set

    C=a+bW, z_j=k_j+bN_j.

Then

    z_0=bI-g, 2z_(j+1)=z_j+C e_j.                   (3)

If a is odd, C is odd and nonzero. Consequently e_j is forced to be
z_j modulo2, and the unrestricted scalar evolution is

    z_(j+1)=(z_j+C*(z_j modulo2))/2.                 (4)

This does not remove the digit guard. Given(4), reconstruct the queue
from its actual initial value and those append bits. Define k_j=z_j-bN_j.
It is integral and satisfies(2), but it is an allowed carry history only
while d_j e_j=0. Conversely every legal history must follow this unique
scalar orbit. Thus a fixed width has at most one continuing physical run.

Explicitly, its read bits are

    d_j=the jth bit of I,       0<=j<m,
    d_j=e_(j-m),               j>=m.                 (5)

The compulsory first00 is e_0=0, equivalently g even. For t>m, zero
queue means that the last m append bits are all0. Acceptance is exactly:
the first row is00, every pair from(5) avoids11, some e_j before t is1,
the last m append bits are0, and z_t=-c. Positive I then supplies a10
row; the first row supplies a00 row. The original58 positive converse
extends the resulting row words to all positive arithmetic coordinates.

## 2. Finite scalar core and its exact period

Put sigma=sign(C), L=abs(C), and w_j=sigma*z_j. The append parity is
unchanged by this sign change, and

    w_(j+1)=(w_j+L*(w_j modulo2))/2.                 (6)

Let dist(w,[0,L]) be the nonnegative integer distance to the interval.
One step of(6) decreases this distance to at most its integer half.
For w<0 this follows from w'>=w/2; for w>L from w'<=(w+L)/2.
Therefore the first entry time mu into[0,L] satisfies

    mu<=bit_length(dist(w_0,[0,L])),                (7)

where bit_length(0)=0. The interval is invariant. Its endpoints0 and L
are fixed; its interior is permuted by division by2 modulo the odd L.
Thus the scalar states and append bits are periodic from mu onward.

If w_mu is0 or L, the period p is1. Otherwise put

    n=L/gcd(w_mu,L), p=ord_n(2).                     (8)

This is the exact period: returning after r steps is equivalent to
L dividing (2^r-1)w_mu, hence to2^r=1 modulo n. In particular
p<=max(1,L-1). Formula(8) is a finite effective computation and makes
no claim about the arithmetic difficulty of varying m without a bound.

For b!=0 there is a useful uniform transient bound. Put
B=abs(b), a'=sign(b)*a, g'=sign(b)*g. Whenever

    BW+a'>0,

the signs of C and b agree and L=BW+a'. Since the even input satisfies
2<=I<=W-2, its initial scalar coordinate obeys

    2B-g'<=w_0<=BW-2B-g'.

Consequently, independently of both the ordinary input and the width,

    mu<=bit_length(E),
    E=max(0,g'-2B,-g'-a'-2B).                        (9)

Only the finitely many powers W failing BW+a'>0 are excluded from this
uniform statement. The fixed-width theorem itself covers those powers too.

## 3. A duration cutoff retaining the queue guard and positive streams

At time S=mu+m the queue consists entirely of periodic append bits.
Its contents, scalar state, and subsequent read/append pairs are therefore
periodic with period p. For the first S+p steps, check(5) explicitly.
If any prohibited11 occurs, all longer histories are invalid. Otherwise
the periodic future introduces no new guard violation.

After one further period the flag recording a prior append1 has stabilized
as well: either a periodic1 has appeared, or the future consists of zeros
and can never change that flag. Thus existence of any accepting duration
at this fixed width is decided by the exact finite bound

    1<=t<=mu+m+2p.                                   (10)

The test also requires t>m and every acceptance condition from Section1.
It does not append zero rows to an accepted history. It checks actual
positions of the unique run, with the original terminal value -c.

There is a sharper restriction for short scalar periods. Every core
cycle except w=0 contains an append1: an all-zero periodic word would
make(6) repeated division by2 and force the state to0. Hence, if p<=m
and this is not the zero cycle, no zero queue can occur at t>=mu+m.
Every accepting duration then satisfies

    m<t<mu+m.                                       (11)

If the eventual cycle is w=0 and c!=0, no time t>=mu can accept instead.
Combining(9) and(11), a scalar period at most m permits only a bounded
number of steps beyond the initial queue width, uniformly over all large
widths and inputs. This is a structural restriction, not an unbounded-
width decision procedure.

Dropping the guard would change the predicate. For

    a=1,b=3,c=-2,g=0,I=2,W=4,

the scalar orbit is z=6,3,8,4,2. At t=4 it has terminal z=-c and two
final zero append bits, giving A=2,D=10,q=16 and satisfying(1).
But its second row is11, so the component rejects that trace.

## 4. A new finite-input obstruction on the boundary c=-b

This section does not require a to be odd. Write F0 for the00 selector.
Every58 history has A even, F0 odd, and t>m; therefore Ltime=q/W is a
positive even integer. The checksum and transport give

    W*(Ltime-A)=I+A+F0+1.

The left quotient Ltime-A is a positive even integer, hence at least2.
Since I<W, this implies the width obstruction

    A+F0+1>W, hence W<=A+F0.                         (12)

Now take b!=0,c=-b and normalize B=abs(b), a'=sign(b)*a,
g'=sign(b)*g. Equation(1) and the checksum give exactly

    (B-a')A+B F0=R, R=-g'-B.                         (13)

If a'<B, equivalently a/b<1, put s=min(B-a',B)>0.
Positivity and(12)--(13) give

    W<=A+F0<=floor(R/s).                             (14)

If R<=0 the source has no witnesses. Otherwise this is an effective
constant bound on width and on ordinary input2x<W. Searching the finite
queue/carry graph at its finitely many widths decides every input. This
excludes universality for an entire boundary region left open by the
earlier closed-cone condition; it is not another application of that
condition, which has distance zero on c=-b.

At a'=B, equation(13) fixes F0 and gives the regular fixed-idle family
linked above. For a'>B it has opposite coefficient signs and the present
finite-width proof does not apply. No claim about that remaining side or
the strict interior -abs(b)<sign(b)*c<0 follows from(14).

## 5. Checks, arithmetic cost, and limits

The [checker](binary_odd_controller_orbit.py) constructs the scalar core
and independently verifies its multiplicative-order period. It compares
the guarded orbit test with the full queue/carry/row-mask graph, including
both signs of C and both transient directions. Constructed legal physical
histories supply positive acceptance examples. Separate tests exercise the
uniform transient bound, the short-period restriction, the exact boundary
width bound, and the guard counterexample above.

Default replay compares1,000 full product graphs, including300 constructed
accepting histories, and860 boundary cases. Two independent proof/source
reviews and fresh default replays passed without findings. One independent
audit generated364 legal row words directly from scalar transport and
disjointness, covering both signs of C and zero/nonzero terminal carries.
Another generated append choices directly from the carry parity, without
the scalar-orbit or order formulas, and matched earliest accepting times
on3,510 cases containing16,834 states and284 accepting endpoints. These
finite audits corroborate the parametric proofs above.

All witnesses returned by the tests have positive x,W-I,q/W,F0,A,D,
first00, disjoint fields, and exact controller and transport identities.
Their full positive Pell extensions are inherited from FIFO58. The paid
general schedule stays63=33M+30A,18 equations and26 positive existential
coordinates. The present analysis adds no arithmetic certificate for a
general finite controller, no source-input loader, and no new universal
bound.
