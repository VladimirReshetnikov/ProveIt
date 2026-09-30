# Direct Boolean ternary rails and an exact 60-operation FIFO

A one-addition change to the positive ternary Pell kernel certifies native
Boolean streams directly. The kernel now uses `Y=3s+1`, so its recovered
central binomial coefficient is prime to3. Kummer's theorem then excludes
every ternary doubling carry. This replaces the previous shifted1/2-digit
fields by actual0/1-digit rails.

The complete typing component costs **55=28M+27A**. With ordinary input
2x, a scalar ternary FIFO and its joint stream bound cost **60=31M+29A**,
with16 equations and27 strictly positive witnesses besides x. The four
rail streams must all be nonzero. No origin label is prescribed. A general
fixed affine carry controller gives an exact69-operation architecture;
a previously studied zero-code controller fits66. These are components
and full labelled relations, not universal representations. A code filter,
ordinary-input compiler and universal acceptance proof remain unpaid.
The established complete universal bound remains76.

## 1. Literal source and exact typing predicate

Supply positive q,F0,F1,F2,F3 and the seventeen coordinates

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux.

Also supply positive bound_beta and alpha. In the retained positive ternary
43-operation core, alias its scale register n2 to q. Keep X=wq, but replace
its instruction Y=sq by

    three_s=3s, Y=three_s+1.                            (1)

This adds exactly one addition, giving44=25M+19A. Every other core
instruction and comparison is unchanged. In mathematical notation put
E=XY, Delta=a^2+6a+8, J=2r+1 and u=J+jc. The ten kernel equations are

    (E^2+X)(Yk)^2=tau(tau+1),
    c=Yk+eta, k=eta+zeta, k=r+1+hE,
    a=Y(X+1), d=X+ac+ga(6a+8),
    d^2=1+Delta*c^2,
    (ic^2)^2=Delta(f^2-1),
    (ic^2)^2(u^2-y_aux^2)=1-y_aux^2,
    u=c+of.                                            (2)

Add the three equations

    r=F0+qF1+q^2F2+q^3F3,
    r+bound_beta=X,
    F0+F1+F2+F3+alpha=q.                               (3)

Three Horner products and three sums cost6. Compute A=F0+F1 and D=F2+F3,
then A+D and its sum with alpha, costing4 additions. The bound on X costs
one addition. Thus (1)–(3) cost55, with13 equations and19 auxiliary positive
coordinates besides the five positive parameters.

Their exact projection is:

- q=3^t for an integer t>=2;
- every Fi is positive, below q, with all t ternary digits in{0,1};
- sum Fi<q and sum Fi is even.

The Fi themselves are Boolean rails; there is no decoded offset to compute.
Zeros at individual time positions are unrestricted. A rail that is zero
at every position is excluded by the strictly positive supplied domain.

## 2. Bootstrap and recovery of the changed kernel

The joint bound and four positive fields imply q>=5, 0<Fi<q, and

    q^3+q^2+q+1 <= r < q^4, r>=156.

The paid bound and (1) give

    X>r, Y>=4, E>r+1, a>2r+1.

Let P=2XY^2+1 and A0=a+3. Then P>A0. Classifying the first Pell norm
in(2) gives k=psi_P(n); modulo E it gives n=r+1, modulo E. Since E>r+1,
n>=r+1. The interval Yk<c<(Y+1)k and P>A0 force the main Pell index
p>=n+1>=r+2>=158. Hence

    c>A0^(p-1)>A0*(A0^2-1)^2,
    c>Y(r+1)>J, c>2p.

These verify every generic relaxed-rank and half-parameter threshold used
in [the retained ternary proof](native_controller_three_selector_53.md).
The auxiliary norms and congruences recover p=J, c=psi_A0(J), d=chi_A0(J),
and an auxiliary main-base index m divisible by c, with m>=c>2p. The
auxiliary parameter R=ic^2 is greater than1 and f>2c. The generic signed
positive-branch theorem in
[the fixed-minus parity proof, Section4](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
therefore applies to the plus signs in(2) and forces **r even**, including
noncanonical auxiliary indices.

The first index is exactly n=r+1. Indeed another positive representative
would be at least r+1+E>J, whereas c>k and P>A0 preclude n>p=J.
These arguments use X,Y and their displayed bounds; none needs q to divide Y.

For completeness, use the lower-ratio estimate before invoking any upper
small-error estimate. With xi=(X+1)^(2r)/X^r, the retained elementary Pell
bounds give the weaker but sufficient estimate

    c/k > xi*(1+3/(2a))^(2r)*(1+1/(2XY^2))^(-r) > xi.

Its final strict inequality follows from 6XY^2>a, valid already for Y>=4
and X>r. Since c/k<Y+1 and xi>X^r, integrality gives Y>=X^r and
`a>X^(r+1)`. Now the usual upper estimate is justified:

    6r/a < 1/2,
    c/k < xi*(1+12r/a),
    0<c/k-xi < 24r/(X+1).                              (4)

For the direct exponent step, the recurrence for
`chi_A0(j)+(3-A0)psi_A0(j)` agrees with3^j modulo6a+8. Equation(2)
thus gives X=3^J modulo6a+8. Both positive representatives are smaller
than the modulus: X<a, while X>r>=156 implies

    3^J=3*9^r < X^(r+1) < a.

Therefore X=3^(2r+1). Since q divides X and q>=5, q=3^t with t>=2.
The error in(4) is now below1/2 and the fractional binomial tail of xi
is below1/6. Together with Y<c/k<Y+1 and c/k>xi, they force

    Y=floor(xi)
     =binom(2r,r)+sum_{j=1}^r binom(2r,r+j)*X^j.        (5)

This is the same general positive kernel proof at the changed Y, with its
thresholds verified explicitly. The scale alias q is not a hidden assertion
that q divides Y: it does not, and that divisibility is never used.

## 3. No doubling carries, and the strictly positive converse

X is divisible by3. Equations(1),(5) give

    binom(2r,r) = 1 modulo3.

Consequently its3-adic valuation is zero. By the factorial-valuation/carry
identity, doubling r in ternary has no carry anywhere. This is equivalent
to every ternary digit of r lying in{0,1}: the first digit2 would already
create a carry, while digits0/1 cannot start one. Since Fi<q and q=3^t,
the packing in(3) has no field carries, so all four fields have precisely
the claimed Boolean digits. Also q is odd, giving r=sum Fi modulo2.
This proves the forward projection.

Conversely, take any four fields in the exact predicate. Their packing r
has digits0/1 and is even. Let z be the number of its1 digits. Ternary
place values are odd, so z is even. Reduction of `(1+T)^(2r)` modulo3,
using `(1+T)^(3^j)=1+T^(3^j)`, gives

    binom(2r,r)=2^z=1 modulo3.                         (6)

For clarity, extracting the coefficient of T^r in that product is
unambiguous: each digit of2r is0 or2 and each selected exponent digit is
between0 and2, so no exponent-digit carrying occurs.

Set

    J=2r+1, X=3^J, w=X/q,
    Y=floor((X+1)^(2r)/X^r), s=(Y-1)/3,
    bound_beta=X-r, alpha=q-sum Fi.                    (7)

q divides X because J>t; (5),(6) make s integral, and Y>X makes s positive.
The two new slacks in(7) are positive. Apply the retained positive plus
kernel map at these actual X,Y,r:

    a=Y(X+1), A0=a+3, Delta=A0^2-1, E=XY, P=2XY^2+1,
    c=psi_A0(J), d=chi_A0(J), k=psi_P(r+1),
    eta=c-Yk, zeta=k-eta, tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/E, ga=(d-X-ac)/(6a+8),
    m=2cJ, f=chi_A0(m), i=Delta*psi_A0(m)/c^2,
    R=ic^2, y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u-c)/f, j=(u-J)/c.

The established congruences make all quotients integral, and the verified
ratio and growth bounds make every coordinate strictly positive. Even r
gives J=1 modulo4, supplying both plus congruences in the auxiliary map.
The only changed quotient is s=(Y-1)/3; its validity was proved in(6),(7).
Thus all thirteen equations hold. This proves the complete positive
converse without materializing the enormous auxiliary coordinates.

## 4. Exact scalar FIFO with ordinary input2x

Supply positive x,W,width_beta,L and add

    I=2x, D=I+WA, I+width_beta=W, q=WL.                 (8)

I costs one multiplication; WA and its transport sum cost two operations;
the width bound and divisor cost one each. Adding these5=3M+2A operations
to55 gives **60=31M+29A**, with16 equations and27 positive existential
coordinates besides x. The already computed A,D are reused.

The exact projection is a t-step scalar ternary FIFO of width m, with
q=3^t, W=3^m, m>=1, initial contents2x<W and terminal contents zero.
Its append trit at each step is the sum of the two Boolean append rails
F0,F1; its read trit is the sum of F2,F3. Each rail is nonzero over the
whole history, and A+D<q is retained. All four Boolean choices at a step
are available, so a scalar1 can be split between its rails in either way.
There is no first-label restriction.

The exact recurrence is

    d=N modulo3, N_next=floor(N/3)+(W/3)*a.

The binary-rail sums are native trit words because their digits are at
most2. Transport and the paid bounds reconstruct the recurrence and its
zero endpoint. In particular D<q and positive A imply q>W, so t>=m+1.

Conversely any such finite run yields(8) by telescoping. Since W is odd,
D=2x+WA gives A+D even. Thus the parity required by the typing component
is automatic; no extra parity equation or padding step is needed.
Apply the positive map from Section3 and take L=q/W and width_beta=W-2x.
This proves both directions with all supplied coordinates positive.

Every positive x has a bare-component witness. Choose a power W of3
strictly larger than2x+1, put q=3W, A=2 and D=2x+2W. Use F0=F1=1 and
split each ternary digit of D into two Boolean digits, placing every2
as1+1. The top digit of D is2, so both read rails are positive. Moreover
A+D<q and the total population is even. These fields describe appending
trit2 once, then zeros until the queue is empty. This construction is
component completeness for ordinary input; it is not acceptance by a
universal controller.

## 5. Precisely costed carry interfaces

Let labels be the four Boolean rail bits in order append0,append1,read0,
read1. A fixed affine controller is

    3k_next=k+h+sum ci*label_i, k0=cs, kt=cf.

Its exact global equality is

    2 sum ci*Fi + (h-2cf)q = h-2cs.                    (9)

The multiplier2 is absorbed into fixed coefficients. Four products, three
summation additions, one product by q and a final addition cost9, with a
free comparison to the fixed right side. Thus the full labelled relation
costs69=36M+33A, has17 equations and the same27 positive witnesses.
Conversely, successive reductions of the global identity modulo3 recover
every integral carry. This includes the entire reachable carry graph;
there is no uncharged edge or block filter.

The older01/10 serialized Rule110 candidate has

    16F0+8F1-176F2-80F3+27q=27.

Reusing A, compute8(A+F0), the two weighted reads and their sum, subtract
the latter, compute27q and add it. Comparison with27 costs nothing. This
adds8 operations, giving68=35M+33A. The nonzero fixed right side needs the
subtraction before comparison; treating a variable expression plus27 as
a free equality operand would incorrectly report67.

The separate00/12 candidate has h=cs=cf=0 and equality

    2F1+56F3=5F0+28F2.

Four products and two sums add6 operations, giving66=35M+31A. These are
exact relations for the previously proposed controllers, including their
uncoded paths. Both still need a proved code filter and raw-input/halting
compiler. The stricter positive-rail interface must also be respected by
any claimed accepting computation.

## 6. Evidence

The [checker](input_bridge_boolean_ternary60.py) independently expands
all source polynomials and checks the retained auxiliary-norm correction,
every literal operation count, and the combined controller schedules.
It checks142,506 pre-power positive field tuples; exhausts all positive
joint-bounded fields through q=81 against independent factorial valuations;
and separately checks999 direct central-binomial residues. The finite
FIFO audit compares290,037 bounded tuples with direct queue execution.
Two hundred ordinary inputs have explicit positive outer maps.

Actual main/first Pell computations at r=4,10,12 check the changed quotient
and canonical interval. These are standalone modified-kernel prototypes,
not instances of the four-field55 source. The general positive extension
is the proof in Section3, not those finite computations.

Default execution compares the saved
[receipt](input_bridge_boolean_ternary60.json). Independent full proof, source, and default-replay review passed.
No source in the retained kernel or existing FIFO packages is modified.
