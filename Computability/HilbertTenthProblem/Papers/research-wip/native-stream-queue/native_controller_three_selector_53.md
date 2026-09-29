# A complete 53-operation native ternary three-selector relation

This is a complete arithmetic relation on three synchronized selector
streams, **not a universal computation certificate**. It proves its own
power geometry, native digit typing, common length, exact-one condition,
positive-witness convention and kernel parity. The complete count is
**53=29M+24A**, using the retained 43-operation ternary Pell kernel.
The first time position selects label 0. A 54-operation variant also
supplies the positive ternary repunit for downstream arithmetic.

The synchronized finite controller, variable incidence, ordinary numerical
input and FIFO transport are not part of these counts. The established
complete universal bound remains 76.

## 1. Exact semantics and supplied coordinates

The positive input parameters are q,F0,F1,F2. The relation holds exactly
when there is an integer t>=1 such that, writing H=(q-1)/2,

    q=3^t,
    Fi=H+Ti,
    Ti has t ternary digits, all in {0,1},
    T0+T1+T2=H,
    digit_0(T0)=1, digit_0(T1)=digit_0(T2)=0.               (1)

The sum condition is coefficientwise exact-one, not merely an untyped
integer partition. Every time position selects one of labels 0,1,2.
The Fi have native digits in {1,2} and are strictly positive, including
when a selector Ti is identically zero. H and the Ti are mathematical
decoded values, not supplied coordinates or uncounted arithmetic registers
in the 53-operation version.

The seventeen positive existential coordinates are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux.

Thus q,F0,F1,F2 plus these witnesses are twenty-one positive coordinates
when a containing certificate chooses all of them existentially. This
module has twelve equations. Its index r is a supplied positive witness;
the packed word P and scale D0 below are computed registers.

## 2. Full source

Set, by the paid schedule below,

    P=F0+qF1+q^2F2,       D0=q^3.

The first two source equalities are

    F0+F1+F2+2=2q,        r=P.                            (2)

For notation in the remaining source put

    X=wD0, Y=sD0, E=XY, Q=XY^2,
    A=a+3, M=6a+8, D=A^2-1=a^2+6a+8,
    J=2r+1, R=ic^2, u=J+jc.

Attach all ten retained ternary Pell equalities:

    tau(tau+1)=(E^2+X)(Yk)^2,
    c=Yk+eta,
    k=eta+zeta,
    k=r+1+hE,
    a=Y(X+1),
    d=X+ac+gaM,
    d^2=1+Dc^2,
    R^2=D(f^2-1),
    R^2(u^2-y_aux^2)=1-y_aux^2,
    u=c+of.                                                (3)

All exponentiation displayed in this mathematical source is evaluated by
the literal primitive schedule. The independently specified penultimate
source polynomial may use D(f^2-1) in place of R^2. Its residual differs
by the earlier auxiliary-norm residual times u^2-y_aux^2, precisely the
retained acyclic correction.

## 3. All bounds before power recovery

From positive Fi and (2), 2q>=5, so the integer q is at least 3. Also

    Fi>0,       F0+F1+F2=2q-2,
    q^2<P<=1+q+(2q-4)q^2<2q^3.

The upper bound places all available excess in the largest coefficient.
Consequently the actual kernel inputs satisfy

    D0>=27, r>=13, r<2D0, D0<r^2,
    X,Y>=D0, E>=D0^2>r+1,
    a>=D0(D0+1)>2r+1,
    6r/a<12/(D0+1)<=12/28<1/2.                           (4)

There is no assumption that q is odd, that any field is below q, or that
P<q^3 at this stage. Those assertions must be recovered after the kernel.

The retained kernel proof from
[the ternary kernel](../../1980/EXPLORATION_BASE_THREE_PELL_KERNEL.md),
with the enlarged-range argument in
[native overflow](../../1980/EXPLORATION_NATIVE_TERNARY_OVERFLOW.md),
applies with these explicitly weaker numerical thresholds as follows.

The first Pell norm, at parameter 2XY^2+1, has index n>=r+1 because
E>r+1. Its base exceeds A, while the interval gives c>Yk>k, so the
main index p is at least n+1>=r+2>=15. In particular
c> A^6>AD^2, c>J and 0<2p<=c. These are the generic auxiliary-rank
and half-parameter hypotheses. They recover p=J. The unchanged positive
difference

    (2(2XY^2+1)-1)-4A=4Y(X(Y-1)-1)-11>0

then recovers n=r+1. No scale being a square is needed.

Put xi=(X+1)^(2r)/X^r. The same ratio proof gives

    xi<c/k<xi*(1+12r/a),
    Y>=X^r, a>X^(r+1), 0<c/k-xi<24r/(X+1).

For clarity, it is the direct ternary recurrence, rather than a stronger
cubic exponent criterion, that is used here. The sequence
chi_A(j)+(3-A)psi_A(j) is congruent to 3^j modulo M. Hence (3) gives
X=3^J modulo M. Both representatives lie in (0,M): X<a, and

    3^J=3*9^r<X^(r+1)<a

because X>=27. Thus X=3^(2r+1). Since q^3 divides X, q is a power
of three. At this point X>48r, so the ratio error is below 1/2; the
unchanged binomial tail is below 1/6. The unit interval forces

    Y=floor((X+1)^(2r)/X^r),     D0 | binom(2r,r).          (5)

These steps prove the same kernel implication at the actual smaller
scale and index; they do not invoke an inherited lower bound of 83.

## 4. A checksum excludes both field carries and packed overflow

Now write q=3^t, H=(q-1)/2, N=3t and L=q^3=3^N. By Kummer's carry
theorem, (5) gives at least N carries when r=P is doubled in ternary.

First suppose P<L. There are at most N positions that can generate a
carry. All N must do so. The units digit must therefore be 2, and every
higher digit must be 1 or 2. Thus P is a native positive word of length
N whose units digit is 2.

We must still recover its supplied q-fields. Since their sum is 2q-2,
at most one Fi is at least q, and every Fi is below 2q. A carry from
that field cannot propagate: propagation would require a following field
of at least q-1, already contradicting the total sum and positivity of
the third field. If an internal field carry occurred, the sum of the
three normalized q-chunks would be

    (2q-2)-(q-1)=q-1=2H.

Each native positive chunk is at least H, so their sum is at least 3H,
a contradiction. Hence all Fi<q and they are the actual native chunks.

It remains to exclude P>=L, which was not an available preliminary
assumption. In this case P<2L, so it has one extra top trit, equal to 1.
The sole q-field overflow must be in F2, and the three low q-chunks of
P-L have sum

    (2q-2)-q=q-2=2H-1.

There are N+1 possible carry positions in doubling P, and (5) requires
at least N. At most one of the low N trits can be zero, because each
zero emits no carry regardless of its incoming carry. A q-chunk with
all positive trits is at least H; one zero can lower this by at most
3^(t-1). Thus these same three low chunks have sum at least

    3H-3^(t-1)>2H-1,

where H+1>3^(t-1) for every t>=1. This is a contradiction. Consequently
P<L, all Fi have t digits in {1,2}, and digit_0(F0)=2.

The checksum has paid for the bounds and rejected the extra top carry.
No per-field bound, fourth mask field or positive slack was assumed.

## 5. True one-hot selection, parity and every positive witness

Define Ti=Fi-H in the proof. Their digits are Boolean and (2) gives
T0+T1+T2=H. If this equality were not coefficientwise exact-one, take
its least nonzero residual digit. It belongs to [-1,2] and must be
divisible by 3, which is impossible. Thus there is exactly one selected
label at every time position. Since F0's units digit is 2, the first
selected label is 0. This establishes all of (1).

Conversely, take arbitrary selectors in (1) and set Fi=H+Ti. They are
positive, their sum is 4H=2q-2, and their packing has positive trits with
units digit 2. Therefore doubling P has all N=3t carries and the
divisibility in (5) holds exactly. Since q is odd,

    P = F0+F1+F2 = 0 (mod 2).

Thus r=P is even. The positive half-parameter converse needs J=1
modulo 4, and this follows without a parity variable or padding step.

For completeness the full witness map is the retained constructive map
at these new D0,r:

    J=2r+1, X=3^J, w=X/D0,
    Y=floor((X+1)^(2r)/X^r), s=Y/D0,
    a=Y(X+1), A=a+3, D=A^2-1, E=XY, B=2XY^2+1,
    c=psi_A(J), d=chi_A(J), k=psi_B(r+1),
    eta=c-Yk, zeta=k-eta,
    tau=(chi_B(r+1)-1)/2,
    h=(k-r-1)/E, ga=(d-X-ac)/(6a+8),
    m=2cJ, f=chi_A(m), i=D*psi_A(m)/c^2,
    R=ic^2, y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u-c)/f, j=(u-J)/c.

The bounds in (4), power divisibility and exact binomial rounding make
w,s positive integers. The ratio interval makes eta,zeta positive;
the retained Pell polynomial congruences make tau,h,ga integral, and
their growth arguments make them positive. The expansion at m=2cJ
gives c^2|psi_A(m). Odd J makes u integral, and J=1 mod 4 gives
u=c mod f and u=J mod c. The same retained growth bound gives u>c>J,
so o,j are positive. All seventeen witnesses satisfy (3).
This is a parametric existence proof; the enormous auxiliary coordinates
are not materialized by finite regression.

## 6. Exact complete ledger and the repunit variant

The ten outer instructions are

    sum01=F0+F1; sum012=sum01+F2;
    checksum=sum012+2; twice_q=q+q;
    p0=q*F2; p1=F1+p0; p2=q*p1; P=F0+p2;
    q2=q*q; D0=q2*q.

Compare checksum=twice_q and r=P for free. These instructions cost
4M+6A. Append the unchanged 25M+18A ternary kernel: the total is
53=29M+24A, with twelve equations and seventeen positive auxiliaries
in addition to the four positive parameters.

For a downstream compiler that needs an actual repunit register H,
replace the first four instructions by these five:

    twice_H=H+H; q_calc=twice_H+1; four_H=twice_H+twice_H;
    sum01=F0+F1; sum012=sum01+F2.

Supply positive H and compare q=q_calc, sum012=four_H. The resulting
module costs **54=29M+25A**, has thirteen equations, and supplies eighteen
positive auxiliaries. It proves exactly the same selector predicate while
making H available. Recovering H from the 53 module is not free.

A label column which is a permutation of trits 0,1,2 projects from the
54 module in two subtractions/additions: its value is H+F_at_2-F_at_0.
A 0/1 column with a single 1 projects as F_at_1-H in one subtraction.
These are exact native-time projections because the selectors are truly
one-hot. Different columns, state compatibility and FIFO transport still
have to be computed and paid. They are not an implemented controller.

## 7. Checks and scope

`native_controller_three_selector_53.py` independently specifies the
source polynomials, verifies the 53/54 literal DAGs and retained residual
correction, checks the pre-power bounds on arbitrary q, and enumerates
positive field triples including all overflow configurations. It compares
the exact factorial valuation of the whole P against the semantic native
selector predicate. Canonical selector words include identically zero
decoded selectors and every possible later label, while the supplied Fi
remain positive. Exact small main/first Pell computations test the reduced
scale's ratio thresholds: r=14 is the q=3 selector tuple (2,1,1), whereas
r=16 is a standalone kernel check, not an admitted selector tuple. The
general proof supplies the unmaterialized auxiliary extensions.

Independent complete proof/source/receipt review passed, including the
smaller bootstrap bounds, both overflow exclusions and every positive
coordinate. Fresh default receipt replay matches.

Default execution compares the adjacent saved receipt; `--write` writes
it. Neither the original kernel sources nor the existing queue interface
is changed. No universal controller, complete bound below 76 or Lean
formalization is claimed by this component.
