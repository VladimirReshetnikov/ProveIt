# Two independent native fields in 48 operations

This complete typing component costs **48=27M+21A**, with13 equations
and19 positive auxiliaries beyond three positive parameters. The
**50=27M+23A** variant exposes the positive repunit H. Both parity
directions are proved: the retained signed auxiliary equations force
the packed index to be even, and the positive converse works for every
typed even index. Optional49/51 sources additionally impose parity by
one explicit multiplication; their exact schedules are also retained.

The result is a native two-field interface, not a complete universal
certificate. Controller transitions, routing, ordinary input and acceptance
remain separate obligations; the established complete universal bound
remains76.

## 1. Exact relation and source

The positive parameters are q,F0,F1. The relation holds exactly when
there exists t>=1 such that

    q=3^t,
    F0,F1 each have t ternary digits in{1,2},
    the units digit of F0 is2,
    F0+F1 is even.                                       (1)

Writing H=(q-1)/2, the decoded words U=F0-H,V=F1-H are two independent
Boolean ternary streams, except that U starts with1 and their combined
number of one digits is even. V may be identically zero. Every supplied
Fi remains strictly positive.

Supply the seventeen retained positive Pell coordinates and two positive
slacks alpha0,alpha1. Construct D0=q^2 and P=F0+qF1, and impose

    F0+alpha0=q, F1+alpha1=q, r=P.                       (2)

Attach the unchanged ten ternary Pell equations, with X=wD0,Y=sD0,
listed explicitly in Section2 of the
[paired-complement proof](native_controller_boolean_pairs56.md).
The source checker builds their polynomials independently at this q^2
scale.

The optional paid-parity source also supplies positive nu and compares
r with the computed product2nu. Its exact semantics remain(1): the
additional comparison is redundant once the signed-parity proof below
is applied, and its converse takes nu=P/2.

## 2. Excluding even radices before any index argument

The positive slacks give q>=2 and1<=Fi<=q-1. An even q is impossible
already in the elementary kernel equations. If q were even, D0=q^2,
X=wD0 and Y=sD0 would be even. Thus a=Y(X+1) and M=6a+8 would be
even. The equation

    d=X+ac+ga*M

would make d even. But its norm equation

    d^2=1+(a^2+M)c^2

would have an odd right side. This contradiction proves q odd and
q>=3 before invoking any Pell-rank, index or parity theorem.

For the optional paid-parity source there is an additional simple check
at q=2: its two bounded fields would both be1, giving r=3, contrary
to r=2nu. The48 proof does not use that additional source equation.

## 3. Small-endpoint bootstrap and the order of ratio estimates

The field bounds imply

    q+1<=r=P<=q^2-1.

Consequently, for any positive source solution,

    D0>=9, r>=4, r<D0, D0<r^2,
    X,Y>=D0, XY>=D0^2>r+1,
    a>=D0(D0+1)>2r+1.                                   (3)

The initial estimate a>=D0(D0+1) does **not** always give6r/a<1/2:
at q=3,r=8 it gives only a>=90. The proof therefore does not invoke
the upper ratio estimate at this point.

The retained first-norm argument gives first Pell index n>=r+1.
Its base exceeds A=a+3, and c>Yk>k, so the main index p>=r+2>=6.
The generic relaxed auxiliary-rank lemma requires c>AD^2, where
D=A^2-1. The ordinary Pell lower bound now gives exactly what is needed:

    c=psi_A(p)>A^(p-1)>=A^5>A(A^2-1)^2=AD^2.            (4)

The frequently used stronger estimate c>A^6 is unnecessary. Also
c>Y(r+1)>2r+1 and c>2p. Thus the retained relaxed-rank and
half-parameter argument applies, yielding

    p=J=2r+1, c=psi_A(J), d=chi_A(J),
    f=chi_A(m), c divides m, m>=c>2p,
    R=ic^2=(A^2-1)psi_A(m).

The unchanged base comparison then gives n=r+1 exactly. These steps
use neither the desired index parity nor the upper ratio estimate.

Put xi=(X+1)^(2r)/X^r. The ordinary **lower** Pell ratio bound gives

    c/k>xi*(1+5/(2a))^(2r)*(1+1/(2XY^2))^(-r)>xi.

The strict lower factor follows from10XY^2>a, already true because
X,Y>=9. Together with the independently supplied interval c/k<Y+1,
this first gives

    Y>=X^r,             a>X^(r+1).

Only now apply the upper ratio estimate. Since X>=9,r>=4,

    6r/a<6r/9^(r+1)<=24/9^5<1/2.

Hence the unchanged binomial estimate yields

    c/k<xi*(1+12r/a), 0<c/k-xi<24r/(X+1).              (5)

This order is noncircular: the lower ratio inequality is established
without6r/a<1/2, and it supplies the stronger bound used to prove that
hypothesis for the upper estimate.

The direct ternary recurrence gives X=3^J modulo6a+8. Both
representatives are in(0,6a+8), since X<a and

    3^J=3*9^r<X^(r+1)<a

even when the preliminary endpoint X=9 occurs. Thus X=3^J. The
scale divisor q^2 then makes q a power of3. The ratio error in(5)
is below1/2 and the retained binomial tail below1/6; the unit interval
therefore gives

    Y=floor((X+1)^(2r)/X^r),   q^2 divides binom(2r,r).   (6)

## 4. Why every positive solution has even r

The needed necessity result is the **generic signed theorem** in
Section4 of
[the fixed-index parity proof](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md).
Although that document's main application uses the minus branch and
A=a+2, its generic statement treats both signs and every A>=2.

All its hypotheses have now been proved at A=a+3. In detail, p=J is
odd and at least9; c=psi_A(p)>2p; c divides m and m>=c>2p; and

    f=chi_A(m)>=chi_A(2p)=1+2(A^2-1)c^2>2c.

Also R=ic^2>1, c divides R, and R^2=(A^2-1)(f^2-1). The positive
normalized root u=J+jc=c+of satisfies

    R^2*(u^2-y_aux^2)=1-y_aux^2,
    u=p modulo c,          u=c modulo f.

These are exactly the theorem's plus-sign hypotheses. Its conclusion is
(-1)^((p-1)/2)=1, hence **r even**.

For completeness, the sign information is essential. If the normalized
auxiliary index is z, the stronger chi step-down modulo4m gives
z=epsilon*p+2m*k. Keeping both polynomial signs gives

    r+m*k even,          r+(m+1)*k even.

The bounds c>2p and f>2c prevent opposite-sign residues from coinciding.
Subtracting the two parity conditions makes k even, then r even.
This argument allows noncanonical m,z and both epsilon signs; it is not
an assumption that the canonical witness choice was made.

## 5. Native typing and positive converse

The two positive field bounds in(2) already make P the proper base-q
packing and give P<q^2. With q=3^t, (6) requires at least2t carries
in doubling P, and there are at most2t positions that can generate a
carry. Thus all positions do so: the units digit is2 and every other
digit is1 or2. The two q-fields align with native length-t blocks.
Together with the proved even r and odd q, this establishes(1).

Conversely, given(1), take alpha_i=q-Fi and r=P. The field bounds are
strict and all these witnesses are positive. The packing has exactly2t
doubling carries, so(6) holds. Its parity is even, giving J=1 modulo4.
The complete positive witness map in Section5 of the paired-complement
proof applies at D0=q^2 and this r: (3)--(5) verify its rank/ratio
hypotheses, and its power and binomial divisibilities give integral w,s.
The same Pell congruences and growth bounds give every remaining positive
coordinate. If the optional nu is supplied, choose nu=P/2>0.

The smallest admitted case is q=3,F0=F1=2,r=8. It is included rather
than removed by a lower-bound guard. The exact first/main Pell and ratio
checks in the receipt use this actual module case.

## 6. Repunit and complete ledgers

The primary48 source appends these five instructions to the43 kernel:

    bound0=F0+alpha0; bound1=F1+alpha1;
    pack_product=q*F1; P=F0+pack_product;
    D0=q*q.

They cost2M+3A, giving48=27M+21A. Compare bound0=bound1=q and
r=P, then impose the ten kernel comparisons. There are19 positive
auxiliaries and13 equations.

The exposed-H variant supplies positive H and adds

    twice_H=H+H; q_calc=twice_H+1; compare q=q_calc.

It costs50=27M+23A, with20 positive auxiliaries and14 equations.
The source proves H=(q-1)/2. Projection Fi-H then costs one subtraction
for each desired Boolean stream; it has not been included for free.

The checker also retains the paid-parity variants. Appending
even_r=2*nu and comparing r=even_r adds one multiplication, one positive
auxiliary and one equation. They cost49=28M+21A and51=28M+23A.
Their semantics are unchanged, and their derivation remains useful when
an explicit parity source is preferred over the signed necessity lemma.

## 7. Evidence and scope

The [checker](native_controller_two_fields48.py) independently constructs
all four source variants and their fresh q^2 polynomials. It audits the
exact instructions and inherited auxiliary-norm correction. Pre-power
checks retain both index parities after excluding even q; they explicitly
record the q=3,r=8 failure of the crude initial ratio bound and verify
the stronger bound available after the lower ratio argument. The index6
rank comparison is also checked symbolically.

Exhaustive bounded field scans through t=6 compare exact factorial
valuation against native typing and separately record the parity
predicate. They do not substitute finite valuation checks for the
signed-parity necessity theorem. Canonical independent Boolean pairs
through t=7 include a zero decoded second word, while all supplied
fields remain positive. Exact first/main Pell calculations test r=8;
the full auxiliary extension is the mathematical converse above.

Default execution compares the
[saved receipt](native_controller_two_fields48.json). All earlier frozen
typing packages remain unchanged. This is a reusable native typing
interface; no arbitrary local Boolean map or universal controller is
claimed from having two typed streams.

Independent mathematical/source review and fresh default-receipt replay
passed, including the even-radix contradiction, index6 rank threshold,
lower-ratio-first endpoint argument, signed-parity hypotheses and full
positive converse.
