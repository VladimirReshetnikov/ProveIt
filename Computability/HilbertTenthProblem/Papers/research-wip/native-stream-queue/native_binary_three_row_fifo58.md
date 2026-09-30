# A binary three-row FIFO in58 operations

Three exact binary selectors cost **53=28M+25A**. Adding a paid ordinary
input2x, width and transport gives a **58=30M+28A** binary FIFO component,
with **26 positive existential coordinates and17 equations**, besides
the ordinary positive input x. Its physical read/append rows are precisely

    00, 01, 10.

Every represented history begins with00, uses all three rows, starts with
the ordinary binary integer2x, and ends with zero queue contents. Every
positive x has a component witness. This is a complete finite FIFO
relation, not an arithmetic certificate for an arbitrary finite controller.
The complete universal certificate bound remains75.

The three rows support
[finite-control, block-coded universal simulation](four_row_queue_block_simulator.md).
The component below provides positive arithmetic extensions of those
coded traces in radix2. A controller certificate and a loader from the
original unencoded source input remain unpaid.

## 1. Literal53-operation selector source

Keep the exact43-operation fixed-minus binary core used in
[the four-selector56 theorem](native_controller_binary_selector56.md),
with the computed scale alias n2=q. Its17 positive coordinates are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y.

The positive selector parameters are q,F0,F1,F2. Also supply positive
odd_half and bound_beta. Put

    X=wq, Y=sq, E=XY, A=a+2, Delta=a^2+4a+3,
    H=4a+3, J=2r+1, U=jc-J.

The ten core equations are

    (E^2+X)(kY)^2=tau(tau+1),
    c=kY+eta, k=eta+zeta, k=r+1+hE,
    a=Y(X+1), d=X+ac+gamma*H,
    d^2=1+Delta*c^2,
    (ic^2)^2=Delta*(f^2-1),
    (ic^2)^2*(U^2-y^2)=1-y^2,
    U=of-c.

The four selector equations are

    r=F0+qF1+q^2F2,
    F0+F1+F2+1=q,
    s=2*odd_half+1,
    r+bound_beta=X.                                     (1)

Horner packing costs2M+2A, the checksum3A, the odd quotient1M+1A,
and the last bound1A. Together with the retained core25M+18A this is
53=28M+25A. The14 comparisons are free under the certificate convention.

## 2. The smaller pre-power bounds still give the exact kernel

Before assuming powers, disjoint fields, or a computation, positivity gives

    q>=4, 0<Fi<q,
    q^2+q+1<=r<q^3, r>=21,
    X>r, Y>=q>=4, E>r+1, a>2r+1.                       (2)

In fact the positive odd_half gives Y>=3q, though that stronger bound is
not needed below. The first Pell parameter `P=2XY^2+1` satisfies P>A.
The first norm has `k=psi_P(n)` for n>=1. Since P=1 modulo E,
the index equation gives n=r+1 modulo E, hence n>=r+1. The main norm
gives `c=psi_A(p)`, `d=chi_A(p)`. The strict interval
`Yk<c<(Y+1)k` and P>A imply p>=n+1>=r+2>=23.

Consequently `c>A*Delta^2` and c>2p. Also

    c>Yk>=Y(r+1)>=4(r+1)>2J.

The retained
[strong auxiliary recovery](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
and [half-parameter index proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md)
apply at these bounds: they recover p=J, an auxiliary index m with c|m,
m>=c>2p, and `ic^2=Delta*psi_A(m)`, `f=chi_A(m)`. The bounds exclude
the unwanted residue sign exactly as in the four-selector proof; no
field parity has been assumed. Since a larger n in its residue class
would exceed p=2r+1, one also gets n=r+1 exactly. The
[fixed-minus sign theorem](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
then proves r odd for every positive solution, including noncanonical
auxiliary indices.

For completeness, the ratio argument also works at r>=21. Set
`xi=(X+1)^(2r)/X^r`. The elementary Pell lower estimate gives

    c/k>xi*(1+3/(2a))^(2r)*(1+1/(2XY^2))^(-r)>xi,

because6XY^2>a. The strict upper ratio c/k<Y+1 and integrality imply
Y>=X^r and a>X^(r+1). Hence6r/a<1/2 already, since X>r>=21.
The ordinary Pell upper estimate gives

    0<c/k-xi<24r/(X+1).

The direct exponent recurrence is `d-ac=2^J modulo H`. Both X and
2^J are below a: X<a, while

    2^J=2*4^r<X^(r+1)<a.

Thus X=2^(2r+1) exactly. Since q|X, q=2^t for t>=2. The displayed
ratio error is now below1/2 for every r>=21. The omitted lower half
of the binomial expansion of xi has size strictly between0 and1/4,
so the interval forces

    Y=floor(xi)
     =binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j.          (3)

These arguments use the actual smaller bounds(2); the four-selector
threshold r>=156 is not silently imported.

## 3. Exact typing and the fresh positive converse

Since X is divisible by2q, equation(3) and the paid oddness of s=Y/q give

    v2(binom(2r,r))=t=popcount(r).

The three base-q fields are bounded by q, so

    sum_i popcount(Fi)=popcount(r)=t
                     =popcount(q-1)=popcount(sum_i Fi).

Binary addition can preserve the total population only when there are no
carries. Therefore F0,F1,F2 partition the t-bit repunit exactly. Since r
is odd, F0 has units bit1. Every field is positive, so all three labels
occur and t>=3, q>=8. In particular F1 and F2 are even and disjoint.
This is the full forward typing projection, not a test only on candidate
Boolean words.

Conversely take any three positive binary words partitioning q-1 for
q=2^t, with F0 odd, and pack their actual r by(1). Then t>=3, r is odd,
popcount(r)=t and r>=q^2+q+1>=73. Set

    J=2r+1, X=2^J,
    Y=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j,
    w=X/q, s=Y/q,
    odd_half=(s-1)/2, bound_beta=X-r.

The exact valuation proves w,s integral, and s is odd. Since Y>=X^r,
s>1; both new slacks are strictly positive. Construct afresh

    a=Y(X+1), A=a+2, Delta=A^2-1, E=XY, P=2XY^2+1,
    k=psi_P(r+1), tau=(chi_P(r+1)-1)/2,
    c=psi_A(J), d=chi_A(J),
    eta=c-kY, zeta=k-eta,
    h=(k-r-1)/E, gamma=(d-X-ac)/(4a+3).

The same ratio bounds, now evaluated at these constructed X,Y, give
`Y<c/k<Y+1`, so eta,zeta>0. The first congruence makes h integral,
and strict Pell growth makes it positive. P is odd, making tau a
positive integer. The direct exponent congruence makes gamma integral,
and `d-ac=2c-psi_A(J-1)>c>X` makes it positive.

For every remaining strong auxiliary coordinate use

    m=2cJ, f=chi_A(m), T=Delta*psi_A(m), i=T/c^2,
    y=psi_T(J), U=chi_T(J)/T,
    j=(U+J)/c, o=(U+c)/f.

The retained divisibility proof gives c^2|T. Odd J makes U integral;
J=3 modulo4 gives `U=-J modulo c` and `U=-c modulo f`, so j,o are
positive integers. Both auxiliary norms hold by the Pell identities.
These are precisely the original strong43 witnesses at this actual r
and scale q. This proves the full strictly positive converse without
materializing the enormous Pell values or weakening the auxiliary square.

## 4. Add ordinary input and fixed-width queue geometry in five operations

Interpret the three labels as00,01,10, and write D=F2, Bappend=F1.
These two ports are existing coordinates and cost no operations. Add
positive W,L,width_beta and the equations

    2x+width_beta=W,
    q=WL,
    D=2x+W*Bappend.                                    (4)

Compute2x as x+x. The schedule uses that addition, the width addition,
two products WL and W*Bappend, and the transport addition: **2M+3A**.
The complete source therefore has58=30M+28A,17 equations, and26 positive
existential coordinates. The ordinary varying input is x itself.

Soundness: q=2^t, so W and L are powers of two. Write W=2^m.
The paid width gives0<2x<W and m>=2. Positive Bappend and D<q give
D>W and hence t>m. For the read bits d_j and append bits a_j, the
transport identity is equivalent to the exact recurrence

    N_0=2x, d_j=N_j modulo2,
    N_(j+1)=floor(N_j/2)+(W/2)*a_j,
    0<=N_j<W, N_t=0.                                  (5)

Successive reduction modulo2 of(4) proves this, and telescoping proves
the converse. Selector typing says no pair(d_j,a_j) is11, the first
pair is00, and each of00,01,10 occurs. All states N_j are mathematical
intermediates and may be zero; no positive state witness is being omitted.

Conversely take W=2^m and any t-step run(5) from2x with0<2x<W, using the three rows,
starting with00, ending with0, and having a nonzero append stream.
The read stream is positive because D=2x+W*Bappend. Thus all three
row-indicator fields are positive; the first row supplies F0>0. Set
q=2^t, L=q/W and width_beta=W-2x. Positive append and transport force
t>m, so L is a positive integer. The53 typing converse supplies every
remaining positive kernel coordinate. This is an exact component theorem
for all such histories.

Every positive x has an explicit bare-component history. Choose the least
power W=2^m exceeding2x. First drain the m input bits while appending0;
then append1 on the empty read0; drain that bit for m further steps.
The resulting values are

    t=2m+1, q=2W^2, Bappend=W, D=2x+W^2,
    F0=q-1-Bappend-D>0.

All three rows occur, the first row is00 because2x is even, and no11
row occurs. This proves ordinary-input coverage, not acceptance by an
unpaid controller.

## 5. Exact extension of the block-coded universal simulator

In the binary corollary of the
[block simulator, Section6](four_row_queue_block_simulator.md), the
fixed code beta(a) is the low-first binary word for2a. Every code begins
with0. When those physical bits are packed in **radix2**, the initial
integer I is therefore even. Its two nonzero sentinels make I>0.
The proved simulated accepting histories begin with00, use every one
of00,01,10, end with zero contents and have positive append stream.

At the ordinary component parameter x=I/2, all hypotheses of Section4
are satisfied. The58 converse supplies every positive arithmetic witness
at the actual row streams and packed index. This is a constructive
extension of the coded trace, with no parity repair or extra selector.
The same physical0/1 digits interpreted in radix3 need not give an even
integer; that different packing is not used here.

Here I/2 is the coded numerical input. A fixed finite controller for those
three rows can simulate arbitrary source machines, but the58 source has
not certified that controller. It also has not converted the original
ordinary source input into this block code. Both remaining interfaces
must be paid before claiming a universal arithmetic reduction.

## 6. Centered61 controllers collapse to finite or fixed-mask languages

For arbitrary fixed signed integers a0,b0,g, the extra relation

    a0*F1+b0*F2=g                                      (6)

costs2M+1A. Thus its literal total is **61=32M+29A**, with18 equations
and the same26 positive existential coordinates. Substitute
I=2x, Bappend=F1 and D=I+W*Bappend to obtain

    (a0+b0*W)*Bappend=g-b0*I.                          (7)

If b0!=0, a solution requires

    2*abs(b0)*x <= max(abs(a0),abs(g)).                 (8)

Indeed if abs(b0)*I exceeded both absolute constants, W>I would make
the left coefficient have sign b0 while the right side has the opposite
sign. Since Bappend>0, this is impossible. Hence every represented language
in this case is finite, with an explicit bound on its ordinary input.
For each of those inputs, deciding existence is also effective: unless
a0+b0W=0, positive integral Bappend forces
`abs(a0+b0W)<=abs(g-b0I)`, bounding W. If the coefficient vanishes, check
whether the right side also vanishes; at such a power W>I, the construction
with Bappend=W supplies a permitted row history.

If b0=0 and a0!=0, set T=g/a0. A witness is possible only if T is a
positive even integer. In that case the language is exactly

    (2x) AND T = 0.                                   (9)

Necessity follows from Bappend=T and its disjointness from D; the low
width bits of D are exactly2x. For sufficiency choose a power
W>max(2x,T). Then `D=2x+WT` is disjoint from T exactly when(9) holds.
Choose a sufficiently large q=2^t divisible by W. The unused top bits
give F0>0, the first bits of D and T are0, and all three row fields are
positive. The58 converse applies. This is a fixed binary-mask language,
so its digit acceptance is regular.

Finally a0=b0=0 gives all positive inputs when g=0 and none otherwise.
Thus no centered controller(6) supplies arbitrary recursively enumerable
languages. This theorem does not apply to a general finite controller
or to an extra duration-dependent term.

## 7. A paid nonabsorbing63 interface remains separate

The more general fixed-coefficient relation

    a0*F1+b0*F2+c0*q=g                                 (10)

costs3M+2A, for a total **63=33M+30A** and18 equations. It is exactly
the integer carry relation

    2k_(j+1)=k_j+lambda(d_j,a_j),
    lambda(00)=0, lambda(01)=a0, lambda(10)=b0,
    k_0=-g, k_t=-c0.

Telescoping gives(10). Conversely reducing the global identity modulo
successive powers of2 forces every intermediate carry to be integral
and recovers the stated endpoint. The carries stay inside
`abs(k_j)<=max(abs(g),abs(a0),abs(b0))`. They are finite mathematical
states, not additional positive existential coordinates.

When c0!=0 the all-zero row does not fix the terminal carry. In particular
one cannot append free zero steps after selecting an accepting history.
For the actual58 outer tuple x=1,W=4,F1=4,F2=18,q=32, relation(10) holds
at a0=0,b0=1,c0=1,g=50. Appending00 keeps both streams and the zero queue
endpoint, but doubles q and violates(10).

The centered classification does not decide whether some nonabsorbing
controller of this form is useful. No missing input or controller
interface is included in the63 count, and no universality claim is made
for(10).

## 8. Checks and scope

The [checker](native_binary_three_row_fifo58.py) expands every source
equation in the53,58,61 and63 schedules, retaining the strong auxiliary
norm correction. It verifies the smaller pre-power thresholds, exact
population typing, and actual central-binomial valuations at small
packed prototypes. It compares arbitrary bounded transport tuples with
direct FIFO execution, and constructs bare positive outer witnesses for
the first300 ordinary inputs. The parametric map in Section3 supplies
the full positive Pell witnesses; those gigantic tuples are not materialized.

Separate checks test the centered classification and exact global/local
carry equivalence, including the nonabsorbing no-padding example. The
centered table coefficients are arbitrary fixed signed integers, while
every supplied existential coordinate remains strictly positive. Default
execution compares the adjacent saved receipt. No universal controller,
original-input block loader, or proof-assistant formalization is included.
Independent full proof, source and default-replay review passed without
findings. That review separately checked16,215 preliminary checksum
triples,1,540 FIFO witnesses with124,740 centered-coefficient evaluations,
and1,932 fixed-mask converse instances. These checks corroborate the
parametric theorems and do not supply an arithmetic universal controller.

From the repository root, with the pinned verification dependencies installed:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_three_row_fifo58.py
