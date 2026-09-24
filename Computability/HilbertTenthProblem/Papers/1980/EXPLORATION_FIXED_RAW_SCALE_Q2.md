# The direct q-cubed to q-squared scale deletion is unsound

Deleting the multiplication `n2=Lbig*q` from the
[complete 81-operation certificate](FIXED_RAW_UNIVERSAL_81_PROOF.md),
and using `Lbig=q*q` wherever `n2` was used, gives a system with
**80 operations: 43 multiplications and 37 additions/subtractions**.
It has the same 33 positive existential unknowns and 21 equations.
This proposed reduction is **false**: there are fixed compiler numerals
for a machine accepting the empty set for which the modified system
has a completely positive solution at raw input x=1.

The obstruction is quantitative. For a genuine one-hot state word
with N cells, let V be the number of its invalid local triples. The
actual packed index has the exact valuation

    v_2 binom(2r,r) = popcount(r) = 3dN - V.                 (1)

Here B=2^d is the fixed cell radix, and 0<=V<=N. The original scale
q^3 requires valuation 3dN, so even one invalid triple is detected.
The proposed scale q^2 requires only 2dN, which every such word
satisfies. The gap is not repaired by the retained positive Pell
equations or the raw-input bridge: explicit formulas below extend
the same outer tuple to all their positive unknowns.

The [checker](../verification/explore_fixed_raw_scale_q2.py) and
[receipt](../verification/explore_fixed_raw_scale_q2.json) verify the
complete modified source and materialize exact outer tuples. The full
machine alphabet and astronomical complete Pell tuples are handled by
the mathematical construction, not numerically materialized. This is
a rejected optimization. The separate
[80-operation certificate](FIXED_RAW_UNIVERSAL_80_PROOF.md) obtains its
saving from a new native compiler while retaining the q^3 scale.

## 1. The exact proposed deletion

Keep all seven outer equations and all four input equations of the
81 proof. In its ten kernel equations replace only

    D0=q^3, X=w*D0, Yp=s*D0

by

    D0=q^2, X=w*D0, Yp=s*D0.                                (2)

All source unknowns, positivity requirements, fixed numerals and
equalities remain unchanged. The checker retains the complete acyclic
schedule, deleting exactly its `n2=Lbig*q` instruction and replacing
the operand `n2` by `Lbig`. It expands all 21 residuals, including the
correction of the auxiliary norm by the preceding norm residual.
Only residuals 7, 8, 10, 11 and 12 change, with zero-based indexing.

| Part | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Outer source with q^2 reused as scale |11|12|23|
| Same ten-equation Pell kernel |25|18|43|
| Same fixed-base raw-input bridge |7|7|14|
| **Rejected system** |**43**|**37**|**80**|

No side condition is added to this modified source.

## 2. Exact loss of one valuation unit per bad triple

Use the native compiler of the 81 proof. It has k genuine states,
clause radix A equal to the least power of two strictly larger than
max(2k,4), clause weights c_0,...,c_(3k-1), and clause mask mu.
The native inner radix R and outer radix B are

    R=the least power of two >= max((m+2)*sum(c_i),mu)+2,
    B=R^(k+m+1)=2^d.

The assumptions in this section are k>=4 and no zero-expression
padding clauses. In particular A>=16 and m>=k>=4. Section 4 proves
these assumptions for the actual full alphabet of a fixed machine.

Represent each genuine state a by the pure one-hot cell R^a, with
all dummy bits zero. The three local fields use coefficients

    D_s=sum_(i=0)^(k-1) c_(sk+i)*R^(k-1-i),   s=0,1,2.

At an actual one-hot triple (a_0,a_1,a_2), put

    fcell=sum_s D_s*R^(a_s),
    phi=sum_s c_(sk+a_s),     MF=mu*R^(k-1).

The coefficient of R^(k-1) in fcell is phi. All its other coefficients
are untested by MF. The following clause calculation is exact.

* Each of the three occupancy clauses has value 1 and mask A-2.
  Its sum is A-1, with no binary carry.
* Each of the two occupancy-equality clauses has value 2 and mask 1.
  Its sum is 3, with no binary carry.
* A forbidden-triple clause has weights 1,1,2 and mask 4. Its value
  v lies in {0,1,2,3,4}. For v<4, adding 4 makes no binary carry.
  For v=4, the addition 4+4=8 loses exactly one population bit.
  Because A>=16, this does not carry into the next clause digit.

Value 4 occurs exactly when all three states match that clause's
forbidden triple. Thus at most one forbidden clause loses a bit,
and it does so exactly when the actual triple is forbidden.

There is also no carry between inner radix-R coefficients. Indeed,
clause by clause, the mask is strictly less than four times the sum
of its weights. For occupancy this uses A<=4k and A-2<4k; for the
other clauses it is immediate. As there are no zero-expression
padding clauses, summing in radix A gives

    mu < 4*sum(c_i).

For a one-hot triple, the sum of all polynomial coefficients of
fcell is exactly sum(c_i), independently of the selected states.
Consequently

    sum(c_i)+mu < 5*sum(c_i)
                    <=(m+2)*sum(c_i)<=R-2.                (3)

All coefficients of fcell+MF are therefore below R. Its degree is
at most 2k-2<=k+m, so fcell+MF<B. Combining the two radix arguments,

    pop(fcell)+pop(MF)-pop(fcell+MF)
        = 1 if the actual triple is forbidden, otherwise 0. (4)

This is a statement about the actual native compiler, not an
independent abstract Boolean mask.

## 3. Complete positive outer tuples from arbitrary marked words

Choose N>=4, 1<=h<=N, 1<=x<N-1, and a state word a_0,...,a_(N-1)
with its only Start (state 1) at 0, its only End (state 0) at x,
and all other states numbered at least 2. No local consistency is
assumed. Pack cells c_i=R^(a_i) using base B and define

    C=sum_i c_i B^i,
    Cright=sum_i c_(i-1 mod N) B^i,
    Cnext=sum_i c_(i-h mod N) B^i,
    F=DC*C+DR*Cright+DY*Cnext,
    q=B^N, P=B^h, W=B^x, u=d*x,
    Jrep=(q-1)/(B-1), align=(P-1)/(B-1), v=q/P,
    Z=C-R-W, alpha=q-C-u,
    kR=(B*C-Cright)/(q-1), kY=(P*C-Cnext)/(q-1),
    z=DR*kR+DY*kY,
    Lambda=q^2, T=Z+qF, M=(MC+q*MF)*Jrep,
    r=(Lambda-T)*(Lambda-1)+M.                              (5)

The wraps kR,kY are positive integers: the cells shifted around the
cyclic boundary are all positive. Hence z>0 and the transport
equation is exact. By (3) each digit of F+MF*Jrep is below B, so
0<F<q-1. At least two non-marker cells remain, so Z>0.

The native bound C<=(B-2)Jrep gives q-C>=Jrep+1. Since x<N,
Jrep>=B^x=2^u>u, proving alpha>0. All twelve supplied outer
coordinates q,P,C,v,Jrep,align,F,alpha,z,Z,r,W are positive.
The seven outer equations, including the strengthened raw bound
C+alpha+u=q, hold exactly.

The native mask MC permits all unmarked genuine states, so
Z AND MC*Jrep=0. This makes the lower field sum Z+MC*Jrep<q.
Equation (3) also gives F+MF*Jrep<q. Therefore

    0<T<T+M<Lambda.

For the two radix-q fields and all N base-B cells, (4) gives

    pop(T)+pop(M)-pop(T+M)=V,       pop(M)=dN.               (6)

For Lambda=2^(2dN), expand (5) as

    r=(Lambda-T-1)*Lambda+(T+M).

The first coefficient is the 2dN-bit complement of T. The second
lies strictly below Lambda, so (6) proves (1). In particular

    pop(r)=3dN-V >= (3d-1)N >= 2dN,
    q^2 <= r < q^4,
    r is odd.                                             (7)

For the lower bound use Lambda-T>=1 and M>=1. For the upper bound
use T>=1 and M<Lambda. Finally Z is even, while MC and Jrep are
odd; qF is even, making r odd. The familiar central-binomial
identity v_2 binom(2r,r)=pop(r) now proves

    q^2 divides binom(2r,r)

for every such word, regardless of local consistency.

## 4. A fixed machine accepting no inputs

Use the fixed alphabet {0,1,2}, start q0, nonhalting q1 and absorbing
halt H. Every q0 transition goes to q1 and stays in place; on 1 it
writes 2, as required by the 81 normalization. Every q1 transition
stays in q1 without moving or changing the symbol. Thus no input
ever halts. This is an allowed semidecision machine for the empty
recursively enumerable set, with the required stationary first step.

Its full lifted alphabet contains the fixed Start and End windows
of the 81 proof, the constant headless blank window, and the constant
headless-1 window. These four windows are distinct and satisfy the
local window predicate, so the full alphabet has k>=4.

For every center window, at least one of the constant blank and
constant-1 windows fails horizontal overlap with it: their required
overlap strips differ at every payload. For each center there is
therefore at least one forbidden right neighbor, and every one of
the k choices of next window then makes a forbidden triple. There
are at least k^2 forbidden triples. Each contributes one population
bit to mu, so m>=k^2 and the compiler adds no zero-expression padding.
Thus Section 2 applies to the **full** fixed alphabet and constants.

Enumerate End and Start as states 0 and 1, and the blank window as
state 2. At x=1 choose

    N=4, h=1, (a_0,a_1,a_2,a_3)=(1,0,2,2).                (8)

The actual triples are (1,2,2), (0,1,1), (2,0,0), (2,2,2).
Only the last is allowed: the first and third fail horizontal overlap,
while (0,1,1) fails vertical overlap.
Hence V=3 and the same full compiler gives

    pop(r)=12d-3 >= 8d,       D0=q^2=2^(8d).              (9)

The original q^3 scale requires 12d and rejects this tuple. The
modified q^2 scale admits the full positive extension below. Since
the fixed machine accepts the empty set, x=1 is a false positive.

For a manageable exact numerical check, the checker also compiles
the induced relation on just the four explicitly displayed windows.
Its allowed triples are exactly (2,2,2) and (3,3,3), and its constants
have A=16, m=73, R=2^273 and B=2^21294. Tuple (8) then gives q=2^85176
and pop(r)=255525, while the weakened threshold is 170352. This
finite subalphabet is explicitly a numerical instance of the general
calculation; the full machine-alphabet construction above is not
silently replaced by that smaller alphabet.

## 5. A fresh positive Pell extension at the actual index

We prove the needed converse directly, since substituting q^2 for
q^3 does not justify importing the old range bound for the soundness
proof. Let r>=64 be odd, and let D0 be a power of two with
D0<=r^2 and D0 dividing binom(2r,r). These hypotheses hold for (5).
For Pell notation write

    chi_A(t)+psi_A(t)*sqrt(A^2-1)
        =(A+sqrt(A^2-1))^t.

Choose the main coordinates anew:

    J=2r+1, X=2^J,
    Y=sum_(j=0)^r binom(2r,r+j)*X^j,
    w=X/D0, s=Y/D0,
    a=Y*(X+1), A=a+2, Delta=A^2-1,
    Q=X*Y^2, E=X*Y, P0=2Q+1,
    c=psi_A(J), dmain=chi_A(J), k0=psi_P0(r+1),
    tau=(chi_P0(r+1)-1)/2,
    h0=(k0-r-1)/E,
    eta=c-k0*Y, zeta=k0-eta,
    gamma=(dmain-X-a*c)/(4a+3).                            (10)

Because D0<=r^2<X and both D0 and X are powers of two, w is a
positive integer. In Y, all nonconstant summands are multiples of X,
and its constant is binom(2r,r), so s is a positive integer too.

Here are explicit bounds establishing the potentially delicate
positive gaps. Put xi=(X+1)^(2r)/X^r. Its omitted binomial tail T0
satisfies

    0<T0=xi-Y <= binom(2r,r)/(X-1)<1/4.                    (11)

Indeed binom(2r,r)/4^r decreases with r, and for r>=2 is at most
3/8; use X=2*4^r. In particular Y=floor(xi) and xi/Y<2.
The elementary Pell bounds

    (2A-1)^(t-1) <= psi_A(t) < (2A)^(t-1), t>=2,

applied to the two pairs in (10) give

    c/k0 > xi*(1+3/(2a))^(2r)*(1+1/(2Q))^(-r) > xi,
    c/k0 < xi*(1+2/a)^(2r) < xi*(1+8r/a).

For the lower inequality, (1+3/(2a))^2>1+1/(2Q) follows from
6Q>a. For the upper one, 4r/a<1/2 follows immediately from
a>=X^r*(X+1), and the binomial/geometric bound
(1+t)^n<=1/(1-nt) applies. Thus

    0<c/k0-xi<16r/(X+1)<1/2,
    Y<c/k0<Y+3/4.                                        (12)

This proves eta>0 and zeta>0. P0 is odd, so tau is integral.
Since P0=1 modulo E, the Pell recurrence gives k0=r+1 modulo E;
strict growth gives h0>0. The Pell norm for P0 gives exactly

    X*Y^2*(X*Y^2+1)*k0^2=tau*(tau+1).

Reducing the main pair modulo 4a+3 gives
dmain-a*c=2^J=X modulo 4a+3. Moreover
dmain-a*c=2c-psi_A(J-1)>c>X, so gamma is a positive integer.
Every first norm, ratio, bound and congruence equation is now exact.

For the four remaining auxiliary coordinates and their signed
intermediate use the fresh fixed-minus construction from the
[odd-index proof](EXPLORATION_ODD_INDEX_PELL_SIGNS.md):

    maux=2cJ,
    f=chi_A(maux), Raux=Delta*psi_A(maux), i=Raux/c^2,
    yaux=psi_Raux(J), Uaux=chi_Raux(J)/Raux,
    j=(Uaux+J)/c, o=(Uaux+c)/f.                            (13)

The Pell addition identities make i and Uaux positive integers.
For example psi_A(cJ) is divisible by c^2, by applying the standard
quotient formula psi_A(cJ)=c*psi_(chi_A(J))(c) modulo c; doubling
preserves the divisibility. Since J=3 modulo 4, the same integer
polynomial identities used in the odd-index proof give

    Uaux=-J modulo c,       Uaux=-c modulo f.

Consequently j and o are positive integers. They satisfy exactly

    Uaux=j*c-(2r+1)=o*f-c,
    (i*c^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)*(Uaux^2-yaux^2)=1-yaux^2.

This supplies all sixteen remaining kernel coordinates at the actual
outer r. It does not reuse any unrelated moderate-index Pell tuple.

Finally set u=d*x, using the compiler bit width d, and choose the
five remaining input-bridge coordinates

    kappa=psi_A(u), muP=chi_A(u),
    delta=(kappa-u)/(a+1), phiP=c-kappa,
    rho=(muP-a*kappa-W)/(4a+3).                            (14)

Here 4<=u<q<J and W=B^x=2^u. Pell recurrence modulo a+1 gives
integral delta; growth gives delta>0 and phiP>0. The same exponent
congruence gives integral rho, and

    muP-a*kappa=2*kappa-psi_A(u-1)>kappa>=2A>W

makes it positive. All four input equations hold. Equations (5),
(10), (13) and (14) therefore specify a solution with all 33
existential unknowns strictly positive, at a false raw input.

## 6. Verification boundary

The checker expands every modified source equality and counts all
80 operations. It verifies every genuine triple for four finite
compiler tables, including the induced four-window machine table,
and checks both the clause-level loss and the full inner-field loss.
It checks 84 exact positive marked-word outer tuples, at several
lengths, marker offsets and cyclic strides, against all seven outer
equations and the exact valuation formula. It also checks the
unchanged input bridge on one of those same outer tuples, using a
moderate independent Pell parameter; that numerical check is not
claimed to be a full packed kernel solution.

Fresh exact main-Pell examples include r=65 and verify the positivity,
norms, congruences and ratio bounds used in (10). Fresh independent
odd auxiliary examples verify (13). The full existential extension
is proved in Section 5; full astronomical tuples and the full lifted
machine alphabet are not numerically enumerated. The 81 source and
its proof are unchanged.
