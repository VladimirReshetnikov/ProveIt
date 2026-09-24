# The single e-bound: exact arithmetic, partial bootstrap, and refutation

This note investigates replacing only the first positive bound in the
published 90-operation binary product certificate by

    e+alpha=q, alpha>0.                             (1)

Its arithmetic cost is 89: 48 multiplications and 41 additions, with
the same 34 positive unknowns and 22 equality tests. Fixed numerals are
free. The candidate is now **refuted** by the full positive construction
in `EXPLORATION_BINARY_E_BOUND_COUNTEREXAMPLE.md`. The exact source
checker is `../verification/explore_round37_e_bound.py`; its receipt
has status `ARITHMETIC_PASS_BUT_REPRESENTATION_REFUTED`.

The canonical necessity construction remains available: its original
coding values satisfy e<q, so replace alpha by q-e>0 and preserve all
other witnesses. The partial sufficiency argument below precisely
identifies the positive first-index period exploited by the counterexample.

## 1. Bounds available without any Pell decoding

Use the published notation

    C=x+g, sigma=(e-ell)C^2>0,
    theta=H+b=B-2>b, q^2=1+(B-1)lambda,
    n=q^8, U=w*n^2, Y=s*n^2, E=UY,
    a=Y(U+1), A=a+2, D=A^2-1,
    Q=UY^2, P=2Q+1, J=2r+1.

Since C>0, the product equation forces e>ell. Thus (1) gives

    0<ell<e<q, n>=64, U,Y>=n^2, E>=n^4.

The fixed threshold and geometry still give B<=q^2 and 3L<=B<=n.
The middle code S2=ell+eq is less than q^2. Also

    Tplus=q^2(1+theta lambda)+ell(theta q^4-b)

is positive. Since 1+theta lambda=q^2-lambda<q^2 and theta<B<=q^2,

    Tplus<q^4+q^7<q^8=n.

The other packed value

    S=g+q^2(ell+eq)+q^4 sigma

is positive, but no upper bound for S, sigma, or C follows here.
Consequently the retained definition

    r=S(n^2-n)+Tplus(n^2-1)

implies r>=n^2-1, but the old upper bound r<2n^3 is unavailable.
In particular it is not legitimate to infer E>r from E>=n^4.

## 2. A sufficiently large main Pell index can still be proved

Classification of the unchanged main and first norms gives positive
indices p,t with

    c=psi_A(p), d=chi_A(p),
    k=psi_P(t), 2tau+1=chi_P(t).

The first norm is exactly the norm at P: its coefficient is
Q(Q+1)k^2=(E^2+U)(Yk)^2. The retained index equation is
k=r+1+hE, so k>1 and t>=2. Further,

    P-A=UY(2Y-1)-Y-1>0.

If p<=t, monotonicity in both index and integer Pell parameter gives
c=psi_A(p)<=psi_P(t)=k, contradicting c=Yk+eta>k. Hence p>=3.

The cases p=3,4,5 are impossible by the first exponent congruence
alone. Put M=4a+3=4A-5 and

    z_j=chi_A(j)-(A-2)psi_A(j).

The sequence has initial values z_0=1,z_1=2 and recurrence
z_(j+2)=2A*z_(j+1)-z_j. The sequence 2^j obeys the same recurrence
modulo M, since 4-4A+1=-M. Thus z_p=2^p modulo M. The retained
equation d=U+ac+gamma M gives

    U=2^p modulo M.

For any of p=3,4,5, both U and 2^p lie strictly between zero and M:
U<a<M, and 2^p<=32<M. Therefore U=2^p<=32, contrary to U>=4096.
This argument uses neither the exact main index nor an exponent
growth hypothesis. It establishes p>=6.

Now the explicit Pell polynomial gives

    psi_A(6)=32A^5-32A^3+6A,
    psi_A(6)-A(A^2-1)^2=31A^5-30A^3+5A>0.

Monotonicity proves c>A*D^2. Also 0<2p<c by elementary Pell growth
for A>=2,p>=6. Independently, the interval and first index equations
give

    c>Yk>Y(r+1)>2r+1=J>1.                         (2)

No bound r<E or a>J has been used.

## 3. Every generic auxiliary-index hypothesis is present

The retained relaxed equation is

    R^2=D(f^2-1), R=i*c^2>0.

The generic rank argument in `PELL_RELAXED_AUXILIARY_PROOF.md`
requires A>1, c=psi_A(p), and c>A*D^2. These have just been proved
independently. It therefore supplies a positive integer m with

    f=chi_A(m), p|m, c|m, R=D*psi_A(m).

In particular 0<2p<c<=m and R>=c^2>A>1. These are precisely the
parameter and comparison-index hypotheses of the generic argument
in Sections 3--4 of `HALF_PARAMETER_PELL_92_PROOF.md`.

For clarity, its remaining hypotheses are also unchanged: the new
norm is K(u^2-y_aux^2)=1-y_aux^2 with K=R^2, and its two linear
descriptions are u=J+jc=c+of. The odd polynomial identity modulo f
and modulo c gives J=+/-p modulo c. Inequality (2) and 0<p<c reduce
this to J=p or J+p=c. The latter is impossible because
psi_A(p)=p modulo 2 while J is odd. Thus

    p=J, c=psi_A(2r+1), d=chi_A(2r+1).              (3)

The original proofs' stronger preliminary p>=66 and a>J are not
being imported. Their generic rank and half-parameter arguments
use only the individually checked hypotheses listed above. No
parity of r, power-of-two radix, or coefficient decoding is used.

## 4. Negative first-index periods are excluded

Because P=1 modulo E, the usual Pell recurrence gives
psi_P(t)=t modulo E. Hence k=r+1+hE implies

    t=r+1+vE, v an integer.                        (4)

At this point r+1<E has not been proved, so v>=0 does not follow
from the congruence alone. It does follow from the interval.

Suppose t<=r. Standard Pell growth and (3) imply

    c/k >= (2A-1)^(2r)/(2P)^(r-1).

The relevant base inequality is strict:

    (2A-1)^2-2P
      =4Y^2(U^2+U+1)+12Y(U+1)+7>0.

Consequently c/k>(2A-1)^2>Y+1. This contradicts the positive
interval, which gives Y<c/k<Y+1 from c=Yk+eta,k=eta+zeta.
Therefore t>=r+1, and (4) has v>=0.

## 5. The remaining positive period and its full counterexample

To finish the published proof one would need to exclude v>=1.
The old exclusion used E>r: then t-1>=r+E>=2r and

    c/k < (2A)^(2r)/(2P-1)^(r+E)
        <= (2A/(2P-1))^(2r)<1,

contrary to c/k>Y. The base inequality still holds, since

    (2P-1)-4A=4Y[U(Y-1)-1]-7>0.

But the exponent comparison is unavailable without the old size
bound. In fact the same calculation only proves that v>=1 forces
r>E; it does not refute this remaining case.

The exact main index gives U=2^(2r+1) modulo M, but an integer
identity U=2^(2r+1) has not yet followed. The direct argument in
`EXPLORATION_PELL_AFTER_BINARY_PRODUCT.md` would need
xi=(U+1)^(2r)/U^r<Y+1, which has only been established after the
exact first index. Using it now would be circular.

Likewise n=q^8 cannot yet be treated as a power of two: that fact
is obtained from n^2|U after the first exponential is decoded.
No binary-mask inference or congruence specific to powers of two
is available solely from the equations proved above.

This isolated a precise remaining case: all necessary canonical
witnesses survive, the exact main index is recoverable, and any
extraneous first index must be r+1+vUY with v>=1 and r>UY.
Restoring the old extra scale
M_scale=(r+1)Y would rule out this case, but its multiplication
cancels the operation saved by (1).

The companion `EXPLORATION_BINARY_E_BOUND_COUNTEREXAMPLE.md` now
constructs this case for every admissible index and every positive
input. It keeps both codes canonical and below q, fixes U,Y,a at
a bounded seed, then lets g grow in a progression preserving the
first exponent congruence. Quadratic equidistribution supplies
positive extra periods v with the exact strict Pell interval.
Every remaining witness is positive and every source equation
holds, including both auxiliary norms and the fixed second index.
Thus an inconsistent circuit index accepts every positive input.

The arithmetic checker verifies all 89 primitive statements and
all 22 complete polynomial source residuals. The general
counterexample proof establishes the failed representation; no
giant Pell witness or finite bound on the density-selected
progression index is claimed by the receipt.
