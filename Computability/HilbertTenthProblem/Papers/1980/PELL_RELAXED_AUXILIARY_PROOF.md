# Recovering integrality after relaxing an auxiliary Pell norm

This note proves the 98-operation system checked by
`../verification/round28_1980_relaxed_auxiliary_certificate.py`.
Starting with the 99-operation composition, replace only E16 by

    (i*c^2)^2=D*(f^2-1),       D=A^2-1, A=a+4.       (1)

The former equation was f^2-1=D*(i*c^2)^2. The change is not an
unconditional equivalence between these individual equations: (1)
can have extra rational Pell solutions. The existing size and interval
hypotheses force exactly the integrality and index divisibility needed
by the doubled signed-index proof. That recovery is proved here.

All fixed numerals are free. The result has 54 multiplications and
44 additions, with the same 34 positive unknowns, 22 equality tests,
and supplied inputs (x,V,H,Tindex). The admissible index and all coding
equations remain those of `COMPOSED_99_PROOF.md`.

## A large main index is available before the auxiliary norm

Use the unchanged definitions

    U=w*n^2, Y=s*n^2, a=Y*(U+1), A=a+4,
    Q=UY^2, P=2Q+1, J=2r+1.

The coding bootstrap, before any Pell auxiliary norm is used, gives

    n>=64, n<=r<2n^3, U,Y>=n^2, UY>r+1.

The unchanged main norm and first triangular norm give positive
indices p and t such that

    d=chi_A(p),       c=psi_A(p),
    2tau+1=chi_P(t), k=psi_P(t).

The first index equation k=r+1+hUY and P=1 modulo UY imply
t=r+1 modulo UY. Since 0<r+1<UY and t>0, one has t>=r+1.
This conclusion does not require the exact main index.

Also P>A: explicitly

    P-A=UY(2Y-1)-Y-3>0

for the available U,Y>=n^2. If p<=r+1, Pell growth would give

    c<= (2A)^(p-1) <= (2A)^r
      < (2P-1)^r <= psi_P(t)=k,

contrary to c=kY+eta>k. Therefore

    p>=r+2>=66.                                    (2)

In particular, with D=A^2-1<A^2,

    c=psi_A(p)>A^6>A*D^2.                          (3)

For the first strict inequality use
psi_A(p)>=(2A-1)^(p-1), p-1>=6, and A>1.
Neither (1), the signed auxiliary norm, an exponential equation,
nor coefficient decoding has been used to establish (2)--(3).

## Two elementary Pell facts used below

For completeness, all assertions about a smaller Pell parameter can
be justified in the integer-coefficient quadratic ring; no assumption
about the full ring of algebraic integers is needed.

Let d_0>1 be squarefree and suppose an integer solution x,y>0 of
x^2-d_0*y^2=1 exists. Choose the least positive unit

    epsilon=F+y_0*sqrt(d_0)>1,
    F,y_0 positive integers, F^2-d_0*y_0^2=1.

It exists by minimizing the positive first coordinate F. Every
positive integer solution beta=x+y*sqrt(d_0)>1 is a power of epsilon.
Indeed, choose j>=0 with epsilon^j<=beta<epsilon^(j+1). The quotient
beta*epsilon^(-j) still has integer coefficients and norm one, because
epsilon^(-1)=F-y_0*sqrt(d_0). It lies in [1,epsilon). If it exceeded
one, its two coordinates would be positive integers (recover them
from z and z^(-1)), contradicting the minimality of epsilon. Thus the
quotient is one. Consequently every such solution has the form

    x=chi_F(j),       y=y_0*psi_F(j).

Secondly, for every integer F>1 the sequence y_j=psi_F(j) is strongly
divisible:

    gcd(y_u,y_v)=y_gcd(u,v).                         (4)

The Pell norm gives gcd(chi_F(j),psi_F(j))=1. The addition identity
y_(u+v)=chi_F(u)*y_v+y_u*chi_F(v) then gives
gcd(y_u,y_(u+v))=gcd(y_u,y_v). The Euclidean algorithm proves (4).
We will also use

    y_(2j)=2*chi_F(j)*y_j>2*y_j^2                  (5)

for j>0, since chi_F(j)>psi_F(j) when F>1.

## The relaxed norm forces an integral Pell solution at A

Set R_aux=i*c^2>0 and suppose (1) holds. Write

    D=d_0*s_0^2,

where d_0>1 is squarefree. This is possible with d_0>1 because A^2-1
is not a square. The known unit A+s_0*sqrt(d_0) supplies a positive
solution, so take the fundamental integer-coefficient unit from the
preceding argument. There is an integer e>=1 such that

    A=chi_F(e),       s_0=y_0*S,
    S=psi_F(e),       D=(F^2-1)*S^2.

Pell composition gives

    psi_F(ep)=S*c.                                (6)

The relaxed norm also yields an integer solution in the same field.
Indeed s_0^2|R_aux^2 implies s_0|R_aux, and squarefreeness gives
d_0|(R_aux/s_0). Put y=R_aux/(d_0*s_0). Then y is a positive integer
and f^2-d_0*y^2=1. Hence, for some n_aux>0,

    f=chi_F(n_aux),
    R_aux=(F^2-1)*S*psi_F(n_aux).                   (7)

Let T=(F^2-1)S, let g=gcd(n_aux,ep), and let

    h=gcd(psi_F(n_aux),psi_F(ep))=psi_F(g).

Since c^2|R_aux=T*psi_F(n_aux), equations (6)--(7) give

    gcd(c^2,T*psi_F(ep))=gcd(c^2,D*c)
                          =c*gcd(c,D)>=c.

The number on the left divides
gcd(T*psi_F(n_aux),T*psi_F(ep))=T*h. Consequently

    h>=c/T>=c/D,                                  (8)

because T=D/S<=D.

If g<ep, then g is a proper positive divisor of ep, so 2g<=ep.
By monotonicity, (5), and (6),

    2h^2<psi_F(2g)<=psi_F(ep)=S*c.

Moreover S<A, as D=(F^2-1)S^2 and F>=2. Thus h^2<A*c/2.
But (3) and (8) give h^2>=c^2/D^2>A*c, a contradiction.
Therefore

    ep | n_aux.

Write n_aux=e*m. Then p|m and Pell composition gives

    f=chi_A(m),       R_aux=D*psi_A(m).             (9)

This proves the required integrality in the original Pell sequence.
The use of c^2, together with the independently proved bound (3),
is what excludes the extra solutions of the individual relaxed norm.

## Recovering the required divisibility of the auxiliary index

It remains to prove c|m. Equation (9) and R_aux=i*c^2 give

    c^2 | D*psi_A(m).

Write m=p*k, using p|m from the rank argument. Expanding
(d+c*sqrt(D))^k and dividing its square-root coefficient by c gives

    psi_A(pk)/c = k*d^(k-1) (mod c).

Since gcd(d,c)=1, the displayed divisibility implies c|D*k.
On the other hand, the positive Pell binomial expansion modulo D
gives

    c=psi_A(p)=p*A^(p-1) (mod D).

Because gcd(A,D)=1,

    gcd(c,D)=gcd(p,D),

which divides p. Put g_0=gcd(c,D). Then c/g_0|k and g_0|p,
so c|pk=m. We have established

    f=chi_A(m),       p|m,       c|m,
    R_aux=D*psi_A(m).                             (10)

This is the precise conclusion needed by the doubled signed-index
argument. It does not claim c^2|psi_A(m), which is unnecessary here
and is not an automatic consequence of the relaxed norm.

## Sufficiency of the entire modified system

The signed auxiliary norm is unchanged as a source polynomial:

    v=of-d^2,
    K=D*(f^2-1)=R_aux^2,
    v*(v+1)=K*(K-1)*(J+jc)^2.

Thus the mathematical auxiliary base is G=2K-1>1. Reduction modulo f
still gives G=-chi_A(2) and 2v+1=-chi_A(2p). The proof of
`PELL_DOUBLED_INDEX_PROOF.md` applies with the index m from (10):
its comparison bound 0<2p<=c<=m follows from (2) and c|m.
Also K=R_aux^2 and R_aux=i*c^2 give G=-1 modulo c directly.
Taking the absolute value of 2v+1, the signed chi step-down yields

    t=+/-p (mod m),       J=+/-p (mod c).

The same parity argument excludes J+p=c and gives p=J. This use of
the doubled proof needs only (10) and the stated G congruence, not
the stronger old condition c^2|psi_A(m).

The exact first index, ratio bounds, common exponent U=4^J, fixed
Pell value Tindex=psi_4(L), second exponent q=B^L, and half-center
coefficient decoding now proceed exactly as in `COMPOSED_99_PROOF.md`.
Every hypothesis of those later arguments has been recovered before
it is used. This establishes sufficiency of the new system.

## Necessity and positive witnesses

Start with the canonical construction in `COMPOSED_99_PROOF.md`.
All coding and main Pell witnesses are unchanged. Its auxiliary
construction chooses the even index m=2cJ and

    f=chi_A(m),       i_old=psi_A(m)/c^2>0.

Keep f and set

    i_new=D*i_old>0.

Then R_aux=i_new*c^2=D*psi_A(m), so

    R_aux^2=D^2*psi_A(m)^2=D*(f^2-1).

The source value K=D*(f^2-1) is unchanged. Consequently the same
G, I, positive o and positive j from the doubled-index construction
still satisfy the signed norm. In particular f is odd, and the
positive integer o=(I+2d^2-1)/(2f) remains integral. All other
positive witnesses and all fixed index components are preserved.
This proves necessity.

## Exact operation saving and residual identity

Jointly, the previous E16 norm and K register required

    z=i*c^2, z2=z*z, AE=D*z2,
    f2=f*f, R16=AE+1, K=D*AE.                 (6 instructions)

The relaxed norm requires only

    z=i*c^2, K=z*z,
    f2=f*f, f2_minus_one=f2-1,
    R16=D*f2_minus_one.                      (5 instructions)

Compare K=R16. The same square K is used directly by the signed
norm. This saves one multiplication, so 99 becomes 98:

    54 multiplications + 44 additions = 98.

No new unknown or equality is introduced. For exact arithmetic, set

    F16=R_aux^2-D*(f^2-1),
    K_source=D*(f^2-1),       K_calc=R_aux^2.

Since K_source-K_calc=-F16, the new correction is

    F17_calc=F17_source
        -F16*(K_source+K_calc-1)*(J+jc)^2.

The checker verifies that every other source residual is unchanged,
checks all primitive instructions and input domains, and retains the
two other triangular corrections for the geometric and second
exponential equations. The recovered Pell integrality and index
divisibility are established by the argument above, independently
of those symbolic checks.
