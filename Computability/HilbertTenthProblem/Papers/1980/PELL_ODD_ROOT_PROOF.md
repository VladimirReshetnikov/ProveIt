# Factoring the odd Pell root and halving its index modulus

This proves an independent 108-operation successor to the 109-operation
certificate. The executable companion is
`../verification/round11_1980_pell_certificate.py`. The change saves one
multiplication while preserving the number of positive unknowns and equations.
It can be combined with independent changes in the coefficient-code bounds.

## The two changed equations

Retain the notation

    N=n, R=r, U=w*N^2, Y=s*N^2, M=R*Y, A=a=M*(U+1),
    Q=U*M^2, P=2Q+1, K=k, C=c, J=2R+1.

The existing instruction `wsq=UM*rsn2` already computes Q. The previous
equations were

    ((2Q+1)^2-1)*K^2+1=tau_old^2,
    K=R+1+h_old*(2Q).

Replace them by

    tau*(tau+1)=Q*(Q+1)*K^2,
    K=R+1+h*Q,                                   (new)

where tau and h are positive integers. All other equations and positive
unknowns remain unchanged. The new tau represents half of the old root
minus one half; its domain is justified below. The new h initially imposes
a weaker index congruence, which will be proved to have the same solutions.
Neither the root transformation nor the halved modulus is treated as a
free arithmetic instruction: the certificate verifies the new polynomial
equations directly.

## Necessity and the forward witness map

Start with a solution of the preceding system. Its mathematical Pell
parameter P=2Q+1 is odd. Every chi coordinate chi_P(t) is then odd, since

    chi_P(0)=1, chi_P(1)=P,
    chi_P(t+1)=2P*chi_P(t)-chi_P(t-1)

preserves oddness. The positive norm equation has tau_old>1, so

    tau=(tau_old-1)/2>=1,
    h=2*h_old>0

are integers. Factoring the norm and dividing its identity by four gives
the first new equation; substitution gives the second. Thus every old
solution gives a new positive solution, preserving every other witness.

## Sufficiency: the weaker congruence still determines the index

The pre-Pell coding proof supplies R>=N>=8. In particular U,Y>=64,
M>=512, and Q>R+1. No parity of N or R is needed in this argument.

Set T=2*tau+1. The new norm implies the exact ordinary Pell equation

    T^2-(P^2-1)*K^2=1, T>1.

The unchanged positive interval says 0<C/K-Y<1. The new congruence has
h>=1 and Q>=1, so K>=R+2. Consequently

    C>Y*K>=64*(R+2)>J.

The unchanged E15--E17 therefore meet the hypotheses of the signed Pell
proof and give

    C=psi_A(J), d=chi_A(J).

The norm for T,K gives a positive index t with

    T=chi_P(t), K=psi_P(t).

The elementary congruence psi_P(t)=t modulo P-1=2Q also holds modulo Q.
Combining it with the new index equation and 0<R+1<Q gives

    t=R+1+vQ, v>=0.

If v>=1, elementary Pell growth gives

    C/K <= (2A)^(2R)/(2P-1)^(R+Q)
         <= (2A/(2P-1))^(2R) < 1/2.

The middle comparison uses Q>=R. For the last comparison,

    2A/(2P-1)=2M(U+1)/(4UM^2+1)<1/2,

which follows from U>=64 and M>=512. This contradicts C/K>Y>=64.
Therefore v=0 and

    K=psi_P(R+1), T=chi_P(R+1).                  (index)

Only the initial growth bounds, positive interval, signed Pell block,
and the new norm and congruence were used. In particular this recovery
does not assume the exponent relations or the final binomial rounding.

## Recovering the old positive witnesses

Apply the elementary Pell congruence to the exact index (index):

    K=R+1 modulo 2Q.

Since the new equation gives K-R-1=hQ, it follows that h is even.
It is a positive even integer, so

    h_old=h/2>0,
    tau_old=2*tau+1>0

restore the old equations. Every other witness is preserved. These are
the reverse maps to the necessity construction, and they establish exact
positive-domain equivalence.

This argument applies whenever the coding stage supplies R>=N>=8 and
the same positive interval and signed Pell equations. Thus it applies
both to the 109-operation encoding and to an independently justified
positive-coefficient bound that establishes the same preliminary facts.
All later exponent, decoding, and binomial conclusions can be taken from
the restored old system and its already proved hypotheses.

## Exact arithmetic saving

After Q is available, the old norm block used seven operations:

    X=2Q, Xplus2=X+2, Dp=X*Xplus2,
    K2=K*K, product=Dp*K2, left=product+1,
    right=tau_old*tau_old.

The new block uses six:

    Qplus1=Q+1, Dhalf=Q*Qplus1,
    K2=K*K, left=Dhalf*K2,
    tauplus1=tau+1, right=tau*tauplus1.

The old E11 product h_old*X is replaced by h*Q, at the same cost. Hence
X=2Q is not needed anywhere in the new schedule. The saving is one
multiplication in the complete certificate, not merely in an isolated
norm equation.

The resulting count is 108 instructions: 59 multiplications and 49
additions, with the same 33 positive unknowns and 21 free equality tests.
The seven existing numeral-construction instructions give 115 when fixed
numerals must be generated from 1. The mathematical parameter P=2Q+1
is never computed by a charged instruction or supplied as a free witness.

The verifier checks every new residual, both inherited triangular
corrections, every serialized primitive, and the exact polynomial maps

    E9_old(tau_old=2*tau+1)=4*E9_new,
    E11_new(h=2*h_old)=E11_old.

Its JSON retains the complete instruction and equality lists, declared
input domains, expanded residuals, numeral chain, and proof dependencies.
The arithmetic checks are exact; the positivity and evenness of the
reverse witness map are supplied by the index proof above.
