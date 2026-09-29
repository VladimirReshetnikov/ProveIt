# Restricting the auxiliary Pell root: a one-operation near miss

This exploration preserves all frozen certificates. Let A=a^2-1 and
C=c. The current E16 and signed parameter construction are

    f^2=1+A*(i*C^2)^2,
    G=1+(a+1)*(f^2-1),
    I=o*f-d.

With A,C^2 already available, computing E16 costs five operations,
G^2-1 costs three more using the shared value f^2-1, and forming I
costs two. These ten operations are the comparison baseline below.

## A valid restricted-root construction

One may restrict f to f=1+A*C^4*v and replace E16 by

    u^2=v*(A*C^4*v+2),  u,v>0.

Put Q=A*C^4 and T=Q*v. This equation gives

    (1+T)^2-1=A*C^4*u^2.

Thus f=1+T and the positive Pell denominator C^2*u satisfy exactly
the old E16, with its required C^2 divisibility. The same index
divisibility fact used by the signed Pell proof remains applicable.

Necessity is constructive. Choose a positive Pell solution

    F^2=1+A*(i*C^2)^2

as in the established construction. Set

    v=2*i^2,  u=2*i*F,  f=2*F^2-1=1+Q*v.

Then u^2=v*(Q*v+2), and f is the positive first coordinate at twice
the index of F. All newly introduced witnesses are positive.

Because this construction additionally ensures f=1 modulo C, the
signed parameter can use the linear expression

    G=1+(a+1)*(f-1)

instead of the original quadratic expression in f. Indeed

    G=-a modulo f,  G=1 modulo C,  G>1.

These are precisely the congruences needed by the signed index proof.
For necessity at the odd target index J=2r+1, take

    I=chi_G(J), H=psi_G(J),
    o=(I+d)/f, j=(H-J)/C.

The congruences make o,j integers; I+d>0 and H>J make them positive.
Thus the restricted construction and the smaller mathematical G are
valid positive-domain alternatives, independently of their circuit cost.

## Exact combined cost

The following five instructions replace E16, using Ac2=A*C^2 from E15:

    Q=Ac2*C^2
    T=Q*v
    Tplus2=T+2
    left=v*Tplus2
    right=u*u

Compare left=right. Then compute G^2-1 in three instructions:

    Gminus1=(a+1)*T
    Gplus1=Gminus1+2
    Gcoefficient=Gminus1*Gplus1

However, f=1+T must still be used in I=o*f-d. That requires three
instructions, whether written as

    f=T+1;  of=o*f;  I=of-d

or by distributing o*(T+1). The combined count is eleven, one above
the existing ten. Introducing a shifted o or d moves this additional
affine operation into another defining equation or norm; it does not
make it free.

## Why a tempting weakening loses the index hypothesis

The already available value Ac2 suggests using Q=A*C^2 and dropping
the factor C from the right-hand square:

    u^2=v*(A*C^2*v+2), f=1+A*C^2*v.

This would save a multiplication, but it only enforces a Pell denominator
of C*u, instead of C^2*u. The extra condition f=1 modulo A*C^2 does
not restore the necessary conclusion C divides the Pell index.

For example, if C=psi_a(J), choose f=chi_a(2J), v=2, u=2*chi_a(J).
The displayed weakened equation holds by the duplication identities,
but f has index 2J, which need not be divisible by C. Already a=2,
J=3 gives C=15 and index6. Thus the exact index-divisibility hypothesis
in the signed proof cannot be dropped on the strength of this congruence.
This is a counterexample to that proposed intermediate implication;
it is not a claim about a complete solution of the weakened universal
system.

No smaller certificate is claimed by this exploration.
