# Independent audit of the 26-unrestricted-integer extension

Reviewed INTEGER26_PROOF.md and build_integer26.py from
agent_integer_reductions. This supplements PRIMITIVE12_INDEPENDENT_REVIEW.md.
It is an ordinary mathematical review, not a new formal-assistant result.

## Domain and the zero-scale boundary

Seven positive coordinates J,F,alpha,z,s,eta,zeta are represented by
seven independent copies of Pos(x,y,z)=x^2+x+y^2+z^2+1. Pos is always
positive and represents every positive integer by Legendre's three-square
theorem applied to 4n-3. With five free coordinates h,i_raw,T,w_raw,t,
the count is 7*3+5=26. The substitutions i=2i_raw+1 and w=w_raw^2 give
i nonzero and w nonnegative.

The transport unit argument first yields Cword>=0 and R>0, including
w=0. Then a=XY+Y, H=4a+3, Delta=a^2+H, c, D, Q and d are positive.
In particular the weight formulas make sense before X>0 is established.

The changed tau coefficient at=2(c+X)+1 is essential at X=0: there
ell=0 and A=1, so the unweighted positive-domain separation argument
would not apply. The new coefficient gives
at*|tau|>=at>c+X and separates the two tau branches uniformly.

The signed-T and signed-i bounds are also valid. In particular
rf=(a+2)(i^2+1)c^2 exceeds sqrt(D), and
C2=c(T^2+1)+c+Rrf exceeds |v|+c/sqrt(D)+R sqrt(D).
For B=2QvZ=0, e=QZ^2-1 is nonzero; otherwise e^2-B^2D cannot vanish
because it would force the integer equality Q(vf+/-Z)^2=1.
These facts prove the nonzero lower bound on every y root and the same
hierarchical separation for all sixteen radical tuples, including any
temporarily nonreal y roots.

The Galois argument therefore restores rational gamma,tau,y,f at every
integer zero. The monic-square equations make tau,f integral; the
rational auxiliary Pell lemma makes y integral; the integer weighted
sum makes gamma integral. Only now is w=0 excluded: the restored main
norm reduces to 0=1 modulo H when X=0. This proof order avoids a circular
appeal to an integral main-root coordinate before it has been recovered.

The resulting tuple has exactly the seven positive guards, odd i,
square w and allowed signed coordinates required by 14-integer29.
Its signed soundness theorem applies directly. Completeness uses that
theorem's canonical odd-i/square-w witnesses; t is unrestricted, so
encoding the weighted sum imposes no further sign or parity condition.

## Rational auxiliary-root lemma

The separate proof using y=a/b in lowest terms is valid. From
rho^2 V^2-(rho^2-1)y^2=1, one gets b^2|(rho^2-1), and
D0=(rho^2-1)/b^2 is a positive nonsquare integer. Both (rho,b) and
(rho|V|,|a|) are positive norm-one solutions for D0. Fundamental-unit
classification and first-coordinate divisibility make the latter index
an odd multiple of the former; composition implies b divides |a|. Coprimality
then gives b=1. This agrees with the independent squarefree proof in
PRIMITIVE12_INDEPENDENT_REVIEW.md.

## Norm polynomial and product finalizer

The builder correctly replaces the positive construction's coefficient
of tau by at and its other two weights by ay,af before applying the same
gamma/y elimination and tau/f norms. No variable exponent, division,
or additional coordinate appears in the emitted integer circuit.

The product finalizer has an algebraic justification independent of
finite tests: the initial eliminated expression is K0^2-4d^2Gz0^2,
which is K0^2 modulo 4. Taking two multiplicative quadratic norms makes
the final P a square modulo 4. Hence 1+P cannot be the unit -1. A zero
of Nindex*Ntransport*(1+P)-1 has P=0 and correlated outer unit signs;
the restored signed-core theorem resolves those signs. This is stronger
and clearer than a statement conditional on a numerical mod-4 check.

## Independent exact-degree check

Under the 26-integer substitutions, deg(H)=12, deg(D)=66,
deg(Q)=90, deg(Z)=74, deg(e)=238, deg(ay)=196 and deg(af)=238.
The f component of z0 has coefficient degree 250; after squaring and
using f^2=D its leading constant term has degree 566. Multiplication
by d gives degree 656. The competing ay^2 e term has degree
2*(12+196)+238=654, so there is no leading cancellation.
The first norm therefore has degree 1312 with scalar leading term;
the tau norm has degree 2624 and the final f norm degree 5248.
The outer factors have degrees 13 and 4, so the product is degree 5265.
These are uniform nonzero leading forms for the authentic positive
fixed coefficient tuple, not just degrees observed on a test line.

## Coefficient transfer

The new pruned T4 binding is covered by PRUNED_T4_PROOF.md, section 6:
its native low-mask congruences, canonical R=3 modulo 4, independent
power-of-five padding and odd d=5^16 preserve the square-w/odd-i
canonical completeness construction. The whole four-port tuple must be
used. The alphabet and synchronization modifications do not change the
algebra of the signed-domain theorem.

No semantic gap was found in the reviewed reduction. The inherited
universal compiler and exact K215 logical endpoint remain explicit
mathematical dependencies.
