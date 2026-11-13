# Independent review: current-port free-main-root witness

This source and arithmetic review found no concrete error in the proposed
symbolic zero of the 61-row **probe**. In particular, the floor argument does
extend to the larger value of X selected by the transport congruence. The
conclusion is conditional on the displayed mathematical arguments and pinned
source identities; this is not a Lean proof, a direct evaluation of the huge
witness, or a zero of the original 65-row equation.

The checker reconstructs the exact 65-to-61 edit, checks row dependencies,
selected normalized factor nodes and liveness, and independently authenticates
all four raw/compressed port payloads. It verifies the rank and valuation
metadata and computes the transport coefficient with one combined modular
inverse, a different grouping from the author's formula. It also checks 36
small instances with X strictly larger than 2^R, including exact rational
intermediate floor bounds, and finite Pell/Chebyshev controls. These finite
experiments corroborate the formulas; they do not establish the general case.

## Larger-X floor argument

Write R=2N+1, X>=2^R and let Y be the stated binomial head. The same binomial
estimates work with an inequality throughout: X>144N and
X^N/2<Y<X^N. Set a=Y(X+1), M=XY², A=a+2, P=2M+1, and

    L=(2A−1)²/(2P),  U=(2A)²/(2P−1),  B0=(X+1)²/X.

The Pell estimates yield L^N/2 <= c/k <= U^N/2, while L>B0 and
U<B0+9/Y. Put H0=B0^N/2. The binomial tail gives
0<H0−Y<2^(2N)/(2X)<=1/4. For the other side, N(9/Y)/B0<1/2, so
(B0+9/Y)^(N−1)<2 B0^(N−1); also B0^(N−1)<2 X^(N−1). Consequently

    U^N/2 − H0 < 9N B0^(N−1)/Y < 36N/X < 1/4.

Thus Y<c/k<Y+1, giving positive integer eta=c−Yk and zeta=k−eta. None of
these inequalities substitutes X=2^R. The cited Pell estimates and binomial
bounds are mathematical inputs to this review, not independently checked Lean
lemmas.

## Actual ports, transport, and factors

For B=94517, beta=2^B−1, q=2^B, lo=MC, hi=MF−beta, the checker verifies
C=beta−lo is coprime to beta and the given rank satisfies R=3 mod 4,
popcount((R−1)/2)=3B+1, and R>3B+2. Independently taking

t = (F−K C) * (C 2^R)^(-1) mod beta

uses R mod B, and gives 0<t<beta with ((K+2^R t)C−F) divisible by beta.
The actual witness has w=2^R t and X=q w, so its transport quotient is a
positive natural. Since v2(X)>=B+R>3B+2, the central term of the binomial
head has valuation exactly 3B and all other terms have larger valuation;
therefore s=Y/q³ is a positive natural.

The first Pell norm gives the first factor 1 and, by its congruence modulo
E=XY, the graph's natural n. The second Pell norm gives the free-root main
factor 1. Raising that unit to c yields strong ordinate L divisible by c²,
so i=L/c² is positive and the strong factor is Delta. For the auxiliary
factor, R=3 mod 4 gives V=-c mod f² and V=-R mod c; the strong norm also
gives f²=1 mod c. Hence T=(V+c+f²R)/(f²c) is a positive integer and the
auxiliary factor is 1. Along with the transport factor 1, the five graph
factors give output 1*1*1*1*Delta−Delta=0. These statements concern the
symbolic definitions; the witness and output were not expanded.

Finally, the main Pell recurrence gives root−a c = 2^R mod H, whereas
0<X−2^R<H. Thus no gamma recovers the original main-root formula with
this same root and the other coordinates fixed. A different original
witness is not excluded. In particular, neither this audit nor the finite
receipt proves existential inequivalence, a consistency equivalence, or
anything about the rendered PDF.

Reproduce without creating intermediate files:

    timeout 35s python3 -I -S -B reviews/current14-free-main-root-current-zero-independent/check.py | cmp - reviews/current14-free-main-root-current-zero-independent/receipt.json

The checker runs under fixed memory and CPU limits. The SHA-256 input pins
cover the original packet and the specific proof-source and port files read;
they are not an authentication of a Lean provider closure or of PDF semantics.
No Lean, build, or staging operation was performed.
