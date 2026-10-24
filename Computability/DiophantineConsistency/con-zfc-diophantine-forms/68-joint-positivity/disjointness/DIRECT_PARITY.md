# A direct three-Pell odd-binomial compiler

Status: a mathematical replacement interface for the carry compiler. It is not
claimed to improve the final variable-count frontier. All variables below are
nonnegative integers. This file constructs an ordinary polynomial system, not
an exponential Diophantine condition.

## Statement

For positive integer inputs S,T put n=S+T. The following finite polynomial
system has a solution if and only if S & T = 0.

There are thirteen existential variables
  y,r,c,p,l,i,j,h,u0,u1,u2,u3,v.
Use the following polynomial abbreviations (not additional variables):

  x = 2(y+1), Y = 2r+1,
  M = 128(n+1)(x+1)(Y+1), A = M(x+1),
  C = n+1+c,
  K = T+1+p(M-1), L = S+1+l(Mx-1),
  D = (A^2-1)C^2+1,
  E = 2(i+1)DC^2,
  F = (A^2-1)E^2+1,
  G = A+F(F-A),
  H = n+1+2(j+1)C,
  I = (G^2-1)H^2+1.

The six residuals are

  R0 = u0^2 - [(2n+6)^3(2n+8)(y+1)^2+1],
  R1 = u1^2 - [(M^2-1)K^2+1],
  R2 = u2^2 - [((Mx)^2-1)L^2+1],
  R3 = u3^2 - DFI,
  R4 = H-C-Fh,
  R5 = K^2 L^2 -64(C-YKL)^2-v-1.

One ordinary integer-coefficient polynomial is P=sum_{a=0}^5 R_a^2.
Its variables are S,T and the thirteen witnesses listed above. Restrict the
inputs to S,T>0; all thirteen witnesses are nonnegative. No binomial,
exponentiation with variable exponent, factorial, division, bit operator or
hidden bounded quantifier occurs in P.

## Proof

Write psi_a(k) for the second coordinate of (a+sqrt(a^2-1))^k. This sequence
is used in the proof, not in the polynomial. Standard Pell facts used:

1. A nonnegative z with (a^2-1)z^2+1 square is psi_a(k) for some k>=0.
2. psi_a(k) = k modulo a-1.
3. (2a-1)^(k-1) <= psi_a(k) <= (2a)^(k-1) for k>=1.
4. (2a)^q(1-q/(2a)) <= psi_a(q+1) <= (2a)^q.
5. U(e,y)=(e+2)^3(e+4)(y+1)^2+1 square implies y>e^e,
   and arbitrarily large such y exist.
6. The Matijasevic--Robinson indexed-Pell certificate: C>=B>1 and D,F,G,H,I
   as above with H=B+2(j+1)C, DFI square and F dividing H-C is equivalent
   to C=psi_A(B), for suitable i,j. This is JSWW1976 Lemma3.8.

R0=0 implies x>128*2^n: here e=2n+4, n>=2 and
2(e^e+1)>128*2^n. R3=R4=0 and C>=n+1 give C=psi_A(n+1).
R1,R2 and rank congruences give
  K=psi_M(T+1+a(M-1)),
  L=psi_(Mx)(S+1+b(Mx-1))
for a,b>=0, since both target ranks lie strictly between zero and the
corresponding modulus. R5 implies |C/(KL)-Y|<1/8, so C/(KL)>7/8.

Neither a nor b can be positive. Indeed a positive a implies the exponent
in the lower bound for K is at least M-1. Since M-1>=2n+1 and
(2M-1)^2>2M(x+1)=2A,
  K >= (2M-1)^(2n+1) > 2(2A)^n >= 2C.
For b>0 the same lower bound applies to L because Mx>=M and its rank
is at least Mx. In either case C/(KL)<1/2, contradiction.

Thus K,L have their intended ranks. Set rho=(x+1)^n/x^S and epsilon=n/(2M).
The four estimates above show both C/[(2M)^n(x+1)^n] and
KL/[(2M)^n x^S] lie in [1-epsilon,1]. Consequently, for sigma=C/(KL),
  |rho-sigma| <= sigma*epsilon/(1-epsilon).
Since |sigma-Y|<1/8 and M=128(n+1)(x+1)(Y+1), this is less than1/128.
The binomial theorem gives rho=Q+f where Q is an integer congruent to
binomial(n,S) modulo x and 0<=f<2^n/x<1/128. Therefore
  |Y-Q| < 1/8+1/128+1/128 <1.
So Q=Y is odd. Because x is even, binomial(n,S) is odd. Lucas' binary
criterion implies S&T=0.

Conversely suppose S&T=0. Choose y with U(2n+4,y) square and set x as
above. The binomial quotient Q=floor((x+1)^n/x^S) is odd and positive;
put Y=Q and r=(Q-1)/2. Define M,A,C,K,L by the intended Pell coordinates.
Their standard congruences give nonnegative p,l, and C>=n+1 gives c.
MR supplies i,j with DFI square and F|H-C. Since H>C, the quotient h
is nonnegative. Choose u0,u1,u2,u3 as the nonnegative square roots.
Now |rho-Y|<1/128 and the relative Pell bound gives
  |sigma-rho| <= rho*epsilon/(1-epsilon) <1/128,
using rho<Y+1 and the definition of M. Hence |sigma-Y|<1/64<1/8.
Thus K^2L^2-64(C-YKL)^2 is a positive integer; choose v to be one less.
All residuals vanish. This proves the equivalence in elementary arithmetic
plus standard Pell facts, and hence in ZFC.

## Why this is not yet a new consistency-equation record

Substituting the packed source S(b,g),T(b,g) does not by itself recover the
required fact that b is a power of two. The previous Jones central-ratio
interface established that fact simultaneously through its exponential
congruence. A replacement must add and prove its own power-of-two guard.
Also the thirteen witnesses here include four square roots. Norm mergers
might remove some, but their integrality and sign proofs are not supplied
here. Neither omission is hidden in the stated standalone theorem.

The useful architecture change is denominator factorization: three Pell
coordinates implement the asymmetric binomial directly without constructing
R=L0(S+T+1)-S-1 or a huge central-binomial divisibility threshold. This is
not a claim of literature novelty; related three-coordinate ratios already
occur in the JSWW1976 prime construction. The new specialization here is
odd quotient detection with a rank-locking proximity inequality.

## Pinned primary implementation sources

ProveIt main9cca523d9f27ad39d52993f4065cbd7e58f8bdd4:
Computability/DiophantineConsistency/Lean/DiophantineConsistency/PellRepresentation.lean
Computability/DiophantineConsistency/Lean/DiophantineConsistency/FactorialRepresentation.lean

Additional audited sources bundled by earlier repository reports:
Diophantine/Paper1976/MR.lean (Lemma3.8, Pell rank congruence and estimates),
Diophantine/Paper1976/Ineq3.lean (Definition3.7 and growth square),
Diophantine/Paper1976/Theorem39.lean (three-coordinate ratio precedent).
Primary article: Jones, Sato, Wada, Wiens, American Mathematical Monthly83
(1976),449--464, https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Jonesh10.pdf .

No Lean/Rocq compilation is claimed for this new specialization.

## Twelve-witness specialization with built-in congruences

Delete h and R4, and replace the abbreviation H by

  H = C + F(n+1+(2j+1)C).

Keep all other abbreviations and residuals. The resulting five-equation
system (one sum-of-five-squares polynomial) has twelve witnesses.

Soundness: F-1=(A^2-1)E^2 is divisible by2C. Consequently H is congruent
to n+1 modulo2C, and to C modulo F. Also H>=n+1+2C. Thus it satisfies
the original MR certificate for some nonnegative integer j_old; all the
preceding soundness proof applies without alteration.

Completeness, carefully separating the two j's: start with a certificate
supplied by MR with H_old=n+1+2(j_old+1)C. It has I square, hence H_old
is a Pell second coordinate for base G. The Pell matrix
  [[G,G^2-1],[1,G]]
has determinant1, so its powers are periodic modulo 2CF. Increasing the
Pell index by multiples of a positive period preserves both coordinates
modulo2CF and yields arbitrarily large second coordinates H_new.
Choose H_new>=C+F(n+1+C). Then H_new-C=Fq with
q>=n+1+C. As F=1 modulo2C, q=n+1-C modulo2C, equivalently
q=n+1+C modulo2C. Hence q=n+1+(2j+1)C for j>=0. This H_new has exactly
the advertised polynomial form and still makes I square. D,F do not
change, so DFI remains square. The other residuals do not use H and
remain satisfied. This proves completeness without any unproved claim
about a particular canonical MR witness's size.

The total-degree upper bounds, treating S,T and each witness as degree1,
are368 for the thirteen-witness polynomial and504 for this twelve-witness
polynomial. The latter corrects the earlier draft value500. Its exact degree
is504: deg(M,A,C,D,E,F,G,H,I)=(3,4,1,10,13,34,68,36,208),
so deg(DFI)=252 and its square has degree504 with a nonzero leading term.
The independent audit gives the full degree argument and confirms the
13-witness degree368 companion.
