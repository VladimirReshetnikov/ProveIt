# Independent audit: direct asymmetric parity interface

## Verdict

The twelve-nonnegative-witness, five-equation representation of binary disjointness for **positive** inputs S,T is mathematically sound, using the stated Pell and Matijasevic–Robinson lemmas. There is one numerical correction: its sum-of-squares polynomial has total degree **504**, not 500, counting inputs and witnesses alike. The thirteen-witness alternative has degree 368 as claimed. This is a standalone interface, not a new Con(ZFC) equation and not a kernel-checked certificate. The underlying three-Pell approximation and rank-locking pattern already occur in JSWW1976; the claim should be specialization and congruence compression, not invention of the general technique.

## Primary-source hypotheses checked

I retrieved the original JSWW1976 article from https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Jonesh10.pdf and inspected printed page 456 (PDF page 8), Definition 3.7 and Lemma 3.8. The indexed-Pell lemma assumes A>1, B>1, C>0 and requires B<=C, the specified D,E,F,G,H,I definitions, DFI square, and integer divisibility F | H-C. The auxiliary parameter is set to zero here, so E=2(i+1)DC². The statement exactly matches the proposed thirteen-witness certificate. The local bundled file Diophantine/Paper1976/MR.lean gives the complete corresponding theorem and proof, not merely an axiom. No new compilation was performed.

Definition 3.7 and its accompanying growth assertion match R0 with parameter e=2n+4. Since S,T>0, n>=2, B=n+1>=3, and C=B+c>=B. All Pell bases exceed one. No zero-rank or zero-denominator exception remains.

## Soundness, with all quantitative steps made explicit

Let all five residuals of the twelve-witness system vanish. Here and below psi_a(k) denotes the Pell second coordinate, not an operation in the polynomial.

1. Growth: R0 gives y>e^e for e=2n+4. Since e>=8, e^e>=2^(3e)>2^(n+7); therefore x=2(y+1)>128·2^n. Also x is positive and even.

2. Recover the ordinary MR certificate. E is divisible by 2C, so F=1 mod 2C. With B=n+1 and H=C+F(B+(2j+1)C), one has H=B mod 2C and H=C mod F. Moreover H>=B+2C. Thus H=B+2(j_old+1)C for a nonnegative integer j_old. The MR lemma applies and yields C=psi_A(n+1).

3. Denominator ranks: R1 implies K=psi_M(k). The standard congruence psi_M(k)=k mod M-1 and K=T+1 mod M-1 imply k=T+1+a(M-1). The representative T+1 lies strictly between zero and M-1. Therefore a is nonnegative, not merely an arbitrary integer. Likewise L=psi_(Mx)(S+1+b(Mx-1)) with b>=0. K,L are positive.

4. Exclude excessive ranks. R5 gives |C/(KL)-Y|<1/8 and Y>=1, so C/(KL)>7/8. If a>=1, the exponent k-1 is at least M-1>=2n+1. Since M>x+1 and M>=2,

   (2M-1)^2>2M(x+1)=2A,

   K>2(2A)^n>=2C.

   The first strict inequality follows by taking the nth power of the displayed inequality and multiplying by 2M-1>2. This contradicts C/(KL)>7/8. If b>=1, its rank minus one is at least Mx-1>=2n+1 and its base is at least M; the same argument applies to L. Hence a=b=0.

5. Approximation constants: for a>1 and q>=0,

   (2a)^q(1-q/(2a)) <= psi_a(q+1) <= (2a)^q.

   This follows from the lower bound (2a-1)^q and Bernoulli's inequality. Set rho=(x+1)^n/x^S, sigma=C/(KL), epsilon=n/(2M). The normalized numerator lies in [1-epsilon,1]. The denominator is the product of two factors bounded below by 1-T/(2M) and 1-S/(2Mx); their product is at least 1-epsilon. Thus both normalized quantities lie in [1-epsilon,1], where 0<epsilon<1. Consequently

   |rho-sigma| <= sigma·epsilon/(1-epsilon).

   Because sigma<Y+1 and M=128(n+1)(x+1)(Y+1),

   (Y+1)n/(2M-n)<1/128.

   Indeed 2M>129n(Y+1)>=128n(Y+1)+n. This proves the claimed strict error bound without an implicit asymptotic argument.

6. Binomial split: expand (x+1)^n/x^S. Its terms with x-exponent >=0 sum to an integer Q satisfying Q=binomial(n,S) mod x. The remaining positive terms sum to f with 0<=f<2^n/x<1/128. Then

   |Y-Q|<1/8+1/128+1/128<1.

   Since Q and Y are integers, Q=Y. Y is odd and x even, so binomial(n,S) is odd. The elementary binary binomial-parity criterion gives S&T=0. That criterion can equally be proved by expanding (1+z)^n over F_2 and comparing the coefficient of z^S.

## Completeness and congruence compression

Assume S&T=0. Choose a growth-square y; such y exist arbitrarily far out. Let Q be the integer part above. Q is odd and positive: the expansion includes a positive constant binomial(n,S), since 0<S<n. Set Y=Q and r=(Q-1)/2. Define M,A and the intended Pell coordinates C,K,L. Their rank congruences give integral p,l. They are nonnegative because psi_a(k)>=k. Set c=C-(n+1)>=0.

The indexed-Pell lemma supplies an ordinary certificate with some i,j_old. For completeness of the compression, one must justify that D,F,I_old are individually squares, not infer this from DFI_old square alone. Here is the missing explicit argument, valid even if the certificate was not the canonical one:

- D divides E, and F=1 mod E; hence gcd(D,F)=1.
- G=A+F(F-A)=1 mod E; hence I_old=1 mod D and gcd(D,I_old)=1.
- G=A mod F and H_old=C mod F; hence I_old=D mod F and gcd(F,I_old)=1.

Thus D,F,I_old are pairwise coprime positive integers. Their product is square, so each is square. In particular H_old is a Pell second coordinate at base G>1.

Let N=2CF. The integer Pell matrix [[G,G²-1],[1,G]] has determinant 1. Its reduction modulo N belongs to the finite group GL_2(Z/NZ), so a positive power is the identity. Adding multiples of this period to the index of H_old preserves both Pell coordinates modulo N. The new second coordinates increase without bound. Choose H_new>=C+F(B+C). Then H_new-C=Fq with q>=B+C. As H_new=B mod 2C and F=1 mod 2C,

   q=B-C=B+C mod 2C.

Hence q=B+(2j+1)C for some nonnegative j, exactly the new H definition. I_new is a Pell square. D,F stay fixed squares; therefore DFI_new stays square. This proves the compression without assuming any unproved canonical-witness bound.

The ratio estimate also works in the reverse direction:

   |sigma-rho| <= rho·epsilon/(1-epsilon)<1/128,

because rho<Q+1=Y+1. Together with rho-Y<1/128 this gives |sigma-Y|<1/64. Thus (KL)²-64(C-YKL)² is a positive integer, and setting v equal to that integer minus one completes R5. Every witness has the required nonnegative domain.

## Degree correction

The straight-line degrees are M=3, A=4, C=1, D=10, E=13, F=34, G=68. For the compressed H, degree(H)=36 and degree(I)=208. Thus degree(DFI)=252 and degree(R3²)=504. The top-degree term does not cancel: it is the nonzero leading part of the product DFI; no other summand of R3 has that degree. The other residual squares have lower degree. Therefore 504 is exact, not merely a safe upper bound. The analogous uncompressed H has degree2, I degree140, giving 368.

## Independent checks and limitations

check_independent.py was authored for this audit and executed independently. It uses integer Pell-pair multiplication rather than the proposal's recurrence implementation. All 64 input pairs with 1<=S,T<=8 pass exact rational growth, parity, congruence, ratio and rank-bound checks. Another 1800 small congruence-compression cases pass. Exact degree propagation reports 504 and368. These finite checks do not establish the universal theorem; the proof above does. They do not materialize enormous complete MR witnesses.

Nothing here shows that substituting packed source words forces the source radix to be a power of two. That remains an explicit integration obligation. A report should not count this component as an improved complete consistency equation before that obligation and the resulting full resource metrics are proved.
