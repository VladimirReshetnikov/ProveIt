# Fourteen unrestricted integers by combining the Jones constructions

## 0. Statement, scope, and provenance

Put L=5^32. This package gives three explicit integer polynomials, with all intermediate names below denoting polynomial abbreviations and NOT additional unknowns:

- F14: 14 unrestricted integer unknowns; exact total degree 813056 L+2752; 1524 binary operations.
- F16: 16 unrestricted integer unknowns; exact total degree 406528 L+10008; 1537 binary operations.
- F15, retained as a derivation bridge: 15 unrestricted integer unknowns; degree 813056 L+4184; 1530 operations. F14 dominates F15 on these three measures.

For each, ordinary mathematics formalizable in ZFC proves that the polynomial has an integer zero if and only if there is a finite ZFC refutation. Consequently ZFC proves its integer unsolvability equivalent to Con(ZFC). This is an equivalence, not a consistency proof. We claim neither an optimal variable count nor a new end-to-end Lean/Rocq certificate.

The pinned repository is VladimirReshetnikov/ProveIt at 8c6eec9d19ef80538c8e61ff6e0180040583446a. This construction combines source30's 31-positive-variable quartic and complete compact943 coefficient tuple, source27's fast Jones digit evaluation, and source29's signed17 square-stack/intersective finalizer. New steps are the j-guard deletion, a signed linear root-separation weight, cofinal power-of-two specialization, and the square-w specialization of the actual ratio-completeness witness. These are application-specific ordinary proofs; no global-priority claim is made for the constituent number-theoretic devices.

The detailed source29 proof is included as upstream/29-simpler-forms__signed17__SIGNED17_PROOF.md. Exact source-level evidence for the two restricted-completeness statements is in upstream/Master3.lean, NineReduce.lean, NineRatio.lean, and Ratio.lean. Reading these files is not rebuilding their proof-assistant dependency graph.

## 1. Fixed coefficient recipe and the imported interface

Use exactly the entire source30 compact943 tuple (beta,K0,MC,MF), with native radix 2^(5^10), K0=DC+B_native DR, and SHIFTED MF=MF_native+B_native−1. The authoritative binding is ../coefficients/COMPACT_COEFFICIENT_BINDING.json, copied also under upstream. No ports from different tuples are spliced.

The literal quartic system upstream/quartic31.json has 31 positive unknowns and 22 quadratic residuals r_j. Set P31(x,n)=sum_j r_j(n+1)^2, independent of its dummy x. Source30's exact G-register elimination proves its positive solvability equivalent to the native compiler's blank K215 language. P31 is normalized: at n=0 its fifth residual equals 1; its degree is four. Together with the imported native-compiler and K215 calibration this gives the finite-refutation endpoint.

Let nu=31, L=5^32. If p_alpha is the coefficient of the 32-coordinate exponent vector alpha in P31, define c_alpha=(4−|alpha|)! product(alpha_j!) p_alpha, for |alpha|≤4. The exact 402 nonzero symbolic records in upstream/COMPACT_CONSTANTS.json, with unlisted coefficients zero, specify every c_alpha as a polynomial in the four fixed ports. Put

s_index=45933757,
z=2^s_index,
e(T)=sum_{|alpha|≤4}(z+c_alpha) T^(L−sum_j alpha_j 5^j),
y=e(2z).

The source30 finite certificate upstream/INDEX_BOUND_CERTIFICATE.json proves |c_alpha|+1<z for all records; it covers the zero records trivially. The exponent positions are distinct and all digits lie between 1 and 2z−1. Thus y<(2z)^(L+1), and y≥2z. All constants are explicit bounded recipes, never quantified parameters. The coefficient and normalization conditions are precisely the admissible Jones index conditions.

For F14 and F15 add the fixed positive constant

kappa=(45933758)(L+1)+1,
a=2^kappa.

Both 45933758 and L+1 are even, so kappa is odd. The displayed bound on y gives a>y. The base scale a is NOT materialized; its binary length is kappa+1, an enormous explicit integer. Fixed coefficients are free leaves only in the arithmetic-operation convention, not free in storage or bit complexity. The original y leaf is unnecessary in F14/F15 after base substitution, but its recipe still identifies the original admissible index and the proof of a>y.

### Exact Jones core

The eight integer coordinates are epsilon,g,h,s,w,phi,i,j. For F16 set b=y+1+epsilon and omega=w. For F15 set b=a epsilon^2 and omega=w. For F14 set b=a epsilon^2 and omega=w^2. (The exported variable named w is the square root parameter in F14.) Define

B=b^5; q=B^L; ell=sum_{r=1}^31 B^(5^r);
lambda=sum_{r=0}^{4L−1} B^r; theta=B−2z;
N=q^16; Gcap=32 b B^(5^31).

R=[g+e(B)q^3+ell q^5+(2(e(B)−z lambda)(1+B+g)^4+lambda B+lambda Bq^4)q^7](N^2−N)
  +[q^3−b ell+ell+theta lambda q^3+(B−2)q^8](N^2−1).

U=N^2 omega; Y=N^2 s; M=RY; P=2M^2 U;
K=R+1+h(P−1); A=M(U+1); B1=2R+1; W1=b omega;
C=B1+W1+phi; J=4A−5; Q=3W1 C−2(W1^2−1);
D=(A^2−1)C^2+1; E=iJDC^2; F=(A^2−1)E^2+1;
G1=A+F(CD+1−A); H=B1+jC; I=(G1^2−1)H^2+1;
a0=(P^2−1)K^2+1; a1=DFI;
m=K^2 Gcap−4(C−KY)^2 Gcap−8gK^2;
D0=JF; T0=QF+J(H−C).

The imported ratio reduction, with epsilon,phi≥0 and g,h,s,omega,i,j≥1, says

a0,a1 are integer squares, D0 divides T0, and m>0                       (JR)

is existentially equivalent to a positive solution of P31. Note that this is a particular structured Jones ratio interface, not an arbitrary nine-variable polynomial. No claim is made that one can apply the signed reduction to an unspecified nine-variable representation.

## 2. Three Jones coordinates need no positivity guards

For every integer assignment D0 is nonzero. Indeed J=4A−5 cannot vanish. If F=0, then (A^2−1)E^2=−1 gives A=0 and E=±1; but J=−5 and E=iJDC^2 is divisible by 5, a contradiction.

If i is nonzero, changing i to |i| does not change any of a0,a1,D0,T0,m: E is the only nonsquared occurrence of i, and all consumers of E in these five expressions use E^2. Thus i positivity can be replaced by i≠0.

### Recovering h positivity (source29, with the unused j guard removed)

Assume b>y, g,s,omega≥1, phi≥0, a0 square, and m>0. Then b≥2, B>2z, e(B)>0, Gcap>0. Positivity of m first gives K≠0,
g<Gcap/8=4b B^(5^31), and 4(C−KY)^2<K^2.
Write t=5^31. Since b≤B and B>5,
1+B+g < 1+B+4B^(t+1) ≤5B^(t+1)<B^(t+2)≤B^(5t)=q.
Also ell<B^(t+1), hence b ell<q<q^3. The only potentially negative part of the first R bracket is absorbed by
lambda Bq^4−2z lambda(1+B+g)^4>0.
All its other terms are nonnegative and g>0; the second bracket is positive. Thus R≥N^2−N≥2. Consequently U,Y≥1, C=2R+1+b omega+phi>0, and P≥2R^2>R+2.

The displayed margin inequality rules out K≤0: if K<0 then |C−KY|=C+|K|Y>|K|. Hence K>0. If h≤0, then 1≤K≤R+1<P. K=1 would give P−1 dividing R, impossible. For 2≤K<P,
(PK−1)^2 < (P^2−1)K^2+1 < (PK)^2,
because the two differences are K(2P−K)>0 and K^2−1>0. This contradicts a0 being a square. Therefore h≥1. None of this uses j positivity.

### New lemma: deleting the j guard by a Pell orbit

Under the preceding hypotheses and (JR), A=RY(U+1)≥4, C≥1, D≥A^2, F>0, and G1>A>1; the latter follows from CD+1−A>0. F≡1 modulo both D and J. Since gcd(J,F)=1, the divisibility condition gives H≡C modulo F. Consequently

G1≡1 (mod D), I≡1 (mod D);
G1≡A (mod F), I≡(A^2−1)C^2+1=D (mod F).

It follows that D,F,I are pairwise coprime positive integers. Their product a1 is a square, hence each is a square.

Set d=G1^2−1>0, a nonsquare, and x=+sqrt(I). Then x^2−dH^2=1, and alpha=x+H sqrt(d)>0 even if H<0. The integer unit eta=G1+sqrt(d)>1 has norm 1. Its matrix [[G1,d],[1,G1]] has determinant 1, so a positive power is the identity modulo the positive integer CF. Write eta^k≡1 modulo CF. For n tending to infinity, the coefficients x_n,H_n of alpha eta^(kn) are integers satisfying

x_n^2−dH_n^2=1, H_n≡H (mod CF), H_n→+infinity.

Choose H_n>B1. Then j_n=(H_n−B1)/C is a positive integer since H≡B1 modulo C. Replacing j by j_n preserves all expressions except H,I,a1,T0, preserves a1 being a square, and changes T0 by J(H_n−H), a multiple of JF. Thus (JR) is unchanged existentially if j is unrestricted. This orbit changes no fixed coefficient or earlier witness and imposes no new unknown in the final polynomial.

## 3. Two cofinal restrictions in the completeness proof

### Cofinal bases, hence F15

The literal proof USys_of_mem in upstream/Master3.lean, lines303–510, starts from a quartic witness vector n and chooses an exponent k=x y+sum_j n_j+1. The equality to that particular bound is used only to establish k≥1, xy<2^k, and n_j<2^k. After those inequalities, all digits and all remaining quantities are defined as functions of b=2^k and the chosen witness; the equality fixing k is never used again. Thus the same proof works for EVERY exponent k at least that bound. In particular one may choose an arbitrarily large k with any prescribed parity.

The subsequent proof NineReduce.reduced_of_mem transports that same chosen b, rather than choosing a new one. Its ceiling parameter is recovered as epsilon_old=b−xy−1. NineRatio.ratio_complete also keeps b unchanged. At x=1 choose k=kappa+2r large enough. Then epsilon=2^r is nonzero and b=a epsilon^2. Conversely, any nonzero integer epsilon gives b≥a>y, so the old nonnegative ceiling coordinate epsilon_old=b−y−1 is legitimate. This proves both directions of the new base specialization. Merely substituting an arbitrary square for the old epsilon would NOT be justified; the construction instead restricts the POWER-OF-TWO BASE via a cofinal family.

### Square omega from the actual canonical witness, hence F14

In upstream/Ratio.lean, exists_B25core lines434–442, the input b=2^k is retained and the positive witness is explicitly

omega=2^(2R+1−k), U=N^2 omega.

This is NOT a statement that U=2^R. The source proves k<2R+1 from k<2^k=b≤R, so the natural subtraction in its exponent does not truncate. For our odd k, 2R+1−k is a positive even integer. Therefore the canonical omega is a positive square. The subsequent NineRatio.ratio_complete lines270–279 retains exactly this omega; its product-Pell step supplies i,j and changes phi but not omega. Choose w=2^((2R+1−k)/2). This proves completeness with omega=w^2 and w≠0. Soundness is immediate because a nonzero integer w gives omega≥1.

Thus for F14 the only inequality guards still needed are

g≥1, s≥1, phi≥0, m>0,

along with nonvanishing epsilon,w,i. For F16 the guards are epsilon≥0,g≥1,s≥1,w≥1,phi≥0,m>0, with i≠0. The h and j witnesses remain unrestricted and are recovered by the lemmas above. There is no claim that the canonical s is a square: its defining floor of a rational square does not imply that.

## 4. A single square test for all remaining inequalities

For F14 let (d1,d2,d3,d4)=(3g−1,3s−1,3phi+2,3m−1), introduce integer z1,z2,z3,z4, and set

C0=1; Bj=1+4dj C_(j−1)^2 zj^2; Cj=C_(j−1) Bj; C*=C4.

For F16 use the six discriminants (3epsilon+2,3g−1,3s−1,3w−1,3phi+2,3m−1), six z variables, and C*=C6. For F15 delete only the epsilon discriminant from that list. In every case each Bj≡1 modulo4 and gcd(Bj,C_(j−1))=1, so all factors are nonzero and pairwise coprime.

If the z variables are nonzero and C* is a square, unique factorization makes each |Bj| a square. A negative square cannot be 1 modulo4; hence each Bj is a positive square. Since C_(j−1) and zj are nonzero, dj<0 would give Bj≤−3. Also dj≡2 modulo3, so dj cannot be zero. Thus dj>0, exactly the required inequalities.

Conversely, every positive dj≡2 modulo3 is nonsquare. Pell's equation u^2−dj v^2=1 has a nontrivial positive solution with v divisible by any prescribed positive modulus: take a power of an integer norm-one Pell unit that is the identity modulo that modulus. In succession choose v divisible by 2|C_(j−1)| and let zj=v/(2C_(j−1)), a nonzero integer. Then Bj=u^2. This inductively makes C* a square. This is source29's coprime stack, now with fewer guards. At EVERY integer assignment C*≡1 modulo4, not just at successful witnesses.

## 5. One divisibility test also enforces nonvanishing

Let Pi(t)=(t^3−t−1)(t^2+23). It has no rational root: the cubic's only possible rational roots ±1 fail, and the quadratic has none. It has a root modulo every nonzero integer. Here is a complete prime-power proof. For an odd prime p≠23, either the cubic has a simple root (its discriminant is −23), or it is irreducible. In the latter case Frobenius is a three-cycle, so the Vandermonde product of its three roots is Frobenius-fixed and gives a nonzero square root of −23 in F_p. Thus the quadratic has a simple root. Hensel lifting handles both. At p=23, the cubic has the simple root3. At p=2, −23≡1 modulo8; an odd solution modulo2^e, e≥3, can be replaced by t or t+2^(e−1) to solve modulo2^(e+1), since the two squares differ by 2^e modulo2^(e+1). The Chinese remainder theorem now applies.

For D≠0 define

Rcal(D,T,v)=((T+Dv)^3−D^2(T+Dv)−D^3)((T+Dv)^2+23D^2).

It equals D^5 Pi(T/D+v), so it is never zero for integer v. Moreover, for any integer Z,

D divides T and Z≠0 iff there exists an integer v such that ZD^5 divides Rcal(D,T,v).

The forward direction writes T=Dq and chooses q+v to be a root of Pi modulo |Z|. Conversely Z=0 would force Rcal=0. If D does not divide T, choose a prime with alpha=v_p(D)>beta=v_p(T). For r=T+Dv one has v_p(r)=beta. The unique least valuations in the cubic and quadratic factors are respectively 3beta and2beta, so v_p(Rcal)=5beta<5alpha, impossible. These universal arguments are inherited from source29.

For F14 put Z=epsilon w i z1 z2 z3 z4. For F16 put Z=i z1...z6; for F15 put Z=epsilon i z1...z5. Set S=ZD0^5 and T=Rcal(D0,T0,v). Thus T is never zero, and S divides T encodes exactly the old divisibility together with every required nonzero condition.

## 6. The explicit final polynomial and its exact elimination property

Define the signed weights and the polynomial abbreviations

w1=C*+1; w2=w1(P^2+K^2+2); X=Su−T;
A0=S^2 C*; A1=S^2 w1^2 a0; A2=S^2 w2^2 a1;
V=X^2+A2−A0−A1; W=V^2+4X^2 A2−4A0 A1;
F=W^2−16V^2 X^2 A2.

For F14 the complete list of unknowns is

(epsilon,g,h,s,w,phi,i,j,z1,z2,z3,z4,v,u) in Z^14.

The export names v,u as residue,normroot. Every other symbol, including S,T,R,P and the compiler ports, is an abbreviation or a FIXED integer. The delivered division-free DAG generated/signed14.json expands all fixed powers into binary arithmetic gates. generated/signed16.json is the lower-degree alternative; generated/signed15.json is the dominated intermediate.

### Signed linear separation lemma

For every integer C*≡1 modulo4, |C*+1|>sqrt(|C*|). If C*≥1 this follows from (C*+1)^2−C*>0. Otherwise C*=−t with t≥3 and (t−1)^2−t=t^2−3t+1>0. Thus w1 is never zero. For all real P,K,

sqrt(|(P^2−1)K^2+1|)≤P^2+K^2+1.

Indeed the radicand's absolute value is at most (P^2+1)K^2+1 and the difference from (P^2+K^2+1)^2 is P^4+K^4+P^2K^2+2P^2+K^2≥0. Therefore

|w1|>sqrt(|C*|),
|w2|>sqrt(|C*|)+|w1|sqrt(|a0|).

Unlike source29's 1+C*^2, our linear weight is allowed to be negative; the proof always uses absolute weights. This is the degree-saving step.

### Exact three-root norm

For complex roots r0^2=C*,r1^2=a0,r2^2=a1, direct multiplication gives

F=product_{sigma in {−1,+1}^3}(X−S(sigma0 r0+sigma1 w1 r1+sigma2 w2 r2)).

If S=0 then X=−T, all A_j=0, and F=T^8≠0. At any zero S≠0, and a signed sum of the three roots is rational, equal to u−T/S. The separation inequalities make distinct sign choices on nonzero roots yield distinct sums: at the largest changed coordinate its weighted absolute value is at least its weight and strictly exceeds the sum of the earlier absolute values. This holds also for imaginary roots. The multiquadratic field generated by the roots is a finite Galois extension of Q. Since the encoded sum is rational, every automorphism fixes that sum; separation forces it to fix each root separately. Hence all roots are rational and therefore integers. Thus C*,a0,a1 are nonnegative integer squares, and T/S is an integer.

Conversely, if S≠0, S divides T, and the three radicands are integer squares, take integer roots and put u=T/S+r0+w1r1+w2r2. One factor vanishes. We have therefore proved, for fixed other coordinates,

exists u:F=0 iff S≠0, S divides T, and C*,a0,a1 are squares.

This covers zero radicands, repeated square classes, negative candidate radicands, and negative weights; no positivity assumption is smuggled into the finalizer.

## 7. Completion of the equivalence

A zero of F14 gives the three square conditions, S≠0 and S|T. The homogeneous merger gives D0|T0 and all nonzero conditions epsilon,w,i,zj. The stack gives g,s≥1, phi≥0 and m>0. Because b=a epsilon^2>y and omega=w^2≥1, the h lemma applies. Replace i by |i|, then apply the j Pell orbit. These changes preserve the required source ratio conditions; the old ceiling coordinate b−y−1 is nonnegative. Thus the original Jones interface has a natural witness, so P31 has a positive witness and there is a finite ZFC refutation.

Conversely a finite refutation supplies a quartic witness through the imported compiler endpoint. The cofinal-base proof selects an exponent k=kappa+2r large enough. Its canonical ratio witness has square omega because k is odd. Take epsilon=2^r and the positive square root w of omega. All four discriminants are positive. The Pell stack supplies nonzero z variables and square C*. The intersective merger supplies v, and the norm lemma supplies u. Thus F14 has an integer zero. The same argument with the unmodified base and omega proves F16; dropping only the base guard proves F15. Negation gives the stated consistency equivalences.

## 8. Evaluation, degree, and reproducible evidence

The fast digit circuit uses t_j=B^(5^j), v_j=B^(5^31−5^j), shared fifth powers, a complete homogeneous polynomial h4 for the all-zero-coefficient background, and a fixed multivariate Horner ordering for the 402 sparse corrections. The identities are

sum_{|alpha|≤4} B^(L−expo(alpha))
 = B^(5^31) h4(B^(5^31), B^(5^31−1),...,1),
lambda=product_{j=0}^31 (1+t_j+t_j^2+t_j^3+t_j^4) (1+q)(1+q^2).

Each five-term factor is evaluated as 1+(t_j^2+t_j)(t_j^2+1), reusing t_j^2. Identical coefficient recipes are aliased and literal coefficient recipes are folded; no coefficients are silently changed. These are polynomial identities valid for every signed argument. The builder further removes six unnecessary source coordinate shifts and evaluates guard factors as 1+(12x+8)(Cz)^2 or1+(12x−4)(Cz)^2.

For F14 the dominant degrees, in units of L, are:

R=470L; P=1900L+4; K=1900L+5;
a0=7600L+18; a1=49280L+98; m=4442L+14;
C*=4442L+133; S=68750L+152; T=68750L+150;
w2=8242L+143; A2=203264L+688.

A2 has strictly larger degree than X^2,A0,A1. Thus V,W,F have successive leading terms A2,A2^2,A2^4. Nonzero leading coefficients prove degree F14=813056L+2752. For F16 the analogous values give C*=2221L+1102, S=34375L+107, w2=4121L+1110, A2=101632L+2502 and degree406528L+10008. The source core leading term is unaffected by the fixed digit coefficients; for F14 it includes a nonzero power of the positive fixed a. The generator independently propagates a symbolic diagonal leading term modulo1000003; its nonzero scalar times a power of a certifies exactness at the actual specialization, not just a structural upper bound.

Run python3 build_signed.py and python3 check_signed.py from this directory, or use the enclosing package's replay driver. The checker uses the actual source30 coefficient bytes in the sibling coefficients directory. It independently computes the digit background through Newton identities rather than the builder's h4 recurrence and compares direct scalar formulas with all three DAGs at216 signed assignments over three primes. Other checks include1000 eight-factor norm evaluations,840 pairwise-coprimality cases,120 negative-to-positive Pell orbits, roots of Pi modulo every modulus1..1200, signed-weight bounds, and exact operation/degree accounting. These finite diagnostics supplement the universal proofs; they are not a consistency oracle or kernel certificate.

Attribution: Jones's original arithmetic reduction and the ProveIt formal-development sources provide the imported interface; source29 provides the earlier signed square-stack and degree-five intersective merger; source30 provides the quartic31 and coherent compact tuple; source27 provides shared-power/h4/Horner evaluation. The new synthesis and its ordinary proofs are AI-assisted. New material is offered under MIT-0; upstream notices remain applicable.
