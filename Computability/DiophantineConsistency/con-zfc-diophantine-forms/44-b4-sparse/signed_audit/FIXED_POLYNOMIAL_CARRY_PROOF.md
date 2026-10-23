# Fixed-polynomial Jones compression with arbitrary B4 weights

Status: ordinary universal proof, independently derived from the literal carry and ratio interfaces in ProveIt at 22e75dd6b87b1b199bb08c778d7cf075ae5aae08. This is not a newly kernel-checked theorem. The argument below replaces the index-transfer part of Jones, not the inherited ratio theorem or the K215/compiler endpoint.

## The input and fixed constants

Let P in Z[X_1,...,X_n] have degree at most four, with P(0) != 0. A natural zero of P is the desired predicate. Write p_alpha for its coefficients and put

c_alpha = (4-|alpha|)! product_i(alpha_i!) p_alpha.

Choose positive integer weights w_1,...,w_n such that all sums sum_i alpha_i w_i for |alpha| <= 4 are distinct. This is equivalent to unique sums of exactly four elements from {0,w_1,...,w_n}, with repetitions allowed. Put t=max_i w_i, L=4t, m=L+4t+1=8t+1, E=m+t+1=9t+2. Choose a fixed power of two z with |c_alpha|<z for every coefficient, and choose a fixed positive integer kappa such that

 a=2^kappa > max(2z(n+1)^4, 2048z, 8).

For both signed specializations use b=2 epsilon^2 and require epsilon != 0. Every successful assignment then has b>=2. Completeness chooses epsilon=2^r, so the base exponents k=1+2r are odd and cofinal. The fixed coefficient scale a is moved into the radix B=a b^4, not into the witness base b. This is the quartic-radix improvement: the radix now has degree eight in epsilon rather than ten, with no extra variable or circuit operation. For the natural specialization any integer base b>=2 is permitted.

At any such base b define the following POLYNOMIAL abbreviations (all exponents are fixed):

 B=a b^4;
 ell=sum_i B^(w_i);
 D(B)=sum_{|alpha|<=4} c_alpha B^(L-sum_i alpha_i w_i);
 q0=B^(t+1);
 Jcarry=2(1+g)^4 D(B) + B sum_{j=0}^{m-1} B^j;
 Tcarry=(B-2)B^L;
 S=g+q0 Jcarry;
 T=q0-1-(b-1)ell+q0 Tcarry;
 N=2B^E;
 R=S(N^2-N)+(T+1)(N^2-1);
 Gcap=32b B^t.

D(B) here is a signed sparse digit polynomial, not the Jones ratio register D. No fixed index y, input-coordinate digit, positive z-background, transfer-carry test, or additional quantified variable is present. Every coefficient recipe is finite and independent of consistency.

## Lemma 1: unconditional bounds on the intended outer domain

Suppose b>=2 and 1<=g<4bB^t. Then B>=4, 4b<B, and 0<g<q0. Because the exponent positions of D are distinct and its coefficients have absolute value <z,

 |D(B)| < z sum_{j=0}^L B^j < 2z B^L.

Since g is integer, 1+g<=4bB^t. Consequently

 |2(1+g)^4 D(B)| < 1024 z b^4 B^(L+4t)
 = (1024z/a) B^m < B^m/2.

The offset B+...+B^m is at least B^m and less than (B/(B-1))B^m <= (4/3)B^m. Thus

 0 < Jcarry < (11/6)B^m < 2B^m.

The mask M=q0-1-(b-1)ell has base-B digit B-b at positions w_i and B-1 at every other position j<t+1. All digits are in [0,B), so 0<=M<q0. Also 0<=Tcarry<2B^m. It follows by integer mixed-radix bounds that

 0<=S<N, 0<=T<N.

Indeed N=q0(2B^m), and both pairs of digits are bounded by their respective radices. In particular R>=N^2-1>=N>=8 and b<=N<=R. These statements hold BEFORE the digit/carry, square or divisibility conditions are known, as long as the displayed g bound holds. They do not assume b is a power of two.

### Stronger unconditional positivity for the actual sum-of-squares input

For the actual P31, P(0)>0. The coefficient c_0=24P(0) is therefore a positive integer and appears at exponent L. Since all weights are positive, every other term of D(B) has exponent below L. Consequently

 D(B) >= B^L - z sum_{j=0}^{L-1} B^j > 0

whenever B-1>z, which is guaranteed by B=a b^4, a>2048z and b>=2. Thus for EVERY g>=1, without the g ceiling, Jcarry>0 and S>0. The mask is nonnegative independently of g, hence T>=0 and R>=N^2-1>=N>=8. This supplies unconditional ratio-register positivity for natural-variable finalizers. The bounds S,T<N still require the ceiling and are asserted only after that ceiling has been recovered.

Also R is unconditionally nonzero even for signed g: modulo q0,

 R = (b-1)ell (mod q0), with 0<(b-1)ell<q0.

This congruence is an exact integer identity; the interval follows from b>1 and the digit mask. It does not require g to be a code or b to be a power of two.

## Lemma 2: the first carry tests exactly the witness code

Assume additionally b=2^k, k>=1. Let tau_2(u,v) be the number of carries in binary addition, equivalently v_2 binomial(u+v,u). Then tau_2(u,v)=0 iff u and v have no common 1-bit.

Put ell_B=kappa+4k, so B=2^ell_B. Binary no-carry testing splits into base-B blocks. The mask digit B-b=2^ell_B-2^k consists of ell_B-k high 1-bits and k low 0-bits, so it has no common bit with an arbitrary base-B digit d exactly when d<b. The mask digit B-1 has every bit set, so no overlap forces d=0. Therefore, for 0<=g<q0,

 tau_2(g,M)=0 iff g=sum_i n_i B^(w_i) with 0<=n_i<b.

This proof works for arbitrary distinct positions w_i, not only powers of five. Conversely every such code satisfies g<bB^t: extend its digits by zeros to every position up to t, and use sum_{j=0}^t (b-1)B^j < bB^t. A zero of P is nonzero by P(0)!=0, hence its code g is positive.

## Lemma 3: coefficient extraction and the shifted carry

Take a code from Lemma 2 and set c(X)=1+sum_i n_i X^(w_i), H(X)=c(X)^4 D(X). Its degree is at most L+4t=m-1. Because all <=4 weight sums are distinct, coefficient matching at X^L gives

 [X^L]H = sum_alpha (4! / ((4-|alpha|)! product_i alpha_i!)) product_i n_i^(alpha_i) c_alpha
 = 24P(n).

To see there are no cross-terms, a term indexed beta from c(X)^4 meets a term indexed alpha from D at X^L exactly if sum beta_i w_i=sum alpha_i w_i; the B4 condition forces alpha=beta. The constant term in c is the unique zero-weight padding coordinate and is not a dummy input.

For each coefficient h_j of H,

 |h_j| <= z(1+sum_i n_i)^4 < z(n+1)^4 b^4 < B/2.

The final inequality uses a>2z(n+1)^4 and B=a b^4. No lower bound b>a is used anywhere in the coefficient or offset estimates.

Here the l1 norm of c^4 is (1+sum n_i)^4; convolution with a polynomial whose coefficients have absolute value <z yields the first bound. For a power-of-two b, B/2 is integer. Thus all a_j=h_j+B/2 are integers in (0,B), and

 Jcarry=2 sum_{j=0}^{m-1} a_j B^j,
 Tcarry=2(B/2-1)B^L.

Multiplication of both operands by 2 does not change whether they have any common 1-bit. After cancelling that common shift, Tcarry has precisely its lowest ell_B-1 bits set in the base-B block at position L. Therefore it has no bit overlap with sum a_j B^j exactly if the low ell_B-1 bits of a_L vanish. Since 0<a_L<B, this says a_L=B/2, equivalently h_L=0. Hence

 tau_2(Jcarry,Tcarry)=0 iff P(n)=0.

This gives both directions without a transfer-index lemma or sign assumptions on D(B).

## Lemma 4: one central-binomial condition

For b=2^k the number N=2B^E is a power of two. By Lemma 1 all four blocks fit. Since q0 is also a power of two,

 tau_2(S,T)=0 iff tau_2(g,M)=0 and tau_2(Jcarry,Tcarry)=0.

Apply Jones's existing central-binomial coding lemma (lemma_2_16, also the generic kernel used in Packing.lean): for a power-of-two N and 0<=S,T<N, the exact polynomial

 R=S(N^2-N)+(T+1)(N^2-1)

satisfies

 N^2 divides binomial(2R,R) iff tau_2(S,T)=0.

Consequently, under b>=2 and 1<=g<4bB^t, requiring b a power of two and this divisibility is equivalent to a natural zero of P. Necessity supplies the stronger g<bB^t, or 32g<Gcap. Sufficiency requires only 8g<Gcap.

## Lemma 5: composition with the existing Jones ratio interface

Retain exactly the ratio registers U,Y,M,PellP,K,A,B1,W1,C,J,Q,D,E,F,G1,H,I and the conditions a0 square, a1 square, Ddiv|Tdiv, margin>0 from the signed Jones proof. Only R,N,b,g,Gcap are replaced by the explicit polynomials above.

With the guards g>=1,s>=1,omega>=1,phi>=0 and margin>0, Gcap>0. The margin forces K!=0 and 8g<Gcap, thus g<4bB^t. Lemma 1 then establishes R>=N>=8 and b<=N<=R. Also 4(C-KY)^2<K^2. The existing h-positivity proof applies: C>0,Y>=1 imply K>0; PellP=2(RY)^2U>R+2, and a0 square excludes 1<=K<PellP. Thus h>=1. The unchanged i-reflection and j-Pell-orbit argument gives positive i,j. Now the existing Nine.ratio_sound theorem applies, yielding b a power of two and N^2 | binomial(2R,R). Lemmas 2–4 recover a zero of P.

Conversely, from any zero of P choose k arbitrarily large and odd, with b=2^k>=2 and all n_i<b. Construct g directly. Lemma 4 provides central-binomial divisibility and 32g<Gcap. Lemma 1 provides every size hypothesis of Nine.ratio_complete. Its explicit canonical witness, through exists_B25core, has omega=2^(2R+1-k), which is a positive square because k is odd. With b=2 epsilon^2 choose k=1+2r, epsilon=2^r. The radix exponent kappa+4k need not be odd; only the exponent k of b controls the parity of omega. The ratio completeness proof preserves b and omega. All remaining guard, merger and norm constructions of the existing signed fourteen-variable proof therefore apply unchanged.

The natural nine-variable finalizer also composes with this positive-domain ratio predicate, but its unconditional bounds must be checked against the new R,N, especially any inequalities previously justified only by old R formulas. The signed fourteen-variable proof above establishes its hypotheses directly and does not appeal to such a substitution shortcut.

## Scope and evidence

The new part is the fixed-polynomial two-carry front end and its composition proof. The B4 certificate must be independently verified. The selected P and all fixed compiler ports must remain one coherent instance. This document establishes an ordinary universal argument, not an evaluated solution or non-solution and not a formal proof-assistant rebuild. Source-level cofinality evidence is independently recorded in the companion audit.
