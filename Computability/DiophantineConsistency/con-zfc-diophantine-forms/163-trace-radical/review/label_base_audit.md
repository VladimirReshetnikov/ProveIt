# Independent audit: the label carrier F = t^t

Audit performed on 25 October 2026 by a separate AI research agent. This is an ordinary mathematical review, not a proof-assistant certificate or outside human peer review.

## Result

**PASS.** For integer t >= 1, F = t^t suffices for the exact positive-label multiplicity conclusion used by the factorial-free binomial CRT construction. The proof below closes the strict coefficient inequality at the boundary F = t^t; merely replacing the old strict coefficient-sum bound by a weak bound would not suffice.

The even-horizon completeness modification also passes: choose h even in t = 16+h^2. Then t is even, v_2(F) = t v_2(t) >= t > v_2(t!), and the inherited parity/CRT construction remains available. Choosing h even is cofinal, so it does not restrict which finite proof trees can be embedded.

## Precise lemma

Let t >= 1, F=t^t, and W_j=1+jF for j in {0,...,t}. Suppose

    product_{i<t} W_{v_i} = W_1 product_{i<t} W_{p_i} W_{q_i},

where every label belongs to {0,...,t}. Then the multiplicity of j on the conclusion side minus its multiplicity among the premises is 1 for j=1 and 0 for every j=2,...,t.

More generally, any two products of W_j with positive labels j<=t are equal, with at least one of the products having at most t factors, only if their multisets of factors are identical.

### 1. Recover the number of factors

Delete all W_0=1 factors. If the two positive-factor counts differ, let r be the smaller count. At least one original side has at most t factors, so r<=t. The side with more factors is at least (F+1)^(r+1), and the side with fewer factors is at most

    (1+tF)^r <= t^r (F+1)^r.

But F+1=t^t+1>t^t>=t^r. This contradicts equality. Thus the factor counts agree and their common value r satisfies r<=t. The case r=0 is included; in the stated application the right side contains W_1 and hence r>=1.

### 2. Bound each coefficient separately

For positive labels a_1,...,a_r<=t, put

    A(z)=product_{i=1}^r (1+a_i z)=sum_{k=0}^r A_k z^k.

For every k=0,...,r,

    binom(r,k) <= A_k <= binom(r,k)t^k <= t^r <= t^t=F.

The middle upper bound follows from

    binom(r,k)=binom(r,r-k)<=r^(r-k)<=t^(r-k).

The lower bound is positive. For another product C(z) with the same number r of positive factors, both A_k and C_k therefore belong to {1,...,F}. Consequently

    |A_k-C_k| <= F-1 < F.

This is the important strict inequality: individual coefficients can equal F, but differences of two positive coefficients cannot.

### 3. Lift equality at F to a polynomial identity

Suppose H=A-C is nonzero, and let s be its least degree with nonzero coefficient h_s. From H(F)=0, division by F^s gives

    h_s+F*(an integer)=0.

Thus F divides h_s, contradicting 0<|h_s|<F. Hence A=C in Z[z]. The linear factors 1+jz have pairwise distinct rational roots -1/j. Their multiplicities agree, proving the claim. This uses ordinary unique factorization in Q[z], or equivalently multiplicity at each rational root.

## Compatibility with the binomial row-selector argument

The reviewed incoming source is

    agent_frontier/incoming/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/report/main.tex

Its row-selector theorem needs R>=Lambda_t^2, where Lambda_t=lcm(1,...,t), and the source uses R=F^2. Since

    Lambda_t <= t! <= t^t = F,

the new carrier meets the same size hypothesis. **Divisibility Lambda_t | F is not asserted and is false in general** (for example t=16). The factorial-free selector uses size rather than that divisibility, so this distinction creates no gap.

The all-primes compatible-row lemma depends only on R>=1 and is unchanged. For t>=16, the new F also retains the coarse growth bound F>=2^t. Any old estimate using the larger equality F=[2(t+1)]^t must be rechecked individually; it must not be silently reused as an identity.

## Completeness and parity

Choose h even, sufficiently large for the inherited finite proof-tree and local label budgets, and set t=16+h^2. Even h is unbounded, and t is even. Thus

    v_2(F)=t*v_2(t)>=t>v_2(t!).

Let O be the odd part of t!, choose any sufficiently large odd multiple w of O, and let y=F w^2. Then y is an even multiple of t!: its odd part contains O because w is a multiple of O, and its 2-adic valuation exceeds that of t!. All beta moduli 1+(i+1)y are odd and pairwise coprime by the inherited elementary argument. Their product is odd, so the common beta representative can be made even by adding that product.

For R=F^2, v_2(R)>=2t>floor(log_2 t). Therefore for every 1<=i<=t,

    v_2(R+i)=v_2(i).

Consequently B=binom(R+t,t) is odd. This preserves the parity freedom of CRT representatives modulo N^2, with N=B^x, and the later odd-square radix construction.

## Scope and recommended statement

The new lemma is a strict sufficient bound; it is not a minimum-threshold theorem. It removes the old coefficient-sum slack while preserving the same label semantics. The review establishes the new label lemma and the stated selector/parity compatibility. Literal polynomial materialization, complete replacement of the power-request base by t, arithmetic metrics, and source-to-endpoint verification are separate obligations.

## Follow-up audit of every F-dependent estimate in the incoming report

I read the source report's complete arithmetic front, soundness argument, and constructive completeness argument (especially its source lines 414-680). No additional numerical threshold in that report fails under F=t^t with t>=16. The required substitutions and checks are as follows.

1. **Initial power recovery:** the old displayed equality F=[2(t+1)]^t changes to F=t^t. The positive base t>=16 remains valid for the same signed-power interface. The threshold improves to F>=16^16=2^64>2^32.
2. **Endpoint growth:** y>=F and x>=2+(t+1)y are algebraic consequences independent of the old base. They imply every old lower bound on x used below.
3. **Binomial coefficient bound:** F>=t and F>=7 hold. The estimate F^2+F<=2^(F-1), hence binom(F^2+t,j)<=2^[t(F-1)] for 0<=j<=t, is unchanged. Combining x>=2+(t+1)F with q>=2^x still gives the exact exponent gap F+t+2.
4. **Derived-label exponent:** ell=2^22, while F>=2^64. Thus x>ell(t+1), as required. The inherited local constructor majorant and its ell are unaffected by the carrier-base replacement.
5. **Local polynomial separation:** the source uses Rcal=2+t+x+y+F<2x and E=2^23. The first inequality still follows from y>=F and x>=2+(t+1)y. The source threshold x>2^32 remains true (in fact x>2^64), so its dyadic estimate E log_2(2x)<x applies unchanged.
6. **Prime-power row selectors:** F=t^t>t!>=Lambda_t for t>=16; the selector's actual size requirement R=F^2>=Lambda_t^2 remains true. No divisibility of F by t! is needed.
7. **Boundary y=F:** the source's zero-propagation contradiction uses only the endpoint congruences and positive weights. It is unchanged.
8. **Completeness parity:** this is the one step that must be changed substantively: choose h even. Then v_2(F)=t v_2(t)>=t>v_2(t!), yielding the even multiple y and odd beta moduli. The old identity t(1+v_2(t+1)) must be removed.
9. **Odd B:** v_2(F^2)>=2t>floor(log_2 t) suffices for v_2(F^2+i)=v_2(i), so B=binom(F^2+t,t) stays odd on the selected completeness witnesses.
10. **Frame atom list and semantic anchor:** t is already an index/atom. The new power base is t, so the explicit old atom 2(t+1) must be removed or replaced in the literal graph and its proof ledger. The existing cofinal choice of a frame that dominates all actual atoms is still available. No new index is introduced.

The conclusion of this follow-up audit is **PASS with the stated formula/atom/parity replacements**. This does not substitute for checking that the generated endpoint actually makes those replacements.
