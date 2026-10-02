# Independent audit: compact-uniform balanced Smirnov repair

Audited 2 October 2026. Scope: the proposed local `balanced-smirnov-repair/repair.md`, the source manuscript's displayed dependent coefficients (local `article-source.tex`, approximately lines 590–910), and the additional formal-operator degree proof communicated by its author. No external files or publications were modified. Historical priority claims were not audited here.

## Verdict

The coefficientwise remainder repair is valid. It proves the needed compact-complex-v-uniform, all-orders integer-power expansion directly, without gamma-tail estimates. The additional formal-operator degree argument is also valid and supplies the missing all-orders factorial-cumulant scaling. Independent exact enumeration and symbolic algebra reproduce the displayed third-order coefficients. No substantive mathematical defect was found in the core repair.

Important qualifications: fix k; use the analytic logarithm normalized at v=0, not an unspecified global principal logarithm; formulate the all-orders degree argument formally in w; do not infer a discrete inverse's exact index solely from asymptotic error notation. The original inverse's stated O(N0^-1) error is valid on the actual count sequence, and its displayed small corrections do not by themselves imply finer inversion accuracy.

## 1. Exact factorial moments: independent combinatorial derivation

In a multiset word, canonically number the k occurrences of each rank from left to right. A same-rank adjacency is one of the k−1 canonical bonds joining successive occurrences of that rank. Select m_i of these bonds for rank i. Contract all selected bonds. This is a bijection between words in which those specified bonds are present and words with k−m_i occurrences of each rank: expand the successive occurrences in the compressed word according to the selected bond components. The number of latter words is (N−M)! / product_i (k−m_i)!, where M=sum_i m_i.

Double-counting words with M selected present bonds, dividing by the total N!/(k!)^n, and summing over all selected bond subsets gives

E binom(X,M) = (N)_M^-1 sum_{sum m_i=M} product_i [binom(k−1,m_i)(k)_{m_i}].

This proves the exact coefficient identity with R_k, independently of integral transformations. For M=0 it is 1. For M>d=n(k−1), define both coefficients as zero rather than evaluating a possibly singular quotient. The formula is needed only for 0≤M≤d<N.

## 2. Positivity majorant and boundary cases

All R_k coefficients are nonnegative and (k)_m≤k^m on 0≤m≤k−1. Thus taking nth powers preserves R_k≤(1+kz)^(k−1) coefficientwise. For 0≤j<M≤d<N, both denominators N−j are positive and

(d−j)/(N−j)≤d/N,

since this is equivalent to Nj≥dj. Therefore E binom(X,M)≤(k−1)^M/M!, including M=0 by empty products and M>d by the zero convention. The n=1 case is included: X=k−1 deterministically. This bound does not assert stochastic Poisson domination.

The bound implies uniform convergence of every polynomially weighted sum of absolute PGF coefficients on each fixed disk. In particular, the eventual remainder constant is independent of n.

## 3. Complete-homogeneous remainder

The inequality h_(a+b)≤h_a h_b is valid for nonnegative variables and nonnegative integer a,b. A monomial's nondecreasing index string has a uniquely specified split after a entries; the split pairs form a subset of all pairs counted by the product. This is a weight-preserving injection, not an unproved cancellation. In the empty alphabet, h_0=1 and positive-degree h's vanish, so the statement still holds.

For M=0 the alphabet is empty; for M=1 it contains only 0. In either case Q_M=1 and H_r(M)=0 for r≥1. For M≥2, x=1/N obeys x(M−1)<1 because M≤d<N. The power series of Q_M converges absolutely there. Applying the inequality to H_(L+1+t) and summing yields the stated exact upper bound

0≤Q_M(x)−sum_(r≤L)H_r(M)x^r≤x^(L+1)H_(L+1)(M)Q_M(x).

The estimate H_s(M)≤(sum_(j<M)j)^s≤M^(2s), for integer s≥1, is valid because the multinomial expansion counts each weak monomial with a coefficient at least one. No 0^0 issue occurs in the asserted s≥1 bound. H_0 is separately defined.

## 4. Uniform operator error

Multiplication of the coefficientwise error by the nonnegative coefficient r_(n,M)(V/N)^M is legitimate. The full Q_M factor on the right converts this exactly into the true factorial moment coefficient c_(n,M)V^M. This is the decisive point: one need not bound Q_M uniformly in M or expand it in an unsupported large-M regime.

The resulting constant sum_M H_(L+1)(M)((k−1)V)^M/M! is finite for every finite V. At V=0 it is zero, because H_(L+1)(0)=0. The bound applies for every n≥1, not merely asymptotically. For a general compact subset of C, choose a containing centered disk.

Polynomiality of H_r(M) follows from the formal identity

sum_r H_r(M)x^r = exp(sum_(j≥1) p_j(M)x^j/j),  p_j(M)=sum_(i=0)^(M−1)i^j.

Faulhaber's polynomial has degree j+1 and the correct M=0 value. At coefficient x^r, the maximum degree is 2r. Consequently H_r(D) is genuinely finite order, with D=v d/dv.

## 5. Analytic integer-power conversion and logarithm

Since R_k(0)=1, log R_k has a unique analytic germ normalized to zero. On any prescribed, slightly enlarged v-disk, choose a sufficiently small w-disk so wv stays inside that germ's domain. Then log R_k(wv)/(kw) has a removable singularity and jointly analytic continuation at w=0 with value (k−1)v. This proves uniform Taylor remainders, including all finitely many v derivatives required for H_r(D), by Cauchy on the enlarged disk.

At w=1/N and n=N/k integer, exponentiating n log R_k(v/N) gives exactly R_k(v/N)^n; there is no fractional-power ambiguity. For each operator index r≤L, expanding through w^(L−r) makes its multiplied remainder O(w^(L+1)). The outer operator remainder is already bounded. Hence the final expansion is rigorous and has only integer powers.

On a fixed disk, e^(-(k−1)v)Phi_n(v)=1+O(N^-1) uniformly. For sufficiently large n its distance from 1 is <1/2 on a neighborhood of the disk. Use the logarithm near 1 there and add (k−1)v. Its value is exactly zero at v=0. This is the intended analytic branch. A principal log of Phi_n over a large complex disk can jump and is not the same statement.

## 6. Additional all-orders cumulant proof

This argument is needed; the mere existence of a uniform Poincare expansion does not imply the claimed cumulant scale.

Work in formal power series in w with coefficients polynomial in v after removing exp((k−1)v). Define

A(w,D)=sum_(j≥1) w^j p_j(D)/j.

The complete-homogeneous identity gives T_w=sum_r H_r(D)w^r=exp A(w,D), because all polynomials in D commute. Every coefficient of w receives only finitely many operator contributions. No operator-series convergence for nonzero w is asserted or needed.

Let exp(t A(w,D))F(w,v)=exp S(t,w,v). Its leading coefficient is exp((k−1)v), so the formal logarithm is well-defined with S_0=(k−1)v. Initially S_s(0,v)=(b_(s+1)/k)v^(s+1), of degree at most s+1. Differentiate formally in t:

partial_t S = sum_(j≥1) (w^j/j) exp(−S)p_j(D)exp S.

Here the conjugated operator is evaluated on 1. For any m, exp(−S)D^m exp S is a Bell polynomial in DS,...,D^mS: each monomial is a product of at most m such factors. This follows by induction from B_(m+1)=D B_m+(DS)B_m, B_0=1.

Assume deg_v S_q≤q+1 for q<s. To extract w^s from the jth summand, j≥1 and the factor orders q_i sum to s−j, so every q_i<s. Since p_j has degree at most j+1, the number a of factors is at most j+1. D preserves polynomial degree; hence the product degree is at most sum_i(q_i+1)=s−j+a≤s+1. Terms with zero factors cause no problem. Thus partial_t S_s has degree at most s+1, and its initial value has the same bound. Induction proves deg_v S_s(t,v)≤s+1 for every s.

At t=1 these are precisely the formal logarithmic coefficients of the already-proved analytic asymptotic expansion. Uniqueness of finite logarithmic expansion identifies them with the analytic coefficients. For fixed r≥2, truncate at L=r−2: all retained corrections have degree <r, so Cauchy coefficient extraction on a fixed circle gives kappa_r^(F)=O(N^(-(r−1)))=O_k(n^(1−r)). The r=2 case uses L=0 and is included. The mean is exactly k−1 directly from the first factorial moment.

## 7. Independent executable checks

`check.py` and `check-output.txt` accompany this audit. The program uses exact rational/integer arithmetic for all finite checks and exact SymPy polynomial identities for coefficient comparisons.

- A dynamic program enumerates the entire multiset-word adjacency histogram for k=2,...,5 and n=1,...,5, and verifies every factorial moment through two indices beyond support. This includes up to 623360743125120 words, counted by state recursion rather than materialized.
- All those moments match the R_k formula and satisfy the Poisson factorial-moment majorant.
- Exact rational checks of the h-submultiplicativity and Q-remainder bound cover M=0,...,14, a,b≤6, L≤7, and ten admissible values of N for every M.
- Independently derived b_j, f_s, P_s, and log coefficients through s=3 reproduce the manuscript exactly.
- The v=−1 probability coefficients and successive-term probability ratio through n^-3 match exactly. The k=2,3,4,5 specializations match the printed coefficients.
- The first local correction reduces algebraically to −((lambda−j)^2−j)/(2N), including j=0 and j=1 where falling factorial terms vanish.

The independently computed coefficients of N^-s in log Phi are

C1 = −(k−1)^2 v^2/2,
C2 = (k−1)^2 v^2 [2(k−2)v−3]/6,
C3 = −(k−1)^2 v^2 [(k^2−6k+7)v^2−4(k−2)v+2]/4.

The count expansion follows by adding the usual Stirling expansion: 1/(12N)−1/(360N^3) supplies exactly the stated A1,A2,A3. The exact count's factorial prefactor makes the ratio conclusion immediate once the probability ratio is checked. Fixed local probabilities follow by Cauchy on a fixed u-circle under v=u−1; this does not claim uniformity in growing j.

## 8. Inverse statement

For Y=B_(n,k) along the exact count sequence, put L=log Y+lambda and let f(x)=x(log x−1), so f(N0)=L. Write g(x)=0.5 log(2 pi x)+A1/x+A2/x^2+A3/x^3. The forward estimate is f(N)+g(N)=L+O(N^-4).

First N~N0; the forward equation and f'(x)=log x show N−N0=O(1), since g(N)=O(log N). Taylor expansion then gives

(N−N0)log N0+g(N0)=O(1/N0),

because f''(x)=1/x and g'(x)=O(1/x). Therefore

N=N0−g(N0)/log N0+O(1/(N0 log N0)),

which is stronger than the displayed O(N0^-1). This does not validate extra inversion digits suggested by retaining A2,A3: unaccounted Newton quadratic terms are larger than some of these corrections. For arbitrary Y, one needs a specified continuous interpolation or a discrete threshold convention; asymptotic agreement alone does not certify integer recovery at a particular finite input.

## Minor editorial recommendations

- Explicitly say nonnegative *integers* a,b for h_(a+b), and integer L≥0 throughout.
- Spell out that H_r(D) means the polynomial extension in M, and define the normalized logarithmic branch.
- Present the additional cumulant degree proof separately from the core uniform-remainder theorem.
- Keep the small-n support convention; it avoids all falling-factorial denominator ambiguities.
- Do not describe these checks or the repair as establishing historical novelty.

## Addendum: revised repair and optional gamma tail

The revised repair's Sections 7–8 have now been checked as written, not only as a communicated outline. Their formal-flow proof, coefficients, and inverse qualifications agree with this audit.

The optional Section 9 gamma-tail proof is also valid. Expanding R_k(V/t)^n inside the Gamma(N+1,1) integral gives a nonnegative finite mixture whose Mth mass is exactly c_(n,M)V^M and whose gamma shape is N−M+1≥n+1>0. For M≤floor(N^(1/3)), its mean is within N^(1/3)+1 of N, so the complement of the N^(2/3) window has the stated Chernoff estimate. The two optimized gamma exponents yield the asserted elementary quadratic lower bounds. Larger M contribute at most the factorial tail of exp((k−1)V), which has the stated faster-than-any-power rate. For degrees proportional to N, the same factorial bound gives exp(−epsilon N log N+O(N)). Endpoint choices floor/ceiling affect only lower-order constants, not the asserted rates. This optional argument repairs the weighted gamma-tail assertion independently but is unnecessary to the clean coefficientwise proof.
