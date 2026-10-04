# Independent audit of uniform growing-sector truncations

4 October 2026, UTC.

## Verdict

**PASS. No mathematical correction is required.** The incoming proof establishes its two exact, simultaneous all-truncation tail theorems for every integer n >= 32, including the unique maximizers. Its coefficient-ratio equivalence and explicit corrected two-sided estimate are valid on their stated domains. The claimed limiting constants follow without an uncontrolled interchange of a supremum and a limit.

This is an independent analytic review and new exact-arithmetic corroboration, not execution of the author's checker or adoption of its previous endorsement. The source proof, source boundary, README, four Python programs, manifests and relevant stored evidence were inspected as inert data. No source or dependency program was run or imported. No interpreter for scientific source, simulator, trajectory computation, saved schedule, Lean rebuild, external publication, or priority search was performed.

The source proof under review is:

- Packet: `/workspace/shared/growing-sector-truncations-20261004`
- PROOF.md SHA-256: `ebd92e3b5bdf684981b2ff248376ac290c57aec403169beee780fef9ea92aa65`
- Manifest SHA-256: `bf48296dc1bd86689df3dbef9cb3bba99903ec84a32f226e2289ec79ea0a3a29`
- ZIP SHA-256: `5155553958eb14f2a2bb0c28aa1262cc2e2ad1871aac3b37d6d3efc2c7355c42`

This external dossier neither revises that packet nor the earlier fixed-order article. Read-only delivery and cryptographic pins make subsequent changes detectable; they are not WORM storage or an externally trusted timestamp.

## 1. Exact object, positivity, and all endpoints

For 0 <= k <= 2n, the sum defining P_k(n) contains at least one admissible pair r,c in [0,n]. All included binomial coefficients and powers of 2 are strictly positive. Thus every P_k and S(n,k) is positive. Expanding (1+2^j)^n gives the double sum of binomial weights times 2^(jc). Complementing both indices gives the normalized exponent -n(r+c)+rc. Consequently A_n is exactly the finite sum of all S(n,k); there is no asymptotic step in the normalization.

Complementing r=n-u, c=n-v gives -n(r+c)+rc=-n^2+uv. This proves S(n,2n-k)=2^(-n^2)P_k(n) at every endpoint as well as in the interior. In particular S(n,2n)=2^(-n^2), P_0=1, and the extra 1 in C_n=a_n+1 has exactly the normalized size of the terminal sector.

For an allowed truncation, j=M+1 lies in [1,2n]. The index l=2n-j therefore ranges over [0,2n-1]. Reversing the finite tail gives E=H_l, with H_0=0 and H_l=(P_0+...+P_(l-1))/P_l. The l=2n case is correctly absent: it would correspond to retaining no sectors at all, M=-1. The maximum at l=3 translates to M=2n-4; l=1 translates to M=2n-2; l=0 translates to the exact terminal truncation M=2n-1.

The interpretation of C_n as the clipping-table count is inherited from the separately proved closure count in the authenticated fixed-order source. The new theorem needs only its exact identity C_n=a_n+1. It makes no additional claim about the unrelated POWER/Pell or physical-model content retained in the upstream dependency archive.

## 2. Raising identity and high-sector bound

Let w_(r,c)=binom(n,r)binom(n,c)2^(rc). Raising r to r+1 multiplies the target weight by r+1, because (n-r)binom(n,r)=(r+1)binom(n,r+1); the extra factor 2^c supplies the exponent change. Raising c contributes c+1. A target pair of total k+1 is consequently counted with total multiplier k+1. Forbidden moves have zero factor n-r or n-c. This verifies the raising identity, including k=0 and k=2n-1.

Writing h=r-k/2 and A=n-k/2, the bracket is exactly

    2^(k/2) [2A cosh((ln 2)h) + 2h sinh((ln 2)h)].

For 0 <= k < 2n, A>0, cosh>=1, and h sinh((ln 2)h)>=0. Division by the positive P_k gives inequality (6). Applying it at l-1, followed by complement symmetry, proves the high-sector ratio bound for 1 <= l <= n.

The numerator l*2^(-(l-1)/2) has values 1, sqrt(2), 3/2 at l=1,2,3; from l=3 onward its next/current ratio is at most (4/3)/sqrt(2)<1. Its exact maximum is therefore 3/2. The denominator 2n-l+1 is at least n+1 in this range, giving q_n=3/[2(n+1)]. This bound requires neither monotonicity of P nor an unproved assertion about the location of the dominant summand.

## 3. Both Gaussian lattices and the low-sector bound

At fixed k the h weights are proportional to b(h)2^(-h^2), where b is the symmetric product of binomial coefficients. On either nonnegative half of its permitted lattice,

    b(h+1)/b(h) = (A-h)(k/2-h) / [(k/2+h+1)(A+h+1)] <= 1.

At the last positive value the next value is zero; beyond the support b stays zero. The displayed ratio is used only where its denominator and b(h) are positive. This resolves the support endpoints, including k=0 and k=1.

For independent base Gaussian variables X,Y, the product (b(X)-b(Y))(f(|X|)-f(|Y|)) is nonpositive whenever f increases with |h|. Its expectation is twice Cov(b,f). Since E b>0, dividing gives E_b f <= E f. The sums are absolutely convergent for both functions used in the proof; the explicit estimates below also verify that fact. No comparison between different lattices is assumed.

For f(x)=cosh((ln 2)x)+x sinh((ln 2)x), its derivative on x>=0 is nonnegative and f(x)<=(1+x)2^x. When k<=n and n>=2, A>=1, so the raising bracket divided by 2A2^(k/2) is at most f(|h|).

On the integer lattice the denominator is at least 1. The j=1 and j=2 contributions, together with j=0, total 13/2 under the stated majorant. For j>=3, j(j-1)>=2j. Summing the remaining geometric derivative series gives 481/72<8.

On the half-integer lattice the denominator is at least 2*2^(-1/4). Substituting h=m+1/2 gives the majorant sqrt(2)*sum_(m>=0)(m+3/2)2^(-m^2). For m>=1, m^2>=m, and the sum is at most 5sqrt(2)<8. The factor sqrt(2) and the two symmetric lattice points are both accounted for correctly.

Thus the low-sector forward ratio is at most 8(2n-k)2^(k/2-n)/(k+1), which is at most d_n=16n2^(-n/2). At n=32, d_n=1/128. The quantity (n+1)d_n has successive ratio (n+2)/(sqrt(2)n)<1 for n>=32, and its initial value 33/128 is below 3/2. Hence d_n<=q_n.

Low ratios cover 0<=k<=n and high ratios cover n<=k<2n; their overlap at k=n leaves no gap. Every ratio is at most q_n<1. This proves strict decrease of S and, by complement symmetry, strict increase of P. A finite geometric majorant now establishes the all-M uniform estimate 3/(2n-1), before the sharp maximizer is sought. There is no circular dependence on the later location of the maximum.

## 4. The unique maximum and strict rational comparisons

The relation H_l<=[P_(l-1)/P_l]/(1-q_n) follows by bounding the consecutive preceding P ratios. It is a finite sum, so convergence of an infinite sector expansion is not invoked.

For first omitted index j<n, the first forward ratio is at most d_n, and the later ones at most q_n. Therefore nH_l<=n d_n/(1-q_n). The factor n^2 2^(-n/2) decreases for n>=32 because ((n+1)/n)^4<2, while 1/(1-q_n) also decreases. At n=32 the product is exactly 11/42, strictly below 9/13.

For j>=n, the complementary index satisfies 0<=l<=n. When 5<=l<n, the ratio of successive g bounds is at most (6/5)(34/33)/sqrt(2)=(68/55)/sqrt(2)<1. The second factor is valid because 2n-l>=n+1>=33. Thus all 5<=l<=n satisfy

    H_l <= 5(n+1)/[4(n-2)(2n-1)].

For n>=32 every denominator is positive. The difference between H_3 and this upper bound has the sign of

    7n^4-146n^3+101n^2-46n+24.

The source's elementary positivity argument already works at n>=21. As an independent certificate, replacing n by t+21 gives coefficients [52860,70346,9425,442,7], all positive, in ascending powers of t.

The fresh symbolic checker derives P_0 through P_4 by multiplying their falling-factorial polynomials. It confirms all five formulas and hence the four displayed H values. The factor 13n^2-15n+2=(13n-2)(n-1) is positive for n>=2. The other H denominator is P_4 times a positive normalization, so it is positive at the needed integer n>=32; its displayed polynomial also directly agrees with the positive finite sector definition.

The remaining comparisons are:

- nH_1=1/2<9/13
- nH_2<9/13 iff n>22
- nH_4<9/13 whenever 53n^3-1470n^2+847n-210>0; after n=t+28 this is [34482,43183,2982,53], all positive
- nH_3=9/13+(174n+21)/[13(13n^2-15n+2)]>9/13

Together with H_0=0, these cover every permitted l, disjointly apart from harmless endpoint overlaps. Every comparison to H_3 is strict except at l=3 itself. The exact upper bound and uniqueness in Theorem 1 follow for every n>=32.

Since the maximum is computed exactly for each n, the limit of n times the maximum is the ordinary limit of a rational function, 9/13. A smaller asymptotic uniform constant is impossible because the truncation M=2n-4 realizes that rational function for every n in the theorem's range. The proof does not claim that n=32 is minimal; finite behavior below 32 cannot strengthen the all-n theorem by itself.

## 5. Merged terminal contribution

When l>=1 the first omitted sector is unmerged and the extra terminal contribution is 1/P_l after division. Thus J_l=H_l+1/P_l. At l=0 the first omitted sector itself is doubled, and its tail consists only of itself, so J_0=0. Using H_l+1/P_l at l=0 would be wrong; the proof explicitly avoids that error.

At l=1, P_1=2n, so J_1=1/n. For l>=2, monotonicity P_l>=P_2 and Theorem 1 give J_l<=H_3+1/P_2. The strict inequality to 1/n reduces to

    12n^3-71n^2+30n-1>0.

Its expansion at n=t+6 has positive coefficients [215,474,145,12], validating the stated threshold 6 and hence the theorem's threshold 32. The unique maximum is l=1, M=2n-2. At the terminal truncation it is exactly zero. Without merging, the final remainder is 2S(n,2n) divided by S(n,2n), so its excess is exactly 1. This exception is retained, not hidden in a small error term.

## 6. Leading monomials, necessity, and corrected coefficients

For k<=n all r+c=k are admissible. Dividing binom(n,r)binom(n,c) by n^k/(r!c!) gives a product B of factors 1-i/n in [0,1]. The ratio P_k/(alpha_k n^k) is a positive weighted average of these products. The inequality product(1-x_i)>=1-sum x_i gives the lower bound 1-k(k-1)/(2n); the upper bound 1 is immediate. A possibly negative lower bound is harmless.

For every valid pair in 0<=k<=2n, log B<=-[r(r-1)+c(c-1)]/(2n)=-U-h^2/n, where U=k(k-2)/(4n). All product factors are strictly positive because r,c<=n makes the largest index n-1. Invalid pairs contribute zero and satisfy the exponential upper bound as well. This proves the upper bound over the entire stated range, including k>n. At k=1, U<0 and the bound exceeds 1; that does not invalidate it.

For necessity in the equivalence, if k^2/n fails to tend to zero, choose a subsequence with k^2/n>=delta>0. Then k>=sqrt(delta*n) tends to infinity, and k(k-2)/(4n) is eventually at least delta/8. The ratio is then at most exp(-delta/8)<1 on that subsequence. Sufficiency follows from the lower product bound because k=o(sqrt(n)) eventually has k<=n. This addresses arbitrary integer sequences, not only monotone k(n).

For the refined estimate, the alpha weights are proportional to binom(k,r)2^(-h^2). The binomial factor decreases with |h| on the appropriate parity lattice, so the same covariance argument applies to f(h)=h^2. The integer Gaussian second moment has upper bound 107/54<2; the half-integer bound is 41/27<2. The integer estimate uses j^2>=2j for j>=2 and handles j=1 separately. The half-integer estimate uses m(m+1)>=2m and the correct denominator 2*2^(-1/4). The new rational algebra check independently evaluates all these geometric sums.

For 0<=x<1, expanding -log(1-x) shows its tail after x is at most x^2/[2(1-x)], proving the logarithmic inequality used in the source. The sum of squared indices in the two products is at most sum_(i=0)^(k-1)i^2: the block 0,...,c-1 can be moved to r,...,r+c-1, which only increases its squares. All denominators 1-i/n are at least 1-(k-1)/n>0 for k<=n. Hence log B lies between -U-h^2/n-epsilon and -U-h^2/n with exactly the stated epsilon.

Averaging exp(-h^2/n)>=1-h^2/n yields

    exp(-epsilon)(1-2/n) <= exp(U) P_k/(alpha_k n^k) <= 1.

The restriction n>=3 keeps the lower factor positive. The degenerate k=0 and k=1 cases also satisfy the formula, with epsilon=0; their products can be evaluated directly. The endpoint k=n has positive denominator 1/n in epsilon, so it is included even though that numerical estimate may be loose.

For an explicit uniform consequence, if 0<=k<=n/2 and n>=3 then epsilon<=k^3/(3n^2). Therefore the corrected ratio differs from 1 by at most 2/n+k^3/(3n^2), with an absolute constant independent of k,n. Every sequence k=o(n^(2/3)) eventually enters this range and has vanishing error. This supplies the uniform content of the O term directly. If k/sqrt(n)->c in (0,infinity), U->c^2/4 and the corrected factor tends to 1, giving exp(-c^2/4) for the uncorrected ratio.

These are coefficient statements. They do not justify replacing every retained exact coefficient in a tail approximation by its leading monomial at the scale of the next sector. The source expressly warns against that substitution. It asserts no growing-order logarithmic or inverse expansion, convergence at noninteger arguments, or flooring formula for an approximate real inverse.

## 7. Independent static evidence

Only newly written standard-library scripts in this dossier were executed. Each was completely printed and inspected before its first execution. Their outputs were created with exclusive file creation, and no input module was imported.

`check_mathematics.py` forms P by a fresh double loop over the entire r,c square, computes both normalizations independently, checks the raising bracket and complement symmetry, and evaluates all allowed H and J tails. It does not load coefficient fixtures or author evidence. For n=1,...,160 it completed:

- 320 direct normalization identities
- 25,920 complement identities
- 25,760 raising identities and 25,760 squared lower-ratio inequalities
- 24,768 global-ratio checks, covering every adjacent sector for n=32,...,160
- 24,768 sharp comparisons for each of the ordinary and merged tails, including equality iff at the claimed unique index
- 13,040 leading-product lower/upper comparisons for every k<=n
- 4,272 rigorous two-sided corrected-coefficient comparisons for n>=3, k>=2, k<=n, k^3<=4n^2
- 321 exact alpha-weight second-moment checks, k=0,...,320

The 4,272 exponential comparisons use rational enclosing endpoints, not floating-point transcendental approximations. For x>=0, reduce x by powers of two to y<=1/4. The odd degree-23 and even degree-24 alternating Taylor sums bracket exp(-y), and repeated squaring preserves the positive bounds. The checks compare the exact coefficient ratio against the stronger inner endpoints, so a successful comparison certifies the claimed inequalities. This finite subset is corroboration; the analytic argument above covers all n>=3 and k<=n, including k=0,1,n.

`check_algebra.py` derives the five low-sector polynomials, checks all rational comparison numerators and positive coefficient shifts, the exact H_3 correction, and the Gaussian constants. Its completed JSON and log are preserved. Finite calculations do not substitute for the all-n proof.

The author's recorded checks and their counts are consistent with its inert source: n=1,...,128 gives 16,640 complements and 16,512 raising checks; n=32,...,128 gives 15,520 global ratios and 97 complete maxima checks. The smaller elementary leading comparison range gives 2,498 cases. These historical results were authenticated as stored evidence; they were not rerun or used as a premise for the new proof review.

## 8. Authentication and preservation boundary

The complete manifest file sets, every payload digest, and every archived byte and file mode were independently checked for five packets:

| Packet | Payloads | ZIP members |
| --- | ---: | ---: |
| growing-sector-truncations-20261004 | 13 | 14 |
| arity-table-asymptotics-20261004 | 20 | 21 |
| independent-arity-asymptotics-audit-20261004 | 20 | 21 |
| two-witness-tensor-compiler-20261004 | 31 | 32 |
| independent-low-arity-audit-20261004 | 20 | 21 |

That is 104 payloads and 109 ZIP members. Extra unmanifested files, missing files, duplicate manifest names, unsafe relative paths, duplicate archive members, symbolic links and nonregular objects are rejected by the fresh integrity checker. All five supplied manifest and ZIP pins match. Full dependency pins appear in `evidence/integrity-before.json` and `evidence/integrity-after.json`.

The preservation inventory covers 333 filesystem objects: all five packet trees, their five ZIPs and five receipts; the complete earlier fixed-order article release tree; its two source-evidence ZIPs; and its adjacent release manifest. For every object it records its path, kind, size, mode and nanosecond mtime, plus SHA-256 for regular files. The before inventory was captured after initial inert inspection and before the fresh mathematics checks; the after inventory is identical. Access times are excluded because reading may update them. Nothing was modified, restored, chmodded or retimestamped within these input boundaries.

The original continuation's 51-object before and after inventories also agree, and their final states match the current independently recorded inventory. This preserves rather than rewrites their narrower historical claim. No assertion is made about unrelated active report trees or any period before the new before snapshot. The earlier fixed-order article is observationally preserved by the present full-tree comparison, not repackaged or revised.

All retained upstream dependency bytes, including unrelated code and compressed evidence, are authenticated. Authentication is not a fresh endorsement of every scientific theorem in those archives. No public references were re-retrieved, so this audit leaves the supplied attribution and earlier bounded literature-search qualifications intact and makes no novelty or priority claim.
