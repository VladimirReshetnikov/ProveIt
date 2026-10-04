# Independent analytic review of the uniform sector article

4 October 2026 UTC.

## Verdict

**PASS for mathematical fidelity, proof completeness, exact-data transcription, and bounded attribution. No mathematical correction is required.** The manuscript faithfully presents the accepted continuation and its fresh independent audit. The known source-directory bibliography typo was corrected before this review snapshot; the verified path is `inputs/uniform-sectors`.

This report reviews the complete 811-line manuscript, not only its theorem statements. The initial analytic snapshot has SHA-256 `67e03c820d31a42c3f14a2af7ddb2ce41c23484a96337c112cf8f74813d1dd78` and is retained as `evidence/analytic-reviewed-article.tex`. Final rendering, layout, and new release packaging claims are separately gated; this analytic verdict does not assert that an as-yet-unfinished build or archive has passed.

## Authenticated sources

The full accepted proof and full fresh independent audit were read as inert text. Their supplied pins matched the filesystem bytes:

- Source proof: `ebd92e3b5bdf684981b2ff248376ac290c57aec403169beee780fef9ea92aa65`
- Source manifest: `bf48296dc1bd86689df3dbef9cb3bba99903ec84a32f226e2289ec79ea0a3a29`
- Independent audit: `4fa84b2ddfe383668c86ea0ad4d7419b0304eb0d9a97725aecbdab7e3b63ff03`
- Audit manifest: `039c112bd070a8b48b92584c76ec05b3876662bb82f186813a0fb445ddd9e36c`

The appendix prints these four complete hashes correctly across its line breaks. The retained audit table file is pinned at `d197301c0c91f2168d92a88639915fc20b34c6796b4febb385898658048c9b0b`. Additional inspected-source pins are in `evidence/INPUT_SHA256.txt`.

## Proof review

1. **Exact object and endpoints.** The finite normalization is obtained by expansion and complementing both binomial indices. Strict positivity holds at every allowed sector. The complement relation includes k=0 and k=2n. The reindexing j=M+1 and ell=2n-j gives exactly 0<=ell<=2n-1; the manuscript correctly excludes ell=2n, which would mean M=-1.

2. **Raising and global-ratio estimates.** Raising each coordinate supplies the target coordinate multiplier; forbidden moves vanish. The hyperbolic expression has the correct positive h*sinh term. The high-sector numerator has its maximum 3/2 at ell=3. The low-sector binomial reweighting is symmetric and decreases radially, including the zero extension at support boundaries. The covariance argument is applied within each lattice. Integer and half-integer normalizers and factors are separately accounted for, with respective majorants 481/72 and 5*sqrt(2), each below the common constant 8. The low and high ratio ranges overlap at k=n. The n>=32 estimates establish strict monotonicity before it is used in tail maximization, avoiding circularity.

3. **Unique sharp maximum.** The low first-omitted range has nH<=11/42<9/13. The high complementary range ell>=5 is bounded by 5(n+1)/[4(n-2)(2n-1)], strictly below H3 by the accepted quartic comparison. The explicit P0,...,P4 and H1,...,H4 formulas are transcribed correctly. The comparisons at ell=1,2,4 are strict, and H0=0. Thus H3 is the unique maximum, translating to M=2n-4. K_n and its exact correction to 9/(13n) agree with the source, including numerator 174n+21 and the factor 13n in the denominator. The ordinary rational-function limit establishes 9/13 without interchanging a supremum and a limit. The convenient threshold 32 is repeatedly identified as nonminimal in intent.

4. **Merged table count.** Only the terminal sector doubles. For ell>=1 the extra excess is 1/P_ell, while ell=0 is treated separately as zero because the denominator doubles as well. J1=1/n and every ell>=2 is strictly smaller using the accepted cubic 12n^3-71n^2+30n-1. The unique index M=2n-2 and exact terminal M=2n-1 are preserved. For the unmerged convention the final excess remains exactly 1; it is not discarded as a small error.

5. **Leading-coefficient boundary.** The positive-weight product representation and the elementary lower bound hold for k<=n. The exponential upper bound is extended correctly to k<=2n by assigning zero contribution to invalid binomial pairs. At k=1 its exponent is positive and is explicitly recognized as harmless. Necessity in the iff statement uses a subsequence bounded away from zero in k^2/n, forcing k to infinity; no monotonicity hypothesis is introduced. Sufficiency eventually places k in the elementary product range. The asserted equivalence is exactly k^2/n -> 0.

6. **Explicit central correction.** The alpha-weight distribution uses the correct binomial radial factor. The two Gaussian second-moment majorants 107/54 and 41/27 are correct and below 2. The logarithmic product bound has the accepted epsilon with denominator 12n^2(1-(k-1)/n). The cases k=0,1,n remain included; n>=3 keeps the lower factor positive. The deficit bound epsilon+2/n and the explicit k<=n/2 consequence 2/n+k^3/(3n^2) agree with the audit. They justify the uniform k=o(n^(2/3)) assertion and the transition exp(-c^2/4) for k/sqrt(n)->c>0.

7. **Scope discipline.** Single-coefficient relative accuracy is separated from accuracy at the first-omitted-sector scale. The manuscript does not replace all earlier exact coefficients by leading monomials, assert a growing-order logarithmic or inverse theorem, claim noninteger infinite-sector convergence, or floor an approximate inverse. Suggested higher-order refinements are framed as unproved questions. No new result exceeds the accepted packet.

## Exact table and evidence counts

Each of the ten displayed rows, n=1,2,5,6,8,9,32,64,128,160, was compared directly with the independent audit's retained `evidence/mathematics.json`. Both rational maxima and both singleton maximizer lists match. The compact literal extraction is retained as `evidence/TABLE_TRANSCRIPTION.tsv`. No sector value, maximum, or scientific inequality was recomputed by a program. The table's below-threshold rows are explicitly illustrative, not a reduction of the proved threshold.

All appendix counts agree with the stored source and independent-audit JSON and prose: the source's 128 n-values, 16640 complements, 16512 raising checks and squared lower bounds, 15520 ratios, 97 complete maxima checks per convention, 2498 elementary leading comparisons, and 129 second moments; the audit's 320 normalizations, 25920 complements, 25760 raising checks and squared bounds, 24768 ratios and sharp comparisons per convention, 13040 leading-product comparisons, 4272 corrected comparisons, and 321 moments. The finite corrected subset is not represented as the all-n proof.

## Background and public attribution

The unchanged predecessor article was inspected only as background, including its count, boundary marks, graph interpretation, and retained primary-source reference. This article gives the short established count C_n=1+a_n and does not repeat its full classification or inverse proofs.

The three public OEIS pages were separately consulted as text on 4 October 2026:

- https://oeis.org/A196460 supports the displayed term formula, Hanna's entry date of 2 October 2011, and Kotesovec's leading asymptotic dated 25 June 2013
- https://oeis.org/A047863 supports the binomial sum k!alpha_k, graphs with two named proper colors, and the parity-dependent theta asymptotic credited to Kotesovec on 24 June 2013
- https://oeis.org/A002027 supports connected labeled graphs with those named colors and the logarithmic relation with a separate constant-at-zero convention

The manuscript restricts the connected interpretation to k>=1, credits the known theta context, and makes no novelty or priority claim. Its bounded literature-search qualification remains accurate. This review is not an exhaustive priority audit.

## Preservation and limits of this review

Only read-only text/data inspection, primary-source retrieval, cryptographic hashing, literal data extraction, and creation of this external review dossier were performed. No scientific source or upstream program was executed or imported; no scientific interpreter, simulator, schedule, Lean, or exact-arithmetic checker was run. No manuscript or predecessor file was edited by this reviewer. No upload or publication was performed.

The source's historical 51-object boundary and audit's 333-object boundary are described with their original scope and temporal qualifications. The fresh freeze receipt records an unchanged scoped input interval; it does not retroactively enlarge the earlier source claim. The final presentation's dependency lock, three-pass isolated build, all-page visual review, archive authentication, and final before/after preservation must be established by their final dedicated receipts. Read-only modes and hashes are not described as WORM storage or independent timestamps.
