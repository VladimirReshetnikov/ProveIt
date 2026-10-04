# Independent mathematical review of the A196460 article

4 October 2026, UTC. Review of the 1,046-line standalone manuscript
`oeis-arity-asymptotics-release-20261004/manuscript/article.tex`.

## Verdict and explicit acceptance scope

**PASS. No mathematical correction or numerical-table correction is required.**
The complete manuscript has been read against the complete accepted asymptotic
proof and complete independent asymptotic audit. Its classification, count,
weighted graph interpretation, all fixed-order forward/logarithmic/inverse
expansions, exact inverse conventions, signs, coefficient formulas, and stated
limitations are mathematically sound.

Acceptance expressly includes the following additions and extensions:

1. **Sharp logarithmic remainder, equation (26), source lines 550–556.** This
   is a valid additional deduction. Apply the proved logarithmic expansion at
   order M+1, subtract the order-M expression, and use
   `[x^(M+1)] L_(M+1)=c_(M+1)/(M+1)! > 0`. The next error divided by the
   displayed leading scale is O(n 2^(-n)), hence tends to zero. Division by
   lambda=log 2 preserves positivity. The conclusion is an eventually
   positive remainder for each fixed order, with precisely the stated
   constant; it is not a sign claim for all small n.
2. **Rectangular count C_(p,q), source lines 897–909.** The formula is valid
   for p,q nonnegative integers with one tail label in each coordinate.
   An accepted tail-tail corner forces exactly the one full table. With
   rejected corner, choose r finite row marks and c finite column marks.
   Their forced union leaves (p-r)(q-c) free interior bits, and the marks
   are recovered uniquely from the boundary. Summing gives exactly
   `1+sum_(r=0)^p sum_(c=0)^q binom(p,r)binom(q,c)2^((p-r)(q-c))`.
   It remains valid when a finite part is empty. No rectangular asymptotic
   estimate is asserted or imported from the balanced case.
3. **Higher-dimensional remark, source lines 905–909.** This restates the
   accepted `ONE_WITNESS.md`, Section 7, whose text was read and pin checked.
   The all-input coordinate-flat argument and product-of-tail-polynomials
   construction apply in every fixed finite dimension. The manuscript makes
   no new exact higher-dimensional counting claim; it poses that as a
   question. The finite-dimension qualification is maintained.

The manuscript is approved at the exact SHA-256 below. This is a proof and
static-data review, not a fresh execution of the retained mathematical
checkers, a theorem-prover certification, a priority search, or an external
submission. The release packaging and full visual QA are separate checks.

## Exact reviewed objects

| Object | SHA-256 |
| --- | --- |
| Manuscript article.tex | `6569cdc99dc96bdf53c819d18ecfccad030771b5a1795b07c7deb02b3e7a901c` |
| Rendered 16-page article.pdf | `2a95d839ec43787f55cd73a7cb8e6a65635210388398f33b30396910cc128910` |
| Asymptotic source manifest | `6ae30398c52b6fe1d07a91346791ed3355e7104c55b19a4103de257299293de1` |
| Asymptotic source PROOF.md | `638e524d058deb926919d15b7df2dafc17f7a44dc2688b33e06ee24f476b7c41` |
| Independent asymptotic audit manifest | `737af333985bc079ecdd688f1854f7221bb86169db7841d91a1115d2f94e7055` |
| Independent asymptotic AUDIT.md | `7405fc28ea33b90ca80471ab368b667e1728b374eb3098f3e62844a91e1f8ca7` |
| Accepted ONE_WITNESS.md | `9135dd0e829adb3190e99ed1b62f8d419f9f7540cfd92a1acd1635726fa7172c` |
| Earlier low-arity AUDIT.md | `6bf14006170df1e126fb98d8e06ee97cfb51786f9ce11bcc0a37370a896d5afe` |

All 20 payload hashes in each of the asymptotic source and independent audit
manifests match their present files. The top-level release `article.tex` has
the same bytes as the reviewed manuscript. All four appendix hash strings
and the two dependency hash strings match their specified files. The PDF
hash was independently read, and `pdfinfo` reports 16 pages. Its extracted
text confirms the sharp-logarithm display is numbered (26) and retains the
rectangular formula and hash table. This review does not claim visual
inspection of the rendered pages.

## Statement-by-statement mathematical review

### 1. Definition, closure, and minimum auxiliary count (lines 68–232)

The domain is explicitly positive integer inputs, one polynomial equality,
fixed finite table data, and unrestricted table-dependent degree. These are
the right hypotheses for the result. The infinite-grid lemma proves that a
restriction vanishing on every tail input is identically zero, so accepting
a tail cell forces its complete coordinate flat. Cells with no tails impose
no replacement condition; their closure is the original cell. This trivial
case does not require the infinite-grid lemma.

The product of sums of squared finite-coordinate deviations is an integer
polynomial. Its positive zero set is exactly the union of the permitted
coordinate flats. Closure prevents unwanted inputs, while each accepted
input supplies a vanishing factor. The empty table and all-tail factor are
handled by the empty product 1 and empty sum 0 respectively. The argument
does not wrongly assume a general representing polynomial is nonnegative.

For the one-witness construction, p_K vanishes exactly below K and is a
positive integer on the tail. A positive value of its product enforces every
claimed tail coordinate, and the finite-coordinate square terms enforce
all remaining labels. The factor zero conditions identify exactly one
clipped cell, yielding a unique positive witness on each accepted input.
The K=1 alternatives are correct. Necessity plus this upper bound proves the
minimum exactly zero or exactly one in the stated class. No stronger global
minimality or composed-encoding conclusion is slipped into the article.

### 2. Boundary count and graph attribution (lines 234–354)

The marks are boundary bits, not accidental all-one interior rows or
columns. Their unique recoverability prevents double counting. The free
interior rectangle and binomial choices prove both sums for a_n; the extra
1 counts only the accepted-corner full table. The seven initial a_n,C_n rows
match retained source data.

Taking edges to be rejected interior entries gives a genuine bijection to
graphs together with a subset of their isolated vertices. The uniform graph
has exactly n² available edges. For a specified r-left, k-r-right vertex set,
the number of prohibited edges is nk-r(k-r), with the cross intersection
counted once. This proves the isolation factorial-moment formula without an
independence assumption on the vertex-isolation events.

The first-order relational sentence has the stated active-subset reading:
B may be false only where both unary predicates are true. The explicit use
of two distinguished domain copies correctly treats B(x,x) as an ordinary
bipartite edge. Attribution to the 2023 version-1 sentence, not to an invented
new combinatorial interpretation, is faithful to the accepted source and
audit. The named authors, OEIS dates, arXiv version, appendix/table/page, and
retrieval limitations are transcribed consistently. Public sources were not
retrieved again during this static manuscript review.

### 3. Forward tail, signs, and rarity (lines 356–461)

The falling-factorial formula correctly vanishes outside valid integer
indices. Exact regrouping is distinguished from a usable asymptotic estimate.
The positive leading coefficient alpha_k and every displayed P_0 through
P_4 agree with the formulas and stored coefficient data.

Vandermonde and r(k-r)<=k²/4 give the stated majorant. The successive-term
bound applies on 0<=k<n, supplies a geometric bound through k=n, and the
quadratic exponent is decreasing on [n,2n]. The large-k tail bound therefore
has the correct negative quadratic scale. The explicit hypothesis n>=M+1
avoids an invalid starting sector. The concrete n>=max(M+1,16) range is safe.
The positive first omitted leading coefficient and the order-M+1 estimate
prove the sharp remainder; the next relative error is O(n2^(-n)).

The exact fraction includes the otherwise easily lost extra full table.
The factor 2^(-2n-1), its equivalence to 2^(1-2K), and F_0=1 are correct.
The complementary fraction has minimum one by the already proved theorem.
There is no convergence or growing-order claim.

### 4. Logarithms and connected colored graphs (lines 463–556)

Formal differentiation yields exactly the L recurrence, and degree at most
k follows inductively. The displayed L_1 through L_4 match both retained
coefficient sources. The actual logarithm argument first bounds u_n near
zero, controls replacement by a finite forward truncation via a bounded
derivative, and bounds discarded Taylor powers. Its finite mixed products
have degree no greater than their exponential index, giving the claimed
fixed-order analytic remainder.

The b_k count is for k labeled vertices with variable color split and two
named colors; it is not the balanced ambient graph count. Component
partitioning proves the exponential identity formally. Choosing the
component of label 1 gives the stated recurrence for c_k. The singleton and
stars prove positivity at every order, including the base case. This proves
the exact leading coefficient c_k/k! of L_k. The eight b_k,c_k rows are
correctly copied. The additional sharp-logarithm consequence is accepted
explicitly above.

### 5. Inverse coefficients and finite-proxy proof (lines 558–709)

The Laurent coefficient ring makes division by 2s legitimate. The new D_m
appears only in 2s delta at order m, proving recursive existence and
uniqueness. The displayed D_1,D_2,D_3 are correct, including the signs of
both inverse-s and lambda-squared terms. The product-degree argument
bounds every contribution from earlier D_j below the direct L_m top
power; therefore the exact largest s power is m-1 and its coefficient is
-c_m/(2 lambda m!). The singular-looking formulas are not asserted at s=0.

The finite H_M is explicitly smooth and is never identified as an arbitrary
interpolation of a_n. The source-point forward residual, s_n-n=O(2^(-n)),
and delta_M=O(t) place the two points inside the stated interval. Expanding
the exponentials only through M-k gives uniform remainders of size
O(s^k t^(M+1)); the remaining finite Laurent polynomial cancels through M
and its higher terms obey the stated degree bound. There is no silent
infinite-series differentiation or convergence assumption.

The derivative lower bound is uniform on [s_n-1,s_n+1] for fixed M. The
mean-value theorem divides the residual difference by at least s_n and
therefore proves precisely the claimed inverse error scale. Applying that
proved theorem one order further, rather than assuming a formal error
sign, establishes the negative sharp remainder and eventual overestimate.
Adding one to a_n changes its logarithm and square root by the specified
beyond-all-fixed-orders amounts; the same coefficient and sharp-remainder
statements consequently hold for C_n. This does not identify the two exact
small-index conventions.

### 6. Exact inverses and comparison boundary (lines 711–807)

The brackets are valid at every n>=0, and the elementary monotonicity proof
is correct. For y>=1, all indices below m qualify, all above m fail, and
exactly one comparison with a_m is needed. At m=0 the impossible negative
index branch is excluded. For C, the strict upper bracket holds only for
n>=1, while C_0=2 lies exactly on the next square boundary. The manuscript
both states this exception and obtains N_C(2)=0 from the correct threshold
rule. The empty qualifying sets below 1 and below 2 are stated.

The square-root boundary expansion has the correct q/ lambda term and
q² coefficient (m-1)/(2 lambda)-1/(2 lambda² m). Its error and restriction
m→infinity are sufficient. The distinction between a proved error bound,
a bare asymptotic O term, and an exact integer comparison is retained.
The schematic figure is consistent with the threshold including its
right-hand boundary ownership; it is not offered as a scale drawing.

### 7. Further questions and scope (lines 887–937)

Growing-order, unbalanced rectangular, and effective-inverse questions are
posed rather than answered by the fixed-order estimates. The rectangular
identity and higher-dimensional restatement are accepted as detailed in
the verdict. The degree 2|S| of the displayed zero-auxiliary polynomial is
correct when S is nonempty with no all-tail cell: every factor then has
nonzero quadratic leading part, and degrees add. It is properly separated
from minimum possible degree and other representation costs. The lower
bound on a_n implies radius zero for both ordinary and exponential
generating series, and neither is used analytically.

## Retained numerical data and transcription

Only already-retained JSON was parsed. Source and audit monomial records
were normalized by the documented h=1/lambda convention and compared as
stored data; no polynomial recurrence, enumeration, logarithm, root,
exponential, asymptotic evaluation, or mathematical checker was run.

- All 21 stored P,L,D families through order six agree between packets
- All 33 source sequence entries agree with the audit's retained entries
- Stored b,c arrays through six agree, and the displayed arrays through
  eight match the audit
- Every one of the nine displayed error-ratio rows literally matches the
  corresponding a-sequence record for M=1,3,6 and n=16,32,64
- Each displayed decimal pair contains the already-stored exact rational
  endpoints; this was also checked for all 36 stored cases
- Every stored signed remainder interval has an ordered pair of endpoints
  with strictly negative upper endpoint, agreeing with all 36 sign flags
- Summing stored inventory counts yields exactly 66,066 tables, 44,298
  direct zero-polynomial evaluations, 66,067 bipartite graphs, and 33,868
  ordinary graphs; the other stated counts are 65 sequence indices, 585
  polynomial values, 4,225 majorants, and 1,012 threshold probes
- The retained formal-check order is eight, with both residual flags true

These are transcription and internal-consistency checks of retained
evidence, not claims that its original numerical computations were rerun.
The retained exact-data pins and comparison results are recorded in
`evidence/static-data-review.json`.

## Provenance and delivery limits

The appendix accurately distinguishes historical preservation evidence from
the new article-build boundary. The source/audit ledger numbers 249,376,132,
44,88,62,87 and the audit start time agree with retained JSON and audit text.
The recorded 132 historical changes are not erased or described as preserved
bytes. No actor is blamed for them. The original audit's input-before and
input-after records are retained, and this review does not replace either.

The claimed presentation-build isolation, exact external build-dependency
locking, archive metadata restoration, and final publication state remain
subject to the separately owned build/packaging verification. They are not
inferred from a mathematics PASS. This review authenticates the manuscript
and source pins, reads retained preservation claims, and approves the
mathematical content; it does not certify an archive that was still being
assembled or imply delivery/publication.

No source or upstream script was executed or imported. No fresh mathematical
checker, source interpreter, physical simulator, saved schedule, or Lean
process was run. Only inert text/JSON inspection, SHA-256 hashing, static
stored-value comparisons, PDF metadata reading/text extraction, and writing
this separately owned review dossier were performed. No input file was
modified. No actionable mathematical change remains.
