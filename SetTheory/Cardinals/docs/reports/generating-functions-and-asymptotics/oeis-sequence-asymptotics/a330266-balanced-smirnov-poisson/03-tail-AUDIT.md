# Independent audit: balanced Smirnov uniform-tail repair

Date: 2 October 2026 (UTC)

## Verdict

**Pass, subject to the stated fixed-multiplicity and asymptotic scope.** I found no remaining mathematical gap in the repair of the compact-uniform all-orders factorial-PGF expansion. The separate logarithmic-degree argument is valid, and supplies the additional justification needed for the higher factorial-cumulant claims. The fourth-order probability coefficient is independently reproduced.

This is a mathematical/code review, not machine-checked formalization, a literature/priority review, or a certified numerical inverse theorem. No publication, upload, repository change, or external communication was performed.

## Material reviewed

- Author's `repair_note.tex`, specifically all proofs and displayed coefficients
- Author's `check_repair.py`, `coefficients.json`, `symbolic_checks.txt`, and source manifest
- Pinned original `source/article.tex` and `source/README.md`, including the originally qualified proof, cumulants, specializations, count/ratio expansions, and inverse discussion
- Original `source/code/derive_symbolic.py`

Original source pin: `4b874cea0012c51a6841ad9c58f6e20fa57c71da`; article Git blob: `afa43ce608b793d078a8887392766122ec36293a`. The checker's Git-blob recomputation agrees with all four source files in the supplied manifest. This verifies local bytes against that manifest; I did not independently retrieve the repository over the network.

At the reviewed snapshot, after the two small text corrections below:

- `repair_note.tex` SHA-256: `0c83ee871c160ab92eb6a1bafacad9a39cd7739ed59c513b4fafd3b885fa682c`
- `check_repair.py` SHA-256: `a455b072810e4557c18e68766dbffa6d0a3d04ac4b72a9a168c55b25c5fef543`

The author may subsequently make PDF/layout edits; these hashes identify the exact reviewed text/code snapshot.

## Mathematical review

### 1. Exact marked-adjacency identity

The directed-path-forest count is correct. A rank with j marked bonds has k−j directed components. Ordering all k labels and choosing j intervening bonds counts each forest (k−j)! times, once for each ordering of its components. Thus a(k,j) = k!/(k−j)! × binom(k−1,j). Contracting all marked components gives (N−m)! arrangements. Unmarked equal-rank bonds are allowed, which is essential to the factorial-moment identity. The support is m ≤ n(k−1) = N−n < N.

There is no undirected-path factor of two missing: the components are directed because they encode the orientation of a consecutive card string.

### 2. Uniform factorial-moment majorant

For 0 ≤ j ≤ k−1, (k−1) falling j ≤ (k−1)^j. Therefore R_k(z) is coefficientwise at most (1+(k−1)z)^k, including the unused top-degree coefficient on the right. Nonnegative coefficientwise multiplication preserves the inequality. Extracting the m coefficient and dividing by (N) falling m yields c(n,m) ≤ (k−1)^m/m! throughout the support. Outside the support the coefficient is zero; one does not divide by a vanishing falling factorial there.

This proves the bound for all n and k in the stated integer domain, even though the asymptotic constants later are only claimed for fixed k. The entire exponential majorant and integer-threshold tail bound follow immediately. This directly treats the growing number of rank cliques and does not invoke an inapplicable fixed-path-family theorem.

### 3. Positive scalar remainder

The inequality h_(a+b) ≤ h_a h_b is valid for a fixed finite list of nonnegative variables: splitting a weakly increasing index string after a entries gives an injective, weight-preserving map into pairs of strings. It also handles the empty list and zero-degree cases.

For m<N all geometric factors converge at 1/N. Summing the resulting coefficient inequality gives the exact positive remainder bound

0 ≤ A(N,m) − sum(s=0..q) H_s(m)/N^s ≤ N^(−q−1) H_(q+1)(m) A(N,m).

Crucially, multiplying by r(n,m)/N^m turns the final A factor back into the exact factorial-PGF coefficient c(n,m). The preceding majorant then controls the full support at once. No exchange of a nonuniform fixed-m expansion with a growing sum is being hidden here.

### 4. Finite uniform operator remainder

The displayed constant C_(q,k,V) is finite because H_(q+1)(m) is a fixed polynomial, of degree at most 2q+2, and is multiplied by the Poisson/exponential series weights. H_s ≤ H_1^s ≤ m^(2s)/2^s proves the stated Touchard upper bound. The resulting error is O(N^(−q−1)) uniformly on the full complex disk, for each fixed q,k,V.

This is stronger and simpler than the original sketch: no growing cutoff, gamma-tail concentration, or half-integer cancellation is needed.

### 5. All-orders analytic expansion

Because R_k(0)=1, log R_k is analytic on a fixed neighborhood of zero. For v in a slightly enlarged compact disk, substitution of v/N gives a uniform analytic expansion of F_N=R_k(v/N)^(N/k), with analytic remainder. Cauchy's estimates on that enlarged disk give the fixed derivatives required by every H_s(D). The sum of finitely many truncated operator terms therefore yields the advertised expansion and explicit P_j formula.

The degree estimate deg A_j ≤ 2j follows from partitioning a total h-order j among terms of degree r+1. Conjugating D by exp(lambda v) produces D+lambda v; applying a polynomial of degree at most 2s raises degree by at most 2s. Consequently deg P_j ≤ 2j.

### 6. Logarithm and sharper degree estimate

The analytic logarithm is handled correctly. On each fixed disk, exp(−lambda v)Phi tends uniformly to 1, so it is eventually in the disk of radius 1/2 about 1. This supplies an unambiguous analytic branch normalized at zero. The statement is not a claim about the principal logarithm at every complex v, nor about zero-freeness on the entire plane for a fixed n.

The formal differential evolution is a valid separate proof of deg Q_j ≤ j+1. Since L_s(D) has order s+1 and s≥1, the coefficient of h^j in the evolution only uses U_a with a<j. For a product with at most s+1 differentiated U factors whose total h-order is j−s, the degree bound is at most (j−s)+(s+1)=j+1. The initial coefficient has that degree as well. Thus induction and integration in the auxiliary parameter are legitimate and triangular at every order.

The identification of those formal coefficients with the already established uniform expansion is valid by uniqueness of asymptotic coefficients. Cauchy coefficient extraction from the uniform log expansion proves the cumulant scale for **each fixed r**, with constants permitted to depend on r. A claim uniform in all cumulant orders would require additional estimates and is not made by the repair.

### 7. Coefficients and local probabilities

The author’s symbolic recurrences for log R, its exponential, H_s, conjugated Euler operators, and the final logarithm are correct. The first three log and probability coefficients match the original source after N=kn. The source k=2,3,4,5 probability specializations match as well. The final checker revision also explicitly compares P_4(−1) and Q_4(−1) with the formulas printed in the note; both targets are correct.

An independent recurrence described below reproduces the full Q_1,...,Q_4 and confirms vanishing through v^12 where the degree theorem predicts zero. It reproduces

C_4(k) = (k−1)^2(15k^6−330k^5+2345k^4−7212k^3+13313k^2−10122k+2183)/5760.

In powers of n^(−1), the fourth coefficients for k=2,...,6 are respectively 361/6144, 110/729, 7395/32768, 2152/9375, and 179035/1492992. All agree with the note.

The fixed-j local correction follows correctly by substituting v=u−1 and using Cauchy extraction on a fixed u-circle; the relative polynomial simplifies to −((lambda−j)^2−j)/(2N). This is a fixed-local-index statement, not an unproved uniform local limit theorem over growing j.

### 8. Count, ratio, and inverse scope

Stirling plus the repaired log-probability expansion gives the source count coefficients. For the ratio, if the leading log-probability coefficients in n are a/n+b/n^2, the difference at n+1 minus n is −a/n^2+(a−2b)/n^3+O(n^−4); substituting the source a,b gives exactly the displayed ratio. No differentiation of an uncontrolled remainder is needed; subtracting two O(n^−4) remainders remains O(n^−4).

For Y equal to an actual sequence value, the count expansion and monotonicity of f(x)=x(log x−1) first give N_0−N=O(1). Taylor expansion then gives a residual O(1/N_0), which dividing by f'(N_0)=log N_0 improves to O(1/(N_0 log N_0)). The note's improved inverse remainder is therefore justified. The same reasoning applies to the specified smooth carrier for arbitrary large Y.

The restriction matters: the expansion alone does not certify the least integer index for arbitrary Y, does not supply explicit finite-n rounding constants, and does not make the standard-deck decimal an a priori bracketing theorem. The note expressly retains those qualifications. Along actual sequence values the o(1) index error implies eventual nearest-integer recovery, but without an effective threshold from the present proof.

The three further questions are appropriately bounded. In particular, the unequal-rank factorial-moment bound by (K−1)^m is valid: each rank polynomial is coefficientwise bounded by (1+(K−1)z) raised to that rank's size, and multiplying gives total exponent N. The note does not claim this alone proves a limiting distribution or all-orders expansion for arbitrary varying compositions.

## Reproducibility review and runs

Environment: Python 3.12.14, SymPy 1.14.0.

The author’s checker was copied into this audit directory with source files and manifest, so reruns did not overwrite the author’s output files.

- Normal run: exit 0
- Optimized `python -O` run: exit 0
- Normal and optimized stdout: byte-identical
- Normal `--inject-error`: exit 1, `ValueError: Log coefficient 3`
- Optimized `--inject-error`: exit 1, same validation failure
- 14,850 exact integer moment inequalities checked
- 19,434 exact rational scalar-remainder cases checked
- General-k operator expansion computed through N^−4

The checker uses explicit exceptions, not removable `assert` statements. The negative test really does perturb Q_3 by v^5 and is rejected by the independent expected-coefficient comparison. The degree test is performed before that injection, but the later coefficient comparison still decisively rejects the injected error under both interpreter modes.

The checker writes its symbolic output files in its own directory; its description “writes no repository files” is accurate for this scratch-package workflow but should not be interpreted as “writes no files.”

### Independent algebra route

`independent_check.py` does not use H_s, the Euler-operator expansion, or the author’s coefficient-generation routines. It starts from the exact identity R(R^n)'=nR'R^n. With C_m(h)=h^m[z^m]R(z)^(1/(kh)), its recurrence is

m C_m = sum_j a_j ((j/k)h^(j−1)+(j−m)h^j) C_(m−j).

It multiplies by the direct finite product of geometric-series expansions of (1−ih)^−1, and then computes log Phi directly as a series in v. Exact h-polynomial arithmetic through order four, for general symbolic k, matches Q_1,...,Q_4 through v^12. The fourth probability coefficient is then reconstructed by an independent scalar exponential recurrence at v=−1. The global degree theorem is the proof that checking those finitely many v coefficients exhausts these orders; the code is a diagnostic, not a replacement for that theorem.

The same program enumerates all rank words for (n,k)=(1,2),(2,2),(3,2),(2,3),(3,3),(4,2), totaling 1, 6, 90, 20, 1680, and 2520 words in the respective cases, and checks every factorial-PGF coefficient against the exact combinatorial formula. Rank words are equiprobable because each lifts to exactly (k!)^n labeled permutations.

Independent output and complete executable source are saved alongside this audit. The checker is self-contained apart from SymPy and uses explicit target formulas transcribed from the note, with no dependency on the author’s generated coefficient files. Normal and optimized runs both exit zero and produce byte-identical output.

## Issues reported and resolved

1. The tail cutoff L was initially stated only as L≥0 despite use of L! and a discrete sum. The author changed it to “every integer L≥0.” Verified in the reviewed snapshot.
2. The checker initially referred to `proof.md`, whereas the proof file is `repair_note.tex`. The author corrected the docstring. Verified in the reviewed snapshot.

Neither issue affected the substantive proof or computed coefficients. No unresolved mathematical or checker defect was found.

## Remaining boundaries

- Fixed k, fixed truncation order, and compact v sets only
- Higher cumulant order and local probability index fixed before taking n→∞
- No growing-k uniformity or exponentially improved/optimally truncated expansion established
- No explicit finite-size total remainder constant for the fully collected analytic expansion or certified integer-inverse threshold supplied
- No proof of historical novelty, complete bibliography, repository provenance beyond manifest-byte agreement, or formalization

These boundaries agree with the repair's own stated scope and do not prevent closure of the original uniform-tail gap.

## Final cosmetic sealing addendum

After the mathematical review, the author changed the TeX rendering of the CLI flag from `\texttt{--inject-error}` to `\texttt{-{}-inject-error}` so the PDF preserves two ASCII hyphens rather than forming an en-dash ligature. This is a typography-only change; no mathematical claim or checker logic changes. I verified the corrected flag and the final `repair_note.tex` SHA-256: `2016c387bec22d70a616e31c9034fd08ff7860e5e9f4f3b971fc35a9d878f9a7`. The pass verdict is unchanged.
