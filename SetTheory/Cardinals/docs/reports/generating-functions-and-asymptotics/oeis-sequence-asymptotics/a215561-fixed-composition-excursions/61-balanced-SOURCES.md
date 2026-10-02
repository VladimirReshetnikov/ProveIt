# Sources and claim provenance

Source check: October 1, 2026. This is a bounded literature and repository audit, not an exhaustive priority search. Sources are cited within the article; this file records the provenance of the package and its external data.

## OEIS definitions, posted claims, and reference terms

1. OEIS A215561: https://oeis.org/A215561
   - Definition of the array of prefix-average multiset permutations.
   - Vaclav Kotesovec's September 7, 2016 conjecture for fixed-row asymptotic growth.
   - Cross-references connecting the rows to the entries below.
   - The fixed-row formula was still labeled a conjecture when checked.

2. OEIS A215562: https://oeis.org/A215562
   - Fourth-row definition and initial terms.
   - The leading constant credited to Kotesovec on January 31, 2015.
   - The article does not claim discovery of that posted constant.

3. OEIS A215570: https://oeis.org/A215570
   - Fifth-row definition and initial terms.
   - The leading asymptotic credited to Kotesovec on September 6, 2016.
   - A conjectured order-three, degree-fifteen recurrence posted by Manuel Kauers and Christoph Koutschan in March 2023.
   - The article neither assumes nor proves this particular recurrence.

4. OEIS A215571: https://oeis.org/A215571
   - Sixth-row definition and initial reference terms.

5. OEIS A215593: https://oeis.org/A215593
   - Seventh-row definition and initial reference terms.

6. A215570 b-file: https://oeis.org/A215570/b215570.txt
   - Table credited to Manuel Kauers and Christoph Koutschan; the entry credits terms 0..47 to Vaclav Kotesovec.
   - The package uses its n=20 and n=50 terms for numerical diagnostics only.
   - These two terms are explicitly marked as external data; all reported n<=16 fifth-row terms were independently enumerated by the supplied program.

The exact initial reference arrays embedded in `code/verify.py` come from the corresponding OEIS entries. The count-vector dynamic program is an independently written implementation of the recurrence proved in the article. It does not use a guessed univariate recurrence.

## Primary mathematical literature

Manuel Kauers and Christoph Koutschan, *Some D-Finite and Some Possibly D-Finite Sequences in the OEIS*, Journal of Integer Sequences 26 (2023), Article 23.4.5.

- https://cs.uwaterloo.ca/journals/JIS/VOL26/Koutschan/kout4.pdf
- Section 6.1, printed pages 29-30, was inspected in both parsed text and page images.
- This section explains the growing transfer matrix, leaves the specific A215570 recurrence conjectural, and asks for a provably correct recurrence for A215562.
- Our all-row D-finiteness argument establishes existence, not the specific operator of Conjecture 15.

Cyril Banderier and Philippe Flajolet, *Basic analytic combinatorics of directed lattice paths*, Theoretical Computer Science 281 (2002), 37-80.

- DOI: 10.1016/S0304-3975(02)00007-5
- https://www-lipn.univ-paris13.fr/~banderier/Papers/tcs_banderier_flajolet_2002.pdf
- Classical basis for the small-kernel-root formula, the bridge/excursion logarithmic relation, and the length-conditioned excursion framework.
- Relevant formula pages were inspected as images as well as text.
- The article supplies the kernel and logarithmic arguments in its own notation and then performs the additional fixed-composition extraction. It does not present the underlying kernel method or the ordinary length-conditioned contact law as new.

Leonard Lipshitz, *The diagonal of a D-finite power series is D-finite*, Journal of Algebra 113 (1988), 373-378.

- DOI: 10.1016/0021-8693(88)90166-4
- The diagonal closure theorem is an explicitly cited classical input. It is not reproved or claimed as a new theorem of this package.

Ferdinand Lindemann, *Ueber die Zahl pi*, Mathematische Annalen 20 (1882), 213-225.

- DOI: 10.1007/BF01446522
- Transcendence of pi is used, together with the proved asymptotic constant, in the even-alphabet generating-function transcendence argument.

## ProveIt repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected snapshot:

    40b17f2fc79a10a6fc1a50ca9c0c3d6f77be69e5

Directly inspected file:

    Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md

Pinned source:

https://github.com/VladimirReshetnikov/ProveIt/blob/40b17f2fc79a10a6fc1a50ca9c0c3d6f77be69e5/Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md

Access used the connected GitHub tools. The README's exact-core, remainder-transport, and staircase-inversion organization informs the article's inversion section. Its own formalization status boundaries are respected. No Lean module was imported, compiled, or treated as a formal verification of the present excursion results.

Repository searches for A215561 and A215562 returned no matches. This narrow identifier search is not an exhaustive nonduplication claim for the repository.

## Results developed in this package

The written proofs address the all-row fixed-composition asymptotic with its algebraic root-product constant; complete inverse-power expansions and algebraicity of their normalized coefficients; all-row D-finiteness; transcendence of every row generating function with r>=3; the explicit r=5 first correction; a fixed-composition contact law; centered rational composition rays; and exact-core asymptotic inversion.

The article separates these deductions from the classical tools and the previously posted fourth- and fifth-row leading constants. No proof of the precise package results was identified in the targeted source search. This statement describes the search result, not a guarantee of worldwide novelty or priority.

## Verification boundaries

- `code/verify.py` independently enumerates the finite count boxes listed in the article, compares reference terms, and checks bridge-logarithm identities exactly.
- `code/derive_alpha5.py` reproduces the sextic elimination and first-correction contractions in exact symbolic arithmetic.
- Multiprecision root values and asymptotic tables are numerical diagnostics, not interval certificates.
- None of these finite tests proves an asymptotic theorem, verifies a Lean development, or establishes the conjectured A215570 operator.
- The manuscript is not externally peer-reviewed, and its mathematical arguments remain available for independent scrutiny.
