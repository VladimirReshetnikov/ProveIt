# Sources and version audit

Access date: September 19, 2026.

## 1. Selected published conjecture

Marco Ripà, *The congruence speed formula*, Notes on Number Theory and Discrete Mathematics 27(4) (2021), 43–61.

- Publisher landing page: https://nntdm.net/volume-27-2021/number-4/43-61/
- Journal PDF: https://nntdm.net/papers/nntdm-27/NNTDM-27-4-043-061.pdf
- DOI: https://doi.org/10.7546/nntdm.2021.27.4.43-61
- Author-version record: https://arxiv.org/abs/2208.02622v1
- Author-version PDF: https://arxiv.org/pdf/2208.02622v1
- Author-version HTML: https://arxiv.org/html/2208.02622

Version distinction: the claim is Conjecture 2 on journal page 57, but Conjecture 4.1 on arXiv page 14. The preceding definition describes the prime set ((k+1)*10^n-1), with n>=1 and k>=0. The source's speed convention compares the stable counts at heights h-1 and h.

Both the conjecture and its prime-set definition were checked on rendered PDF pages. The numbering difference is real, not an inferred renumbering.

## 2. Later work checked to avoid claiming known results

Marco Ripà and Luca Onnis, *Number of stable digits of any integer tetration*, Notes on Number Theory and Discrete Mathematics 28(3) (2022), 441–457.

- Publisher: https://nntdm.net/volume-28-2022/number-3/441-457/
- DOI: https://doi.org/10.7546/nntdm.2022.28.3.441-457
- Record: https://arxiv.org/abs/2210.07956v1
- PDF: https://arxiv.org/pdf/2210.07956
- HTML: https://arxiv.org/html/2210.07956v1

Relevant material: Corollary 2.2 states eventual-speed formulas; Section 2.2 discusses stable-digit bounds and onset behavior. Its displayed base 781249 has a nontrivial transient, but it is composite (7*233*479). The present article expressly credits the prior eventual-speed formula and the prior study of delayed stabilization.

The publisher PDF retrieval timed out in this session; the author-version PDF and HTML were used instead. The relevant displayed examples were checked on a PDF screenshot.

## 3. The second selected source: OEIS A324017

OEIS A324017, created by Davis Smith, March 28, 2019.

- Entry: https://oeis.org/A324017
- Internal format: https://oeis.org/A324017/internal

At retrieval on 19 September 2026 the internal header read `#91 Feb 16 2025 08:33:57`, and all three comments were still explicitly labeled conjectures. The retrieved entry defines A(m,n)=T_m(2n-1) modulo (2n)^m. The article writes the three statements out as C1, C2 and C3, proves the first two — each in a strictly stronger form than stated — and disproves the third in every case n>1, m>1. The entry's own displayed array establishes the row-height/column-n convention.

C3 asserts a congruence for j and then an equality with j. The article fixes j as its least nonnegative representative, which is the strongest natural interpretation available to the statement; literal equality with an arbitrary congruent integer would already be meaningless. C3 is false even under that reading.

The website-wide last-modified footer is not interpreted as the revision date of this individual entry. The displayed conjectural labels establish the source status at retrieval, not that no previous proof or correction exists elsewhere.

The entry's old link to Crux Mathematicorum, Problem 559, redirected to the journal landing page during an additional check. That linked item is **not** used as evidence for any theorem or priority claim in this package.

No edit, comment or submission has been made to OEIS as part of producing this package. Appendix C of the article proposes replacement text for the three comments; it has not been sent anywhere.

## 3a. Background works cited for context, not for proofs

Markus Hittmeir, *A reduction of integer factorization to modular tetration*.

- Record: https://arxiv.org/abs/1707.04919
- Version 3: 13 February 2018.
- Journal: International Journal of Foundations of Computer Science (2020).
- DOI: https://doi.org/10.1142/S0129054120500197

Used for the distinction between the restricted family treated here and general modular tetration. The abstract states a deterministic polynomial-time reduction of squarefree-part computation to modular tetration. The restricted algorithm in this package does not claim to address that general computational problem; the citation marks the boundary of the claim.

István Mező, *The p-adic Lambert W function*.

- Record: https://arxiv.org/abs/1801.00657
- Version 1: 2 January 2018.
- HTML: https://arxiv.org/html/1801.00657v1

Used for the established p-adic Lambert function and its convergence neighborhood. The article re-derives the power-series coefficients and applies the small branch with the sign appropriate to each local component of this tower family. The Lambert section is optional and nothing else in the article depends on it.

## 4. External infinitude theorem

P. G. Lejeune Dirichlet, *There are infinitely many prime numbers in all arithmetic progressions with first term and difference coprime*. Original paper published in 1837; English translation by Ralf Stephan.

- Translation: https://arxiv.org/abs/0808.1408v2

Used only to infer infinitely many primes in each CRT class after its coprimality with the modulus has been proved.

## Search outcome and limits

Targeted searches included the conjecture number and title, “2749 tetration”, “2749 congruence speed”, “congruence speed counterexample”, and A324017 with proof/counterexample terms. No explicit prior resolution of the selected prime conjecture, and none of the three A324017 statements, was located in those searches. Search results were sometimes sparse or irrelevant. This is not evidence that every potentially relevant source has been examined.

Accordingly, the package states a proved refutation of a published conjecture, a proved resolution of the three retrieved OEIS comments, and their consequences — not a certified first resolution of problems known to remain open everywhere as of the access date.

No priority certification, independent peer review, or OEIS submission has occurred as part of producing this package. The results should be assessed through the proofs and reproducible calculations. Source status is reported for the retrieval date, not as a promise that web entries will retain their wording indefinitely.

Third-party full texts are not redistributed in this archive.
