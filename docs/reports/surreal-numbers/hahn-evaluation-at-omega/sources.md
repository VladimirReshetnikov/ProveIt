# Primary sources and version audit

Inspected on 20 September 2026. URLs below are provided for reproducibility;
no third-party paper is included in this archive.

## 1. Selected open question

Paolo Lipparini, *Monotone infinitary operations on ordinals (extended version)*.

- Version-specific record: https://arxiv.org/abs/2505.00424v2
- Version-specific HTML: https://arxiv.org/html/2505.00424v2
- PDF: https://arxiv.org/pdf/2505.00424v2
- Submission history: https://arxiv.org/abs/2505.00424

The record inspected lists v1 (1 May 2025) and v2 (30 April 2026), with no later
version listed. In v2, Problem 7.7 is on printed p. 38, zero-based PDF page 37.
The statement was checked in both parsed text and a screenshot of the PDF page.
It specifies increasing surreal exponent supports and an ordinary ring
homomorphism sending x^a to Conway's omega^a. It does not impose strong
additivity. The earlier formulation is Problem 6.8 in v1, whose title was
*Another infinite natural sum*.

The v2 record explains that this is an extended version of the shortened
journal article *A Monotone Infinitary Operation on Ordinals*, Mathematical
Logic Quarterly 72 (2026), related DOI 10.1002/malq.70019. The answer in this
package is addressed to Problem 7.7 in the extended preprint. It does not
assume that the same question appears in the abridged journal article.

## 2. Normal forms and the classical exponent-reversing embedding

Lou van den Dries and Philip Ehrlich, *Fields of surreal numbers and
exponentiation*, Fundamenta Mathematicae 167(2) (2001), 173–188.

- DOI: https://doi.org/10.4064/fm167-2-3
- Publisher record:
  https://www.impan.pl/en/publishing-house/journals-and-series/fundamenta-mathematicae/all/167/2/89226/fields-of-surreal-numbers-and-exponentiation
- Publisher PDF:
  https://www.impan.pl/shop/en/publication/transaction/download/product/89226

Printed p. 175 states the decreasing-exponent normal-form representation.
Printed p. 176 explicitly displays the canonical map
sum s_gamma t^gamma -> sum s_gamma omega^{-gamma}
for a set-sized additive subgroup Gamma of No. Both pages were inspected
as PDF screenshots. The paper's later results on exponential functions and
birthday bounds are not used here.

## 3. Hahn fields, summability, and Conway's omega-map

Alessandro Berarducci and Vincenzo Mantova, *Surreal numbers, derivations and
transseries*, Journal of the European Mathematical Society 20 (2018), 339–390.

- DOI: https://doi.org/10.4171/JEMS/769
- Inspected preprint: https://arxiv.org/abs/1503.00315v3
- HTML: https://arxiv.org/html/1503.00315v3

The preprint's Sections 2.3–2.6 provide the specific background used:
Hahn supports and convolution; Definition 2.9 on summability; and Fact 2.17
on the ordered-group properties of Conway's omega-map. The normal-form sign
and monomial magnitude conventions agree with the exponent reversal used in
this article. The new derivation and transseries results of that paper are
not needed for this problem.

## 4. Well-quasi-ordering of finite words

Graham Higman, *Ordering by divisibility in abstract algebras*, Proceedings
of the London Mathematical Society, series 3, 2(1) (1952), 326–336.

- DOI: https://doi.org/10.1112/plms/s3-2.1.326
- Publisher record:
  https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/plms/s3-2.1.326

The publisher record was used to verify bibliographic metadata. The article
supplies a complete proof of the well-ordered-alphabet special case it uses;
it does not rely on inaccessible text from this source for an omitted proof.

## 5. References carried from the merged manuscript, not re-verified here

This package is a merge of two independently produced reports. The two
references below appeared only in the second of them, `reversed-hahn-series`.
They are cited in the merged article for standard background only — surreal
normal forms, Hahn operations, the distinction between arbitrary and strongly
additive maps, and the omega-map. Their bibliographic details were **not**
independently re-inspected while preparing this package, and they are
deliberately listed here separately from the version-audited entries above
rather than being folded into them.

Elliot Kaplan, Lothar Sebastian Krapp and Michele Serra, *Decomposing the
automorphism group of the surreal numbers*, arXiv:2509.22374v1, dated
26 September 2025.

- Record as cited: https://arxiv.org/abs/2509.22374v1
- Status: version string and date carried over from the merged manuscript.
  Not checked against the arXiv submission history in this session, so a later
  version may exist.

Olivier Bournez and Quentin Guilmant, *Surreal fields stable under exponential
and logarithmic functions*, arXiv:2201.08199, 2022.

- Record as cited: https://arxiv.org/abs/2201.08199
- Status: no version suffix was recorded in the merged manuscript, so the
  cited record is the version-agnostic abstract page. Not checked in this
  session.

Nothing proved in the merged article depends on either reference. Every
statement attributed to them is also covered by the version-audited sources in
sections 2 and 3 above, which were inspected directly.

## Search boundary

Focused searches included combinations of the author's name, “Problem 7.7”,
“surreal”, “Hahn”, “increasing”, “homomorphism”, and “square root”, together
with inspection of the arXiv version record and the exact problem statement.
No prior resolution was located. Some broad search results were irrelevant
and were not used as evidence.

This is a report of a bounded search, not an assertion of exhaustive coverage.
An unpublished observation, private communication, differently worded answer,
or unindexed later resolution might exist. The correctness of the explicit
algebraic obstruction is independent of this uncertainty about priority.
