# Literature and source audit

Checked September 19, 2026.

## The chosen open question

Harry Altman, *Bounding finite-image sequences of length omega^k*.

- Version checked: arXiv:2409.03199v2.
- ArXiv revision date: March 10, 2026.
- Date printed on the manuscript: March 9, 2026.
- Specific location: Example 3.15, printed page 10 (zero-based PDF page 9).
- Primary source: https://arxiv.org/abs/2409.03199v2
- HTML: https://arxiv.org/html/2409.03199v2
- PDF: https://arxiv.org/pdf/2409.03199v2

This example gives the binary antichain upper bound omega^(omega^4), leaves
its sharpness unverified, and improves the binary chain upper bound to
omega^(omega^3). Both the HTML formulas and a rendered PDF page were checked.
The abstract page's submission history listed v1 (September 5, 2024) and v2
(March 10, 2026), with v2 latest at the time of checking.

The question is a precise finite-alphabet sharpness gap, not an assertion
that all the general transfinite-word problems in the paper have been solved.

## Classical inputs

D. H. J. de Jongh and Rohit Parikh, *Well-partial orderings and hierarchies*,
Indagationes Mathematicae (Proceedings) 80(3), 195-207 (1977).
DOI: https://doi.org/10.1016/1385-7258(77)90067-1

Diana Schmidt, *Well-Partial Orderings and their Maximal Order Types*, in
*Well-Quasi Orders in Computation, Logic, Language and Reasoning*, Trends in
Logic 53, 351-391 (2020), a reprint of the 1979 work.
DOI: https://doi.org/10.1007/978-3-030-30229-0_13

Graham Higman, *Ordering by divisibility in abstract algebras*, Proceedings of
the London Mathematical Society, series 3, 2(1), 326-336 (1952).
DOI: https://doi.org/10.1112/plms/s3-2.1.326
Cited for the well-quasi-order assertion behind the finite Higman formula.

The classical maximal-order-type product formula and the finite-alphabet
Higman formula are also explicitly stated in Altman's Section 2 and
Theorem 2.3. The rendered PDF page 3 was checked for these formulas.
The present argument imports these established results, rather than treating
the computer checks as replacements for them.

## Related work

Alakh Dhruv Chopra and Fedor Pakhomov, *Well-quasi-orders on finite trees and
transfinite sequences*, arXiv:2602.09830v1, 10 February 2026.
https://arxiv.org/abs/2602.09830v1

This studies the limit cutoff omega^omega through finite trees. The present
article addresses the finite cutoff omega^2 and the explicitly identified
two-letter example, so the two lines of work are complementary. It is recorded
as related work, not as an input to the proof and not as a source of the
finite-poset formula.

## Merge provenance

This report is the merge of two independently produced research reports,
`order-types-below-omega-squared` and `guarded-periodic-blocks`, both dated
19 September 2026 and both prepared with ChatGPT for Vladimir Reshetnikov. The
two reports checked the same source, Altman arXiv:2409.03199v2 Example 3.15,
and reached the same formula by the same core argument. Neither carried an
independent literature search beyond the one recorded above, so the merged
report inherits exactly the same, limited, priority position. Where the two
reports worded a caveat differently, the more cautious wording was kept.

## Search limitations and priority

Targeted web searches used the arXiv identifier, title, author, the binary
sharpness case, finite alphabets, maximal order types, and downsets. No later
resolution of this exact question was identified. Such a search cannot rule
out unpublished proofs, material not indexed by the search system, or an
equivalent result stated in different terminology.

Accordingly the result is presented as an unrefereed **proposed solution**.
It has not been submitted to or reviewed by Altman or another expert, and no
priority claim beyond the derivation in this research session is certified.
Broader contemporary work on transfinite words was considered during problem
selection but is not an input to the proof or evidence of its correctness.

No source article PDF is redistributed in this archive.
