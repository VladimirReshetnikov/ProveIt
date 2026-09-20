# Sources, version provenance, and literature-check limitations

Research date: **20 September 2026**.

This file and its companion `STATUS.md` come from the two packages merged here
(`mu-welker-binomial-decomposition` and `recursive-binomial-real-rootedness`).
Both are retained deliberately: neither alone contains all of the page-level
source audit, the enumerated search queries, the consulted author publication
list, the journal-metadata caveat, and the `f_{i-1}` versus `a_i` indexing
correspondence. Appendix C of the article summarises the union of the two.

## Primary target

Lili Mu and Volkmar Welker, *On a question about real rooted polynomials and
f-polynomials of simplicial complexes*, arXiv:2503.24076v1, 31 March 2025.

- Versioned record: https://arxiv.org/abs/2503.24076v1
- Versioned PDF: https://arxiv.org/pdf/2503.24076v1
- HTML: https://arxiv.org/html/2503.24076v1
- arXiv DOI: https://doi.org/10.48550/arXiv.2503.24076

The mathematical definitions were checked against the PDF, not inferred
from snippets. Section 3.2 on page 5 defines the recursive decomposition.
Question 3.10 is on page 6. Its page image was inspected to confirm the
numbering and wording because the HTML rendering did not retain all theorem
numbers correctly.

Other distinctions checked in that same source:

- Question 1.1 is the Bell–Skandera face-polynomial realization question.
- Conjecture 3.8 concerns the coefficientwise inequalities `h_i <= g_i`.
- Question 3.10 concerns real-rootedness of both canonical outputs.

Only the last question is answered negatively here. The main example
satisfies the coefficientwise inequalities and has an explicit realization
as the face polynomial of a simplicial complex.

### Journal metadata and limitation

The arXiv record and publisher discovery identify the journal version as
*Advances in Applied Mathematics* **175** (2026), article 103041, 16 pages.

DOI: https://doi.org/10.1016/j.aam.2026.103041

The final full text at the publisher could not be inspected with the
available browsing access. The DOI open attempt returned an access error.
Consequently, this package does not assert that the journal version retains
the same question, numbering, or lack of a counterexample. The explicitly
versioned arXiv question is the target of the article.

## Background reference

Jan Vondrák (instructor), Scott Mutchnik (original scribe),
*Lecture 11: Real-rooted Polynomials*, Math 233: Non-constructive methods in
combinatorics, Stanford University, 2018.

https://theory.stanford.edu/~jvondrak/MATH233A-2018/Math233-lec11.pdf

Theorem 11.2 states Newton's inequalities. The article gives its own short
proof of the first inequality, so the new arguments do not require this
reference as an unproved black box.

## Literature check

Queries included the paper title, author names, the arXiv identifier, its
DOI, and combinations of “recursive decomposition,” “real rooted,” and
“counterexample,” as well as searches for the small example. An author's
publications listing was also consulted:

https://www.mathematik.uni-marburg.de/~welker/publications.html

No previous answer was located in these searches. This is not a guarantee
of originality or an exhaustive survey. In particular, inaccessible journal
content, unpublished communications, differently worded results, or
unindexed corrections could contain an earlier answer.

## Mathematical provenance

The definitions of the canonical split and the target question come from Mu
and Welker. The small examples, finite certificate, cubic classifications,
uniform all-degree bound, and scaling-limit arguments in this package were
derived during this work. “Derived during this work” does not certify that
no one previously obtained the same or stronger results.

No third-party full text is redistributed. URLs are provided for source
verification; the article contains the needed definitions and proofs.
