# Primary-source audit

Audit date: 18 September 2026. Sources were inspected directly, including
PDF page images for the displayed questions and older theorem statements.
A targeted search is not an exhaustive specialist novelty review.

## Selected question

Peter M. Gerdes, *Comparing Notions of Dense Computability on omega^omega and
2^omega*, arXiv:2508.06925v1, 9 August 2025.

- https://arxiv.org/abs/2508.06925
- https://arxiv.org/html/2508.06925v1
- https://arxiv.org/pdf/2508.06925

Question 7 is on printed page 64 (zero-indexed PDF page 63). It explicitly
asks for an element of least Turing degree in the coarse/effective-dense
classes, and gives the nonuniform coarse formula used in the paper.
The arXiv record retrieved in this audit listed the v1 submission.

The author-hosted July 2026 ASL North American Meeting slides repeat the
least-Turing-representative question for uniform/nonuniform coarse and
effective-dense degrees:

- https://invariant.org/coarse.pdf
- Slide 45/48; the fully displayed overlay is physical PDF page 93/98
  (zero-indexed page 92).

The source version and slide date establish that the question was displayed
there. They do not establish that no answer could already be deduced from
older work. In fact, such a deduction is explained in this package.

## Older result implying the negative coarse answer

Denis R. Hirschfeldt, Carl G. Jockusch Jr., Rutger Kuyper, Paul E. Schupp,
*Coarse Reducibility and Algorithmic Randomness*.

- Preprint: https://arxiv.org/abs/1505.01707
- PDF: https://arxiv.org/pdf/1505.01707
- Journal: Journal of Symbolic Logic 81(3) (2016), 1028–1046.
- DOI: https://doi.org/10.1017/jsl.2015.70
- Author publication record:
  https://www.math.uchicago.edu/~drh/Papers/coarsereducibility.html

The preprint was submitted on 7 May 2015. Definition 3.1 introduces the sets
computable from every coarse description of X. Theorem 4.2 states that this
collection is exactly the computable sets for a 1-generic X. The preceding
text notes that a 1-generic set is not coarsely computable. Theorem 4.3 gives
trivial common information when the coarse computability bound gamma is 1.
The theorem statements were checked on printed page 16 (zero-indexed PDF
page 15). Section 2 supplies the coarsening-embedding framework.

Our deduction is that a least representative would have to be computed by
every description, hence would be computable, contradicting non-coarse-
computability. The paper distinguishes this deduction from the stronger,
self-contained perfect-family construction it develops.

## Supplied survey

`turing_degrees_unified.tex`, supplied by the user, dated 18 September 2026.
Entry C1 gives the selected formula and proposes a minimal-pair route.
The section on coarse spectra notes that density-zero modifications stay
coarsely equivalent. The present note takes those definitions literally.
It does not treat the survey's inherited open-status label as conclusive
against the older theorem.

## Novelty boundary

Searches focused on combinations of "coarse descriptions", "perfect",
"minimal pair", "least Turing degree", "spectrum", and "infimum", and on
the source papers and author materials. No exact match was identified for
the protected-column perfect-family theorem or the arbitrary-base
unattained-infimum formulation. This negative search result is not a proof
of originality. Related formulations may be standard consequences under
other terminology, and the older coarsening framework is explicitly credited.

No third-party paper or slide deck is redistributed in this archive.
