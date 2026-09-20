# Research status and source provenance (signed-cancellation route)

**One of two audits in this archive.** This file records the sources and the
bounded-search status for the *signed-cancellation* proof of Conjecture 6.3.
The companion file `LITERATURE.md` records the sources and status for the
*finite-state* proof of Conjectures 6.2 and 6.3, including the record of which
printed pages of the source were inspected as rendered images and the
Ekhad-Zeilberger version dating. Neither list contains the other; the article's
bibliography is their union.

Date of this report: September 19, 2026; carried unchanged into the merged
archive on September 20, 2026, except where marked.

## Selected documented problem

Richard P. Stanley, *Theorems and Conjectures on Some Rational Generating
Functions*, arXiv:2101.02131v3, September 30, 2021, Conjecture 6.3,
printed page 24. The journal publication is European Journal of
Combinatorics 119 (2024), article 103814.

- Versioned preprint: https://arxiv.org/abs/2101.02131v3
- PDF: https://arxiv.org/pdf/2101.02131v3
- HTML: https://arxiv.org/html/2101.02131v3
- Journal DOI: https://doi.org/10.1016/j.ejc.2023.103814

The conjecture states the rational generating function for the number of
odd coefficients of product_(i=1)^n (1+x^(F^(k)_(i+k-1))), with the first
k k-bonacci numbers all equal to one. The actual conjecture page, not merely
a search snippet, was checked. This report uses the arXiv version's numbering.

## Result established by this route

The article supplies an elementary, uniform-in-k proof of that formula,
and proves the same count for every superincreasing seed list continued
by the same recurrence. A key intermediate theorem proves finite-product
flatness for every sign block of length k+1 with product -1, repeated
periodically. The article also derives exact recurrences, a finite
multinomial expression, asymptotic growth, and algorithms.

This is a claim about the mathematical argument presented here, not a
claim that a journal, author of the original conjecture, or independent
reviewer has accepted it. The proof has not been formally verified in Lean
or another proof assistant.

## Prior work that must not be presented as new

1. Yufei Zhao proved flatness of truncated all-minus Fibonacci products
   (the order-two situation).
   *The coefficients of a truncated Fibonacci power series*, Fibonacci
   Quarterly 46/47 (2008/2009), 53-55.
   https://yufeizhao.com/research/fibprod.pdf
   https://doi.org/10.1080/00150517.2008.12428188

2. Hansheng Diao introduced the quasifibonacci seed conditions used here
   and proved flatness for the infinite all-minus product for even order.
   *A poset structure on quasifibonacci partitions*, arXiv:0802.1293v1
   (2008), Definition 1.1 and Theorem 1.1.
   https://arxiv.org/abs/0802.1293
   https://arxiv.org/pdf/0802.1293

3. The order-two counting sequence is already represented by OEIS A104767:
   h_2(n) = 2*A104767(n) for n >= 1, with h_2(0)=1 separately.
   https://oeis.org/A104767

4. Symbolic-generation work by Ekhad and Zeilberger and the separate
   challenge solved by Tang and Xin are neighboring results, not targets
   newly resolved by this archive:
   https://arxiv.org/abs/2103.12855
   https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/stern.html
   https://arxiv.org/abs/2506.13375

## Search and priority limitations

The bounded literature search examined the primary sources above and
searched for the precise conjecture, paper identifier, and related
quasifibonacci parity/flatness results. No later proof of the specific
all-order parity generating function was located. Search results can omit
relevant literature; this is not proof of an exhaustive priority claim.

In particular, this archive does not certify that the conjecture remained
open everywhere immediately before this report. The selected version
explicitly states it as a conjecture, and the present archive supplies an
independently developed, self-contained argument for its statement.
Historical novelty should be checked more fully before publication.

## Boundaries

- The signed-cancellation argument does NOT prove Stanley's rationality
  conjecture for every modulus. For moduli greater than two, changing a
  factor's sign no longer leaves its residue unchanged, so the parity lift is
  unavailable in this form. (Added September 20, 2026: that conjecture is
  addressed in this archive only by the separate finite-state argument
  audited in `LITERATURE.md`. Nothing in the present route contributes to it.)
- No higher-moment conjecture from the Stanley paper is claimed solved.
- No explicit bijection between colored compositions and odd coefficient
  positions is supplied; their equinumerosity is proved by generating functions.
- Coherent signing is sufficient; all flat signings are not classified.
- Non-superincreasing seed lists are not covered by the theorem.
- The density conclusion of this route concerns all positions from exponent
  zero to the polynomial degree, including zero coefficients. No assertion
  about density among nonzero coefficients only is implicit in it. (Added
  September 20, 2026: the merged article does prove that second statement,
  but only via the support generating function of the finite-state route,
  and only for Stanley's initialization. The two statements are kept as
  separate theorems with their denominators named.)
- Numerical constants use high-precision decimal approximations, not
  certified enclosures; the asymptotic assertions have analytic proofs.
- Exhaustive finite checks supplement but do not replace the proof.

No external paper copies or font files are redistributed in this archive.
