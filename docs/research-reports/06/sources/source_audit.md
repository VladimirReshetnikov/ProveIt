# Source and novelty audit

Audit date: 18 September 2026.

## 1. Exact input target

Input: `input/turing_degrees_unified.tex`, unchanged user-supplied source.
Section 5, C1, asks whether every nonuniform coarse class contains a
representative whose Turing degree is below that of every other representative.
It gives a nonzero coarse class containing a Turing minimal pair as a
sufficient counterexample strategy. The present article follows this exact
formula and retains the distinction between least and minimal.

The source's C2 uses effective-dense descriptions with explicit omissions
but no wrong numerical answers. That problem is not settled by the argument.
The original file is preserved, including its inherited open-status labels;
the status correction is in the new article, not silently inserted into it.

## 2. Gerdes: the displayed question really is present

Peter M. Gerdes,
*Comparing Notions of Dense Computability on omega^omega and 2^omega*.
arXiv:2508.06925v1, 9 August 2025.

- Abstract/version page: https://arxiv.org/abs/2508.06925
- HTML: https://arxiv.org/html/2508.06925v1
- PDF: https://arxiv.org/pdf/2508.06925
- Location: Question 7, printed page 64 (PDF index 63).

The displayed question explicitly uses `g equivalent_nc f` and asks that
every `g' equivalent_nc f` be Turing above g. This was checked in parsed
text and in a rendered screenshot of page 64. Thus the selected C1 is not
an accidental reinterpretation of a different question in this source.
The paper's broad question also mentions effective-dense degrees, which
must be separated from the coarse clause.

## 3. Older result already supplies the basic negative answer

Denis R. Hirschfeldt, Carl G. Jockusch Jr., Rutger Kuyper, Paul E. Schupp,
*Coarse reducibility and algorithmic randomness*.
Journal of Symbolic Logic 81 (2016), 1028–1046.
DOI: 10.1017/jsl.2015.70.

- arXiv: https://arxiv.org/abs/1505.01707
- arXiv HTML: https://arxiv.org/html/1505.01707
- May 2015 PDF: https://arxiv.org/pdf/1505.01707
- Author's publication page:
  https://www.math.uchicago.edu/~drh/Papers/coarsereducibility.html
- Later preprint reached by following the author's preprint link:
  https://www.math.uchicago.edu/~drh/Papers/Papers/coarsereducibility.pdf
- Journal page:
  https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/coarse-reducibility-and-algorithmic-randomness/68A8F59E5FAC65460C9FAFEB9E6ACCA1

Theorem 4.2 says that if X is 1-generic, every set computable from all coarse
descriptions of X is computable. It occurs on printed page 16 in the
20-page May 2015 preprint, and on printed page 19 in the 23-page preprint
dated 8 October 2015. The theorem was checked in the arXiv HTML and parsed
PDF text, and again in the later author-hosted preprint. Attempts to obtain
web screenshots of the HJKS pages returned cache-miss errors; the successful
Gerdes screenshot should not be confused with visual inspection of HJKS.
Publication details were checked on the author's page and the journal page.

The bridge to C1 is proved in the new article, Proposition 2.3: every coarse
description of X is itself uniformly coarse equivalent to X. A least
representative would therefore be computable from every such description,
so its graph would be computable by Theorem 4.2. That would make X coarsely
computable, contradicting 1-genericity. This also applies to natural-valued
representatives, not only binary ones.

No priority claim is made for this implication. The new report does not
claim that Gerdes accepted this observation, that an erratum exists, or
that any correspondence with the authors took place.

## 4. Independently developed mathematical content

The finite-extension proof in the new report is independent of HJKS's
cone-avoiding compactness theorem. Its ingredients are proved in full:

1. A one-bit connectivity trilemma for two oracle functionals.
2. A global all-prefix variation budget and a buffering operation.
3. A lifting lemma extending a selected pair's suffixes to an entire frontier.
4. A 0''-computable two-path construction and a perfect-family fusion.
5. Equality of the representative Turing spectra for density, uniform coarse,
   and nonuniform coarse equivalence.
6. A block-code characterization of least-degree existence.
7. The bounded/unbounded budget dichotomy and two supplementary corollaries.

Sparse coding and robust repetition codes have classical antecedents; the
article does not claim to have invented those methods. The supplied input
already includes a sparse-coding upward-closure lemma.

Targeted searches included combinations of:
`Turing minimal pair density`, `minimal pair coarse descriptions`,
`1-generic minimal pair perfect`, `minimal pairs Hamming computability`,
`minimal pair symmetric difference`, and `coarse least Turing degree`.
They identified relevant coarse-reducibility literature but did not identify
the precise arbitrary-budget common-variation perfect-family theorem stated
here. Search non-detection is not evidence sufficient to establish novelty.

## 5. Certification status

The article contains a complete conventional proof of its claims, subject
to ordinary mathematical review. No external expert review, Lean kernel
check, or real halting-oracle execution is asserted. Executed finite checks
are supplied and their limited scope is documented. The basic negative
answer to C1 has the independent older-theorem route as well as the direct
construction route; the quantitative refinement relies on the direct proof.
