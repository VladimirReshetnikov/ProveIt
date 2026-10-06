# Public sources and attribution

Source checks were performed on 5 October 2026. The package redistributes no
third-party paper. The research article proves its analytic assertions
self-containedly; these notes distinguish prior exact identities, prior
asymptotic results, and bounded source checks.

## Exact model

- https://oeis.org/A138178 defines symmetric nonnegative integer matrices with
  no zero rows or columns and total entry sum n. Positions are ordered and
  distinguished. The entry also gives the normal semistandard-tableau
  interpretation and the geometric-weight generating function, credited to
  Vladeta Jovovic, 9 December 2009. The displayed prefix n=0..24 was used for
  exact verification. The entry's sequence-specific revision in the inspected
  official record was 18 December 2022. Its global site-footer date is not a
  sequence-specific revision date
- Official record:
  https://github.com/oeis/oeisdata/blob/main/seq/A138/A138178.seq
- https://oeis.org/A135588 is the symmetric binary companion. Its displayed
  prefix was separately checked. Official record:
  https://github.com/oeis/oeisdata/blob/main/seq/A135/A135588.seq
- The linked A138178 b-file through n=500 was attempted during source research
  but the web retrieval returned a cache-miss. This package does not claim
  independent comparison of all 500 official terms. Larger internally exact
  computations are not a substitute for that external comparison

## Established binary asymptotics and collision precedent

Peter Cameron, Thomas Prellberg and Dudley Stark, Asymptotics for incidence
matrix classes, Electronic Journal of Combinatorics 13 (2006), R85.

- https://doi.org/10.37236/1111
- https://arxiv.org/abs/math/0510155
- https://arxiv.org/pdf/math/0510155
- Published author PDF: https://webspace.maths.qmul.ac.uk/t.prellberg/papers/pub051.pdf

The actual 4 April 2006 version was inspected. Section 4, Proposition 4.2,
printed pages 14-15 in that version, proves the symmetric binary leading
constant exp(-log(2)-(log(2))^2/4), with the involution and ordered-Bell
normalization. The binary leading formula in Report238 is explicitly a
recovery of that known result.

Section 2, PDF pages indexed 7-8 in the inspected version, obtains a
Poisson((log(2))^2/2) collision limit for pairs of random preorders in the
nonsymmetric binary-incidence argument. This is relevant methodological
precedent, and the report does not claim that Poisson collision mechanisms
are new. The inspected statement is not the diagonal/off-diagonal joint
collision law of the uniform symmetric nonnegative model considered here.

## Related models actually inspected

- Emanuele Munarini, Maddalena Poneti and Simone Rinaldi, Matrix Compositions,
  JIS12 (2009), 09.4.8:
  https://cs.uwaterloo.ca/journals/JIS/VOL12/Rinaldi/rinaldi.pdf
  The paper's ordered rectangular matrices, fixed-row asymptotics, and
  palindromic rows do not impose square transpose symmetry
- Giulio Cerbai and Anders Claesson, Enumerative aspects of Caylerian
  polynomials, actual author version 30 July 2025:
  https://akc.is/papers/047-Enumerative-aspects-of-Cay-polys.pdf
  arXiv metadata: https://arxiv.org/abs/2411.08426
  Its exact packed-matrix/Burge-polynomial framework was inspected; it is not
  used as a proof of this report's symmetric saddle theorem

## Bounded duplicate boundary

The actual current source of the existing ordered matrix-composition report
was inspected, rather than relying on its title. Its fixed-row rectangular
model and lack of transpose symmetry differ from A138178. Existing reports
169 (A261784 packed matrices) and 177 (A262810 diagonal alignments) were read
at their definitions and relevant results and likewise concern different
models. Exact-ID/title and targeted semantic checks found no direct matching
report. Selected complete repository subtrees and relevant primary papers
were checked; a truncated whole-repository tree was not treated as an absence
certificate.

These checks are bounded negatives. No statement here establishes worldwide
priority, excludes inaccessible versions or unpublished work, or turns the
absence of an asymptotic formula on an OEIS page into a literature theorem.
The novel-content boundary is the set of results actually proved in this
report, with the established sources above credited expressly.
