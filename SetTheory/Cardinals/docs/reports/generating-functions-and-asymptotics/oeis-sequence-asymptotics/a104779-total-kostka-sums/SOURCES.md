# Public sources and attribution

The article uses the public sources below. These notes state the source boundary;
they do not certify global novelty. Sources were checked on 5 October 2026.
No third-party PDF is redistributed in the package.

## Counting sequences and indexing

- [A104779](https://oeis.org/A104779) is the ordinary total Kostka sum, with
  offset zero and the symmetric sorted-positive-margin matrix interpretation
- [A178718 official record](https://github.com/oeis/oeisdata/blob/main/seq/A178/A178718.seq)
  explicitly identifies it as a duplicate of A104779. Its offset is one;
  positive indices agree without shifting
- [A321652](https://oeis.org/A321652) counts nonnegative rectangular matrices
  with positive weakly decreasing row and column margins, offset zero
- [A068313](https://oeis.org/A068313) is the binary companion, offset one.
  The package uses the empty-object value at zero only as an explicitly labelled
  extension

The short fixtures support exact checks through n=20. They are not fitted
asymptotic data or a claim that a published entry lacks all relevant literature.

## Exact enumeration foundation

Ludovic Schwob, [On the enumeration of double cosets and self-inverse double
cosets](https://arxiv.org/abs/2506.04007), arXiv:2506.04007v1, 4 June 2025.
The [actual full text](https://arxiv.org/html/2506.04007v1#S4.SS3) was inspected.
Section 3.1 gives the permutation square-root cycle formula; Section 4.3,
equations (4.5)-(4.8), supplies the exact Kostka-total/Young-subgroup identity
and cycle-index product; equations (4.9) and (4.11) give the companion sums.
These exact identities and their counting interpretations are prior work.

The journal publication is *Advances in Applied Mathematics* 173 (2026),
102982, [DOI](https://doi.org/10.1016/j.aam.2025.102982). Its full text returned
an access error and was not compared with the arXiv text. No absence claim
about an unexamined journal revision is made.

## Classical involution asymptotics

Leo Moser and Max Wyman, [On solutions of x^d=1 in symmetric groups](https://doi.org/10.4153/CJM-1955-021-8),
*Canadian Journal of Mathematics* 7 (1955), 159-168. The publisher PDF was
inspected; equations (3.39)-(3.40) give the complete saddle framework and initial
corrections. OCR makes the modern reference below preferable for the displayed
normalization.

Moser and Wyman, *Asymptotic Expansions*, *Canadian Journal of Mathematics* 8
(1956), 225-233. The publisher PDF was inspected, including the Gaussian
polynomial remainder method in Section 3:
[publisher source](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/F0799E705A46C05A47ACC202E8176A0D/S0008414X00036701a.pdf/div-class-title-asymptotic-expansions-div.pdf).

Folkmar Bornemann, [Asymptotic Expansions Relating to the Lengths of Longest
Monotone Subsequences of Involutions](https://arxiv.org/html/2306.03798v5#A3),
Appendix C, equation (120), explicitly corroborates the first three nonconstant
multiplicative coefficients. [Published article](https://doi.org/10.1080/10586458.2024.2397334).
The separate longest-subsequence distribution assumptions elsewhere in that
article are not used for this coefficient expansion.

## The exact two-sector refinement

[NIST DLMF 12.5.1](https://dlmf.nist.gov/12.5.E1) supplies the precise
parabolic-cylinder integral normalization. The half-axis involution moments
are n! exp(-1/4) U(n+1/2,-sigma)/sqrt(2 pi). The normal-moment split and its
alternating sign are derived directly in the appendix.

F. W. J. Olver, [Uniform asymptotic expansions for Weber parabolic cylinder
functions of large orders](https://doi.org/10.6028/jres.063B.014), *Journal of
Research of the National Bureau of Standards B* 63B (1959), 131-169. Section 11,
particularly equations (11.7)-(11.10), was checked in the original NIST PDF's
indexed text; the formulas were also checked in the clean modern transcription
[DLMF 12.10(v)](https://dlmf.nist.gov/12.10.v). Substitution of the two arguments
in the article gives the classical separate large-order sectors. The present
result transfers them through the Kostka support expansion, with an elementary
real-saddle proof and separate fixed-order remainders.

## Scope of the present development

The public article supplies the global support bound and fixed-support
stabilization for the Kostka aggregate, the coefficient-tail algorithms,
controlled inverse with rounding qualifications, joint geometric margin law,
and corresponding factorial companion analysis. General saddle asymptotics,
the exact cycle index, and the involution counting method are not presented as
new inventions. The results concern every fixed algebraic order, including each
of two exactly defined half-axis sectors. They do not establish optimal
truncation, all further exponential effects, or Stokes/resurgence theory. No
explicit numerical asymptotic onset or certified finite-input inverse is supplied.

The package contains no private review notes or private source locations.
