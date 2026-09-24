# Sources and status audit

Research date: 18 September 2026. Primary sources were inspected online. The
links below identify sources, not bundled copies of the publishers' papers.

## User-supplied basis

**Turing Degrees: A Unified Research Report**, unified edition 18 September 2026.
The attached file `turing_degrees_unified.tex` is preserved unchanged in `input/`.

Relevant source text:

- Original lines 494 onward: “Coarse and effective-dense representative spectra”.
- C1: the universal least-Turing-representative statement for nonuniform coarse
  equivalence, with representatives in omega^omega.
- The diagnostic proposition proposes a nonzero class containing a Turing
  minimal pair as a sufficient certificate for no least representative.
- C2 explicitly distinguishes effective-dense omission from coarse error.

Our treatment follows those definitions. The historical assessment of C1 is
revised explicitly in the new report; it is not silently inherited as a current
open-status guarantee.

## Gerdes: the exact question

Peter M. Gerdes, *Comparing Notions of Dense Computability On omega^omega and
2^omega*, arXiv:2508.06925v1, 9 August 2025.

- Abstract and version record: https://arxiv.org/abs/2508.06925
- Full HTML: https://arxiv.org/html/2508.06925v1
- PDF: https://arxiv.org/pdf/2508.06925

Section 7, **Question 7**, asks for a least Turing-degree representative and
explicitly displays the nonuniform coarse instance. Definitions 2.3–2.4 specify
coarse descriptions and reductions. Definitions 2.7–2.8 concern effective-dense
notions, which are not settled here.

The question's presence in a 2025 preprint is evidence that it was posed there,
not evidence that its coarse instance is independent of earlier theorems.

## HJKS: the prior result that already implies a negative answer

Denis R. Hirschfeldt, Carl G. Jockusch, Jr., Rutger Kuyper, and Paul E. Schupp,
*Coarse Reducibility and Algorithmic Randomness*, Journal of Symbolic Logic
81(3) (2016), 1028–1046. DOI: 10.1017/jsl.2015.70.

- Author's publication page:
  https://www.math.uchicago.edu/~drh/Papers/coarsereducibility.html
- Preprint record: https://arxiv.org/abs/1505.01707
- Consulted PDF: https://arxiv.org/pdf/1505.01707
- Publisher DOI: https://doi.org/10.1017/jsl.2015.70

In the consulted 20-page author preprint:

- Section 3 defines the intersection of lower cones of all coarse descriptions,
  denoted X with superscript fraktur c; this is K_X in our report.
- Theorem 3.7 (PDF page 10, one-based) is cone-avoiding compactness.
- Theorem 4.3 (PDF pages 16–17, one-based), credited there to Igusa by personal
  communication, says gamma(X)=1 implies the core contains only computable sets.
- Its adjacent discussion records examples with gamma(X)=1 that are not
  coarsely computable.

The source PDF's theorem statements and displayed formulas were inspected in
both parsed text and page rendering where needed. The preprint currently served
has a later manuscript date than the journal publication; theorem numbers in
our article refer to that consulted preprint, not an assumed version number.

### Consequence for C1

If X has trivial core but is not coarsely computable, every least representative
would be below all actual coarse descriptions, hence computable. But a
computable representative would yield a computable coarse description of X.
This contradicts non-coarse-computability. The same implication works for the
uniform class, because every density-zero modification is uniformly equivalent.

This deduction is why the negative C1 answer is **not claimed as a new solution
to a previously unresolved literature problem**. The article's self-contained
proof does not depend on assuming this earlier result.

## Earlier c.e. examples and density diagonalization

Carl G. Jockusch, Jr., and Paul E. Schupp, *Generic Computability, Turing Degrees,
and Asymptotic Density*, Journal of the London Mathematical Society 85(2)
(2012), 472–490. DOI: 10.1112/jlms/jdr051.

- Preprint record: https://arxiv.org/abs/1010.5212
- PDF: https://arxiv.org/pdf/1010.5212
- Publisher DOI: https://doi.org/10.1112/jlms/jdr051

Theorem 2.26 establishes a generically computable c.e. set that is not coarsely
computable. The earlier sections use positive-density computable columns and
separate generic computability from coarse computability. We do not identify
their construction with our gated-column formula or claim that the existence
of such c.e. examples is new.

## The perfect-set step

Jan Mycielski, *Independent Sets in Topological Algebras*, Fundamenta
Mathematicae 55(2) (1964), 139–147. DOI: 10.4064/fm-55-2-139-147.

- Primary publisher record:
  https://www.impan.pl/en/publishing-house/journals-and-series/fundamenta-mathematicae/all/55/2/95633/independent-sets-in-topological-algebras
- DOI: https://doi.org/10.4064/fm-55-2-139-147

The report attributes the Cantor independent-set construction to Mycielski and
proves the precise binary-relation case used. The required Baire and
Kuratowski–Ulam implications are also proved directly in the appendix.

## Novelty-search limits

Targeted searches used combinations of “coarse descriptions”, “least Turing
degree”, “minimal pair”, “exact pair”, “Baire”, “Polish”, and “density zero”.
These searches did not establish a prior publication or priority claim for the
fixed-coordinate exact-pair theorem, the perfect-family formulation, or the
prescribed-principal-core examples as formulated here. This is **not** a claim
that no such prior result exists. The mathematics is presented with proofs;
bibliographic novelty remains unverified.

No emails were sent, no specialist endorsement was obtained, and no external
library or repository was modified.
