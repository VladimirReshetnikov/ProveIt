# Research and evidence audit

## Scope

Requested task: develop probability using surreal probabilities or logits,
with a detailed article and LaTeX/PDF delivery. This is a mathematical
construction and synthesis, not a claim of exhaustive literature priority.
All sample spaces, fields, coefficient supports, and parameter collections
used as objects are set-sized. The full surreal field is treated as an
ambient class, not a sample set carrying a probability distribution.

## Repository snapshot and access

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit:

    d22a5b35d5b3040e870c3cfd6d1c8f7259e094b0

The commit metadata reports 2026-09-23 00:19:23 UTC, which is 22 September
in the user's Pacific time zone. The article uses the local date.

Read through the GitHub connector:

1. `docs/README.md`: report catalogue, reading routes, topology and support
   warnings, and descriptions of the neighboring reports.
2. `docs/surreal/hahn-valued-measures-and-probability/README.md` at the pin:
   the complete maintained guide, including the two additivity regimes,
   the scope of strong atomicity, product criteria, limitations, and review status.
3. `docs/surreal/hahn-valued-measures-and-probability/article.tex`, source
   lines 1–230 at the pin: the report's opening definitions, scope, and framing.
4. The default-branch commit metadata, to establish the exact snapshot.

This is not an independent audit of the full 64-page probability report,
all neighboring articles, or the repository's Lean declarations. Descriptions
of the foundations and Markov reports are supported by the maintained guide;
no complete source review of those two reports is claimed.

The article expressly preserves the distinction that finite-support
standard parts and the omega+1 hidden-negativity threshold are strong-class
statements, not statements about every Hahn-valued probability. Its two
independent-coin nonextension proofs are presented as elementary special
cases, not as new substitutes for the repository's general product criteria.

## Primary literature consulted

The bibliography contains stable publication metadata and links. The web
review used primary author, arXiv, publisher, or institutional pages.

- Van den Dries–Ehrlich, *Fields of surreal numbers and exponentiation*,
  Fundamenta Mathematicae 167 (2001), 173–188,
  DOI 10.4064/fm167-2-3: the official IMPAN abstract supplies the elementary
  real-exponential-field statement used for scalar inequalities. The
  erratum in volume 168 (2001), 295–297 is explicitly listed; no ordinal
  length estimate from the original paper is used.
- Gonshor, *An Introduction to the Theory of Surreal Numbers* (1986), and
  Conway, *On Numbers and Games*: standard scalar foundations, cited as
  foundational books rather than represented as newly downloaded full texts.
- Bournez–Guilmant, arXiv:2201.08199: manuscript and selected rendered pages
  concerning set-sized exponential/logarithmic surreal fields.
- Benci–Horsten–Wenmackers, arXiv:1106.1524; published in Milan Journal of
  Mathematics 81 (2013), 121–151, DOI 10.1007/s00032-012-0191-x:
  manuscript and publisher metadata; precedent for all-subsets
  non-Archimedean probability with a different infinite-addition rule.
- Halpern, arXiv:cs/0306106 and the Cornell author manuscript `lex.pdf`;
  Games and Economic Behavior 68 (2010), 155–179: finite and infinite
  distinctions among lexicographic, conditional, and nonstandard probability.
- Brickhill–Horsten, arXiv:1608.02850: the preprint and its HTML version,
  including the fine-ultrafilter and conditional-probability connections.
  The article cites the preprint's title and does not guess a later journal citation.
- Hammond, DOI 10.1007/978-94-011-0774-7_2: official publisher abstract and
  metadata explicitly identify extended logarithmic likelihood ratios as
  prior literature. No first surreal/non-Archimedean logit claim is made.
- Spohn, *Ordinal conditional functions* (1988): primary institutional
  publication record and manuscript source. Ordered-group valuations in the
  present article are not identified with ordinal arithmetic.
- Loeb, Transactions of the AMS 211 (1975), 113–122,
  DOI 10.1090/S0002-9947-1975-0390154-8: official indexed metadata was
  available, but direct AMS page/PDF access failed. The article states the
  standard internal/saturation framework and gives the short premeasure
  argument; it does not claim a fresh full-text audit of Loeb's paper.
- Kallenberg, *Foundations of Modern Probability*, third edition (2021),
  DOI 10.1007/978-3-030-61871-1: official metadata and table of contents.
  Ordinary real disintegration, product laws, and strong laws are explicitly
  imported standard results, not purportedly re-proved surreal analogues.

No bibliography entry is a certification that every theorem in its source
has been independently checked. No named published conjecture is claimed
resolved, and no absence claim about all published literature is made.

## Mathematical checks and limitations

The manuscript was reviewed specifically for:

- Set/class size and the difference between field closure and full transfer.
- Canonical surreal exponential versus the Conway omega-map.
- Nonzero and infinitesimal denominators in conditional formulas.
- The difference between conditional shadows and complete utility preferences.
- Support conditions for Hahn sums and coefficientwise measures.
- Positivity of normalized hierarchical laws and the limits of termwise integration.
- Real conditional kernels supplied as input, with versions and integration order stated.
- Positive finite cylinder laws versus incompatible infinite-extension axioms.
- The scope of ordered-field embeddings: not automatically exponential or internal.
- Finite versus tail observations in the latent-regime martingale example.
- Fine convergence, intrinsic order convergence, coefficient convergence, and Loeb limits.

The final latent-regime discussion distinguishes two failures accurately:
ordered-field convergence fails at infinitesimal resolution on all paths,
while the disagreement between the limit of posterior standard parts and
the tail conditional standard part occurs on the rare regime event, whose
real shadow measure is zero.

## Executable verification

`verify.py` is standalone Python, using fractions and exact polynomial
arithmetic to compute in Q(t). It does not use a small floating-point value
for t. The delivered run passed 2,145 assertions in 19 test families.
The accompanying JSON records the actual counts and Python version.

The finite checks do not prove an infinite theorem. In particular, they do
not implement full surreal arithmetic, exponentiation, strong infinite
summation, uncountable supports, logical compactness, or Loeb saturation.
No new Lean verification is claimed.

## Build and visual review

The final LaTeX build has no unresolved references or citations, no LaTeX
warnings, and no overfull or underfull boxes. The PDF has 35 pages.
Every page was rendered to a contact sheet, with selected pages inspected
at higher resolution, including the title, technical prose, equations,
and the latent-regime/standard-part discussion. A separate geometric scan
checks that text spans stay on the page. Compilation and visual review
are typesetting checks, not mathematical proof certificates.

The delivered archive contains only the finished source, PDF, checks,
results, build script, and documentation. No external font files or
third-party full articles are included. The user's repository was not modified.
