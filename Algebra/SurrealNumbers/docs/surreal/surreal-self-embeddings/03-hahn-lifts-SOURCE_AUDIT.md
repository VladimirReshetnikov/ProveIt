# Source and verification audit

Research date: 3 October 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `b0d4af4f30b24529fec877e2ad4a5952888146e9`

Actual surreal-project path: `Algebra/SurrealNumbers/`.

Inspected through the GitHub connector:

1. Root `README.md` and the surreal-project `README.md`.
2. `docs/surreal/exponential-automorphism-rigidity/README.md`.
3. `Surreal/Foundations/SignSequence.lean`, first 200 lines.
4. `Surreal/Algebra/ExponentialProfile.lean`, first 180 lines.
5. Directory metadata for the exponential-rigidity report.

The sign-sequence source contains the actual universe-indexed carrier,
first-disagreement order, birthday bounds, smallness/non-smallness results,
and the prefix and simplicity relations. This file by itself does not
provide field arithmetic or the normal-form equivalence.

The exponential-profile source contains its detailed theorem inventory,
`OrderedExp`, and the finite displacement-probe proof. The inventory refers
to further generic declarations not all read in their full proof bodies.
The header explicitly lists the actual surreal exponential/natural-valuation
instantiation as pending. That boundary is retained in the article.

No Lean executable was used and no repository dependency/axiom audit was
rerun. The article does not equate a README claim with an independently
verified build. No repository files were modified.

## Principal literature

- Kaplan, Krapp, Serra, *Decomposing the automorphism group of the surreal
  numbers*, arXiv:2509.22374v3. Version submission date: 23 April 2026.
  https://arxiv.org/abs/2509.22374v3
  The relevant PDF page containing Questions 5.4 and 5.6 was also visually
  inspected. HTML rendering dates were not treated as publication dates.
- Bagayoko, van der Hoeven, *Surreal substructures*, Fundamenta Mathematicae
  266 (2024), 25–96; arXiv:2305.02001.
- van den Dries, Ehrlich, *Fields of surreal numbers and exponentiation*,
  Fundamenta Mathematicae 167 (2001), 173–188, and its erratum.
- Kuhlmann, Serra, *The automorphism group of a valued field of generalised
  formal power series*, Journal of Algebra 605 (2022), 339–376.
- Ehrlich, Kaplan, *Surreal ordered exponential fields*, Journal of Symbolic
  Logic 86 (2021), 1066–1115; arXiv:2002.07739.
- Berarducci, Mantova, *Surreal numbers, derivations and transseries*, Journal
  of the European Mathematical Society 20 (2018), 339–390; arXiv:1503.00315.
- Conway and Gonshor's foundational books; Wilkie's model-completeness paper;
  Hamkins's author exposition of class-recursion principles.

Full bibliographic information and relevant links are in `article.tex` and
in the compiled PDF.

The research agenda distinguishes questions in the examined KKS version
from targets proposed by this article. It does not assert that every target
has been exhaustively certified open in the current literature.

## Delivered verification

The finite checks use exact rational arithmetic and a deterministic seed.
They cover finite sign-prefix/order transport, repeated-sign witnesses,
rational lower/upper branch inverses and iterates, finite two-level Hahn
addition/multiplication/order/composition, binomial units, and the finite
displacement probe.

The PDF was compiled with pdflatex through latexmk. Its reference resolution
and LaTeX overflow diagnostics were checked, and rendered pages were visually
reviewed. These production checks are not mathematical peer review.
