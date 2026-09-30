# Arithmetic Convolution Factors of Fabius-Type Laws

**Exact divisibility, fractal remainders, and classification barriers**  
Research manuscript prepared for the ProveIt programme, 28 September 2026.

## Files

- `article.pdf` — the 26-page article, including complete written proofs,
  ten further research questions, a verification ledger, and references.
- `article.tex` — the self-contained LaTeX source used to generate that PDF.
- `verify.py` — deterministic exact finite regression tests; standard library only.
- `verification_results.json` — the successful run's machine-readable output.
- `SOURCES.md` — source locations, repository snapshot, and audit limitations.
- `Makefile` — build, verification, and auxiliary-file cleanup commands.

## Principal results

For strict divisibility ladders A and B starting at 1, let mu_A be the law
of the sum of independent centered unit uniforms divided by A_k. The article
proves that

    mu_A = dilation(c, mu_B) * nu

for a probability measure nu exactly when c = 1/m for a positive integer m
and A_k divides m B_k for every k. The remainder is unique and is explicitly
constructed as an independent random digit series.

Consequences include:

1. Complete geometric cross-base classification for an integer-base target.
2. A compact family of smooth, unscaled convolution divisors of the single
   Rvachev up-law encoding inclusion modulo finite sets. Mutual scaled
   factorability is exactly finite-change equivalence on the encoded sets.
3. No Borel real-valued or countably real-valued complete invariant on that
   compact smooth family.
4. Pi^0_1-completeness at a fixed reciprocal-integer scale and
   Sigma^0_2-completeness for existence of any positive scale, on valid
   primitive-recursive ladder presentations. All the input densities remain
   uniformly computable in every derivative.
5. A finite exact algorithm for certified eventually periodic ratio schedules.
6. Explicit, strictly positive Wasserstein lower bounds at forbidden scales.
7. A complete integer-regularity classification for same-base remainders,
   sharp Fourier power decay, and sharp Holder exponents for separated digits.

## Proof and originality status

All asserted mathematical results have written proofs in the article.
The Python tests check finite arithmetic and finite probability identities;
they do not formally verify the infinite theorems. No Lean compilation,
proof-assistant verification, or peer review is claimed for this package.

The article distinguishes classical facts and identified repository overlaps
from the extensions developed here. In particular, the dyadic sinc product,
its zero multiplicities, and dyadic identical-convolution rootlessness are
not claimed as new. The classical nonsmoothness of finite-change equivalence
is also not claimed as new; the explicit smooth probability-law realization
is the application developed in the article. Originality beyond the reviewed
sources has not been established by an exhaustive priority audit.

The work was generated with ChatGPT assistance. It is a standalone research
manuscript, not a repository modification or a submitted pull request.

## Reproduce

Use Python 3.9 or later for the exact tests:

    python3 verify.py --output verification_results.json

They require no third-party packages, randomness, floating-point arithmetic,
or network access. They raise an exception on any failure. They ran
successfully in preparing this package. The receipt includes 78,732 finite
ladder/scale cases, 65,536 ordered pairs of finite sets, 6,144 periodic
schedule/scale cases, and the additional exact checks described in the paper.

With a standard TeX installation containing the packages named in the
preamble:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

Alternatively run `make all`. No external figures, bibliography database,
network downloads, or font files are needed. The PDF was generated from the
included source and visually checked after rendering. The final typesetting
log had no overfull/underfull box notices, unresolved references, or LaTeX
warnings. Standard PDF timestamps may change on rebuilding.

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `fbba58593dc0622aa914972896150d4848f935b5`.

See `SOURCES.md` for the exact inspected files and limitations. In particular,
the large geometric-q monograph was not fully retrieved. Its unread content
was not used as proof evidence or as a basis for a global novelty claim.

## Editorial amendments (ProveIt, 2026-09-29)

Made in the editorial pass after batch 56 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-29)`.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-29)" is defined in the preamble. A note after the discussion of
  the question "Beyond divisibility ladders" records that the later
  unreviewed draft `../Simultaneous_Convolution_Divisors_Fabius_Type_Laws/`
  answers it for prime-power geometric targets: there zero-divisor
  domination is equivalent to a nested matching and to factorization by a
  probability measure, and its base-six theorem gives the requested
  counterexample (`Unif_{1/2} * Unif_{1/3}` does not divide `mu^[6]`
  although all zeros cancel); targets that are not prime powers remain
  open. The note also gives the normalization change (that draft's `X_p` is
  twice a variable with law `mu^[p]`) and says that the draft does not cite
  this article, whose one-ladder theorems are single-stream cases of its
  results. A second note, after the discussion of "Multivariate arithmetic
  factors", records that the same draft settles the product-target case:
  a sum of uniform laws along arbitrary vectors divides `(mu^[p])^(tensor d)`
  exactly when every generator is coordinate-aligned with a signed
  reciprocal-integer length and each coordinate satisfies the matching
  criterion, and the real matrices `C` for which the image law is a factor
  are exactly the partial monomial matrices with nonzero entries `±1/n`;
  nested boxes, parallelotopes and lattice fundamental domains in general
  remain open. The title page no longer sets a PDF page anchor (it
  duplicated the destination `page.1`).
- `article.pdf`: rebuilt from the amended source by the three passes above
  (MiKTeX pdfTeX 1.40.29): 26 pages (25 as delivered); the final log has no
  error, overfull or underfull box, unresolved reference, duplicate
  destination, or LaTeX warning; the pages carrying the notes were rendered
  and inspected.
- `README.md`: the page count under "Files", and this section.
