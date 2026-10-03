# Arithmetic Convolution Factors of Fabius-Type Laws

**Exact divisibility, fractal remainders, and classification barriers**  
Research manuscript prepared for the ProveIt programme, 28 September 2026.

## Files

- `article.pdf` — the 27-page article (since the editorial amendments of
  2026-10-01 below), including complete written proofs, ten further
  research questions, a verification ledger, and references.
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

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 69 and 70 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-09-30)") is defined after `ednote`. Three notes cite
  the later unreviewed draft
  `../Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/` (batch 69,
  2026-09-30), written in this article's normalization:
  - after the 2026-09-29 note to "Beyond divisibility ladders": a second
    sufficient hypothesis, pairwise rationally incommensurable target
    lengths, under which zero-divisor domination, entire extension of the
    Fourier quotient, and an injective assignment of the uniforms to target
    coordinates refined by integers are equivalent (its `thm:separated`);
    its `thm:channels` does the same for `mu_p`, `p = r^(-e/h)`, `r` prime;
  - after the discussion of "Two arbitrary geometric ratios": answered for
    every target ratio `p` with no rational positive power
    (`mu_p = D_c mu_q * nu` exactly when `c = p^a/n`, `q = p^m/d`,
    `m, n, d >= 1`; its `thm:geometric`) and, by a finite orbit criterion,
    for `p = r^(-e/h)` (its `thm:orbit`), zero inclusion being sufficient in
    both cases; with this article's `thm:crossbase`, open only for targets
    whose least rational power `p^h` is `A/B` with `A > 1`, or `1/B` with
    `h >= 2` and `B` not a prime power; the draft re-proves
    `thm:self-spectrum` (its `prop:same`) without citing this article;
  - after the discussion of "Optimal approximate factorization": the draft's
    `thm:metric` bounds `inf_nu W_1(mu_q, U_{1/N} * U_{1/M} * nu)` below for
    nonresonant `q` by the mechanism of `prop:wasserstein` (uncited), and its
    `thm:perturbation` gives a family near `q = 1/2` on which exact
    factorability fails while the distance tends to zero; the sharp rate is
    open there too.
- Relation recorded elsewhere: `thm:self-spectrum` with `q = 1/b` proves
  item 1 of `conj:general-base` of
  `../Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/` for every
  integer base `b >= 2`; that report now carries a second note saying so.
- `article.pdf`: rebuilt from the amended source by the three passes above
  (MiKTeX 26.2, pdfTeX 1.40.29): 26 pages, as before; no error, undefined
  reference, multiply defined label, duplicate destination, overfull or
  underfull box; no Type 3 font. The pages carrying the notes were rendered
  and inspected.
- `README.md`: this section.

## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 73 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-10-01)`, every change to `verify.py` and the `Makefile`
`ed. (2026-10-01)`. The mathematical text is unchanged.

- `article.tex`: a third unnumbered environment `ednotethird` ("Editorial
  note (ProveIt, 2026-10-01)") is defined after `ednotelater`. Two notes
  cite the later unreviewed draft
  `../Wasserstein_Contact_Orders_Uniform_Factor_Resonances/` (batch 73,
  2026-10-01), which credits Proposition 3.9 (`prop:wasserstein`) and the
  question "Optimal approximate factorization":
  - after Proposition 3.9 and the leading-coefficient formula (24): that
    draft's Lemma 2.1 compares Fourier derivatives instead of values (for
    `mu` supported in `[-R, R]` and `eta` with finite first moment,
    `|(hat mu)'(t) - (hat eta)'(t)| <= 2 pi (1 + 2 pi |t| R) W_1(mu, eta)`). When the
    target zero is simple (`r = 1`, that is `A_1` does not divide `t_0`), the
    factor's zero has order at least two, and the lemma gives
    `W_1(mu_A, D_{1/m} mu_B * nu) >= a_1 / (2 pi (1 + 2 pi t_0 R_A))` for
    every probability `nu`, linear in `a_1`, whereas (23) at the largest
    admissible `h = a_1/(2 D_1)` is `a_1^2 / (8 pi D_1 (t_0 + h))`. The draft
    has no analogue for `r >= 2` and no upper bound for ladder targets;
  - after the 2026-09-30 note to "Optimal approximate factorization": the
    rate left open there is known. `inf_nu W_1(mu_q, U_{1/2} * U_{1/3} * nu)`
    is of exact first order at `q = 1/2`, with one-sided coefficients between
    `|P|/(6 pi (1 + 12 pi))` (about `6.33e-5`;
    `P = prod_{k>=2} sinc(6 * 2^(-k)) = -0.0462...` in this article's
    normalized `sinc`) and `1/4`, and at most `|q - 1/2|/4` for every `q`;
    for `U_{1/B} * U_{B^-j}` (fixed integers `B >= 2`, `j >= 1`) it is of
    exact order `|q - 1/B|^j` on both sides of `1/B`. The question itself,
    for divisibility-ladder targets, remains open.
- `article.pdf`: rebuilt from the amended source by three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 27 pages (26 before), 554,705
  bytes, A4; no error, undefined reference, multiply defined label,
  duplicate destination, overfull or underfull box; every font embedded, no
  Type 3 font. The pages carrying the notes were rendered and inspected.
  The source is now 1,853 lines/90,077 bytes.
- `verify.py`: without `--output` it now writes
  `rerun/verification_results.json` beside itself (as delivered it wrote
  `verification_results.json` in the current directory), and it writes LF
  line endings on every platform (as delivered, CRLF on Windows). The
  command under "Reproduce", run in this directory, still overwrites the
  recorded file: run it on a copy, or omit `--output`. A rerun on a copy
  (2026-10-01, `py verify.py`, Python 3.14.4) passed and wrote a file equal
  to `verification_results.json` byte for byte. On the ProveIt machine use
  `py` for `python3`.
- `Makefile`: its `verify` target now writes `rerun/verification_results.json`;
  its `pdf` target still compiles in this directory and overwrites the filed
  PDF, so build on a copy.
- `README.md`: the page count under "Files", and this section.
