# Exact Type Beyond Log-Convexity

**A complete reversion criterion, sharp distortion, and dimension-free nonlinear calculus**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Main result

For any positive coefficient weight N, with N[0] = 1, define

    S[n] = max product(N[j_i]) over positive compositions sum(j_i) = n.

For tangent-to-identity f(z) = z + sum f[n+1] z^(n+1), define

    T_N(f) = limsup (abs(f[n+1]) / N[n])^(1/n).

Every formal compositional inverse preserves this exact type if and only if

    N[n]^(1/n) -> infinity, and log(S[n]/N[n]) = o(n).

No log-convexity, monotonicity, moderate growth, or derivative-closure
hypothesis is assumed. For superexponential-root weights the exact optimal
universal multiplicative distortion is

    Delta(N) = limsup (S[n]/N[n])^(1/n).

The key estimate identifies the positive extremal inverse coefficient as
S[n] exp(o(n)), for each fixed positive amplitude. A strengthening shows
that this particular envelope estimate needs only unbounded primitive
roots; the complete zero-loss classification still needs the full root limit.

## Other results

The article proves a sharp maximum bound for two divergent composition
arguments, with equality for unequal types and every output type between
zero and the common type possible at equal types. Type-zero coordinate
changes preserve exact type even when the coordinate changes diverge.

The same tangent calculus holds for formal Banach-space maps with the
specified multilinear coefficient norm. General invertible Jacobians admit
sharp norm bounds; an explicit two-dimensional example shows why a single
scalar type does not determine the inverse type.

Explicit weights include an admissible staircase with no subexponentially
equivalent log-convex representative, an admissible weight with persistent
downward root jumps, every finite distortion c > 1, and a deep-dip weight
for which a type-zero series has an inverse of infinite type.

## Repository question addressed

The principal source is ProveIt's `Sharp_Weighted_Type_Formal_Reversion/`
article, specifically its questions on arbitrary weights, two divergent
composition arguments, and multivariate/operator-valued inversion.
The pinned source and the limits of the repository/literature inspection
are recorded in `notes/provenance.json` and in the article.
No upstream repository files were modified.

## Files

- `article.tex`: standalone LaTeX source with embedded bibliography and tables.
- `article.pdf`: compiled A4 article, with full proofs and ten research directions.
- `code/verify.py`: exact rational finite verification, standard library only.
- `data/verification.json`: recorded check counts and verification boundaries.
- `data/*.csv`: finite diagnostic data, including explicitly non-certified logarithms.
- `data/diagnostic_rows.tex`: generated diagnostic table rows.
- `notes/proof_audit.md`: assumptions, proof-sensitive points, and limits.
- `notes/provenance.json`: source identifiers, access scope, and references.
- `notes/build_report.json`: PDF build, rendering, and reproduction audit.
- `Makefile`, `build.sh`: reproduction commands.

## Reproduce

The verification program requires Python 3.10 or later and no third-party
packages. The recorded run used Python 3.13.5. A standard TeX Live
installation providing the packages listed in the source is sufficient
for the PDF; no private fonts, external figures, or bibliography processor
are needed.

From this directory:

```sh
python3 code/verify.py --order 36
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or run `make all` / `sh build.sh`. `PYTHON` and `PDFLATEX` can select other
executables. Verification reruns default to `build/verification/` and do
not overwrite the recorded `data/` files. The article compiles independently
of all data files. PDF bytes can change on a rebuild because pdfTeX embeds
timestamps; the recorded build hashes of `article.tex` and `article.pdf`
describe the files as amended and rebuilt on filing (see below).

## Executed verification and mathematical status

The recorded run passed 5,443 counted exact finite checks. Structured
weight coefficients were computed through excess degree 36, independent
partition checks through degree 18, 24 signed scalar cases through ordinary
degree 13, and eight bivariate inverse jets through total degree 7.
Both composition identities, finite majorants, explicit envelopes,
convexity defects, and the deep-dip lower bound were checked.

These are conventional mathematical proofs with finite computational
audits, not Lean-verified or independently peer-reviewed results. The
literature check was targeted and does not establish global publication
priority. The package does not claim analytic summability, resurgence,
arbitrary Hahn-support generality, or polynomial bit complexity.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 52 (see `docs/incoming/README.md`). The
following changes were made on 2026-09-29; everything else is as delivered.

- `article.tex`: an unnumbered `ednote` environment (the article's remarks
  share the theorem counter, so the notes leave its numbering unchanged) and
  six visible "Editorial note (ProveIt, 2026-09-29)" paragraphs, each
  preceded by a `% ed. (2026-09-29)` comment:
  - end of Section 1.3: the exact lines of the three answered questions of
    `../Sharp_Weighted_Type_Formal_Reversion/article.tex` at the pinned
    revision (1485-1493, 1495-1503, 1505-1513; `notes/provenance.json`
    records the wider range 1457-1547, and editorial notes added to that
    article on filing move its line numbers), and the four questions of
    that article that Section 12 re-poses without citing them;
  - after Theorem 8.5 (`thm:zerotoinfinity`): the deep-dip weight shows that
    the polynomial test (ii)⇔(iii) of that article's `thm:iff` genuinely
    needs its log-convexity hypothesis (consistent with that theorem);
  - end of Section 9.2: an editorial deduction for the uncited question of
    `../Near_Linear_Boundary_Exponential_Feedback/` on the root scale of its
    inverse. With that article's `lem:b` (`b` eventually nondecreasing,
    `b → ∞`, `b = o(log x)`), the weight `e^{m b_m}` is admissible
    (Theorem 2.2(iii), with `V_n = exp(n max_{m≤n+1} b_m)`), and
    Corollary 6.5 gives `limsup |q_n|^{1/n} e^{−b_n} = 1` for the inverse
    coefficients. It was re-derived on filing; it is a limsup, not a root
    limit, and is in neither article;
  - end of Section 11.4: the repository's existing Lean proofs of the finite
    Lagrange–Bürmann formula (`Fabius.Lagrange.coeff_solution`) and of the
    Catalan inverse of `z + cz²` (`QuadraticInverse.coeff_succ_inverse`),
    both under `Analysis/FabiusFunction/Lean/FabiusFunction/`;
  - at the question "Optimal subexponential overhead": answered for
    factorial weights by the independent batch-52 package
    `../Sharp_Subexponential_Cost_Gevrey_Reversion/`
    (`log h_{n+1}(C) − log S_n ~ C n^{1−s}` for `0 < s < 1`; the fixed ball
    is stable under inversion exactly for `s ≥ 1`); the general-weight
    question stays open;
  - at the question "Hahn supports and accumulating actions": the repository
    packages on Hahn-support reversion (support controlled, beyond
    Archimedean valuations, action accumulation), none of which treats
    weighted coefficient types.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`
  (28 pages; the delivered PDF had 27; no errors, undefined references,
  multiply defined labels, duplicate destinations or overfull boxes). Line
  numbers of `article.tex` after line 203 differ from the delivered file.
- `notes/build_report.json`: `article_pages` and the `article.tex` and
  `article.pdf` digests were recomputed for the filed files; an
  `editorial_rebuild` field says so. Its other fields describe the delivered
  build.
- `notes/provenance.json` is kept as delivered; its `pinned_question_range`
  1457-1547 is a superset of the three answered questions (1485-1513).
- The delivered checksum ledger `SHA256SUMS` was verified in full on filing
  (14/14, batch 52) and not kept; the delivered archive remains in the
  repository history (see `docs/incoming/README.md`, batch 52 row).
- Rerun on a copy (Windows, Python 3.14.4, `py code/verify.py --order 36
  --output build/verification`): 5,443 checks passed; the four CSV/TeX
  outputs were byte-identical to `data/`, and `verification.json` differs
  only in its `"python"` line, which records the interpreter version. The
  program already writes LF on every platform and never writes to `data/`
  by default. `Makefile` and `build.sh` call `python3`; on Windows pass
  `PYTHON=py`. `make pdf` and `build.sh` rebuild `article.pdf` in place,
  which changes its digest (pdfTeX embeds the build date).
