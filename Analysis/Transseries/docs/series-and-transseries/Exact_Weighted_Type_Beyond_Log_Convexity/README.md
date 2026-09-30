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
timestamps; recorded build hashes describe the delivered files.

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
