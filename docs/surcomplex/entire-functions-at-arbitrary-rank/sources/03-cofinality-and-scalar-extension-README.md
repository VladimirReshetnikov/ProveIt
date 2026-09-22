# Cofinality and Scalar Extension in Surcomplex Entire Function Theory

**Sharp convergence and unit criteria beyond rank one**  
Prepared for Vladimir Reshetnikov by OpenAI ChatGPT, 21 September 2026.

## Contents

- `article.pdf` — the typeset research article.
- `article.tex` — complete standalone LaTeX source, including bibliography.
- `code/verify.py` — standard-library, exact-arithmetic finite regression checks.
- `data/verification.json` — descriptions and results of all 664 checks, plus the
  finite preparation coefficients.
- `data/verification.txt` — concise recorded verification result.
- `LITERATURE_AUDIT.md` — sources, repository snapshot, and novelty boundaries.
- `Makefile` — build, check, and clean targets.

## Main mathematical results

The coefficient field is C, the value group Gamma is a nonzero set-sized
**divisible ordered abelian group**, and K_Gamma is the full Hahn field
C((t^Gamma)). Strong summability means well-ordered union of supports and
finitely many contributions at each exponent. All powers have ordinary
nonnegative integer degrees.

1. **Global strong convergence and cofinality** (Theorems 3.2 and 3.4):
   strong evaluation at every point is equivalent to v(a_n)/n tending to
   positive infinity through the whole value group. Nonpolynomial entire
   series exist exactly when Gamma has countable cofinality.
2. **Restricted units** (Theorem 4.2): a nonconstant restricted series is
   invertible in the same restricted algebra precisely when its constant
   coefficient strictly dominates and its least positive valuation gap is
   an order unit, meaning that the positive integer multiples of this gap
   are cofinal in Gamma.
3. **Universal extension domain** (Theorem 7.2): for Gamma contained in Delta,
   every nonpolynomial entire series over K_Gamma has the same exact strong
   evaluation domain in K_Delta: zero together with points whose valuations
   are bounded below by an element of Gamma. This is a coarsened valuation ring.
   Entireness persists exactly for cofinal extensions (Corollary 7.3).
4. **Zero conservation and no alternative continuation** (Theorems 7.4 and
   7.6): no new zeros occur in that domain, and no alternative entire series
   on a noncofinal extension can agree with the old series even on all
   ordinary complex constants.
5. **Arbitrary-rank divisor classification** (Theorem 8.3): nonzero entire
   functions modulo constants correspond to effective divisors finite in
   each closed valuation ball, via genus-zero canonical products. The rank-one
   antecedent is classical and is not claimed as new.

The explicit infinite-rank example has simple positive surreal zeros
omega^(omega^j), j >= 0, in the workspace with value group equal to the
finite rational span of 1, omega, omega^2, ... . This group has countable
cofinality but no order unit. An appendix extends the convergence and unit
criteria to finitely many variables.

## Build and reproduce

Use Python 3.10 or newer; the verification program has no third-party dependencies:

```sh
python3 code/verify.py
```

Expected output:

```text
PASS: 664 exact finite checks.
finite regression checks only; not a proof of infinite or cofinal statements
```

The program regenerates both verification data files. Its output directory is
resolved relative to the script, not to the shell's current directory.

Build the article with a LaTeX installation containing the standard AMS packages,
newpx, microtype, tcolorbox, titlesec, fancyhdr, xurl, hyperref and latexmk:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The bibliography is embedded in `article.tex`: no BibTeX file, external graphics,
or network access is needed for compilation. `make` builds the article;
`make check` runs the finite checks. Font files are not included in this archive.

## Status and limits

This is an AI-assisted research manuscript. The proofs are written out, with
standard Hahn support lemmas and algebraic closedness identified as imported
inputs. They have not been independently refereed or machine-checked.

The main arbitrary-rank classifications and their combined extension-domain
formulation are proposed contributions, not certified claims of historical
priority. No named published open conjecture is represented as solved. The
article explicitly credits classical rank-one function theory and the known
higher-rank distinction between positive valuation and topological nilpotence.

The 664 checks are finite algebraic regression tests. They do not verify
arbitrary well-ordered supports, infinite products, cofinality, or the
necessity direction of the unit theorem. Full Hahn fields, intrinsic valuation
convergence, strong summability, and the fine topology of the whole surreal
class are kept distinct throughout.

The repository was read at commit
`aa846271b4dcae2c055b216126a87210292ec19b`.
No repository files were modified.
