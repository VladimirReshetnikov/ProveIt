# Gamma functions over the surreals: a sharp convexity classification

`article.pdf` (29 pages) — source `article.tex`, checks in `code/`, recorded
evidence in `data/`.

An unrefereed AI-assisted draft, dated 21 September 2026. Not refereed and not
verified in Lean or any other proof assistant
(`data/build-quality.json` records `formal_proof_assistant_checked: false`).

## What it establishes

Write `M(x)` for the leading Conway monomial of a positive infinite surreal
**with its real coefficient stripped**, and `pp(x)` for the purely infinite
part. For an arbitrary class assignment `a` on the class of positive infinite
monomials — no regularity assumed — set `h_a(x) = a(M(x))·pp(x)` at positive
infinite `x` and `0` at positive finite `x`, and put `L_a = L_0 + h_a` over the
Taylor–Stirling log-Gamma baseline `L_0`.

**The main theorem is a two-sided sharp threshold:**

> `L_a` is convex on all of `No_{>0}` **iff** `m·a(m)` is finite for every
> positive infinite monomial `m` — and in that case it is *strictly* convex.

Pointwise in `m`, no uniform real bound across monomials, both signs allowed.
There are no merely-convex, non-strictly-convex members.

And **every** member, convex or not, agrees with the baseline at every positive
finite argument and preserves `Γ_a(1) = 1`, the recurrence
`Γ_a(x+1) = x·Γ_a(x)`, every finite
Gauss multiplication formula, every normalized finite-translation germ, and all
positive-order fine derivatives of log-Gamma.

Consequences worth naming:

- **The literal surreal Bohr–Mollerup conditions do not give uniqueness.** Taking
  `a_λ(m) = λ·exp(−m)` for real `λ` gives pairwise distinct, strictly
  log-convex Gamma extensions agreeing on all of the above. Their logarithmic
  differences and relative differences `Γ_λ/Γ_μ − 1` are smaller in magnitude
  than *every* ordinary inverse power at *every* infinite argument
  — at `x = ω` the log-difference from the baseline is exactly `λ·ω·exp(−ω)`. Adding all
  ordinary-order signed first-omitted-term Stirling envelopes does not restore
  uniqueness either (`thm:enveloping`). This does not bound absolute Gamma
  differences: `Γ_1(ω) − Γ_0(ω) > ω^N` for every ordinary `N`, as proved in
  `warn:absolute-difference`.
- **A convexity proof with no second derivatives and no mean value theorem.**
  It works with the tangent gap `D_F(y,x) = F(y) − F(x) − F'(x)(y−x)` and
  proves strict positivity in four exhaustive relative-scale regimes for
  infinite arguments, with margins `(y−x)²/(2x)`, `x(r log r − r + 1)`,
  `y log q` and `x`. The `(y−x)²/(2x)` margin is exactly what generates the
  `O(m^{-1})` threshold. The mechanism is then isolated as a reusable abstract
  theorem, the *scale-margin gauge principle*, with `L_0` realizing it at
  `κ = 1/2`.
- **A positive second derivative does not imply convexity in this calculus.** A
  worked counterexample: take `a(m₀) = 1` and `a(m) = 0` elsewhere. All positive-order
  fine derivatives of `L_0 + h_a` equal those of `L_0`, yet `x = m₀`, `y = m₀ − √m₀` has a
  *negative* tangent gap. Gauges of this shape are finely locally constant —
  constant on cosets mod the finite surreals — so global convexity simply
  cannot be decided locally.
- **Scalar rigidity.** Compatibility with the Berarducci–Mantova derivation via
  the chain rule `d(L(x)) = L'(x)·d(x)` forces every `h_a(x)` into `ker(d) = R`;
  a real infinitesimal is zero, which kills every infinitesimal locally
  constant gauge, and a `√m`-shift argument then kills every member of the
  monomialwise family except `a = 0`. But `prop:real-gauge` exhibits a
  *different* real-valued, non-flat gauge that survives scalar compatibility —
  so scalar compatibility alone is **not** a universal uniqueness
  characterization.
- **An exact finite-phase domain.** On the tube `Re(z) > 0`, `Im(z)` finite,
  the constructed surcomplex log-Gamma has finite imaginary part exactly on
  `Ω`: finite real part, or infinite real part `x` with `Im(z)·log(x)` finite.

## Where it sits

`surreal/` — the object is **No** itself, not `No[i]`; the surcomplex sections
are a secondary tube computation. It is a **standalone** report and can be read
on its own.

The report's central subject is its Gamma gauge classification. The original
targeted catalogue audit found no other Gamma-specific package; it did not
establish absence of related material throughout the collection. Relevant
points of contact include:

- [`surcomplex/differential-equations`](../../surcomplex/differential-equations/)
  for the **Berarducci–Mantova scalar derivation**, imported here to eliminate
  infinitesimal locally constant discrepancies. Its different uses of phase
  should not be conflated: this report uses **finite-angle**
  `cis(b) = exp(i·st(b)) Σ_k (i(b−st(b)))^k/k!` for finite scalar `b`.
  The criterion here concerns the scalar value `Im(log-Gamma(z))`; no primitive
  is being chosen.
- [`surcomplex/trigonometry`](../../surcomplex/trigonometry/) and the shared
  [notation guide](../../NOTATION.md) distinguish this finite-angle
  exponential from a global phase prescription. This article defines its
  convention directly in “Surcomplex log-Gamma and an exact finite-phase tube.”
- The word **"rigidity"** is used in this collection for at least three
  unrelated statements. The one here is *scalar* rigidity, in the exact sense
  above. It is not the all-scale polynomial rigidity of
  [`surcomplex/analysis`](../../surcomplex/analysis/), and not the
  automorphism faithfulness of
  [`exponential-automorphism-rigidity`](../exponential-automorphism-rigidity/).

The article records an original targeted audit of `docs/README.md` and
`docs/surcomplex/differential-equations/article.tex`, and describes the
catalogue as holding *eighteen* research packages — fewer than are here now.
The eighteen-package count describes that historical tree
(`VladimirReshetnikov/Surreal`, `aa846271b4dcae2c055b216126a87210292ec19b`),
not the current collection. Its original repository operations were reads.
The maintained article now labels this scope explicitly; the historical
`data/source-audit.json` is preserved unchanged.

## What it does NOT claim

- **Not a resolution of a named published open problem.** The article says so
  outright. The search behind it was targeted, some exact-phrase searches were
  sparse or noisy, and no priority certificate or exhaustive negative claim
  about the literature is offered.
- **The classification is exact only for the named monomialwise-linear family**
  `a(M(x))·pp(x)`. It classifies neither all surreal Gamma extensions nor all
  finite-translation-invariant homogeneous gauges; `prop:real-gauge` is a
  second, inequivalent mechanism, and a full classification is left open.
- **Derivative agreement is for log-Gamma only.** An in-text Warning states it
  explicitly: `Γ_a^{(k)}(x) = exp(h_a(x))·Γ_0^{(k)}(x)`, so the *unnormalized*
  derivatives of Gamma itself do **not** agree across the family.
- **The surcomplex results live only inside the finite-imaginary-part tube.**
  `thm:phase-domain` is exact for *this* prescription's canonical finite-angle
  exponentiation. It is **not** a maximality or analytic-continuation claim and
  does not rule out other extensions outside `Ω` chosen by noncanonical phase
  data. No value is prescribed for `cis` of an infinite argument — there is no
  `sin(ω)` and no `exp(iω)` here.
- Local Hahn–Taylor descriptions are explicitly distinguished from global
  analytic continuation: no connected complex path to the real axis, no
  identity theorem propagating equality between fine components.
- All differentiation orders, multiplication indices and Stirling truncation
  indices are **ordinary integers**. No transfinite product, hyperinteger-indexed
  recurrence, proper-class sum, proper-class contour integral, global surcomplex
  exponential or maximal surcomplex Gamma domain is supplied.
- The scalar-rigidity theorems rely essentially on the local-constancy
  hypothesis. The article declines to conclude uniqueness among arbitrary
  functions satisfying a scalar chain rule plus a Stirling expansion.
- Set-sized Hahn workspaces are auxiliary only, and are admitted **not** to be
  invariant under every operation discussed. Restricted-analytic transfer is
  routed instead through an adequately large `No(ε)` for an ordinal
  ε-number `ε`.
- **A recorded guardrail worth keeping:** the real identity
  `ψ'(x) = Σ_{k≥0} (x+k)^{-2}` must **not** be substituted at infinite surreal
  `x`. Every summand shares the leading monomial `M(x)^{-2}` with nonzero real
  coefficient, so the family is not strongly summable. The differentiated
  Stirling strong series is the correct object.
- The 130 symbolic checks cover finite algebraic identities and finite sparse
  normal-form bookkeeping only. They establish none of the all-scale surreal
  inequalities, the class quantification, Neumann's support lemma, first-order
  transfer, or novelty; the normal-form tests use a toy sparse model.

## Maintained proof review

The 22 September 2026 review followed the proof dependencies from strong
substitution and local calculus through the recurrence, Gauss identities,
all-scale tangent gaps, convexity threshold, flatness, phase domain, and scalar
rigidity. The main classification and its consequences remain intact.
The maintained text now proves the absolute-difference counterexample above,
labels monomial versus exponent support, states the distinct-point condition
in the abstract tangent-gap theorem, and distinguishes surreal-valued Taylor
coefficients from ordinary real constants. Finite-argument agreement includes
the recurrence-based prescription at positive infinitesimals, where Gamma has
no Taylor series centered at zero.

The restricted-analytic transfer import was checked against
[Costin–Ehrlich v5, Proposition 93](https://arxiv.org/html/2208.14331v5), which
records the `No(ε)` result of van den Dries–Ehrlich, Proposition 4.7.
The classical Binet and signed remainder inputs match
[DLMF 5.9.10](https://dlmf.nist.gov/5.9.E10) and
[DLMF 5.11(ii)](https://dlmf.nist.gov/5.11.ii).
These source checks do not establish priority for the report's claims.
Historical `code/` and `data/` files remain unchanged; build and rerun evidence
below concerns the maintained article.

## Build

A LaTeX distribution with `latexmk` and the packages named in the preamble. No
external graphics, no bibliography database, no custom font files.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without `latexmk`, run `pdflatex -interaction=nonstopmode -halt-on-error
article.tex` until cross-references stabilize — normally three passes. Last
verified build: three passes, exit 0, **29 pages**, no LaTeX warnings, no
undefined references, zero overfull or underfull boxes. Baseline and revised
builds were checked in temporary directories and changed pages were rendered
and inspected. The preserved `data/build-quality.json` describes the original
29-page build, not the current review.

## Rerun the checks — run them on a copy

Python 3.9 or later with SymPy; the tested pin is in `data/requirements.txt`
(`sympy==1.14.0`). The checks use exact `Fraction`/`Rational` arithmetic and
truncated formal power series, with no floating point standing in for an
infinite surreal.

> **Warning — the script overwrites the package's own evidence.** `--output`
> **defaults to `data/verification.json`**, which is the shipped record itself,
> and the `check` target in `code/makefile-Makefile` passes exactly that path.
> So a bare `python code/verify.py` from the package root, or a `make check`,
> silently replaces `data/verification.json` — including its recorded
> Python/SymPy provenance fields. **Copy the package elsewhere before running,
> or redirect the output**, and diff against the shipped record rather than
> overwriting it:

```sh
cp -r . /tmp/gamma-check && cd /tmp/gamma-check
python -m pip install -r data/requirements.txt
python code/verify.py --output /tmp/verification-rerun.json
```

The default is resolved relative to the *current working directory*, so
running from elsewhere writes a stray `data/verification.json` there instead.
The archived Makefile ships as `code/makefile-Makefile`; `make -f` can select
it from the package root, but its `check` target still overwrites the original
JSON. Use the explicit redirected command above to preserve that record.

The script exits 0 only when every check passes and prints its count. Rerun
here: `130/130 checks passed.`, exit 0, on Python 3.13.14 with SymPy 1.14.0,
reproducing the counts in `data/verification.json` (recorded on Python 3.13.5).

The 130 checks cover the first six Stirling coefficients `b_j = B_2j/(2j(2j−1))`
and the alternating sign of `b_j` for `j = 1..16`; the shift-recurrence defect
vanishing through degree `2J+1`; Gauss defects for `n = 2,3,4,5,7`; the `Φ` and
`Ψ` tangent-kernel expansions; the remainder-bracket coefficients for
`k = 1..17`; the exact elementary tangent-gap identity; sparse normal-form
bookkeeping for `pp` and `M`; the derivative mismatch `λ(1−ω)exp(−ω)`; and
leading polygamma sign coefficients. `data/source-audit.json` records the audit
scope, eight primary references, and the observed repository revision.
