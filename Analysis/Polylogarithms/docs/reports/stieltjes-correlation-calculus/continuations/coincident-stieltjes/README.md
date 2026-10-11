# Coincident-Point Stieltjes Calculus

**Exact Quadratic Closure, Polygamma Parity, and Polylogarithmic Collision Subtraction**  
Research continuation for the ProveIt programme, 10 October 2026.

## Article

The main deliverable is [`article/article.pdf`](article/article.pdf), a 21-page article. Its complete, self-contained LaTeX source is [`article/article.tex`](article/article.tex). The article includes full analytic proofs, explicit evaluations, a normalization audit, reproducibility details, and seven further research directions.

The inspected shifted-Hurwitz report asks for collision expansions and a comparison with same-point Hadamard products. This package resolves the **off-point expansion and finite-constant comparison at all Stieltjes indices**, and extends the result to all argument-derivative orders. It does **not** claim to determine the remaining delta-supported terms in the periodic distributional extension.

## Main proved results

1. **All-index quadratic Stieltjes closure (Theorem 4.1; Corollary 4.2).** With the fixed unit-coordinate Hadamard finite part, every moment of `gamma_m(x) gamma_n(x)` is linear in ordinary Stieltjes constants. The highest index is `m+n+1`, its coefficient is `(m+n+2)/((m+1)(n+1))`, and index `m+n` is absent.
2. **Complete derivative-moment kernel (Theorem 5.1).** For total argument-derivative order `r>0`, all moments reduce to spectral zeta derivatives at the one integer `r+1`, with explicit finite harmonic-number and zeta coefficients. Corollary 5.3 gives the exact polygamma parity law at every order.
3. **Exact collision subtraction (Theorem 7.1).** Every separated correlation is exactly `a^(-r-1) P(log(a)) + R(a)`, where `P` is explicit, has degree at most `m+n+1`, and `R` is analytic for `|a|<1`. Its value `R(0)` is the directly defined same-point Hadamard moment.
4. **Antiderivatives and normalization.** Proposition 8.1 generates exact primitives of every collision polynomial. The primitive section also records compatible mean-zero Hurwitz/gamma formulas. Proposition 6.1 distinguishes the coordinate finite part from the raw bivariate Laurent constant of the spectral kernel.

For example, with precisely the subtraction convention in Definition 2.1,

    FP integral_0^1 psi(x)^2 dx = 2 gamma_1 - pi^2/3,
    FP integral_0^1 psi'(x)^2 dx = 2 zeta(3) + 4 zeta'(3),
    FP integral_0^1 psi'(x) psi''(x) dx = -3 zeta(4).

These are finite-part identities, not ordinary convergent square integrals. An ordinary-integral version of the first is

    integral_0^1 [psi(x)^2 - x^(-2) - 2 gamma/x] dx
        = 1 + 2 gamma_1 - pi^2/3.

The classical Hurwitz product kernel and the log-Gamma square moment are credited as antecedents, not presented as new discoveries. Global priority for every specialization has not been established. There is no claimed proof of S6, S8, period independence, or a general product of singular distributions.

## Reproduction

From this directory:

```sh
python -m pip install -r requirements.txt
python code/exact_engine.py
python code/verify_numerically.py
python code/build.py
```

On Windows, `py` may be substituted for `python`. Do not use Python's `-O` option for the exact verifier; it deliberately rejects optimized execution so its assertions cannot be silently disabled. The build requires `pdflatex` and the standard packages listed in the article preamble. `make all` provides an equivalent workflow where Make is available.

The delivered exact run generated **420 moments and 420 collision polynomials**, with **1,641 recorded finite check groups**. The independent numerical run completed **49 diagnostics at 55 decimal digits**, including **24 same-point finite-part quadratures** and three changed-splitting-point checks. All passed their recorded tolerances. The largest absolute residual in those 27 quadratures was less than `4.3e-42`. These are floating-point diagnostics, not interval certificates or substitutes for the analytic proofs.

The shifted singular-split checks compare explicit special-function formulas; they are not described as independent shifted-integral quadratures. The full scope of every diagnostic is recorded in the article and JSON evidence.

## Layout

- `article/`: final PDF and complete standalone TeX source.
- `code/exact_engine.py`: exact sparse coefficient engine and structural checks.
- `code/verify_numerically.py`: independent local-series integration, ordinary quadrature, and special-function comparisons.
- `code/build.py`: three-pass isolated PDF build with error and overflow checks.
- `data/exact_moments.json`, `data/collision_polynomials.json`: machine-readable exact identities.
- `data/exact_validation.json`, `data/numerical_validation.json`: executed verification records.
- `data/source_snapshot.json`, `data/theorem_status.json`: provenance and scoped proof status.
- `data/build_status.json`, `data/pdf_review.json`: production and visual-review receipts.
- `integration/`: thematic placement, source audit, and a proposed collision-status note.

## Integration and inspection limits

Proposed destination:

    Analysis/Polylogarithms/docs/reports/
      stieltjes-correlation-calculus/continuations/coincident-stieltjes/

Observed repository revision:

    16c7e342d7a4a15f59911f322eb90b7f96c2a8b5

No repository files were modified. The relevant earlier report was read in selected source ranges; the canonical README and incoming inventory/intake guidance were inspected. **The five incoming ZIP archives were inventoried, but their binary contents could not be retrieved and were not audited.** The delivery therefore makes no exhaustive overlap claim across the repository or those archives.

No concrete false theorem was identified in the inspected source portions. The raw-Laurent versus coordinate-finite-part example is an extension safeguard, not an allegation that the earlier report made that error. No independent peer review or proof-assistant formalization has taken place. Successful intake or finite replay should remain separate from canonical mathematical acceptance.

No third-party source PDFs or standalone font files are included.
