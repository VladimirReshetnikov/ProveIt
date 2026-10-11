# Quartic Digamma Bridges, Harmonic Tail Moments, and Complex Resolvent Powers

Research continuation prepared with ChatGPT for Vladimir Reshetnikov and the ProveIt project, 11 October 2026 (UTC).

## Read the article

- `Quartic_Tails_and_Complex_Resolvents.pdf` — complete article with proofs, examples, source audit, and 16 further research questions.
- `Quartic_Tails_and_Complex_Resolvents.tex` — self-contained TeX source; compile directly with pdfLaTeX.
- `article.tex`, `preamble.tex`, `references.tex`, and `sections/` — equivalent modular source for repository integration.

## Main results

1. **Quartic digamma bridge.** The coordinate finite part of the integral of `psi(x)^4` is reduced to the specified linear Laurent coefficients of the strict depth-three and depth-two harmonic zeta functions, with every ordinary zeta/Stieltjes correction fixed. An explicit combination with the inherited cubic moment removes the depth-two coefficient. The article also gives an absolutely convergent harmonic sum, an elementary kernel for the depth-three coefficient, a normalized primitive, and all argument derivatives.
2. **All moments of every pair of even harmonic tails.** A finite Bernoulli formula evaluates every centered nonpositive even spectral value for every pair of positive even orders. Each entire moment sequence belongs to a fixed finite span of ordinary zeta values and their products. Its analytic generating function is a finite classical-polylogarithm expression. For the `(2,4)` pair, all moments are rational combinations of the first four; one exact elimination gives the displayed convergent polygamma sum equal to `-88`.
3. **Complex resolvent powers and complete resonant germs.** A beta–polylogarithm transform extends the cotangent resolvent to complex powers, with a specified branch, full endpoint corrections at every integer power, arbitrary Stieltjes indices and logarithmic powers, exact parameter derivatives, and normalized primitives.
4. **Ordinary Gamma–Gauss moments.** An independent generating function evaluates all polynomial moments. At two imaginary base points it becomes a Gamma quotient organized by generalized harmonic numbers, including explicit convergent negative-half-power examples.

These results address the explicitly requested quartic case of Cubic Harmonic Question 6, the pure two-tail family of Harmonic Parity Question R1, and its complex-power Question R4. They do not settle the added harmonic factors in R1, all higher digamma powers, or an ordinary-constant reduction of the retained depth-three coefficient. The Gaussian `S6` and revised `S8` conjectures remain open.

## Build

Requirements: Python 3.10 or newer for the convenience scripts; a standard TeX Live installation with pdfLaTeX and the packages listed in `preamble.tex`.

```bash
python3 build.py
```

The build expands the modular TeX into the self-contained file, runs three pdfLaTeX passes, and rejects overfull boxes or unresolved references. It requires no network access, external bibliography processor, or shell escape. Build intermediates are placed under `build/`.

## Replay the mathematics checks

The recorded Python dependencies are pinned in `requirements.txt`:

```bash
python3 -m pip install -r requirements.txt
python3 run_verification.py
```

Run on a copy if you want to retain the shipped JSON outputs byte for byte. Each suite refreshes its JSON file; the runner saves a summary and logs under `verification/replay/`.

| Suite | Exact checks | Other evidence |
|---|---:|---|
| Quartic bridge | 44 | Four independent arithmetic/quadrature records at 100 working digits |
| Mixed harmonic tails | 94 | 36 independently evaluated moments and three generator records at 110 working digits |
| Continuous-power moments | 9 | One corruption control and 19 independent numerical comparisons at 55 working digits |
| Endpoint contacts and primitives | 36 | 20 deliberately omitted-phase formulas rejected |

The packaged replay passed all four suites. The total is **183 exact finite symbolic checks and 21 deliberate corruption controls**. The proofs establish the all-index identities. The floating-point calculations are independent diagnostics with the stated analytic tail estimates; their rounding errors are not interval-enclosed. No formal proof-assistant certification or arithmetic independence claim is made.

## Integration and provenance

The source baseline is ProveIt commit `7bd45777a8a127e5dc69aff8887ca36a79a3059d`. See:

- `INTEGRATION.md` for exact source questions, proposed scoped status updates, and section labels.
- `claims.json` for the machine-readable claim inventory.
- `provenance/SOURCE_AUDIT.md` for audit scope and findings.
- `provenance/source_manifest.json` for source hashes.
- `provenance/independent_review_record.txt` for the mathematical review record.
- `SHA256SUMS` for deliverable integrity.

No ProveIt repository files were modified. Original source archives are identified by hash and are not duplicated in this package. New relative-to-corpus results are distinguished from classical inputs in the article and bibliography; exhaustive literature priority is not asserted.

