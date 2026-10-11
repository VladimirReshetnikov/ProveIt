# Barnes Resolvents and Higher Harmonic Identities

Research continuation prepared for Vladimir Reshetnikov, 11 October 2026.

The complete article is `Barnes_Resolvents_and_Harmonic_Identities.pdf`.
The matching `.tex` file is standalone. The same source is supplied in modular
form as `article.tex`, `preamble.tex`, seven section files, and `references.tex`.

## Mathematical contributions

The article develops four questions from the incoming ProveIt reports at
repository commit `7bd45777a8a127e5dc69aff8887ca36a79a3059d`.

| Source target | Result | Scope |
|---|---|---|
| Harmonic Parity, R6 | Polynomial Hurwitz master transform; individual multiple-Gamma resolvents at every rank; explicit Barnes-G formula | Unit periods, arbitrary polynomial weights, fixed zeta normalization; ordinary and depth-two polylogarithms and their order derivatives |
| Harmonic Parity, R4 | Joint generator for complex cotangent powers; explicit moving amplitudes and finite-part conversion | Joint meromorphic continuation for all complex parameters; pointwise finite-part comparison for positive real part of the kernel exponent, including all positive integer crossings |
| Cubic report, Q6 | Exact fourth digamma finite part and its strict harmonic Laurent bridge | Fully specified depth-two/depth-three coefficients, an absolutely convergent arithmetic series, normalized primitive, and all differentiated identities |
| Harmonic Parity, R10 | Ordinary convergent integral generator for the symmetric Tornheim germ; explicit transverse coordinate and cyclic fifth derivatives | The requested normalized-integral alternative; no finite ordinary-zeta evaluation of the two retained fifth-order coordinates is claimed |

Several concrete formulas make the reductions testable. The real component
of the Barnes-G transform at `z=3*pi*i` reduces to ordinary polylogarithms
and one order derivative at `q=1/2`. The quartic digamma finite part is

    Q4 = 18*zeta(4) + 12*zeta(3) - 12*gamma*zeta(2) + 4*zeta'(3)
         + 12*(gamma^2-zeta(2))*gamma_1 + 24*gamma*eta - 24*beta_1.

The exact strict Laurent definitions of `eta` and `beta_1`, and independent
ordinary convergent Mellin representations of both, are in Section 5.
The cyclic fifth-derivative formula retains the diagonal derivative
`Omega_5` and the explicitly evaluated integral coordinate `chi`.

The article includes twelve further research questions. Its source audit
also corrects a pointwise algebraic line in Mező's log-Barnes paper while
preserving that paper's subsequent integrated equality.

## Status and prior work

All theorem claims are supported by proofs in the article. Finite symbolic
checks and independent numerical diagnostics accompany them. These files
are mathematical research documents, not machine-checked ProveIt proof objects.

The current manuscript's `S6` and revised `S8` evaluations remain conjectural.
The older frozen `S8` vector was rejected in the existing manuscript and is
different from the revised candidate. No new ordinary-constant evaluation
or arithmetic independence of `eta`, `beta_1`, `chi`, or `Omega_5` is asserted.

Classical input is attributed: Hurwitz Fourier series, the multiple-Gamma
zeta conversion, the Barnes-G Fourier coefficients, balanced primitives,
beta-integral binomial identities, harmonic-zeta Laurent theory, and cyclic
Tornheim desingularization. The preceding report's formal quartic and cyclic
structure is used as a baseline, not presented as a new discovery.

## Build the article

Requirements: Python 3, a standard TeX Live installation with pdfLaTeX and
the packages listed in `preamble.tex`, and optionally `latexmk`.

```sh
python3 build_standalone.py
latexmk -pdf -interaction=nonstopmode -halt-on-error Barnes_Resolvents_and_Harmonic_Identities.tex
```

With no `latexmk`, run `pdflatex -halt-on-error` on the standalone TeX file
three times to resolve the contents and references. `make` performs the
standalone generation and `latexmk` build. Editing the modular files and
regenerating is preferable to editing the generated standalone source.

## Replay the calculations

Python 3.12.14, mpmath 1.3.0, and SymPy 1.14.0 were used. Once the two
dependencies in `requirements.txt` are installed, no network or repository
checkout is needed.

```sh
python3 verification/barnes/verify_normalization.py
python3 verification/barnes/verify_barnes.py
python3 verification/weighted/check_weighted_transform.py
python3 verification/weighted/check_tail_backend.py
python3 verification/complex/verify_complex_powers.py
python3 verification/quartic/check_quartic_exact.py
python3 verification/quartic/check_quartic.py
python3 verification/quartic/check_quartic_mellin.py
python3 verification/cyclic/verify_fifth_exact.py
python3 verification/cyclic/verify_fifth_numeric.py
```

Run the quartic arithmetic program before the quartic Mellin program: the
latter reads its independent quadrature record. Other branches are independent.
Do not run Python with `-O`, which disables the assertions used by the checks.
Most scripts replace the result JSON beside themselves. The cyclic branch
preserves `recorded_results/` and writes reruns to `generated_results/`.
Use a copy of the package to preserve all delivered hashes during replay.

The exact checks concern finite coefficient algebra. The numerical programs
compare independent representations, but do not use interval arithmetic.
The records include working precision, truncations, tolerances, and residuals.
The weighted branch explains why scaled Euler–Maclaurin tails are used for
large complex orders rather than unguarded tiny Hurwitz evaluations.

## Integration and provenance

- `integration/INTEGRATION.md`: suggested insertion points, dependencies,
  normalization choices, and retained open claims.
- `integration/CLAIM_LEDGER.json`: theorem-level status and scope.
- `integration/CORRECTIONS.md`: exact published correction and its consequence.
- `provenance/repository_inventory.json`: pinned revision, the 85 materialized
  manuscript text files, and the 11 incoming archive hashes and text-member data.
- `verification/cyclic/SOURCE_PROVENANCE.json`: precise provenance for the
  one reused Tornheim numerical evaluator; its original attribution is intact.
- `verification/pdf_build_report.json`: final compilation and visual review record.
- `package_manifest.json`: SHA-256 hashes and sizes for delivered files.

All new LaTeX labels and bibliography keys use the `bhr:` prefix.
External papers are linked in the bibliography and are not redistributed.

To verify the delivered file hashes before running scripts:

```sh
python3 verify_manifest.py
```
