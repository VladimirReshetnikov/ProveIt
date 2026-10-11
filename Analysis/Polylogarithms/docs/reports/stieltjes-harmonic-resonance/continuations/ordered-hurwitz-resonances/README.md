# Ordered Hurwitz Resonances and Cubic Stieltjes Products

**Research continuation for Vladimir Reshetnikov / ProveIt — 10 October 2026**

This package contains the complete article, its modular and standalone TeX
sources, exact coefficient checks, independent numerical diagnostics, and
integration notes. The source baseline is ProveIt commit
`4c1286161c425eca957b4b9f7cd436c37a4c98f3`.

## Principal results

1. An elementary common-shift construction of the canonical ordered Hurwitz
   Laurent germs, with normally convergent harmonic–Stieltjes coefficient
   sums. The general ordered framework is credited to the existing literature.
2. Every nonpositive Laurent coefficient of
   `Z_d(1+p ε,1+q ε,…,1+q ε;a)` closes in finitely many ordinary Hurwitz
   derivatives and generalized Stieltjes constants, for every depth and every
   pair of slopes with nonzero prefixes. Explicit finite parts are supplied
   through depth five.
3. The complete arbitrary-direction depth-three finite part uses ordinary
   Hurwitz data and one named harmonic Stieltjes coefficient. A convergent
   Mellin kernel, shift relation, and parameter derivative make that coefficient
   explicit. The same kernel gives the entire strict harmonic hierarchy.
4. For analytic curves with prefix orders `ν_1,…,ν_d`, the pole order is
   exactly `Σν_j`; the curve jet through `Σν_j+max ν_j` is sufficient and
   necessary in the worst case. Explicit reparametrization and tangency
   examples are included.
5. Residue formulas invert the one-slope coefficient family. Across depths,
   general directional finite parts determine every Taylor coefficient of
   the regular ordered germs.
6. A holomorphic completion generates every cubic coincident Stieltjes
   moment and every triple of argument-derivative orders. The unit-coordinate
   digamma cube reduces exactly to one specified diagonal Tornheim third
   derivative, evaluated independently through a polylogarithmic Mellin
   formula.

The article gives proofs, a targeted primary-literature comparison, proposed
status updates, and **eleven further research questions**. The short `S6` and
revised `S8` candidates remain conjectural. The further reduction of the
remaining Tornheim derivative to a chosen depth-one algebra is unresolved
here. No new source erratum or arithmetic independence result is claimed.

## Files

| File or directory | Purpose |
|---|---|
| `Ordered_Hurwitz_Resonances.pdf` | Complete 27-page compiled article. |
| `Ordered_Hurwitz_Resonances.tex` | Self-contained flattened source; compiles by itself. |
| `article.tex`, `preamble.tex`, `references.tex`, `sections/` | Editable modular sources used to generate the standalone file. |
| `build.py` | Regenerates the standalone TeX and PDF. |
| `verification/` | Five exact or numerical verification programs. |
| `results/` | Recorded exact, numerical, build, and PDF review receipts. |
| `integration/` | Source hashes, claim ledger, prior-art audit, and proposed placement/status notes. |
| `requirements.txt` | Pinned Python dependencies for verification. |

## Build the article

Run from this package directory:

```bash
python build.py
```

This flattens the modular inputs and runs `pdflatex` three times to resolve
the table of contents, equation references, and bibliography links. It writes
the PDF to the package root and a receipt to `results/build_receipt.json`.
Temporary LaTeX files go to `build/`. No network access or verification run
is needed to compile the article. The TeX uses standard AMS, Latin Modern,
geometry, microtype, booktabs, enumitem, fancyhdr, and hyperref packages.

To regenerate only the standalone source, use `python build.py --tex-only`.
Alternatively, compile `Ordered_Hurwitz_Resonances.tex` directly in a normal
LaTeX installation. Edit the modular sources before rerunning `build.py`;
the standalone file is generated from them.

## Reproduce the exact checks

The recorded environment is Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0.
Install the dependencies into an appropriate local environment:

```bash
python -m pip install -r requirements.txt
```

Run each of the following commands:

```bash
python verification/verify_ordered_core.py
python verification/audit_ordered_coefficients.py
python verification/audit_cubic_coefficients.py
```

The programs record their results under `results/` and stop on a failed
exact identity. The first uses Newton's elementary-symmetric recurrence
with independent formal symbols for the Hurwitz jets. The independently
written audits check the higher-depth coefficients, complete cubic stuffle
symmetrization, pole cancellations, Mellin exponents, and digamma-cube
coefficient. **All 72 exact checks passed.** Analytic convergence and
continuation are proved in the article, not established by finite testing.

## Reproduce the independent numerical diagnostics

```bash
python verification/verify_ordered_numeric.py --dps 50 --points 20 --cutoff 36 --order 20 --guard-dps 40 --tolerance 1e-32 > results/ordered_numeric_50dps.json
python verification/verify_cubic.py --dps 35 --terms 50 --tolerance 1e-28 > results/cubic_validation_35dps.json
```

The ordered program computes continued double/triple sums with finite heads
and Euler–Maclaurin tails, followed by Cauchy extraction. It does not use
the canonical regular-germ formula to evaluate the left side. Its largest
depth-three comparison residual is `6.984629386…e-35`; the independent
Mellin comparison for the harmonic coefficient is `9.352473089…e-40`.
Forty guard digits protect tiny Hurwitz tail values before multiplication
by large convolution coefficients. Cauchy aliasing, asymptotic tail
truncation, and roundoff still remain numerical errors.

The cubic program evaluates the diagonal Tornheim jets through a
polylogarithmic Mellin continuation. It compares the resulting identity
with a separately integrated endpoint-subtracted digamma cube. The residual
is `4.0324158e-34`. Both programs report JSON and fail if the specified
diagnostic tolerance is exceeded.

These are floating-point comparisons, **not interval certificates**.
The nominal working precision is not a claim that every printed digit
is certified. No numerical integer relation is used as a proof.

## Integration and status

See `integration/INTEGRATION.md` for the proposed thematic placement and
specific status updates, `integration/claim_ledger.json` for proof labels
and qualifications, and `integration/SOURCE_AUDIT.md` for prior art and
review scope. The source archive hashes are in
`integration/source_snapshot.json`.

The proposed proofs received independent internal AI review and separate
coefficient calculations. They have not been externally peer reviewed or
formalized in a proof assistant. The delivered package does not modify the
repository. Its claims should be integrated through the repository's normal
mathematical review process, with the stated hypotheses and regularization
conventions retained.
