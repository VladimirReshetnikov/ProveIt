# Uniform Asymptotics and Zero Bifurcations for Polylogarithmic Families

Research continuation for Vladimir Reshetnikov's ProveIt project,
prepared with OpenAI assistance on 10 October 2026.

The starting manuscript is pinned to revision
**cc34f73596336f2466d9754cb0f3635bd2bedade**, under
Analysis/Polylogarithms/docs/manuscript.

The article distinguishes analytic proofs, proofs completed by finite exact
rational certificates, and numerical conjectures. **The S6 and S8 identities
remain conjectural.** Their exact residual enclosures prove proximity only.

## Read the article

- **article.pdf** is the compiled research article.
- **article.tex** is the editorial main source, using the six section files.
- **polylogarithms_saddles_and_zeros.tex** combines those sources into one TeX
  file. It still uses the two vector PDFs in the figures directory.
- **sections/** contains the mathematical sections for integration.
- **integration/** contains a proposed source documentation patch and detailed
  integration notes.

## Main results

1. A relative saddle expansion to every fixed order, uniform as the outer
   exponent p tends to infinity over all integer depths h ≥ 1 and all shifts
   a > 0, with no lower or upper restriction on p/h. It resolves the source's
   expanding-range question and includes the transition p = h(log h + c).
2. A strict reflected log-gamma inequality and unique saddle for every positive
   exponent ratio. The compact part of the inequality is proved using 112
   exact rational interval checks; the endpoint arguments are analytic.
   Consequences include the sharp product bound, a full proportional joint
   moment expansion, and the exponential small-ratio saddle expansion.
3. An independent analytic critical-window expansion when
   n/(m+1) − log m stays bounded. The normalized moment tends to
   exp(d exp(−s)), with d = ζ(2)/(2γ) − γ. In particular, m/n → 0 alone
   does not justify the fixed-m leading approximation.
4. General Puiseux unfolding of the multiple elementary Lerch root.
   At first derivative order the exact small-positive-parameter count is one
   positive zero for odd index and two for even index. Nine exact endpoint
   signs force an interior multiple-root transition at indices three and four.
5. A logarithmic expansion at the Stieltjes endpoint, precise C^(k−1) but not
   C^k deformation regularity, and the displacement of simple endpoint zeros.
6. A new weight-nine S8 identity candidate. Independent Euler and Mellin
   diagnostics support its frozen integer vector. Two exact rational schemes
   certify proximity for both S6 and S8; the stronger scheme bounds each
   normalized left-minus-right difference by 10^−355.

The twelve further questions in the article address exact S6/S8 proofs,
general even-index reductions, explicit uniform error constants, joint moment
matching, and complete Lerch discriminant geometry.

## Fast exact replay

The exact proof replay needs **Python 3.11 or newer and its standard library
only**. Python 3.12.14 was used for this package. Do not pass Python's -O flag,
which disables assertions in the component verifiers.

From the package root:

    python3 code/replay_exact.py

This reconstructs and compares, without network access:

- all 112 compact reflected-inequality bounds;
- all nine Lerch endpoint sign enclosures;
- the N = 1100 S6/S8 source-bound rational intervals;
- the N = 1200 S6/S8 direct-bound rational intervals.

Only the elapsed runtime field is ignored in the Gaussian JSON comparison.
All mathematical endpoints are compared exactly. Fresh Gaussian calculations
use a temporary directory, so replay does not overwrite the stored proof objects.
The concise receipt is written to results/replay_summary.json.

This finite replay complements the analytic coverage and error-bound proofs in
the article. It is not proof-assistant formalization. In particular it cannot
establish a conjectured exact identity from a nonzero-width residual interval.

## Build the PDF

A LuaLaTeX installation with the standard packages listed in article.tex is
needed. LuaHBTeX 1.17.0, TeX Live 2023/Debian, was used. No shell escape,
bibliography download, or external network call is required.

    make pdf

Equivalently, run the following command three times:

    lualatex -interaction=nonstopmode -halt-on-error article.tex

To regenerate the combined TeX:

    python3 code/make_standalone.py

The combined TeX can also be compiled with LuaLaTeX from this directory.
Keep the figures directory alongside either source. The section inputs are
needed only by article.tex.

## Optional symbolic and numerical reproduction

The exact proof replay does not require any third-party Python package.
The optional scripts use the tested versions in requirements.txt. Install
them into an appropriate environment, then use the commands below.

| Command from package root | Output and mathematical status |
|---|---|
| python3 code/compile_saddle_coefficients.py | Exact symbolic coefficients through d3, including the pure-gamma cancellation check; requires SymPy |
| python3 code/check_uniform_saddle.py --dps 75 | The 24-case positive-integral harmonic diagnostic set |
| python3 code/check_gamma_joint_asymptotics.py | Eight proportional and twelve critical-window moment diagnostics at 65 digits |
| python3 code/check_lerch_endpoint.py | Nine endpoint difference-kernel diagnostics at 65 digits |
| python3 code/scan_lerch_integral.py | Ordinary numerical Lerch scans and two candidate multiple-root solves |
| python3 code/search_s8.py | PSLQ discovery settings, frozen integer vector, and fresh 500-digit Euler audit |
| python3 code/integral_audit.py | Independent 220-digit Mellin audit of the S8 vector |
| python3 code/interval_certificate.py | Regenerates both full exact Gaussian certificate files |
| python3 code/certify_gamma_saddle.py --check | Replays and compares the reflected inequality certificate |
| python3 code/verify_lerch_bifurcations.py | Regenerates the exact Lerch endpoint sign file |
| python3 code/plot_harmonic_saddle.py | Reproduces the harmonic PDF/PNG/SVG figure and its plotted-data metadata |
| python3 code/plot_gamma_joint.py | Reproduces the reflected-moment PDF/PNG figure |

The individual regeneration programs write under results/, except figures and
their plotted-data receipts, which go under figures/. Numerical runs may take
several minutes depending on the machine. The exact replay is much shorter.

The numerical integrators are ordinary quadrature, sometimes with explicit
finite truncations. The scripts and article record those limitations.
High working precision is not presented as a proved error bound.

## Files and provenance

- **code/**: all certificate, discovery, symbolic, diagnostic, plotting, and
  source-assembly programs.
- **results/**: exact rational proof objects and clearly labeled numerical data.
  Large rational integers are stored as decimal strings where needed.
- **figures/**: two vector research figures, raster previews, and a harmonic
  SVG plus plotted-data exports.
- **provenance/upstream_snapshot_manifest.json**: hashes for the 40 inspected
  manuscript text files; all 35 chapter blobs match their pinned Git objects.
- **provenance/upstream_chapter_git_objects.json**: original Git object metadata.
- **provenance/runtime_versions.json**: tested Python and package versions.
- **provenance/validation_report.json**: final build, replay, and PDF review
  receipt for the delivered package.
- **SHA256SUMS**: hashes of the final package contents except the checksum file
  itself.

The upstream manuscript is identified and cited, rather than duplicated in
this package. The proposed patch is a narrow documentation update to the S6
evidence paragraph. No remote repository was modified.

## Scope of the audit

No fresh substantive mathematical error was found in the targeted source
material. The chapter's account of S6 diagnostics should mention the separate
exact residual certificate already recorded in VALIDATION.md. The source's
fixed-m and eventual-derivative-order restrictions remain mathematically
meaningful and are retained.

The article claims the stated new results relative to the inspected revision.
It does not assert worldwide priority for every inequality, reformulation, or
application of established asymptotic methods.
