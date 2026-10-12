# Boundary Contacts and Logarithmic Spectral Integrals

Research continuation for Vladimir Reshetnikov's ProveIt project, prepared on 11 October 2026 with OpenAI assistance.

Repository baseline: `e3d7ec5d3f9be259c1f91edaea4389f4e79b5b03` of <https://github.com/VladimirReshetnikov/ProveIt>.

## Read the article

- `Boundary_Contacts_and_Logarithmic_Spectral_Integrals.pdf` is the complete article, with proofs, examples, source audit, research agenda, and references.
- `Boundary_Contacts_and_Logarithmic_Spectral_Integrals.tex` is a self-contained LaTeX source. It has no external figures, bibliography database, or section-file dependencies.
- `article.tex`, `preamble.tex`, `references.tex`, and `sections/` are the corresponding modular sources for repository integration. Edit these sources and run `build.py` to regenerate the standalone file.
- `CLAIMS.json` gives machine-readable statuses, domains, dependencies, and article labels for the principal results.

## Principal mathematical results

### 1. Every independent bilinear contact

Section 2 completes the independent two-order contact problem for the Gamma-normalized, independently shifted alternating Hurwitz tails. It gives finite ambient coefficients at every resonance `p + q = -2m`, all mixed order derivatives, exact fixed-cutoff translation, sharp highest-degree generators, and normally convergent subtractions. The orders are independent complex variables; both shifts have positive real part.

The distinction between an ambient coefficient and its restriction to a resonance is essential: differentiation takes place before restriction. The alternating problem retains its two separate parity finite parts. Concrete ordinarily convergent sums on the first negative-total-order hyperplane evaluate in pi, log 2, and rational numbers.

The finite endpoint identity, Gamma normalization, first symmetric contact 1/2, and previous diagonal contact theory are inherited and retain their attribution. The new result completes the source question headed **Every bilinear contact hyperplane** in the Bilinear Tails and Determinants incoming report.

### 2. Stieltjes, harmonic, and polygamma boundary identities

Section 3 converts every independent order jet into finite combinations of generalized Stieltjes constants or Hurwitz-zeta derivatives. It gives an explicit absolutely convergent first-Stieltjes boundary series, including its necessary logarithmic subtraction and an endpoint value in Euler's constant, pi, and log 2. Argument derivatives give polygamma formulas and generalized harmonic reductions at integer and half-integer shifts.

### 3. One ordinary integral for every scalar spectral jet

For `a > 0`, finitely many positive masses, and the scalar spectral zeta function formed from the products of `(n+a)^2 + mu_j`, Section 4 gives every derivative at zero as a massless Hurwitz-zeta derivative plus one absolutely convergent real integral. The explicit density is polynomial in real logarithms and pi. Its kernel is the digamma resolvent of the one-sided lattice.

The same mechanism gives compactly supported densities for connected logarithmic products of arbitrary order, exact vanishing moments, coincident-mass limits, divided resolvents, a critical odd-weight ordinary sum, polygamma derivatives, and anchored log-Gamma primitives. The fixed-regulator polynomial-weight correction is explicitly identified as a specialization of the already-preserved local spectral hierarchy.

### 4. Every even polynomial weight and every negative integer point

Section 5 subtracts the finite polynomial-logarithmic asymptotic part before forming the cut density. The result is one ordinary digamma integral, with an explicit finite Hurwitz-derivative baseline, for every even polynomial weight and every derivative order. Choosing the weight as an integer power of the product of the quadratic factors yields every spectral derivative at every nonpositive integer.

An explicit formula for the one-mass third derivative at -1 is included. Both that example and a two-mass second derivative at -1 were checked independently by finite-subtraction continuation, binomial Hurwitz continuation, and quadrature of the cut integral.

### 5. A harmonic and polylogarithmic transform of the density

Section 6 derives the beta/Gamma generating function of the repeated-mass density. Its moments are unsigned Stirling numbers and generalized harmonic polynomials. The density transforms an ordinary polylogarithm of any complex order, at an argument of modulus less than one, into a height-one multiple polylogarithm. Fixed order derivatives are included. Confluent mass expansions and half-lattice/bilateral formulas give further ordinary identities.

The Gamma, Stirling, and height-one multiple-zeta ingredients are classical. The article proves their role in the new density construction without claiming priority for familiar constants or for the classical reductions themselves.

## Corrections, attribution, and open questions

`integration/STATUS_UPDATES.md` maps the results to exact predecessor questions and labels. It also records that the diagonal negative-order cutoff target and the general cubic Stieltjes germ already have preserved solutions. Those are reconciled source statuses, not newly claimed proofs.

`integration/corrections.patch` proposes one definite correction in the canonical digamma-power chapter: the last numerator term in the fifth reciprocal-Gamma coefficient must be `+24\zeta_5`, replacing `+24\zeta\alpha_5`. The derivation is in Section 7. The patch passed `git apply --check` against the pinned checkout and was not applied to the source repository.

Section 8 proposes twelve further investigations, including a short recurrence for all contact coefficients, cyclotomic and three-tail extensions, full scalar odd-weight jets, selected finite arithmetic reductions, complex masses with controlled branch jumps, rational-shift projections, cubic Stieltjes coefficient reduction, and the remaining reconstruction problems.

The unrestricted unequal-even-order reconstruction problem and the full gap-six family remain open. An ordinary one-variable integral representation does not assert finite reduction to a smaller prescribed special-value alphabet. The negative-point theorem supplies an alternative representation and does not prove the separate higher Fourier/Bessel-order recurrence requested in the predecessor programme.

## Reproduce the checks

The recorded environment used Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0, and standard pdfLaTeX packages. Python dependencies are pinned in `requirements.txt`.

From the extracted package directory:

```sh
python3 verification/verify_manifest.py
python3 -m pip install -r requirements.txt
python3 verification/run_all.py
python3 build.py
```

For exact symbolic checks alone:

```sh
python3 verification/run_all.py --exact-only
```

The standalone TeX file can also be compiled directly with `pdflatex`; repeat the run until cross-references settle. The supplied build script performs three passes and checks the labels, bibliography keys, final references, and layout warnings. Its dependencies are listed in `preamble.tex`; no shell-escape feature is needed.

The six verification programs passed in the recorded full run. They include **123 exact symbolic assertions**, **32 contact/Stieltjes decimal diagnostics**, and independent checks of full and compact spectral densities, weighted sums, polylogarithmic transforms, and negative-point jets. The runner checks all 29 recorded residual fields in the latter four reports against a conservative `1e-40` threshold. A residual field count is not a count of independent mathematical theorems or distinct parameter cases.

`data/verification_summary.json` records program outcomes. Separate JSON files preserve exact and decimal evidence. These calculations check finite algebra and numerical consequences; the article's all-order conclusions depend on the written analytic proofs. The decimal runs are not interval certificates, and the package is not a proof-assistant formalization or external peer review.

Verification and rebuilding overwrite generated reports and may change PDF metadata. Run the distributed-byte manifest check before such regeneration; changed hashes afterward need not indicate changed mathematical content.

## Source provenance and integration

`data/source_manifest.json` records the seven incoming archives and eight directly inspected source texts, with repository paths, source roles, SHA-256 hashes, and the immutable commit. Each listed local byte string was compared with its pinned Git blob before hashing. Archive identities record targeted inspection and comparison, not a complete proof audit or replay of every historical verification program.

Suggested integration sequence:

1. Preserve the original incoming archives as historical evidence.
2. Add this package as a research continuation, retaining its modular sources, verification programs, result files, and attribution.
3. Review the single correction patch and the proposed status updates against the current repository state.
4. Integrate the proved results into the manuscript using the article labels in `CLAIMS.json`; retain the stated domains, cutoff/regulator conventions, and distinctions between new and inherited results.

No repository source was modified and no remote publication or repository action was taken during preparation of this package.

## Package map

| Path | Purpose |
|---|---|
| `Boundary_Contacts_and_Logarithmic_Spectral_Integrals.pdf` | Complete article |
| `Boundary_Contacts_and_Logarithmic_Spectral_Integrals.tex` | Self-contained LaTeX source |
| `article.tex`, `preamble.tex`, `references.tex`, `sections/` | Modular sources |
| `build.py`, `requirements.txt` | Rebuild instructions and dependencies |
| `verification/` | Reproducible exact and decimal verification programs |
| `data/` | Results, provenance, PDF checks, and distributed-file hashes |
| `integration/` | Proposed source correction and research-status changes |
| `CLAIMS.json` | Result/status/dependency map |

Temporary TeX files, page renders, caches, and build logs are excluded from the distributed ZIP. `data/pdf_build_report.json` records the clean build; `data/pdf_visual_review.json` records the rendered-page review. `data/package_manifest.json` hashes the other distributed files and deliberately excludes itself.
