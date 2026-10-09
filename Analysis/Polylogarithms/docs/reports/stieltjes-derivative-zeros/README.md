# Stieltjes parameter-derivative research continuation

## Article and status

**Zeros, Distribution Modules, and Regularized Duality in the Stieltjes Parameter-Derivative Tower** is a 24-page, self-contained mathematical article prepared for Vladimir Reshetnikov's ProveIt project on 7 October 2026.

The article is `Analysis/Polylogarithms/docs/articles/stieltjes-zeros-distribution-duality.tex`, with the compiled PDF alongside it. Its scope is the generalized-Stieltjes, Hurwitz-jet, and cyclotomic-polylogarithm thread in the supplied drafts, not an exhaustive audit of the entire Polylogarithms directory.

The article supplies ordinary mathematical proofs of a global zero bound, a uniform all-order expansion for large parameter-derivative zeros, an all-denominator formal distribution-rank theorem, its finite-jet extension, and an all-order regularized Dirichlet functional equation. Classical ingredients are attributed. The explicit zero-location results and their positive Lerch deformation are proposed research contributions; exhaustive literature priority has not been established. This AI-assisted research draft has not been independently refereed or verified by a proof assistant. No arithmetic independence theorem is claimed.

## Main results

For every fixed Stieltjes index `n >= 0` and parameter-derivative order `k >= 1`, `gamma_n^(k)(a)` has at most `n` positive zeros, counted with multiplicity. For fixed `n`, all `n` zeros are present and simple for all sufficiently large `k`. These assertions extend to the positive Lerch deformation `0 <= rho <= 1` described in the article, with a large-order threshold uniform in `rho`.

The zeros have complete expansions in descending powers of `k`. Their slopes are the exponentials of negatives of the real roots of reciprocal-gamma Appell polynomials. The first two coefficients are explicit, the next has a directly implementable formula, and an all-order recursion is proved. At `n = 1` there is a unique simple positive zero for every `k`; it lies strictly above `exp(H_(k-1))`, at or below `exp(H_k)`, decreases with `rho`, and moves right with `k`.

The formal distribution quotient has dimension `phi(q)`, and dimension `phi(q)-1` after making the integral coordinate background, for every denominator and every complex weight with positive real part. The jet version is a free module of the same rank. These are dimensions modulo specified relations, not dimensions of spans of actual numerical constants.

The functional equation is normalized after removing the simple trivial zero. This gives the exact `L''(-k)/(2 L'(-k))` first logarithmic derivative and an explicit formula at every higher order.

## Additive integration

Copy the `Analysis/Polylogarithms/` subtree into the matching repository directory. All filenames in this bundle are new. No historical article is overwritten and no GitHub commit or pull request is created by this bundle.

The focused review and the copy-ready correction fragment are:

- `docs/reports/stieltjes-zeros-distribution-duality-review.md`
- `docs/reports/stieltjes-zeros-distribution-duality-corrections.tex`

Paths in that pair are relative to `Analysis/Polylogarithms/`. The `.tex` correction file is intentionally a fragment, not a second standalone paper. Read the review before applying individual passages to historical sources. Rebuild the corresponding historical PDF whenever its source is edited. The article itself already includes the full correction discussion.

Root support files have project-specific names to avoid replacing an existing repository README or Makefile. `PROVENANCE.stieltjes-tower.json` pins the reviewed commit and source blob hashes. Original source bytes are not included. `SHA256SUMS.stieltjes-tower` hashes the delivered files except itself.

## Build and test

From the extracted bundle root, with Python and the listed LaTeX packages available:

```sh
python -m pip install -r Analysis/Polylogarithms/tools/stieltjes_tower/requirements.txt
make -f Makefile.stieltjes-tower pdf
make -f Makefile.stieltjes-tower test
```

The PDF build uses three pdfLaTeX passes and an isolated `.build/stieltjes-tower` directory. The article has an embedded bibliography and no external data or image inputs. Standard packages used are `fontenc`, `inputenc`, `lmodern`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `booktabs`, `longtable`, `array`, `microtype`, `enumitem`, `fancyhdr`, `xurl`, and `hyperref`.

Direct test command:

```sh
python Analysis/Polylogarithms/tests/stieltjes_tower/verify.py --full
```

Omitting `--full` reduces the exact-matrix test ranges. Tests regenerate the three files under `data/stieltjes_tower/`; the elapsed time in the JSON will therefore change. Check the distributed manifest before rerunning tests. Do not use Python's `-O` option, which disables test assertions.

Tested environment: Python 3.13.5, mpmath 1.3.0, SymPy 1.14.0, and pdfLaTeX. Python 3.10 or newer is expected to work, but other versions were not tested in this run. The full suite took about 78 seconds in the preparation environment; runtime is machine-dependent.

## Verification record

The delivered `verification.json` records **380 passing cases**, including **45,105 exact rational coefficient equalities**. Independent exact matrix ranks were checked for `2 <= q <= 24` at weights 2 and 3. Prime-step extensions were checked through denominator 60 at weights 2, 3, and 7. Symbolic central-moment coefficients, Mellin quadrature, direct Stieltjes differentiation, Lerch series, both parities of the functional equation, a complex character, Fourier order derivatives, harmonic zero brackets, and zero asymptotics are also tested.

Numerical tests use a 55-digit target precision with scale-dependent extra precision before rescaling tiny Hurwitz jets. The guard is `10 + ceil((k+1)*max(0,log10(a)))` digits. Four large-order roots are separately cross-checked using scale-first gamma-expectation quadrature. Fourier order derivatives are evaluated by a fixed Cauchy contour sum, avoiding unstable tiny-step differentiation at integer orders. These implementation issues and their resolutions are recorded in the article.

**Numerics are not certified intervals.** mpmath's arbitrary precision is not outward-rounded interval arithmetic. The truncation bound is proved analytically in the paper, but its implementation returns an ordinary floating-point evaluation, not a machine-certified enclosure. Decimal roots in the CSV are approximate roots, not isolating intervals. Exact finite tests supplement, rather than replace, the all-parameter proofs.

`pdf_validation.json` records the final compilation and layout checks. Every page was rendered with Poppler; contact sheets and selected full-size mathematical pages were visually inspected. The rendered images are preparation artifacts, not bundled research dependencies.

## Further research

Section 11 gives eight concrete directions: effective uniform zero thresholds; exact zero counts at every derivative order for the undeformed Stieltjes family; growing-index root and slope asymptotics; monotonicity of all zero branches in the deformation; interval-certified computation; resonant-weight integral distribution modules; formalization and Fourier certificate transport; and arithmetic relations beyond the formal module.
