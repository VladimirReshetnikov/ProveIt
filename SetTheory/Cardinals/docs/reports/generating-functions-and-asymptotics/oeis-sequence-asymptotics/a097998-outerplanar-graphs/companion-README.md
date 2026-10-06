# Report 170: reproducible labeled outerplanar-graph computations

This bounded, offline companion verifies the exact identities and finite coefficient calculations used in Report 170 for connected labeled outerplanar graphs (OEIS A097998) and all labeled outerplanar graphs (A098000). Graphs are abstract simple graphs on a fixed labeled vertex set, counted once regardless of embeddings.

The mathematics rests on the proof in the report. Finite comparisons do **not** prove convergence, establish an asymptotic error constant, certify decimal intervals, or give a certified inverse for a particular finite input.

## Run

Tested with Python 3.12.14, SymPy 1.14.0 and mpmath 1.3.0. Only the standard library and the two pinned packages in `requirements.txt` are used. With the dependencies installed, no network access is needed.

From this directory:

```sh
python build.py --output results-new
python -O build.py --output results-new-optimized
diff -r results-new results-new-optimized
python tests.py
python -O tests.py
(cd results-new && sha256sum -c SHA256SUMS)
```

`build.py` defaults to 200 positive terms per sequence and four asymptotic corrections. `--terms` accepts only 8 through 240. Values below 200 perform a deliberately smaller OEIS check; values 201 through 240 have no corresponding archived OEIS oracle. The default output, if `--output` is omitted, is `results-local` alongside the script. Every output path must be new and its parent directory must exist. Existing paths are rejected before computation and checked again at creation; nothing is overwritten. The shipped `results/` directory is the 200-term reference build. Use a different output name to reproduce it.

Commands can be invoked by absolute or relative script path from any working directory. Input paths are resolved relative to the scripts. Output data contains no host-specific paths, timestamps, timing measurements or random identifiers. With the same interpreter/library versions and unchanged inputs, ordinary and optimized Python builds are byte-identical. Runtime versions are recorded in `manifest.json`; different dependency versions may legitimately change decimal formatting or last-place numerical results.

`tests.py` builds both modes in temporary directories, compares every byte through SHA-256, tests no-clobber behavior, symlink parents and leaves, dangling links, parent traversal, existing regular files and CLI bounds, deliberately triggers checks under normal and optimized Python, rejects an altered algebraic certificate and fixture integrity failure, and verifies output hashes. It does not silently delete or replace user-selected result directories.

## Mathematical specification and conventions

Set `C(z)=sum(c_n z^n/n!, n>=1)`, `G(z)=exp(C(z))`, and `T=z C'(z)`. The block derivative is

```
b(u) = (1+5u-sqrt(1-6u+u^2))/8
     = u + u^2/2 + 3u^3/2 + 11u^4/2 + 45u^5/2 + ... .
T = z exp(b(T)),  psi(u)=u-u b(u)+integral_0^u b(t) dt,  C=psi(T).
```

The `u` term includes the single edge as a block; there is no singleton block. The connected EGF has `c_0=0`, although the archived A097998 b-file prepends the conventional entry 1. The all-graph constant is `g_0=1`. Only positive-index connected terms are compared to OEIS.

The selected algebraic root `tau` is in `(17076/100000,17077/100000)` and satisfies `3tau^4-28tau^3+70tau^2-58tau+8=0` and the unsquared equation `tau b'(tau)=1`. Exact certificates are in the basis `1,tau,tau^2,tau^3`; each list entry is a rational string. The root interval is an exact algebraic root selection, not a floating-point enclosure for every printed constant. The correction coefficients belong to `QQ(tau)`. Leading amplitudes also contain `sqrt(2*pi)` and exponential factors and are not claimed to belong to this field.

## What is checked

- `exact_counts.py`: exact radical square-root recurrence and a separately specified large-Schröder recurrence `S=1+uS+uS^2`. It obtains connected counts independently through integer Bell coefficients and ordinary rational exponentiation, and all counts through labeled SET convolution. Both block recurrences and both connected enumerations agree. Note that `S` has **large** Schröder coefficients `1,2,6,22,...`; for positive indices these are twice the little Schröder coefficients.
- Both 201-row OEIS fixtures are checked for consecutive indices, the zero convention, SHA-256 integrity, and all requested positive terms up to 200. The default verifies 200 positive terms for each sequence.
- Every simple graph on one through five fixed labels is separately enumerated. Existence of a cyclic vertex order with no alternating-endpoint edge pair tests outerplanarity; connectivity is tested directly. A graph is counted once when some order works. These literal counts are `c_1..c_5=1,1,4,37,602`, `g_1..g_5=1,2,8,63,893`.
- Component polynomials `f_n(v)=n![z^n]exp(v C(z))` through `n=8` are obtained by exact SET convolution. Their values at `v=0,...,n` verify both the direct Lagrange formula and its integration-by-parts form. The degree bound is at most `n`, so these are complete exact finite polynomial identities, not isolated spot checks.
- `exact_algebra.py`: irreducibility and exact real-root selection; a square-root recurrence for `b(tau exp(t))`; the unsquared saddle; exact Gaussian-moment extraction through four corrections. All coefficients of the marker polynomials `d_0(v),...,d_4(v)` are encoded in `QQ(tau)`. An a priori degree bound of `2j` makes exact interpolation at `2j+1` nodes complete; the resulting coefficients above degree `j` vanish exactly.
- Closed forms for `d_1(v)`, `d_2(v)`, the second mean/variance/connectivity corrections, and the four logarithm-plus-Stirling coefficients are checked as identities in the algebraic field.
- Algebraic evaluations are compared to the frozen high-precision regression fixture: absolute coefficient tolerance `1e-50`, constant tolerance `1e-60`, using 100 working decimal digits. This fixture has lower precision than the exact certificates and is not a definition of them.
- `independent_series.py` computes ordinary Taylor coefficients about `T=tau`, solves `T-tau=-X F(T-tau)^(-1/2)` coefficient by coefficient, integrates to recover `C`, and transfers half-integer powers using a central-binomial recurrence. It consumes no saddle derivatives or coefficients before its final comparison. Its central-binomial coefficients are themselves derived by an exact rational recurrence. It compares all four corrections at `v=0,1,2,0.5+0.3i` against the exact marker polynomials with absolute tolerance `1e-70`; leading amplitudes are compared at `1e-90`. This is an independent formal/numerical check, not a second analytic proof requiring an unprovided Delta-domain theorem.
- `diagnostics.py` records finite exact moment convolutions, scaled asymptotic remainders, and the continuous fourth-order inverse at exact sequence thresholds. It checks elementary moment ranges, a root-equation residual below `1e-85`, and strict increase at the sampled exact thresholds. There is intentionally no “convergence passed” or finite integer-bracket claim. In particular, the naive ceiling of the continuous root can differ from the exact inverse at an equality threshold.

All checks use explicit exceptions rather than removable Python assertions.

## Results and integrity

`results/` contains:

- `exact_counts.json`: decimal-string integers, OEIS checks, literal graph counts and exact component polynomials
- `exact_algebra.json`: algebraic certificates, exact marker polynomials, 100-digit evaluations and regression differences
- `independent_series.json`: independent Taylor/central-binomial evaluations and comparison errors
- `finite_diagnostics.json`: explicitly labeled finite moment, remainder and inverse diagnostics
- `manifest.json`: input hashes, result hashes, configuration and runtime versions
- `SHA256SUMS`: SHA-256 of all result JSON files, including the manifest (it does not recursively hash itself)

`fixtures/provenance.json` supplies provenance and immutable SHA-256 values for all four input fixtures. `exact_certificates.json` freezes every exact coefficient certificate and is compared explicitly against each fresh field computation. The values at `v=0,1,2` also matched previously independently generated exact rational-basis certificates before freezing. The numerical fixture is author-generated regression data, not an external numerical oracle or interval certificate. The b-files are archived public OEIS data, not current live queries. The result manifest records hashes of all source scripts, this README, requirements and fixtures. The package contains no third-party PDFs. Output I/O requires POSIX `O_NOFOLLOW` and `O_DIRECTORY`; parent traversal and symlink parents/targets are rejected, and all output creation is exclusive through a pinned directory descriptor.

## Sources and attribution

The leading asymptotic theorem and limiting shifted-Poisson law are established results. The report's role is explicit higher-order specialization and reproducible computation, not a priority claim for those theorems or for the existence of fixed-order expansions.

- [OEIS A097998](https://oeis.org/A097998), [archived b-file source](https://oeis.org/A097998/b097998.txt)
- [OEIS A098000](https://oeis.org/A098000), [archived b-file source](https://oeis.org/A098000/b098000.txt)
- [Bodirsky, Giménez, Kang and Noy, published article](https://web.mat.upc.edu/marc.noy/uploads/2013/05/Graphs-SP.pdf)
- [Earlier full BGKN preprint, a different source version](https://arxiv.org/abs/math/0512435)
- [Kang habilitation thesis](https://edoc.hu-berlin.de/server/api/core/bitstreams/23f83814-f327-4458-9787-474e750b8262/content)
- [Bodirsky–Kang enumeration and sampling](https://doi.org/10.1017/S0963548305007303)
- [Asymptotic study of subcritical graph classes](https://web.mat.upc.edu/juan.jose.rue/Research/Subcritical.pdf)

See the report for the version-specific amplitude discussion. The computations do not identify the origin of a source's numerical discrepancy.
