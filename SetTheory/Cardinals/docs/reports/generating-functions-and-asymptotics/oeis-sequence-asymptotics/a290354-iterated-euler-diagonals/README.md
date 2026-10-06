# Report 225

Diagonal and proportional height asymptotics for iterated Euler transforms

5 October 2026. An unrefereed mathematical research report, not a proof-assistant formalization.

## Results and scope

The report proves a_n ~ c (2n/pi)^n n^(-4/3) for OEIS A290354, identifies a finite strictly positive amplitude by an absolutely convergent Fourier integral, and proves uniform proportional-height asymptotics for the A290353 array when n/m lies in a fixed compact subset of (0,infinity). The density is smooth and strictly positive away zero. Fixed and square-root height shifts and the exact floor phase are included; the Gaussian-shaped height profile is not a probability central limit theorem. A Lambert W inverse gives eventual nearest-integer recovery at exact sequence values. There is no effective onset, certified decimal value of c, general integer-threshold guarantee, or full all-orders asymptotic theorem.

The numerical value near 4.4923 agrees with Kotesovec's conjecture only numerically. Polynomiality and the zigzag/tangent leading profile are credited to Kaneiwa; the distinct labelled Bell antecedent is distinguished. Bechtloff Weising's algebraic antecedent and the related labelled iterated-Bell methodology are credited. No worldwide novelty claim is made.

## Requirements

Exact code and tests require Python 3.11+ and only its standard library. The PDF builder requires pdfTeX/TeX Live with geometry, fontenc, lmodern, microtype, amsmath, amssymb, amsthm, mathtools, booktabs, hyperref, bookmark, and enumitem. The optional amplitude diagnostic needs NumPy and SciPy. The authoring runs used Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0, and pdfTeX 1.40.26. Optional floating-point libraries do not provide interval certification.

The builder creates a private pdfLaTeX format and never installs packages or changes user-global TeX configuration. For the stripped Debian tree it uses the existing unindexed /usr/share/texlive/texmf-dist directory when needed. Byte identity is expected for identical toolchains; different TeX/font versions can change PDF bytes.

## Exact commands

From this directory:

    python -B code/exact_euler.py --max-index 20
    python -B code/exact_euler.py --max-index 20 --height 10
    python -B code/test_exact.py --cap 640
    python -B -O code/test_exact.py --cap 640
    python -B code/coordinate_series.py --order 9

Degree and height are independently capped at 640. The independent finite product routine is capped at degree 20 and is tested across all entries through degree 12 and height 12. A full diagonal run uses O(N^3) integer arithmetic operations and O(N) stored integers, with growing bit complexity; the cap 640 test can take several minutes. Tests compare a separately generated exact fixture through n = 414 and the actual displayed OEIS terms n = 0..21. They do not claim a full OEIS b-file comparison.

The exact code stores F_h with constant zero. The user-facing A290353 row reports A(0,h)=1 and the A290354 diagonal reports a_0 = 1 separately. Every division and pass/fail invariant is checked with explicit exceptions, including under python -O. Local chunked decimal serialization handles long integers with PYTHONINTMAXSTRDIGITS=640; no global digit-limit setting is changed. Commands emit JSON on stdout and do not mutate source files.

The formal-coordinate generator supports orders 0..12; its public tests validate the nine coefficients used by the diagnostic. It proves only finite rational identities, not convergence or an analytic error bound.

## Optional numerical experiment

    python -B code/amplitude_diagnostic.py --depth 100 --sigma 0 --cutoff 3000 --step .02 --out /tmp/new_amplitude.json

The output path must be new. The supported depth is 50..200, sigma is -2..0, cutoff is 10..10000, step is 0.005..0.1, and at most one million intervals are allowed. A Simpson mesh is adjusted to an even number of intervals and the actual spacing is reported. The calculation solves a truncated Fatou inverse, propagates value/derivative, and subtracts a rational Fourier kernel. It has no interval error controls. Varying parameters is a numerical check, not proof of any digits of c.

## Source preserving PDF and ZIP build

Choose a new output directory outside this source directory, with no symlink ancestor:

    PYTHONINTMAXSTRDIGITS=640 python -B build.py --out /tmp/report225_normal --cap 640
    PYTHONINTMAXSTRDIGITS=640 python -B -O build.py --out /tmp/report225_optimized --cap 640

The cap option is 414..640 and defaults to 640. The build invokes the exact tests, including rational formal-coordinate checks, in the same optimization mode as its parent. Optional NumPy/SciPy diagnostics are not required for a build. No packages are installed automatically.

The builder checks MANIFEST.sha256 (including missing or unexpected sources), compiles three times without shell escape, rejects overfull boxes/missing glyphs/undefined references, checks source bytes were preserved, and writes Report225.pdf, Report225.zip, and a deterministic build receipt. The ZIP has sorted members, fixed timestamps, and uncompressed storage. Logs and the private TeX working directory are kept outside the ZIP. Compare complete ZIP bytes and member lists/bytes between builds, not only summary hashes. Reproducibility does not replace mathematical review or inspection of each rendered PDF page.

An extracted ZIP can itself be rebuilt. The manifest excludes only the two reserved generated root files Report225.pdf and build_checks.json; these are regenerated and included exactly once. A builder output directory must not preexist and must be outside the source package.

## Contents

- src/report225.tex: complete editable proof and discussion
- code/exact_euler.py: exact recurrence and independently implemented product method
- code/test_exact.py: optimization-safe exact tests and fixtures
- code/coordinate_series.py: exact formal Fatou coefficients
- code/amplitude_diagnostic.py: optional noncertified numerical experiment
- data/exact414.json: independent generated exact fixture
- data/amplitude_diagnostic.json and data/amplitude_grid.json: illustrative floating-point results, including six parameter-sensitivity checks
- sources/: source ledger and the 22 displayed OEIS numerical terms
- build.py and MANIFEST.sha256: deterministic source-preserving builder and integrity check

No external publication, repository update, or OEIS communication is performed by these scripts.
