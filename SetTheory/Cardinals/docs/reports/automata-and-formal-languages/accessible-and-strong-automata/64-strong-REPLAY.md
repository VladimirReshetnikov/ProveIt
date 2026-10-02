# Reproduction results

A fresh isolated replay was completed on 2 October 2026 with Python 3.12.14, mpmath 1.3.0, and sympy 1.14.0. Each computation was run from the shipped scripts in a fresh working directory. All 13 generated JSON outputs match the distributed values; only the machine-dependent `seconds` fields are ignored.

## Checks passed

- Fixed-order generator: k = 2,3,4 through degree five at 70-digit output precision
- Higher-precision replay: 70 versus 100 digits for k = 2,3,4; 60 versus 100 digits for k = 500 at first order
- Exact complex phase checks for exponents 0 through 10004
- Independent reconstruction of p and b through degree three, tau through degree two, and the small-state source through degree three; all coefficient differences below 1e-68
- Exact integer auxiliary and strong recurrences through n = 600 for k = 2,3,4, with separately computed Stirling diagonals
- Direct graph enumeration and the strict renewal identity
- Exact unrooted sectors, prime-index corrections, one-letter cycles, and terminal-subset classes
- Connected cyclic-voltage lifts for all strong binary quotients with (m,l) = (1,2), (1,3), (2,2), and (2,3)
- 36 original smooth-inverse evaluations for B/R/U, plus 48 all-model checks including labeled L; the degree-five smooth root improves the two-correction approximation in every tested case

These checks validate finite implementations and examples. The proof in the article establishes the asymptotic theorem. None of the numerical outputs is an interval certificate, and no inverse experiment certifies an unconditional ceiling rule.

## Article build and rendering

The TeX source compiles in three passes with package-local format/font-map fallbacks. The finished PDF has 21 pages. Every page was rendered and visually inspected; there are no missing references, overfull boxes, clipped equations, or overlapping text in the final build. A fresh extracted-package build was also used to verify that the TeX source and helper snippet are self-contained with the documented installed dependencies.

## Repeat locally

    bash replay.sh
    bash build.sh
    python verify_manifest.py

The build should be run before checking the distributed manifest only if exact PDF reproducibility is expected from your TeX installation; different TeX/font versions may produce a valid but byte-different PDF. The mathematical replay does not overwrite the distributed data.
