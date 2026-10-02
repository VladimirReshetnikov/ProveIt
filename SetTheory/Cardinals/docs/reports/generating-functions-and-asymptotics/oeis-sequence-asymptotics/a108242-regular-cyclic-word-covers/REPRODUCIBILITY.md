# Reproducibility record

Release date: 2 October 2026.

## Executed checks

The extended exact computation at (n,r)=(48,7) was freshly recomputed and passed, alongside the main replay suite. The final additional-grade and partition-count regressions also passed, both independently and in the final fresh-extraction replay. That count visited 6,727,282 memoized states and took 75.2244 seconds in this run. Both exact counts match the stored independent reference input. Timings are not mathematical data and vary by machine.

The released archive was then safely extracted to a fresh directory. Every manifest hash was verified before an ordinary replay, which passed using only package-relative paths. That ordinary replay intentionally reused the saved (48,7) count and reported `extended_case_recomputed_in_this_run: false`; all other requested checks were recomputed. The separately recorded extended run has that field set to true in `results/exact-results.json`.

The tests comprise 54 OEIS terms, two eighth-order rational coefficient lists, 30 signed literal-necklace/logarithmic-product comparisons, 24 signed literal-product/Python/C++ comparisons, cubic symbolic coefficients, finite general-length coefficient regressions (including lengths 5, 6, 8 and 9), 34 independent partition-count checks, quartic exact counts, and degree-two/inverse formal checks. The 18 numerical cases in the extended run retain complete exact integers in JSON. Floating-point ratios and errors use 80 decimal digits of working precision and are not interval-certified bounds.

## Document checks

The final article has 18 pages. A clean-extracted PDF rebuild passed using only package-local caches, including generation of the missing LaTeX format and font map from installed TeX files. All 18 rebuilt pages were pixel-identical to the visually approved rendering. All pages were rendered and visually inspected. Equations and tables are readable, without clipping or overlap. The last LaTeX build had no overfull or underfull boxes, undefined references or unresolved citations. The PDF contains a linked table of contents, equation references and primary-source bibliography links.

## What the checks establish

Exact finite and symbolic checks test the formulas and implementations. They do not prove uniform asymptotic errors. The weighted-mode, collision-forest and Taylor-remainder arguments in the article supply that proof. Integrity checks establish byte consistency; the fresh extraction replay tests portability in the stated dependency environment.

The package does not claim an exhaustive novelty search, convergence of the infinite asymptotic series, a uniform positive-compact critical expansion down to lambda=0, or a scalar inverse for an unspecified varying-degree path.
