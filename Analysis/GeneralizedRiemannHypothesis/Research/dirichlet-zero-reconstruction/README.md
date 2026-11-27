# Recovering Dirichlet characters and twist packets from zeros

November 27, 2026

## Papers

**character_windows.pdf** proves uniform recovery of every primitive Dirichlet character of conductor at most Q from positive zero ordinates up to O(log²(2Q)/log log(3Q)), using the Dirichlet GRH theorem of the cited Lean project. The translated-window theorem, a lower bound for the cost of matching the lists, and a finite-alphabet recovery theorem appear in the same paper. The constants in the analytic bounds are not evaluated numerically.

**twist_measurements.pdf** gives sharp fixed-list and adaptive query counts for a local cyclic twist histogram. The counts apply to exact individual balanced Fourier products in the worst case over integer multiplicities. The algebraic results are unconditional. Their application to pooled positive Dirichlet zero ordinates uses Dirichlet GRH.

## Rebuild

Run the following in this directory on a standard TeX Live installation.

```sh
pdflatex -halt-on-error character_windows.tex
pdflatex -halt-on-error character_windows.tex
pdflatex -halt-on-error twist_measurements.tex
pdflatex -halt-on-error twist_measurements.tex
```

Keep kernel_part.tex beside character_windows.tex. Each paper contains its bibliography.

## Reproduce the checks

From the checks directory run these commands. Each script has a corresponding saved .txt output. The two exact checks use the Python standard library. The numerical zero scan uses mpmath, and the decoder demonstration also uses SciPy. The delivered outputs were reproduced with mpmath 1.3.0 and SciPy 1.17.0.

```sh
python prime_probes.py
python check_twist_measurements.py
python complex_zeros.py
python decoder_demo.py
```

The prime-probe check certifies a bound for the contribution of nearby prime powers using integer arithmetic. The twist check uses integer polynomials modulo cyclotomic polynomials. The two numerical scripts scan for sign changes and test residuals of Dirichlet L-values. The decoder example illustrates signs, normalization, and recovery at finite height. Completeness of the numerical lists has not been certified. The general proofs do not rely on any numerical example.

## Source snapshots and proof status

- [grh-lean exported theorems](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean)
- [grh-lean definitions](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean)
- [grh-lean reported checks](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/README.md)
- [ProveIt recovery results and questions](https://github.com/VladimirReshetnikov/ProveIt/blob/dec3e4f216305071186a1cc4c42fe1cdb38df9be/Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex)
- [ProveIt short-interval results](https://github.com/VladimirReshetnikov/ProveIt/blob/dec3e4f216305071186a1cc4c42fe1cdb38df9be/Analysis/GeneralizedRiemannHypothesis/Article/sections/zer.tex)

The two new papers provide research proofs, with comparisons to the linked collection and to related published work. Upstream machine checks are reported in the source repository. The new proofs have not been Lean-formalized or independently peer reviewed.
