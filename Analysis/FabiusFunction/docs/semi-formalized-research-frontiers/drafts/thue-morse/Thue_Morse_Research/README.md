# New Deductions from Thue–Morse Cancellation

**Date:** 4 September 2026  
**Subject:** Global spline corrections, exact dyadic reconstruction,
local-limit expansions, and spectral moment twins.

## Files

- `Thue_Morse_New_Deductions.tex`: self-contained LaTeX article.
- `Thue_Morse_New_Deductions.pdf`: compiled article.
- `verify.py`: reproducibility script; Python 3.10+, standard library only.
- `verification_results.json`: output from the verification run used for the article.
- `README.md`: this file.

## Main results

The article proves a global all-orders correction expansion for the finite
uniform-convolution approximations to the Rvachev up-function. Its explicit
supremum-norm bound is asymptotically sharp; the leading uncorrected constant
is 4/9. A fixed-order Hölder version and an increasing-order absolute-error
certificate are also included.

At a fixed dyadic point of reduced denominator 2^d, the finite spline
values eventually form an exact polynomial in 4^(-m) of degree floor(d/2).
A finite extrapolation formula recovers the limiting value exactly, with
absolute input-error amplification less than two independently of order.

For the positive coefficient array obtained by summing a finite Thue–Morse
block m times, there is an exact finite differential conversion to the
splines, an explicit uniform all-orders local-limit expansion, and an exact
terminating version on fixed dyadic odd-level lattice subsequences. The
leading normalized uniform lattice error constant is 4/3.

Finally, the normalized Fourier-energy measure has even moments 2^(r(r+1)).
Explicit symmetric lognormal and purely atomic measures share these moments.
A separated geometric family extends the norm and moment calculations.

All hypotheses, normalizations, and proofs are in the article. In particular,
absolute approximation error must not be mistaken for relative endpoint
accuracy, and lattice point-mass convergence must not be mistaken for total
variation convergence to a density.

## Reproduce the checks

```sh
python verify.py
```

This overwrites `verification_results.json` in the same directory. Algebraic
assertions use integers and `fractions.Fraction`. The recorded run passed
3,796 categorized exact checks. Finite theta-sum checks are numerical and
are labeled separately. These checks supplement, rather than replace, proofs.

The direct signed spline formula can involve large cancellations. The
implementation performs them exactly. The stable extrapolation weights do
not by themselves make naive floating-point evaluation of the inner signed
sums stable.

## Compile the article

With a full TeX Live installation (including New TX fonts and the listed
standard packages):

```sh
pdflatex Thue_Morse_New_Deductions.tex
pdflatex Thue_Morse_New_Deductions.tex
pdflatex Thue_Morse_New_Deductions.tex
```

No separate bibliography file, illustrations, generated table files, or Python
execution is required to compile the LaTeX source. No font files are distributed.

## Research status

The article extends the supplied ProveIt Thue–Morse Atlas and cites classical
background explicitly. It presents proved deductions and potentially novel
refinements relative to the inspected source, not an assertion of exhaustive
worldwide publication priority. It has not been peer reviewed or formalized
in Lean, and no repository files were modified.

The live repository URL inspected is recorded in the article. It is a `main`
branch URL, not an immutable commit reference.
