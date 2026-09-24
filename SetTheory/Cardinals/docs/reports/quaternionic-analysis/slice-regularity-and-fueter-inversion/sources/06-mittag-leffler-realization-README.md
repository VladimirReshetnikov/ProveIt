# Global Fueter Primitives and Spherical Singularities

## Affine periods, complete principal parts, and a Mittag–Leffler realization theorem

Research manuscript dated 21 September 2026. The compiled article is 22 pages.

## Included files

- `global_fueter_primitives.pdf`: the complete article, with proofs, examples,
  literature comparisons, references, and a verification appendix.
- `global_fueter_primitives.tex`: the self-contained LaTeX source.
- `verify_results.py`: exact symbolic checks and numerical checks of the
  explicit generators, period normalizations, and critical-growth constant.
- `verification.txt`: recorded output from a successful verification run.
- `README.md`: this guide.

The supplied `quaternionic_analysis.tex` was the starting exposition. It has
not been modified or silently incorporated as a new result; it is identified
as reference [1] in this manuscript. The new article is self-contained apart
from standard results of one-variable complex analysis and elementary topology.

## Main results

1. Two closed quaternion-valued one-forms, computable directly from an axial
   monogenic target, give a necessary-and-sufficient criterion for a global
   single-valued slice-regular Fueter primitive on the unchanged domain.
   Their periods are the coefficients of the primitive's affine monodromy.

2. Explicit logarithmic generators realize every period vector on a finite
   winding basis. The obstruction space has real dimension 8m for m upper-base
   holes. The article includes quantitative correction bounds, closed range,
   and a continuous normalized inverse on the zero-period subspace.

3. Reflected generators extend through the real axis. The complement of the
   unit imaginary sphere gives explicit smooth, single-valued axial monogenic
   targets without global slice-regular Fueter primitives. One counterexample
   is also a sphere average of the ordinary Cauchy–Fueter kernel. A separate
   complex-analytic argument verifies its obstruction.

4. A complete spherical singular normal form consists of an affine residue
   pair, the Fueter transform of a complexified-quaternionic Laurent principal
   part, and a unique regular remainder. Modulo removable germs, uniform
   O(rho^(-N)) singularities have real dimension 8N. The critical removability
   condition is o(rho^(-1)), and exact leading growth constants are proved.

5. A Mittag–Leffler theorem realizes arbitrary locally finite families of
   finite spherical principal parts and affine residue pairs. The construction
   uses the globally single-valued second derivative of a local primitive.

## Compile the article

Use a LaTeX installation providing the packages named in the preamble
(including `newtxtext`, `newtxmath`, `microtype`, and `hyperref`):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error global_fueter_primitives.tex
```

Alternatively, run `pdflatex global_fueter_primitives.tex` three times to
resolve the contents and cross-references. No BibTeX invocation, external
figures, or shell escape is needed. The bibliography is in the source.

## Run the independent checks

The script requires Python, SymPy, and NumPy. The recorded successful run used
Python 3.13.5, SymPy 1.14.0, and NumPy 2.3.5.

```sh
python -m pip install sympy numpy
python verify_results.py
```

The script raises an exception if any exact identity fails or a numerical
check exceeds its stated tolerance. Seven symbolic residuals simplify exactly
to zero. In the recorded period tests, the largest component error was about
2.62e-14. The numerical asymptotic experiment uses the exact supremum over
imaginary units but samples the remaining planar angle; it is not an interval
certificate or the proof of the asymptotic theorem.

## Research status and limitations

The local Fueter transform, its affine kernel, the Vekua equations, and local
inverse constructions are established results, not claims of novelty here.
The proposed new contributions are the explicit global-period classification,
its realized obstruction space, the spherical normal form and sharp growth
laws, and the simultaneous realization theorem. The literature discussion
records the scope of the primary sources checked; a negative search does not
establish absolute priority.

The results concern axial monogenic functions and their slice-regular
primitives. They do not classify arbitrary Cauchy–Fueter singularities.
The local spherical estimates assume a nonreal sphere and are not uniform as
its radius tends to zero. The realization theorem does not impose boundary
norms or conditions at infinity. The article distinguishes an unqualified
same-domain surjectivity formulation from local or continuation-based inverse
statements rather than rejecting the inverse Fueter theory as a whole.

All proofs are in the article. Symbolic and numerical checks supplement them;
they are not independent peer review or a formal proof-assistant verification.
