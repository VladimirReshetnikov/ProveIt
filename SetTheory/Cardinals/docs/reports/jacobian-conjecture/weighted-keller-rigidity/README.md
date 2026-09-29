# All-Degree Rigidity of a Weighted Keller Class

**Classification, degenerations, and an obstructed double point**  
Research report prepared for Vladimir Reshetnikov, September 24, 2026.

## Read the article

`article.pdf` is the compiled report. `article.tex` is self-contained LaTeX,
including the bibliography; no separate bibliography file or figure assets
are required.

The report develops the Jacobian-conjecture research direction in the
ProveIt repository. Its baseline is the existing weighted map and the
repository's finite, degree-seven coefficient/sparsity calculations. The
original counterexample is not presented as a new result of this report.

Pinned repository snapshot:

```
e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9
```

Relevant repository paths:

```
Algebra/JacobianConjecture/README.md
Algebra/JacobianConjecture/Research/README.md
Algebra/JacobianConjecture/Research/verify_equivariant_sparsity.py
```

Immutable source URLs are in the article's bibliography.

## Results established in the article

For the source weights (-1,1,2), put t=xy and v=x^2*z. Write a weighted map
as (p(t,v)/x^2, q(t,v)/x, x*r(t,v)), with polynomiality of the lift imposed.
Over any characteristic-zero field, after normalizing the three nonzero
origin coefficients:

1. If p and q are affine in v and r is affine in (t,v), the Keller maps
   are exactly an explicit tame family and a two-parameter diagonal orbit
   of the known map. Every noninvertible map in this class has coordinate
   degrees (7,6,4) and 16 expanded monomials. There is no input degree bound.
2. The result extends to r=R(t)+gamma*v with gamma a scalar and arbitrary
   polynomial R. Every noninvertible member is a classified map composed
   on its source with (x,y,z) -> (x,y,z+y^2*h(x*y)). Its possible maximum
   degrees are precisely 7 and every even integer at least 8.
3. The reduced closure of the normalized nonconstant affine-r branch is
   an embedded parameter plane. Its invertible members are exactly its
   coordinate axes. Fixing r=1+t+v gives rigidity over every reduced
   coefficient algebra, in all ordinary degrees.
4. In the fixed degree-seven coefficient scheme with r=1+t+v, the full
   coordinate algebra is Q[epsilon]/(epsilon^2), not just a reduced point.
   A nonzero tangent is explicitly obstructed at second order. Restoring
   the two nonzero coefficients of r gives a torus times this double point.

The article includes complete proofs, explicit inverse/collision formulas,
an exact ideal presentation, and nine further research directions.

## Reproduce the finite checks

Python 3.10 or later and SymPy are required. The supplied run used the
exact versions recorded in `verification.json`.

```sh
python -m pip install -r requirements.txt
python verify_results.py --output verification.json
```

The successful run has **13 PASS groups**. `verification.txt` is the
captured output. These are exact symbolic identities and rational linear
algebra checks: no random samples, numerical tolerances, or floating-point
arithmetic are used. Four explicit monomial choices of the source-shear
polynomial additionally check the general degree formula proved in the
article; these examples are not represented as an exhaustive proof.

The script reconstructs the coefficient equations and derivative matrix.
The JSON includes the equations, full matrix, coordinate/monomial order,
tangent, rank minor, obstruction vector, and cokernel functional.

Particularly small certificates are:

- an 11-by-11 minor with determinant -18874368;
- a one-dimensional tangent with q21 component equal to 1;
- a left-kernel functional pairing with the quadratic residual to -1/72.

The script checks one ideal containment by direct substitution. The reverse
containment and the all-degree statements use the proofs in the article.
No claim of an exhaustive computer search or a proof-assistant verification
is made.

The verification script does not access the network, download anything,
execute repository code, or modify the ProveIt repository.

## Build the PDF

A standard TeX Live or MiKTeX installation with the packages imported at
the top of `article.tex` is sufficient.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex article.tex` twice. The source uses standard
LaTeX fonts; font files are not distributed in this archive.

## Scope and verification status

These are research-draft results with human-readable proofs and exact
companion checks. They have not been formalized in Lean or Rocq, externally
peer-reviewed, or established to have publication priority. The article
carefully distinguishes its extensions from the pre-existing map and
repository calculations.

The classification does not cover unrestricted polynomial Keller maps,
quadratic dependence of p or q on v, or an arbitrary nonconstant
coefficient of v in r. The all-degree field/reduced-ring conclusions do
not prove stabilization of the nonreduced coefficient schemes at higher
degree. The double-point and torus-times-double-point claims explicitly
refer to the degree-seven coefficient problem.

## Contents

- `article.pdf`: compiled research report.
- `article.tex`: complete LaTeX source and bibliography.
- `verify_results.py`: exact verification script.
- `verification.json`: machine-readable equations and certificates.
- `verification.txt`: successful run output.
- `requirements.txt`: dependency version for the reproduced run.
- `README.md`: this file.
