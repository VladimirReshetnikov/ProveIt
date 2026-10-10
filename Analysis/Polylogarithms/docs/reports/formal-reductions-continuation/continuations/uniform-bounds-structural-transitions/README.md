# Polylogarithms: Uniform Bounds and Structural Transitions

Research continuation prepared for Vladimir Reshetnikov and the ProveIt
programme, 10 October 2026.

The complete article is **article.pdf**. Its source is **article.tex**
with the files in **sections/** and **references.tex**. This package is
self-contained for compilation and certificate replay; it does not need
the original repository checked out.

## Baseline and scope

The audited baseline is ProveIt commit
**3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f**, principally
Analysis/Polylogarithms/docs/manuscript.

The article advances four specific research directions. It gives
ordinary mathematical proofs and exact arithmetic certificates.
It is not a proof-assistant formalization, and it makes no claim
that all of the source repository has been independently audited.
The literature comparison is recorded explicitly; novelty statements
refer to the pinned repository unless otherwise qualified.

## Principal results

1. **Uniform Euler errors at every positive real order.** A sharp
   two-point kernel inequality proves the optimal global constant
   C* = max over b>0 of beta(b) + 2^(-b) eta(b).
   The axis maximum was already proved in the manuscript; the
   new step is the comparison of every scaled remainder with that
   axis quantity. A finite rational certificate proves C* < 57/50.
   The argument also gives a sharp analogue for harmonic sums built
   from arbitrary finite positive moment measures, with universal
   constant (1+sqrt(2))/2 times the two measure masses.

2. **New remainder identities and moving-order limits.** A positive
   gamma-series identity expresses the scaled remainder using gamma
   increments. For b>1, its first term has error at most zeta(b)-1,
   independently of the outer order and truncation index. When the
   two orders grow proportionally to log N, the scaled remainder
   obeys an explicit phase law, with normal-distribution profiles
   on the two boundaries. The optimal constant at index N tends
   to one, although the constant uniform over all indices is C*>1.
   An explicit axis construction proves a lower asymptotic of order
   N^(-log(2)/log(3/2)); the matching global upper asymptotic is
   stated separately as a new conjecture.

3. **Full binary depth under finitely many letter directions.**
   A free-Lie decomposition and confluent interpolation give an
   exact all-weight rank formula, covering the six Möbius maps
   and the larger formal GL(2) orbit. Their ranks already differ
   at weight seven. The article also supplies independently
   replayable certificates for a known Nielsen reduction at
   weight seven and its corresponding weight-eight obstruction.

4. **A certified radial degeneracy and two actual extrema.**
   Exact rational intervals isolate one simultaneous zero of the
   quadratic and quartic radial coefficients. The sixth coefficient
   is negative and the coefficient Jacobian is nonzero. This proves
   a quarter-power birth of a local maximum and a region with a
   minimum followed by a maximum. An explicit rational parameter
   pair has exactly two extrema on a specified radius interval;
   the certificate treats the actual implicit function and its
   infinite-series tails.

5. **Growing reflected log-gamma exponents.** A uniform saddle
   calculation proves Gaussian damping for m=O(sqrt(k)), with an
   explicit first correction. A separate signed-cut argument proves
   the half-term truncation law for m=O(sqrt(N)). A shifted saddle
   proves a small proportional m/k range for the coefficients,
   extends the Gaussian leading formula to m=o(k^(2/3)), and gives
   the cubic transition at m of order k^(2/3).

## Attribution and unchanged open problems

Charlton, Gangl, and Radchenko, *On functional equations for Nielsen
polylogarithms*, already give the weight-seven congruence used here
(Proposition 28 of arXiv:1908.04770v1), its Nielsen depth setting,
and the weight-eight nonreduction phenomenon. The article credits
those results. The supplied product expansion and normalized Lie
witness are independent certificates, not claims of new functional
equations or new period independence.

The S6 and revised S8 special-value evaluations remain conjectural.
The sharp rate conjecture for the index-specific Euler constant is
unproved beyond its matching lower bound. Global uniqueness of the
quartic radial transition is not proved.
The full-radius integer-order monotonicity questions also remain open.
The new proportional-exponent coefficient theorem does not, by
itself, enlarge the half-term remainder theorem.

The audit proposes a wording correction to an unsupported
non-elementarity assertion. It does not dispute the displayed
hypergeometric evaluation. See **integration/** for a checked,
exact-context patch and a chapter integration map.

## Build the article

Use a standard TeX Live installation with latexmk and the packages
listed in the article preamble:

~~~bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
~~~

The two supplied vector figures are sufficient for compilation.
Regenerating them is optional.

## Replay the exact certificates

Python 3.10 or newer is recommended. The four exact verifiers require
only the standard library:

~~~bash
python3 code/reproduce.py
~~~

This replays:

| Program | What it verifies |
|---|---|
| code/verify_euler.py | Rational axis enclosures, the 57/50 budget, selected Gaussian enclosures, and rejected false controls |
| code/verify_depth_orbits.py | Exact word ranks through weight ten, 155 height-one membership checks, product expansion, and primitive obstruction |
| code/certify_radial_degeneracy.py | The simultaneous-zero rectangle, transversality, sixth coefficient, and quarter-power prefactor |
| code/certify_two_extrema.py | Actual implicit roots, all necessary infinite-series tails, three derivative signs, and uniform concavity |

The replay records per-program logs in **data/replay_logs/** and a
summary in **data/reproduction_receipt.json**. Each certificate can
also be run individually. The two radial scripts must remain beside
one another because they share the exact interval primitives.

## Optional numerical work

Install the versions listed in **requirements-optional.txt**, or
compatible versions of mpmath, SymPy, and Matplotlib.

~~~bash
python3 code/reproduce.py --numerical --figures
~~~

The reflected-moment checks are slower than the exact certificates.
The optional computations compare independent numerical
representations and repeat precision; they are diagnostics, not
interval proofs. The raw data retain cases with substantial
preasymptotic deviations.

The article contains the actual-function radial plot and an Euler
bound plot. The plotting scripts, high-precision sample tables,
diagnostic receipts, and vector/raster figure files are supplied.

## Package map

| Directory or file | Contents |
|---|---|
| article.tex, article.pdf | Standalone article source and compiled document |
| sections/ | Modular mathematical sections, audit, and research agenda |
| references.tex | Primary bibliography and pinned source reference |
| code/ | Exact certificates, diagnostics, plots, and replay entry point |
| data/ | Exact rational outputs, numerical diagnostics, and replay logs |
| figures/ | Vector and raster figures with caption notes |
| integration/ | Proposed wording patch, chapter map, and macro/label notes |
| provenance/ | Source commit and hashes, literature comparison, and runtime versions |
| MANIFEST.sha256 | SHA-256 digests of the deliverable files |

The SHA-256 manifest records the delivered bytes. Optional replay regenerates
some outputs and the timing receipt, so their hashes can change afterward.

No repository changes were applied. The package is intended for
mathematical review and subsequent integration into ProveIt.
