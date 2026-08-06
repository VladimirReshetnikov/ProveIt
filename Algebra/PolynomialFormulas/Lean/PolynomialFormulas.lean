import PolynomialFormulas.Basic
import PolynomialFormulas.Cubic
import PolynomialFormulas.Quartic
import PolynomialFormulas.GaussianPolynomialSolver
import PolynomialFormulas.GaussianRadicalBounds
import PolynomialFormulas.GaussianPolynomialApproximation
import PolynomialFormulas.LazardQuintic
import PolynomialFormulas.LazardQuinticFourier
import PolynomialFormulas.GaussianQuinticSolver
import PolynomialFormulas.AbelRuffini
import PolynomialFormulas.QuinticRadicalDecision
import PolynomialFormulas.SexticRadicalDecision
import PolynomialFormulas.SelmerAbelRuffini
import PolynomialFormulas.GenericAbelRuffini
import PolynomialFormulas.Examples

/-!
Public import surface for the degree-one-through-four polynomial formulas,
the coefficient-only radical solver for every Gaussian-rational polynomial of
degree at most four (including zero leading coefficients), certified rational
bounding boxes for its exact complex root values, fully executable
Gaussian-rational root approximations with certified Manhattan error, the
proof-oriented conditional transcription of the corrected Lazard radical
formula for quintics, a coefficient-only Gaussian-rational quintic dispatcher
whose zero-leading branch is verified by reduction to the degree-at-most-four
solver and whose genuine-quintic branch returns pointwise-verified Lazard
roots when its Fourier certificate package exists (with a complete-radical
fallback for singular solvable cases), the
usual rational-coefficient Abel--Ruffini obstruction, the rational Selmer
all-roots obstruction, and the generic rootwise obstruction in every degree
at least five.  It also exports the directly evaluable, verified
primitive-recursive decision for radical solvability of integer quintics and
its Turing-machine realization theorem.  It also exports the recursive
(not presently claimed primitive-recursive) sextic decision and its verified
Turing-machine realization theorem.
-/
