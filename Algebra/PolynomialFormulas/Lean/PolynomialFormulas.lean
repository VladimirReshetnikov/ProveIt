import PolynomialFormulas.Basic
import PolynomialFormulas.Cubic
import PolynomialFormulas.Quartic
import PolynomialFormulas.LazardQuintic
import PolynomialFormulas.AbelRuffini
import PolynomialFormulas.QuinticRadicalDecision
import PolynomialFormulas.SexticRadicalDecision
import PolynomialFormulas.SelmerAbelRuffini
import PolynomialFormulas.GenericAbelRuffini
import PolynomialFormulas.Examples

/-!
Public import surface for the degree-one-through-four polynomial formulas, the
proof-oriented conditional transcription of the corrected Lazard radical
formula for quintics, the
usual rational-coefficient Abel--Ruffini obstruction, the rational Selmer
all-roots obstruction, and the generic rootwise obstruction in every degree
at least five.  It also exports the directly evaluable, verified
primitive-recursive decision for radical solvability of integer quintics and
its Turing-machine realization theorem.  It also exports the recursive
(not presently claimed primitive-recursive) sextic decision and its verified
Turing-machine realization theorem.
-/
