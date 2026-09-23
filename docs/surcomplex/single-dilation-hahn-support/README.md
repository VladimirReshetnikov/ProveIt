# A Single Dilation Recovers Hahn Support

**Exact difference cohomology, definable normal forms, and centralizers of
monomial automorphisms**

Research article prepared with ChatGPT for Vladimir Reshetnikov.
Date: 22 September 2026.

## Contents

- `article.tex`: standalone LaTeX source, with an internal bibliography.
- `article.pdf`: compiled article.
- `verify.py`: exact finite verification using only the Python standard library.
- `verification.txt`: output from the delivered verification script.
- `PROOF_AUDIT.md`: hypothesis/dependency and verification-scope checklist.
- `Makefile`: commands to rebuild the PDF and repeat the finite checks.

No font files or repository copies are included. The source does not depend on
any external images, bibliography database, or custom TeX style files.

## Main mathematical content

For a full Hahn field K = k((t^Gamma)) of characteristic zero, the article proves
an exact strong partial inverse for sigma - lambda, where sigma fixes k and
sends t^g to chi(g)t^(theta(g)). Only exponents fixed by theta with character
value lambda are obstructions. All orbit sums are justified by well-ordered
support and finite fibers, not by a presumed topological limit.

For a finite commuting family, an explicit Koszul homotopy retracts the complex
onto its joint-resonant coefficients. This computes additive cohomology in all
degrees, the principal-unit part of multiplicative cohomology, and the exact
criteria for compatible multiplicative equations.

The main application is structural: when Gamma is nonzero and 2-divisible,
field operations together with exponent doubling define the canonical
coefficient field, every coefficient, monomials, support, the valuation ring,
and truncation. The centralizer of doubling among all field automorphisms is
therefore exactly the untwisted coefficient/exponent lifts. Neither strong
additivity nor valuation preservation is an assumption in that theorem.

The expansion uniformly interprets full monadic second-order arithmetic. The
arithmetic theory's undecidability is transferred to the signature with one
automorphism and no named monomial parameter. A coefficient-equality formula
also directly witnesses TP2. For divisible Gamma, every nonidentity positive
rational dilation recovers the same data, although distinct rational dilations
are not conjugate.

The elementwise results transfer to No and No(i) through Conway normal forms.
Ordinary group cohomology is stated first for set-sized Hahn fields; class
statements and their support-localization requirements are kept separate.

## Reading route

Theorem 4.1 is the scalar resolvent, Theorem 5.2 is the Koszul contraction,
Theorems 6.3 and 6.4 are the multiplicative criteria, and Theorem 7.1 gives
rational-dilation cohomology. The main definability theorem is Theorem 8.1;
Theorem 9.1 is the unrestricted centralizer. Sections 10 and 11 contain the
logical consequences and the rational-dilation extension. Section 13 gives the
surreal and surcomplex formulations. Appendices contain the formula dictionary,
finite-verification scope, and novelty ledger.

## Build

Use Python 3.10 or newer and a reasonably complete TeX Live installation.
The document uses standard packages, including newtxtext/newtxmath, amsmath,
amsthm, geometry, microtype, hyperref, booktabs, and longtable.

```sh
python3 verify.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `make`. Without latexmk, run pdflatex at least twice and again
if cross-reference warnings remain.

The recorded run passed **66,131 exact finite checks**. These are finite
operator and coefficient identities. They do not establish Hahn summability,
quantify over arbitrary groups, verify first-order interpretations, certify
class mathematics, or constitute a Lean formalization. The infinite claims
rest on the written proofs. There are no claims of independent refereeing.

## Sources and novelty scope

The comparison used repository commit:

`465a54b479a1ee842cbf7db1689a7d2f6bfe25e1`

The root README, report catalogue, and the surcomplex-automorphism report's
statement guide were inspected through read-only GitHub access. The repository
was not independently built and its full article collection was not exhaustively
audited. The manuscript distinguishes inherited Hahn and automorphism machinery
from its proposed additions.

Primary related literature includes Kaplan–Krapp–Serra on surreal automorphism
groups, Faverjon–Roques on Hahn solutions of Mahler equations, Pal on
multiplicative valued difference fields, and Camacho on truncation and
arithmetic interpretations. The support-to-arithmetic mechanism has a prior
Camacho precedent; the proposed new step is defining the support structure from
one named dilation and deriving the unrestricted centralizer and related
consequences.

A focused search did not locate these main statements in the proved form.
That is not a certification of priority. No named published open problem is
claimed resolved. In particular, the article does not settle the existence or
image of nontrivial exponential automorphisms of the surreal numbers, nor
Camacho's monomial-definability question in a smaller language without the
additional dilation.
