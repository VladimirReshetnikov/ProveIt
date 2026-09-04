# Transseries: the polynomial–logarithmic calculus and its inversions

**Single consolidated volume for the whole `series-and-transseries` group.**
`transseries_and_inversion.tex` and the PDF built from it in the same run.

## Status: merge in progress

| Source group | Lines | State |
| --- | --- | --- |
| `polynomial-logarithmic-transseries/` (1 volume, 8 parts) | 36,033 | **absorbed** — Parts I–VIII |
| `special-function-inversion/` (1 volume, 10 chapters) | 16,771 | **absorbed** — Parts IX–XII |
| `lambert-inverse-transseries/` (3 articles) | 5,209 | pending |
| `sequence-transseries/` (5 articles) | 9,743 | pending |
| `transseries-tutorials/` (4 articles) | 26,099 | pending |

The two already-consolidated volumes are in. The three groups that were never
consolidated are being merged next, then the apparatus is deduplicated across
the join, and then the absorbed sources are deleted.

## Why these two fit together

The `series-and-transseries` README recorded, as an explicitly open question,
whether the polynomial–logarithmic calculus and the inversion calculi of the
special-function articles coincide. They largely do, and the merge makes that
checkable. A title-level concordance of the inversion volume's Chapter 0
against the calculus volume finds that the calculus already contains:

* Lagrange–Bürmann reversion at infinity, and its finite-point form;
* Newton iteration with precision doubling;
* residual-to-error transfer, and slope transport;
* ordinary and exponential partial Bell polynomials, with Faà di Bruno;
* affine-logarithmic reversion and the pure Lambert block in closed form.

What the inversion apparatus adds, and the calculus does not have, is: the
exponential–power model `C exp(a x^α) x^b exp Q(x^-δ)`; the monomial
α-reduction; the axiomatized admissible dominant core; perturbed inversion
around an exactly invertible core; and the entire **discrete** theory — the
three inverse objects of a sequence, the staircase theorem, and certified
discrete inversion. The calculus is about functions; that part is about
sequences.

Deduplicating the overlap is the next step after the remaining groups are in.

## Structure

Parts I–VIII are the calculus: the polynomial–logarithmic scale; arithmetic
and differential calculus; composition; series reversal at infinity; Wright
omega, the Lambert polynomials and Lambert `W`; from formal transseries to
analytic asymptotics; algorithms, certificates and diagnostics; extensions.

Parts IX–XII apply it: the apparatus for inverting a rapidly growing
function; four combinatorial sequences (rooted trees A000081, the double
factorial, the partition numbers A000041, the swing factorial A056040); four
special functions (Γ and Barnes `G`, the hyperfactorial `K`, the subfactorial,
a real-argument Fibonacci function); and a synthesis.

## Build

The volume is assembled by a script from its sources rather than edited in
place; the assembled `.tex` carries a header saying so. Three `pdflatex`
passes. Current: 52,636 lines, 666 A4 pages, 12 parts, 50 chapters, 2,945
labels all distinct, no dangling references, no LaTeX errors, no undefined
references.
