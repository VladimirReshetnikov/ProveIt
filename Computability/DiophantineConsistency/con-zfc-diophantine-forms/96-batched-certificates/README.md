# Shared arithmetic certificates for Diophantine consistency equations

This archive delivers explicit fixed polynomials whose lack of solutions is
equivalent, by ordinary mathematics formalizable in ZFC, to the syntactic
consistency of ZFC. The primary contribution is a substantially smaller
direct proof-calculus quartic. A separate supplement lowers the degree of
the incoming thirteen-integer construction.

Start with [the paper](report/report.pdf), its [TeX source](report/report.tex),
or the exact equations listed below.

## Results

All natural variables range over {0,1,2,...}; integer variables are unrestricted.
Height means the largest absolute coefficient in the expanded polynomial.

| Construction | Domain | Variables | Degree | Quadratic residuals | Expanded monomials | Height |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Primary direct quartic | Naturals | **667** | **4** | 535 | 23,747 | 2,649,643,818,040 |
| Alternative with smaller support | Naturals | 680 | 4 | 548 | 18,302 | 690,871,812,080 |
| Small-coefficient checkpoint | Naturals | 1,153 | 4 | 1,021 | 9,234 | 127,778,299 |
| Direct integer companion | Integers | **1,690** | **4** | 842 | 21,381 | 2,649,643,805,758 |
| Reanchored thirteen-integer norm | Integers | **13** | **1,072** | Not a squared-sum presentation | Supplied as a 195-operation circuit | Inherited fixed coefficient tuple |

The primary comparison is the incoming 3,614-natural-variable direct quartic:
667 variables is a reduction of 2,947, or about 81.5%. Its degree remains four.
The baseline's smaller coefficient height and monomial count are recorded in
the paper; the change is not an improvement in every metric.

The thirteen-integer construction reduces degree 1,088 to 1,072 while keeping
the same thirteen unrestricted integer unknowns, complete fixed coefficient
tuple, and 195 binary arithmetic operations. This supplement retains its
parent's native/Pell and K215 calibration.

The repository already has equations with fewer variables, including a
37-integer quartic with a different coefficient architecture. No global
minimum, worldwide priority, or universal simplicity ordering is claimed.
The direct family uses neither a K215 execution tableau nor Jones's
universal polynomial.

## Exact equations

The primary equation is exactly

    P(X_0,...,X_666) = sum over the 535 listed rows r of r(X)^2 = 0.

The rows, coordinate order, and all coefficients are fixed in
[direct/output/compact667/equation.json](direct/output/compact667/equation.json).
The same single polynomial is fully collected in
[direct/output/compact667/expanded_polynomial.json](direct/output/compact667/expanded_polynomial.json).
Every term is a pair [integer coefficient, sorted list of coordinate indices].
Repeated indices denote powers; an empty list denotes the constant monomial.
There are no variable exponents, unnamed coefficient parameters, or
uncomputed arithmetic macros in either presentation.

The integer companion is supplied in
[integer/signed_output/equation.json](integer/signed_output/equation.json)
and [integer/signed_output/expanded_polynomial.json](integer/signed_output/expanded_polynomial.json).
The thirteen-integer equation is the division-free straight-line circuit in
[guard13/equation.json](guard13/equation.json), with all numerical coefficient
leaves and their complete provenance supplied under its upstream directory.

## The main mathematical step

The compiler had been choosing existential arithmetic witnesses separately
at each occurrence. The new construction proves that a common choice works
for the whole finite computation.

1. All sixteen binomial graphs use one radix, larger than every coefficient
   in their binomial expansions. Repeated lower arguments share powers.
   The total number of positive-power requests falls from 55 to 28.
2. All congruence equations use a single natural offset for signed quotients.
3. All 28 power requests share one Pell frame, with 23 groups of literally
   identical exponent expressions. The common bound includes every proposed
   output, so the local output-bound witnesses are unnecessary.
4. A period of the determinant-one Pell matrix modulo four times the square
   of the product of the required ordinates supplies the simultaneous
   divisibility conditions. This is stronger than separate divisibility
   statements and requires its own completeness proof.
5. Exact monic affine and quadratic substitutions reduce the resulting
   1,153-coordinate quadratic system to 667 coordinates. The archive gives
   a reverse-restoration certificate for every deletion.

The integer conversion first guards all 358 original nongate coordinates of
the 1,153-variable checkpoint by x = a^2 + b^2 + c(c+1). The remaining 795
gate coordinates are nonnegative by their actual triangular definitions.
Only after that proof-preserving conversion are signed monic eliminations
performed. This order avoids assuming positivity after substitutions have
changed the visible dependency graph.

The direct proof chain is

    polynomial zero
      <=> finite direct arithmetic certificate
      <=> derivation of contradiction in C222
      <=> finite ZF refutation
      <=> finite ZFC refutation.

Negating gives the requested no-solution equivalence. All statements concern
the fixed syntactic consistency predicate identified in the source pins.
The equivalence assumes neither consistency nor arithmetic soundness.

## Reproduce

Python 3.10 or later and its standard library suffice for every new algebraic
check and reconstruction. No network or repository checkout is needed.
From the extracted archive directory:

    python3 verify.py
    python3 -O verify.py
    python3 verify.py --rebuild

The first two commands audit the literal polynomials, all coordinate
restorations, domain conversion, exact expansions, numerical coefficient
bindings, and integration links. The third also regenerates sixteen primary
direct files and six primary integer files in temporary directories and
compares their bytes. The thirteen-integer graph is reconstructed and checked
in every run. Verification includes negative controls for corrupted
restorations, a missing sign guard, and a modified fixture output.

To save a fresh receipt outside the immutable package:

    python3 verify.py --rebuild --receipt ../fresh-audit.json

The complete delivered-file manifest can be checked alone:

    python3 verify.py --manifest-only

Component READMEs give commands for rebuilding their outputs in place.
The guard13 checker refreshes its deterministic audit receipt. The other
default checkers read the delivered data.

Compile the paper from the report directory with a standard LaTeX
installation, running this command twice for references:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex

All included TeX dependencies are local. No generated image or external
bibliography file is required.

## What is proved and what is checked

The paper proves the unbounded shared-certificate, natural projection,
integer conversion, and guard-placement equivalences. These proofs compose
with the inherited C222 calibration and classical Pell theorems, whose
identities and retained sources are documented.

The software checks exact finite algebra, transcription, full coefficient
collection, and the stated measurements. A builder-free direct audit and a
separate projection checker are included; the integer audit imports neither
the builder nor the optimizer. Checks remain active under Python optimization.
Small fixtures illustrate the mathematics but do not replace its proof.

This archive does not prove Con(ZFC), decide whether these equations have
solutions, or provide a new end-to-end Lean/Rocq or object-language ZFC proof
term. The mathematical review in verification was performed by a separate
agent in the AI collaboration; it is not external human peer review.

## Provenance and incorporation

The comparison snapshot is ProveIt commit
a88aefd7ddab4771534bb049c67350e397c91b9a.
The two immediate incoming archives, their SHA-256 identities, the direct
source's earlier pin, and the logical dependency boundary are recorded in
[PROVENANCE.json](PROVENANCE.json) and the component pin files.

The original source archive names contain 2026-10-24 and are retained as
identifiers; this contribution is dated 23 October 2026. Source copies,
licenses, and notices are included. New code and text follow the repository's
MIT No Attribution license. The archive is prepared for incorporation into
ProveIt and contains no automatic publishing or repository mutation step.
