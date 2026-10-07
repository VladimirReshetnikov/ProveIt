# Mathematical proof and validation audit

This audit is an internal review accompanying an unrefereed draft. It does not
claim an independent referee or a proof-assistant certification.

## Core proof chain

1. The finite-difference top symbol is independent of the base point, symmetric,
   additive in every increment, and p-torsion. This determines its field-valued
   representative through the specified embedding.
2. At degree p+1, multiplying a phase by p produces a quadratic phase. The
   p-repeated contraction of its top tensor is minus the quadratic symbol, hence
   is symmetric. This proves necessity of the critical defect condition.
3. The coordinate low-depth lifts realize an arbitrary symmetric Frobenius
   contraction. Subtracting their full symbol leaves only multiplicities less
   than p, which integrate with invertible individual factorials.
4. Each canonical block has defect a wedge b. Symplectic elimination and the
   critical integration criterion give the normal form and exact half-rank repair.
5. At fixed quotient increments, expand T over all faces. A primitive for each
   face gives a vertex-phase decomposition. All vertex phases differ from the
   common top primitive by degree at most d-1.
6. Gowers--Cauchy--Schwarz on H therefore loses no local phase information. Keeping
   the entire quotient cube yields the U^d(a) bound. Young's inequality and Jensen
   give the sharp fractional-moment and mean bounds.
7. In the all-degree theorem, strong isotropy makes every mixed-face defect zero.
   The established general integration criterion supplies the face primitives.

## Specific hazards checked

**Signs.** The additive derivative is forward difference and the multiplicative
derivative is `f(x+h) conjugate(f(x))`. The cube parity is `d-|omega|`.
Gauge removal and the minus sign in the Frobenius/top-quadratic identity use this
same convention. Odd degrees are not silently assigned even-degree signs.

**Zero amplitudes.** The energy identity, the face argument, and the finite
localization checks allow f to vanish. No quotient of function values is used.

**Characteristic two.** The diagonal critical primitive is `|x|/8`.
Antisymmetrization and alternation coincide in the expected characteristic-two
sense. Alternating rank is even; the half-rank cost remains valid.

**Carries.** Low-depth coordinate lifts may contribute unrepeated top
coefficients. The proof and implementation subtract the full symbol before
applying the classical correction. This is not optional bookkeeping.

**Normalization.** The global energy is a d-fold cube average with one base
average, or a squared normalized Fourier coefficient averaged over d-1
increments. Its unnormalized scale is `|V|^(d+1)`. A single supported coset has
energy exactly `index(H)^(-(d+1))`, not `index(H)^(-d)`.

**Optimality.** Exact restriction codimension concerns primitives of the
specified tensor. It does not preclude unrelated correlations of a particular
function on a larger set. The correction-support lower bound is a radical
argument and is not a partition-rank assertion.

**Higher-degree scope.** Ordinary integrability of the top restriction is not
automatically enough for all mixed faces. The explicit degree-p+2 example has
zero top restriction but a nonintegrable proper face. This refutes that inference,
not every conceivable analytic inequality under weaker assumptions.

**Acceptance versus energy.** The repeated-variable pair-query probability is
an exact rank diagnostic. It is not an upper bound on the selected Fourier-square
energy. Uniform noise on arbitrary tensor tuples need not control diagonal queries.

**Experiments versus general maxima.** The ternary census exhausts all 81 tensor
symbols with a fixed nonzero defect. Its interpretation covers polynomial-phase
gauges of degree at most four on F_3^2. It does not cover arbitrary bounded
complex functions or dependence on ancillary dimensions. The broader extremizer
statement is labeled a conjecture.

## Finite validation actually performed

The checker completed successfully; see `data/verification.json` for the exact
output, seed, versions and cases. Integer residues encode circle-valued primitive
tables exactly. Degree and symbol assertions are tested with exact basis-direction
difference operators at every base point. Matrix ranks, isotropic counts, and
the fixed-defect census use finite-field integer arithmetic.

For ternary root-of-unity cube energies, the counts of omega and omega-squared
terms are checked to agree, then the real energy is recovered exactly as a
rational number. Fractional moments are not evaluated using floating-point
powers for a pass/fail decision: rational bisection gives certified lower bounds,
and the exact energy is compared with the resulting rational expression. The
single-coset equality is handled separately with its exact support formula.

The source compiled successfully with pdfLaTeX. The PDF was rendered and
visually checked; unresolved cross-references, clipped formulas, and an isolated
final bibliography entry were addressed before delivery. These production
checks do not certify mathematical truth.

## Remaining review priorities

The face-phase decomposition and its signs are the best first targets for
independent mathematical review. Next review the nilpotent-operator degree
lowering and the coordinate primitive in small characteristic. For a formal
implementation, preserve the all-degree dependency on general integration rather
than treating it as already proved by the critical-degree construction.
