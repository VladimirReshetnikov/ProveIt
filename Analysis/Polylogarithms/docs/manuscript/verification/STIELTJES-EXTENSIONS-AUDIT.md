# Stieltjes contour, product and exceptional-moment research audit

12 October 2026 (Pacific). This milestone continues the generalized Stieltjes
research from publication `4b9e83b4bf3379a7f11415b8e1422561f3a9e798`.
The conventional functions are the Laurent coefficients gamma_n(a), with
gamma_0(a)=-psi(a). The three new sections form one progression: transport
the translation identities across the cut; balance the tails to integrate
products; then exploit simultaneous colored-tail zeros for extra moments.

## Attribution and resolved scope

The preserved `stieltjes-correlation-calculus/continuations/balanced-stieltjes-moments`
report already proves the scalar balanced kernel, its decay, its Mellin
transform and its adjacent-shift recurrence. These foundations now receive
self-contained canonical proofs and the existing `stmell:balanced` citation.
The explicit Barnes product coordinate answers its question 5 at the level
of an exponentially convergent one-contour function class. The factorial,
finite-zeta and hypergeometric evaluations give a fully evaluated adjacent-
shift subfamily. Unrestricted products are not asserted to reduce to a
finite list of single zeta values.

The later `stieltjes-harmonic-resonance/continuations/gamma-normalizations-colored-moments`
report, especially `sections/03_colored.tex`, already resolves the older
report's colored-balancing question. It proves the slit-color domain,
scalar transform, interval-in-shift uniqueness, Stieltjes dictionary,
first exceptional moment and Catalan/beta family. These are credited to
`stcol:report`, not rediscovered results. The canonical section develops
the complete fixed-shift coefficient space, the necessary-and-sufficient
consecutive-zero criterion for higher ordinary moments, and the explicit
alternating golden-shift example. This resolves the dimension and moment
consequences asked for in `sections/06_audit_research.tex`; classification
of the entire algebraic zero locus remains open. The source report's
Gamma determinants, Gaussian moment laws, primitives and color-one limit
retain their separate integration scopes.

The preceding canonical digamma reconstruction assumed positive shifts.
The new contour section proves its principal-slit continuation and precise
upper/lower bank formulas, answering question 2 of the balanced-moments
report for these translation families. Existing multishift-reflection
reports provide antecedents for logarithmic cuts and Plemelj methods;
their horizontal-cut Gamma/Lerch resolvents do not supply this formula.
Arbitrary winding contours and the entire complex-shift program are not
claimed to be settled.

These are proved extensions in this manuscript. Targeted source and primary-
literature checks do not establish worldwide historical priority. Original
reports, their PDFs and delivered evidence have not been edited.

## Analytic proof obligations

* For complex shifts off the nonpositive real axis, the zero-sum digamma
  kernel is O(x^-1) at infinity, uniformly on compact shift sets. Its
  subtracted numerator is O(x) at the origin. These bounds justify successive
  holomorphic continuation of the existing reconstruction.
* On a negative real bank, equal pole locations are combined first. The
  upper-bank correction is minus i*pi times the residue of p_n(log x)f(x)/x.
  Independent symmetric exclusions define each Cauchy principal value.
  The even-index origin term and the split at one are retained. A separate
  Hurwitz shift calculation verifies the jump and its sign.
* Higher Stieltjes kernels across a pole are derivatives of locally
  integrable powers of the boundary logarithm. The beta-cut formula is
  proved first where both pieces converge ordinarily, then continued as
  one expression before spectral differentiation. This is a distributional
  prescription, not an unchanged ordinary real-axis integral.
* The uncolored scalar Mellin proof explicitly subtracts the leading
  Hurwitz tail. It differentiates only within the initial convergent strip
  and continues the differentiated kernel afterward. The Barnes product
  uses Mellin inversion and a displayed absolute Fubini bound. Its contour
  split covers exactly 0<Re(v)<p+q+2; cosecants give exponential decay.
* Adjacent-shift products reduce under t=log(1+a/x) to a positive Laplace
  series. A finite polynomial vanishes at the omitted initial integers,
  giving the exact zeta-minus-one coefficients with every zeta argument at
  least two. Unequal shifts have an explicit Euler hypergeometric integral;
  its parameter derivatives precede continuation beyond Re(v)=2.
* The colored tails are locally uniform Laplace expansions. Pochhammer
  derivative coefficients are positive, so a nonzero tail cannot be hidden
  by a vanishing coefficient. In the homogeneous ansatz the logarithmic
  powers are distinct; at the final allowed inverse power, positive
  logarithmic powers must also vanish. This proves the full affine-space
  classification, including the boundary constraint.
* For an exceptional ordinary moment, every colored tail from q through
  m-1 must vanish. The first surviving constant times a real power cannot
  converge conditionally, even for complex colors. The consecutive-zero
  condition is therefore necessary as well as sufficient.
* At the golden shift, E4=E5=0, A3=sqrt(5)/8 and A6=1/2 exactly.
  Q4(5)=1, Q4(6)=3 and Q5(6)=1; the next tails are 35/(12*x^7) and
  7/(4*x^7). The two independent order-six moments consequently have ratio
  three. All proof constants were checked independently of the draft.

## Reproducible evidence and its limits

`check_stieltjes_contour_exact.py` checks eight reconstruction polynomials,
eight jump polynomials and exact coalescence of rational pole locations.
`check_stieltjes_contour_numeric.py` checks nine directly subtracted
principal-value quadratures, one precision/cutoff refinement, six ordinary
beta-cut quadratures and three rejected sign/contact corruptions.
The nine PV discrepancies are below 1e-43 (observed worst about 9.18e-54);
the refined discrepancy is about 9.91e-67. The beta diagnostics use a
separate 1e-13 threshold (observed worst about 7.61e-16).

`check_stieltjes_bilinear.py` compares three direct product integrals with
independent Barnes contours, tests five factorial moments and checks seven
Gram determinants exactly. The numerical tolerance is 1e-28.
`check_stieltjes_bilinear_shifted.py` supplies nine integer-weight and
unequal-shift diagnostics at tolerance 1e-30, seven exact coefficient
polynomials and 28 exact Laguerre products. One unequal-shift example is
beyond Re(v)=2; the largest reported residual is about 1.93e-38.

`check_stieltjes_colored_exact.py` supplies 1,070 exact checks and five
rejected corruptions, including all abstract tail-zero patterns through
order eight, inverse binomial coordinates and the golden constants.
`check_stieltjes_colored_numeric.py` evaluates the golden moments by the
Stieltjes dictionary and a preserved Euler--Maclaurin kernel evaluator,
then compares with independent Lerch/Hurwitz order derivatives. Its
precision, cutoff and tail-order refinements are recorded beside the code.

These numerical computations have finite quadrature cutoffs and truncated
asymptotic evaluators. They are floating-point diagnostics, not interval
certificates. Exact finite checks test coefficients and formulas; the
written analytic proofs establish the all-index statements. No Lean
formalization, arithmetic independence, or exact-commit remote CI is
asserted. Exploratory failures remain in ignored scratch: floating-point
pole keys initially split an equal pole, and the first golden-tail cutoff
was too short for the chosen tolerance. Both led to corrected evaluators;
no incorrect theorem was published.
