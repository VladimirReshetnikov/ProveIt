# Formalization outline

This is a plan, not a completed Lean formalization. No new theorem in this
archive is represented as kernel-checked. In particular, this file does not
hide the analytic argument behind an axiom asserting its conclusion.

## 1. Local algebra

Work over a complete discrete valuation ring O with fraction field F,
uniformizer pi and residue field k. Use matrices indexed by `Fin d`.
A representation is a group homomorphism into `GL (Fin d) O`.

Define:

1. `imageOrder rho`: the O-submodule spanned by the image matrices. Prove
   that it contains the identity and is closed under multiplication.
2. `hasOrderBound rho e`: every matrix multiplied by `pi^e` lies in that
   submodule. Avoid defining the least exponent until needed.
3. `intertwinerMod rho sigma n`: the submodule of matrices over O/(pi^n)
   killed by each map `X ↦ sigma(g) X - X rho(g)`.
4. `traceDepthAtLeast rho sigma a`: every trace discrepancy is divisible
   by `pi^a`. The exact depth can be the infimum of finite valuations.
5. The relation submodule R of the dual of the free matrix module.

The proof should be split into these independently useful lemmas:

### A. Finite relation presentation

Noetherianity supplies a finite generating set of relation rows. Smith
normal form over a DVR yields relation exponents b_i, a basis C_i of the
matrix module, and the formula `length H_n = sum_i min(n,b_i)`.
An infinity flag can encode free factors, or free and torsion factors can
be stored separately. The minimum finite exponent divides every relation
coefficient. Evaluating at the identity proves `b_min <= a`.

### B. Singular primitive obstruction

From a singular primitive matrix X choose a primitive kernel vector v.
If X intertwines to precision r, apply the image-order containment to
`pi^e E_ij v`. A unit coordinate of v proves that r cannot exceed e.
Apply the same argument to transposes to obtain the minimum of the two
order bounds. This lemma should be proved for the normalized valuation
after a finite field extension as well.

### C. One residual direction

Two independent residual intertwiners determine a matrix pencil. The
homogeneous determinant polynomial has a projective root over an
algebraic closure, defined over a finite extension. Normalize the two
coefficients to be integral with at least one unit. Flat residue-field
extension preserves their residual independence, giving a primitive
singular intertwiner. Lemma B yields a contradiction for r > e.
Consequently at most one relation exponent is greater than e.

### D. Compensation

Choose a primitive Smith direction X of longest relation length b > e.
Lemma B makes X invertible over F. Let t be its largest matrix Smith
exponent. If t > 0, set its highest diagonal entry to zero in Smith
coordinates. The resulting primitive singular matrix has precision at
least min(b,t+b_min), forcing `t+b_min <= e`. Multiplying by X inverse
and taking traces gives `b <= a+t`. Combine these with Lemma C to obtain
the sharp total bound. The t=0 and d=1 cases are separate short branches.

### E. Finite precision and sharpness

Split into n <= e, n > e with a >= n, and n > e with a < n.
The first case uses `b_min <= a`; the second uses Lemma C; the last uses
the total bound. Formalize the matrix-unit examples directly rather than
inferring their generality from the Python certificates.

The theorem can be stated using certified upper bounds for the conductors
and for trace depth, avoiding minimization machinery in applications.

## 2. Positive spectral grids

Define the coefficient list of `(1+z+...+z^k)^m` as repeated finite
convolution over the natural numbers; divide by `(k+1)^m` in the reals.
Prove positivity, total mass one, and the generating-function identity.
This algebraic part has no connection to GRH and is suitable for a first
formalization target.

For a finite or summable family of complex exponential modes, prove that
the grid average has multiplier U_k(w)^m. The quantitative proof then needs:

- the exact variance of a uniform integer in {0,...,k};
- `1-cos u >= 2u^2/pi^2` for |u| <= pi;
- the sine-denominator estimate outside the nearest-alias neighborhood;
- the convex endpoint-chord bound for exp(-a x);
- summability of log(n)/n^2;
- an alias-cell decomposition indexed by the nonzero integers;
- interchange of a finite average with an absolutely convergent series.

Keep the abstract spectral theorem independent of L-functions. Only the
application imports Dirichlet GRH, the explicit formula, and local zero
counts. The explicit formula is a substantial formalization obligation;
the article's prose proof is not automatically a Lean theorem.

## 3. One-sided detection and arithmetic recovery

Formalize the meromorphic transform identity for the ramp. A forward
translation changes the Laplace transform by its exponential multiplier
plus an entire compact-interval integral. Prove the two multiplier
zero-location statements separately. The Landau lemma requires the
singularity of a positive Laplace transform at its real abscissa of
convergence, followed by the residue-sign contradiction.

For the individual-character corollary, prove `chi0 + Re chi >= 0`, equality
of central orders for conjugate characters, and nonvanishing of the
principal factor at 1/2. State the rounding conclusion with explicit
error constants as premises. Do not replace an unknown spectral gap with
an uncertified numerical guess.

## 4. What can be reused from the supplied Lean repository

Use its public final statement for Dirichlet nonvanishing/critical-line
zeros. Inspect the actual types before reusing its congruence length and
one-sided analytic lemmas; they use particular coefficient and character
module conventions. The report's source manifest names the relevant
files. No transitive-import compatibility or build success is asserted
for this future integration plan.
