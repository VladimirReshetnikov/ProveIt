# Independent finite algebra review of the minimal-growth construction

Prepared as a separate review within the AI-assisted research workflow, 25 October 2026. This is not external human peer review or an end-to-end proof-assistant certificate.

## Inspected boundary

The inherited raw arithmetic source is the exact `factorial_free_affine/raw_source.json` from the incoming Factorial-Free Binomial CRT package. Its SHA-256 is:

`7b2d75791f10c717bbadca278e78e9f315508d56acdc8ad3eb82b63ddbb2e855`.

The new raw source has SHA-256:

`0b977e5a6e5b0a7dfb9b9a05da14810e3746826d417e25a83c25e0fc11ae469a`.

The translated 242-coordinate source supplied to the affine reduction has SHA-256:

`50f88c245d3a32b5c041924ea4ac07b9149e5da24c859f3a167ea984d93e18d2`.

The independent checker reconstructs the new source from the inherited coefficients and the mathematical substitutions; it does not accept the producer's edit list as its specification. In particular, it checks the actual even index `C=2c`, the exact base `B(2+4 sum(actual representatives))`, the alias `R=F`, the odd affine beta multiplier, and the minimal-growth choices `t=16+4h^2` and power base `t`. The source has eleven edited rows and three deleted rows. All eighteen power-congruence rows remain present.

The reason these semantic source changes preserve refutation existence is an unbounded mathematical argument supplied separately. A coefficient replay alone does not establish that theorem.

## Algebraic reductions and their proofs

After the source change, the inherited Horn factorization uses seventeen verified affine-square identities and an eleven-link private product chain. Its factor-root output equality follows from

`product(L_i^2) * bundle = product(L_i)^2 * bundle`.

The checker verifies every local definition, every external use of the final Horn root, and the absence of unintended uses of private wires. It verifies the bundle refactoring separately. Eighteen rewritten rows and two deleted rows are authenticated. No global expansion of a huge product is used as a heuristic; the stated identity follows from the exact identified factors.

Each subsequent monic elimination has the form

`epsilon*x_v - epsilon*f = 0`, with `epsilon` equal to +1 or -1,

where `f` is an integer polynomial independent of `x_v`. The equation uniquely recovers `x_v=f`. Substituting that polynomial into every other residual preserves existence in both directions. The checker verifies the unit coefficient, the complete literal restoration, its absence of already removed coordinates, and the fact that all intermediate residuals remain quadratic. It replays 202 such eliminations. The 117 additional discarded coordinates occur in no remaining residual; they can be assigned arbitrary integer values on extension. This last step is an existence equivalence with free fibers, not a bijection of entire raw zero sets.

The 69 coordinate translations are integer bijections. After these steps the intermediate equation has 242 integer coordinates and 178 quadratic residuals.

The final affine reductions transfer the credited six coordinate shears and five residual-row operations of the incoming Factorial-Free package. The exposure rows are matched by their exact polynomials in variable names, rather than by coincidental numerical row indices. Three affine unit pivots remove `add.145`, `mul.346`, and `base4.T`. The 238-coordinate version additionally removes the already affine `add.380` row. The restored values are supplied as complete integer affine polynomials.

Each coordinate shear has the form `old_x_i = new_x_i + sum(a_j new_x_j)`, with no occurrence of `i` on the right-hand sum, and has an integer inverse. Each residual operation has the form `R_i <- R_i + k R_j`, with `i != j`, and has inverse obtained by replacing `k` with `-k`. Such row operations preserve simultaneous vanishing, although they generally change the sum-of-squares polynomial away from its zero set.

For every final endpoint, the checker independently pulls back all 178 intermediate source residuals through the delivered restoration map. It then reverses every recorded final and exposure row operation, reinstates the zero pivot rows, and compares every coefficient. This establishes the claimed affine zero-set equivalence, in addition to a forward replay.

## Final verified endpoints

All coordinates are unrestricted integers.

| Endpoint | Variables | Quadratic residuals | Exact degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Reduced dimension endpoint | 238 | 174 | 4 | 13,149 | 6,144 |
| Reduced height endpoint | 239 | 175 | 4 | 6,723 | 4,432 |
| Sparse endpoint | 239 | 175 | 4 | 4,963 | 7,968 |

Every final residual coefficient has absolute value at most 64. The height column is measured after full collection of the sum of residual squares, not inferred from that residual bound. Every declared variable occurs in the fully collected polynomial. The entire expansion is compared coefficient by coefficient.

The exact degree is four: each residual has degree at most two and at least one has a nonzero homogeneous quadratic part. The degree-four homogeneous part of the sum of squares is the sum of squares of these real homogeneous quadratic polynomials and therefore cannot vanish identically.

## Verification scope and controls

`check_pipeline.py`, `check_affine.py`, and `finite_controls.py` use only Python's standard library and import no producer, optimizer, or inherited source compiler. Required checks use explicit exceptions, not Python assertions. The complete final pipeline passed both ordinary Python and Python `-O`.

Three targeted corruptions were rejected in both modes:

1. Replace the coefficient enforcing `C=2c` by one, while editing the recorded delta to agree with the corrupted source. Independent mathematical reconstruction still rejects it.
2. Alter a Horn output coefficient and update the declared output digest. Independent local coefficient replay still rejects it.
3. Change a monic restoration by one. The verified pivot equation rejects the incorrect restoration.

The finite checks do not prove consistency, decide whether a root exists, verify the inherited C222/ZF/ZFC calibration from first principles, or replace the new unbounded bootstrap, selector, CRT, growth, and range-decoding proofs. Their role is to connect the explicitly stated arithmetic source to every literal coefficient of the delivered finite polynomials.
