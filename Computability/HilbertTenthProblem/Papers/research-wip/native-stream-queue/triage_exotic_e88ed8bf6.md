# Bounded Hankel and occupancy triage at e88ed8bf6

Neither archive supplies a Turing-complete computational substrate or a paid ordinary-integer Diophantine compiler in the interfaces reviewed. The Hankel package offers a useful exact polynomial-certificate pattern for one recurrence. The occupancy package offers exact distributional identities and finite rational moment recurrences, followed by analytic limit theorems. No operation-count improvement follows from either package. No substantive error was found in the selected spans; this is not a full-proof endorsement.

## Immutable inventory and execution boundary

Arrival checkpoint: `e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9`.

| Archive | Bytes | Regular members | Git blob | SHA-256 |
|---|---:|---:|---|---|
| `docs/incoming/A279619_Hankel_Positivity.zip` | 412400 | 20 | `39b2b18e2c93cd0ea8bdbf8cb93ee92c20c2d467` | `e22116d5fecba79b48e6d60c3432dae520ab5f3364135d090055886d4398f7b2` |
| `docs/incoming/Zero_Bias_Occupancy_Research_Package.zip` | 890651 | 19 | `e7d79b3d2b069ff6ffc89418ff0ab301d72b6443` | `591c49ca4bcd255c17bab3ced941e954599320d78a48778ac5d36b95af26e17e` |

The fresh companion collector authenticated all 39 member contents, unique safe paths, ZIP CRCs, and the Hankel archive's 19 checksum-manifest entries. Every entry matches the corresponding archived member. The manifest itself is separately hashed. The occupancy archive supplies no internal checksum manifest; all 19 members were authenticated directly against the immutable Git ZIP bytes. The JSON records each path, byte count, SHA-256, and coverage. Hashing a PDF or program is not a visual or semantic review.

No archived, supplied, predecessor, frozen, or copied predecessor helper was executed or imported. No builder, PDF renderer, package installation, external service, repository edit, or Git mutation was used. The only executed program was this review's new standard-library collector and its explicitly bounded arithmetic diagnostics. Normal and `-O` invocations from `/` produced byte-identical receipts before freeze. The source reports' saved test runs and PDF-validation claims were read as claims, not replayed or independently certified.

The incoming retention instruction was read at `docs/incoming/README.md` 426–440. The Fabius-local instruction file was consulted as context; no file under that subtree was edited or placed. Its publication/build rules are not invoked by this read-only triage of the separate top-level incoming archives. No source claim has been removed or silently repaired.

## Exact read coverage

All spans below use inclusive original-member line numbers. Their original-byte hashes appear in the JSON.

**A279619.** Fully read `README.md` 1–93, `SOURCE_AUDIT.md` 1–78, `OEIS_NOTE.txt` 1–26, `SHA256SUMS.txt` 1–19, `code/verify_certificates.py` 1–177, and `data/validation.json` 1–15. In `article.tex` (1,396 lines), read 50–230, 293–348, 441–663, 761–777, 850–873, 1045–1289, and 1329–1355. These cover the principal statements, negative-moment witness, full certificate interface and interpolation degree argument, selected coefficient-generator formulas, inverse-rounding qualification, computation boundaries, research questions, and data schema. The entire certificate JSON was parsed as inert data to check scales, shifts, degrees, signs, and counts. Its defining polynomial identities were not replayed.

**Occupancy.** Fully read `README.txt` 1–65, `numeric_notes.txt` 1–57, and `data/verification_summary.json` 1–62. In `occupancy_article.tex` (1,920 lines), read 55–365, 605–718, and 1502–1882: abstract/status/principal results, exact allocation and operator/conditioning interfaces, the Hilbert-space and sharp square-root-summability statements and their displayed proofs, numerical recurrences, all ten further questions, formalization plan, and provenance. Read `verify_occupancy.py` 1–100, 522–548, and 665–699 inertly; remaining functions were only located by name and are not certified.

Neither manuscript was read in full. Unread mathematical dependencies include the Hankel finite spectral repair proof and most all-orders asymptotic derivations, and the occupancy uniform local limit, full frontier/entropy/large-deviation proofs, and most detailed analytic estimates. The selected occupancy convergence proofs use those unread estimates, so the full convergence conclusions remain unaudited here. The original repository conjecture, external bibliography, literature priority, figures, PDFs, and formal Lean developments were not independently audited. Optional symbolic generators and most CSV numerical records were only hashed.

## Hankel interface and bounded findings

The sequence is fixed by its second-order polynomial recurrence and two initial values. The sharp source claim is global strict total positivity through order five, with a specific negative shifted order-six minor. These are sequence-positivity questions, not an input/program simulation interface.

The certificate mechanism has a meaningful finite-to-infinite argument. A decreasing ratio recurrence propagates an explicitly bounded rational interval from the base index five. Substituting that interval into each fixed-size determinant gives a Bernstein polynomial in a parameter in `[0,1]`; positivity of its coefficient polynomials after translation gives positivity for every real index at least five. The full polynomial identities are reduced to exact interpolation on grids exceeding independently stated degree bounds. This is stronger than sampling positive determinant values, provided the identities and coefficient data are actually checked. The finite-order contiguous-to-all-minors step still uses the source's cited strict Fekete criterion; that external theorem was not independently researched in this triage.

The fresh data check confirms 21 records with 1,090 strictly positive coefficients, positive rational scales, shift five, and consistent degree lengths. It does not establish that the records equal their claimed rational-determinant expressions. The supplied 177-line checker was read completely as inert text: it uses raised checks and exact fractions, enforces those identities on the stated grids, and is separate from the symbolic generator. Its saved successful run remains source evidence, not a replay by this review.

As a separate small check, this review generated `c_0,...,c_11` directly from the displayed recurrence and computed the six-by-six determinant by the 720-term Leibniz permutation formula, rather than the archive's Gaussian elimination. The result is exactly

`D_6(1) = -26875777009408537346562624`.

This verifies the concrete obstruction checked here: a positive measure on the nonnegative reals would make the shifted matrix positive semidefinite because its quadratic forms are integrals of `x P(x)^2`. It does not prove the positive order-five result, the optimal repair, or the asymptotics.

The source correctly distinguishes fixed-order eventual positivity from one common tail that works for all orders. Its inverse-rounding constants are explicitly existential and are not an effective numerical stopping rule. The coefficient generator works to a chosen finite order; no fixed paid graph for unbounded order or automatic certificate discovery is supplied. The useful next interface, if pursued for other recurrences, would be a compiler that produces and verifies the denominator/degree bounds and positive coefficient vectors with an explicit size and arithmetic-cost bound. This archive certifies one instance, not that general compiler.

## Occupancy interface and bounded findings

The general profile has infinitely many positive real weights summing to one; geometric weights specialize to `(1-q)q^j` with `0<q<1`. Allocation vectors are nonnegative integer sequences of total `m`, weighted by factorial expressions. “Universal” in the Hilbert-space theorem means all such positive summable profiles with exact saddle centering. It is not computational universality. The sharper `l1` theorem requires square-root summability, and finite/zero-support edge cases are expressly separated.

The exact local algebra checks out in the read span. With `D=t^(-1)d/dt` acting on even moment-generating functions, Leibniz and normalized iterates give the zero-bias allocation mixture. The factorial identity `2^k/(2k+1)! = 1/(k!(2k+1)!!)` gives its coefficient normalization. This review independently checked that identity at `k=0,...,20`; the all-k proof is the elementary even/odd factorial factorization, not an inference from the finite checks.

The conditional representation is also carefully scoped: independent variables are first constructed with their individual odd-conditioned Poisson laws, then their almost surely finite allocation sum is conditioned to equal `m`, an event of positive probability. The paper explicitly rejects conditioning a single infinite ordinary-Poisson vector on every coordinate being odd, which would be a probability-zero event. This avoids treating an invalid infinite conditioning operation as a computational primitive.

For rational geometric `q`, the moment recurrence and marginal formula give exact rational finite-level computations. Their loops and data sizes grow with `m`; the exact residual-total chain does not supply a fixed-arity certificate for an unbounded computation. General real profiles, infinite sums, hyperbolic functions, limiting Gaussian fields, and saddle solutions also require representations and error controls before they become algorithms on integer inputs. The manuscript explicitly leaves effective local/global error constants and exact sampling with a certified infinite tail as research questions. Its float64 tail estimates are not interval enclosures of all rounding and quadrature errors.

The read portions of the companion use ordinary `assert` checks for exact and floating comparisons; this is not a mathematical defect, but such checks would be disabled by Python `-O`. The package's saved normal-run checks must not be promoted to optimization-independent verification. This review did not run that program in either mode. Its own collector uses explicit raised guards instead.

No computational hardness, universal machine, or paid Diophantine compiler is asserted in the read interfaces. A potential practical continuation is a costed exact finite-level sampler or rational recurrence implementation with certified tail handling; neither a limiting law nor a cheap real-valued operator provides that integer interface automatically.
