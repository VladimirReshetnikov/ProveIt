# Late Library comparison addendum

Inspected 24 October 2026, approximately 03:59–04:04 UTC. These are separately pinned Library v0 snapshots received after the original round13 comparison freeze, not replacement baselines or a current repository-wide frontier survey. The earlier 7e533c… baseline remains intact. Exact archive/PDF byte hashes and identities are in `LATE_SOURCE_PINS.json`; individual equation hashes and finite checks are in `LATE_LITERAL_AUDIT.json`.

## Independently checked literal quartics

A new checker, which imports and executes no supplied upstream program, expanded every quadratic residual square over exact integers and compared the entire collected polynomial with the delivered coefficient table. All listed coordinates occur in the resulting polynomial. These are independently recounted metrics, not merely copied author summaries:

- 3,776 unrestricted integers: degree 4, 2,015 residuals, 20,194 monomials, coefficient height 47,959.
- 3,671 unrestricted integers: degree 4, 1,942 residuals, 26,271 monomials, coefficient height 3,835,369,234.
- 2,473 nonnegative integers: degree 4, 2,089 residuals, 20,580 monomials, coefficient height 127,808,289.
- 4,860 nonnegative integers: degree 4, 4,476 residuals, 14,719 monomials, coefficient height 1,837.
- Eight-column projection: 7,617 unrestricted integers, degree 4, 4,379 residuals, 148,220 monomials, coefficient height 8,974,652,400,619,654,748,160.

The first two endpoints invalidate any suggestion that the new 4,087-integer round13 equation is a smallest-known direct quartic. The comparison is still a genuine different construction/complexity tradeoff. Natural and unrestricted-integer variable counts must not be mixed. The 2,170-natural endpoint has fewer variables than this late 2,473-natural endpoint; that isolated comparison is not a global optimality claim.

## Independently counted arithmetic graphs

All nodes are reachable in the three late native DAGs and all variable leaves are live. Counting every binary addition/subtraction/multiplication, including scalar multiplication and squaring, gives:

- 12 integers, author exact degree 4,832: 248 operations = 64 additions + 153 multiplications + 31 subtractions.
- 12 integers, author exact degree 16,000: 223 operations = 53 additions + 139 multiplications + 31 subtractions.
- 13 integers, author exact degree 1,072: 190 operations = 40 additions + 118 multiplications + 32 subtractions.

Syntactic degree propagation independently gives bounds 4,832 and 16,000 for the two 12-variable graphs. For the 13-variable graph it gives only 1,152: its sharper degree 1,072 depends on exact cancellation and remains attributed to the supplied degree proof in this limited review. No new full coefficient-numeral binding audit or calibration rebuild was performed here. The 13-variable/190-operation competitor must be acknowledged when discussing the round13 13-variable/1,072-degree companion. The independent 14-variable/378-degree/145-operation endpoint remains a different tradeoff.

## Mechanisms worth composing, without silently changing this release

The 3,776/3,671 package starts from the direct shared-CRT natural core at comparison pin 278bc68df1af125d62f9cbfe28c9fd3ebcf50d5b. It replaces 221 private differences of natural quotients with single signed quotients, restores the original pair by positive/negative parts, normalizes 110 semantic signs with diagonal zero-set symmetries, derives further positivity from ordered implications x A = B with A > 0, and then eliminates monic coordinates by polynomial substitution with an explicit reverse lift. The sign pivots are an auxiliary Z/product wire and a Pell U with its two congruence quotients, twice per 55 power graphs. Quadratic substitutions are allowed only when the eliminated variable occurs scalar-linearly elsewhere. These are ordinary algebraic mechanisms. A second fresh checker independently verified all 110 diagonal sign symmetries against every core row in each variant and replayed every ordered polynomial lower-bound implication: 645 retained guards and 2,382 derivation steps recover all 2,723 natural core coordinates in the affine variant; 661 retained guards and 4,942 steps recover all 4,854 natural core coordinates in the retained-wire variant. The exact source and certificate hashes are in `LATE_SIGN_AUDIT.json`. This is a replay of those sign/bound certificates, not a new replay of signed-quotient projection, all monic elimination steps, or inherited calibration.

The 2,473-natural package orients four Pell congruence quotients and fixes W=n+k for positive inputs. It then substitutes A=n+a+1 and polynomially defines X,S,R, giving an eleven-auxiliary-coordinate/six-equation power graph. Its root comparison snapshot is a88aefd7ddab4771534bb049c67350e397c91b9a; the direct equation declares inherited source commit 08200eb10fde2db408c69dffd840d6920a569b1f. Those pins have distinct roles and must not be conflated.

The projection package uses eight bounded local coordinates (a,b,c,d,S,q,S_next,q_next), with heterogeneous bounds (N,N,N,N,y,U,y,U). It projects deterministic constructor and label coordinates branchwise, pads the proof horizon to bound rule parameters, and takes an explicit monotone label bound H(N) before constructing the accumulator and beta encoding. The scale y already bounds beta remainders, eliminating two remainder slack columns. Enlarging the factorial argument makes every bound factorial coprime to the CRT product and removes one factorial graph. The literal source binding has exactly eight encoded columns; the actual call ledger contains 40 power, 40 Pell, 27 division, 11 binomial, and two factorial calls. Its baseline snapshot is 04a1d79222d55cabe4ba52897863fc33baa8c268, while inherited logical files retain 9a33342a03d19cf5b061b2083c6b5d3f27f752ed. These are not the signed-quartic package's pin.

The twelve-variable package uses the intersective monotone quintic (x^2+31)(x^3+x+1), a full Pell interpolation result allowing a prescribed auxiliary residue, and a nonvanishing carrier. This is not permission to delete an arbitrary positivity witness from the round13 kernel. Its 13-variable companion instead takes a rational trace before radical separation. The detailed composability assessment is separate from this finite census.

## Read limits and proof status

Read complete README/proof entries for the direct signed-quotient transformation, guard minimization, semantic review, projected eight-column source, and eleven-coordinate positive-power graph; inspected all listed literal equation payloads and native DAGs. The native interpolation README was read and its detailed proof passed to the native-family reviewer. The delivered PDF was materialized and hashed but not visually audited. No incoming code, builders, release verifiers, Lean files, or other upstream executables were run. Upstream PASS receipts are not presented as newly reproduced checks. These finite counts and identity checks do not independently establish the inherited C222/native/K215 calibration, consistency of ZFC, or a new kernel-checked end-to-end theorem. Each package's ordinary mathematical claims remain tied to its explicitly named dependencies.

The standalone comparison checkers and original incoming archives are not included here. This directory records the comparison audit and exact input hashes; it is not counted as an offline replay suite. All newly selected equations elsewhere in the release retain complete local verification inputs.
