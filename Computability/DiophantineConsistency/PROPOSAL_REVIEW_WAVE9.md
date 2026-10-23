# Wave-nine review and the next research targets

Reviewed 23 October 2026 following the owner's pointer to placement commit
`a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49`. The eight original ZIPs arrived
at `0c6be9a074`; their numbered packages are 60–67. All eight complete normal
release replays pass. Detailed checks and proof boundaries are recorded in
[the arithmetic review](PROPOSAL_REVIEW_WAVE9_ARITHMETIC.md) and
[the structural review](PROPOSAL_REVIEW_WAVE9_STRUCTURAL.md).

## Decision

For the **nine-positive-variable branch**, adopt package 66's
[H2082 simple circuit](con-zfc-diophantine-forms/66-gap-congruence/nine/generated/H2082_simple_positive.json)
as the next delivered cost target: **444 operations, degree 1,845,940**.
Its natural version has 451 operations. A separate checked
[whole-tuple compact54-sharp instance](candidates/gap2082-compact54/README.md)
reduces this to **443 positive / 450 natural operations**, at the same
degree. Use this local instance as the next cost target to formalize.
These improve both measures over
the delivered package-59 target of 473/1,910,404 and over our separate
456-operation shared-power version of that same polynomial.

Retain package 65's **458/1,675,396** shared-tap form as the most direct
lower-degree extension of the current source proof. Its authoritative
expanded source agrees with every row of the old-z source already checked
in Lean. Package 67's **487/1,494,006** form is the lowest reviewed
nine-positive degree, with new higher-majorant inequalities to formalize.
There are intermediate tradeoffs; none is silently discarded.

This is one research branch, not a requirement that the final answer use
nine variables, K215, or a Jones universal equation. The only required
semantic endpoint is a ZFC-provable equivalence between unsolvability and
syntactic `Con(ZFC)`. Direct proof-certificate encodings and an explicit
quartic obtained before Jones compression are being investigated in
parallel. Variables, degree, operation count and constant size remain
separate measures; no globally simplest equation is claimed.

## Nine-positive frontier

The table compares the full wave-nine catalogue on operations and degree,
keeping the witness domain fixed. Natural companions add seven operations.
Exact degrees are supported by replayed cancellation-aware certificates.

| Package / variant | Operations | Degree |
|---|---:|---:|
| 66 H2082 simple | **444** | 1,845,940 |
| 66 H2068 simple | 449 | 1,834,516 |
| 66 H2057 simple | 451 | 1,825,540 |
| 65 shared-tap economy | 457 | 1,738,228 |
| 65 shared-tap primary | 458 | 1,675,396 |
| 67 order 1 | 475 | 1,663,788 |
| 66 H2082 refined | 476 | 1,520,178 |
| 66 H2068 refined | 481 | 1,510,770 |
| 66 H2057 refined | 483 | 1,503,378 |
| 67 order 4 | 487 | **1,494,006** |

The other delivered nine-positive principal points are 60's
465/1,797,796, 62's 453/1,834,516, 63's 504/1,573,266 and 64's
470/1,781,068. Each is dominated within this operations/degree comparison.
They can still offer useful coefficient bindings or proof techniques.
The nine-positive variable count is unchanged by wave nine.

Package 66 uses the complete original31 tuple. The separate
whole-tuple compact54-sharp rebinding now passes both sealed release
replays, with all 85 kernel coefficient bounds, threshold parity and eleven
live fixed leaves recomputed. Its even radix exponent removes one gate.
The native tuple occupies 215,492 raw bytes and the derived live fixed
leaves occupy 1,565,018 raw bytes. This is a local finite-certificate result;
it does not change the delivered package or close its Lean semantic proof.

## Other domains remain relevant

* Fifteen positive variables: package 60 reduces the degree-24 form from
  90 to **89 operations**. The older 66-operation, degree-157 point remains
  a different tradeoff.
* Fourteen positive variables: 64 gives **83/30**, while 65 gives
  **92/26**. Package 63's 87/34 is dominated by 64's point.
* Thirteen positive variables: 62 gives **83/114**, and 61 gives **93/34**.
  These improve the previous degree/cost frontier in different directions.
* Twelve positive variables: 61 adds **104/118** and **103/172**. The older
  89/258 and 94/242 choices retain lower operation counts.
* Ten unrestricted integers: the new frontier includes 66's
  **490/3,547,076** and **494/3,507,876**, and 67's
  **519/3,327,556**. The additional Sun bridge is not formalized here.
* Low-degree unrestricted systems: 64 gives **41 variables at degree 4**;
  62 gives **35 at degree 6** and **30 at degree 8**. These use their own
  complete coefficient tuple and sign-restoration proofs. Counts for
  multiple residual systems are not substituted for single-equation costs.

## Reuse and new proof obligations

Package 66 changes two source coordinates by
`P_old=P_new+eta+zeta` and `N_old=N_new+q`. The old positive zero equations
justify the inverse positive domains. Its new 85-record source needs a
fresh literal extraction certificate; its historical unrepaired layout
really fails a new interaction and is explicitly rejected. The repaired
H2082 layout, affine source reconstruction and population parity factors
must be formalized. The simple variant reuses the current free-carrier
tail; the refined variants require new seventh-order majorants.

Package 65 permits a repeated kernel position only when every owner has
the same complete coefficient polynomial in all four ports. This is not
an arbitrary numerical collision, and the coefficient is stored once.
Its source rows and free-carrier tail are unchanged. The next proof work
is the compatible-overlap extraction certificate and generalized numeric
geometry/range/calibration constants.

The checked package-59 result is preserved: all 22 authoritative old-z
rows, all 89 literal kernel records, sharp port-box height, exact
source/binomial/finalizer composition, unbounded cofinal witnesses and
the actual nine-variable `MvPolynomial` source equivalence pass Lean.
Our joint-power version additionally saves 17 gates, with its particular
generic-ring and multivariate-polynomial rewrite now checked in Lean.
Its counted-DAG/source-recipe identification remains separate. These remain useful proof
checkpoints even though the numerical target has changed.

The signed native Pell step-down and main bootstrap are also checked under
explicit native port relations. They do not yet identify the fixed payloads'
native/tableau predicate with K215 refutation. That remaining calibration
and the internal object-language ZFC biconditional are distinct from the
finite package replays. Alternative encodings can bypass those specific
interfaces, but must supply their own complete proof of the same endpoint.

## Verification evidence

The full original manifest-bearing archives were extracted from the arrival
commit. Deduplicated placed trees were not repaired or mistaken for full
release trees. All eight normal root drivers pass, including coefficient
rebuilds, exact algebra and degree checks. Declared optimized replays and
critical independent `-O` stages pass as documented in the two receipts.
Intentional root optimization rejections are policy controls, not failures
of their separately replayed mathematical checkers.

[`review_wave9_frontier.py`](tools/review_wave9_frontier.py) independently
audits **136 selected wave-seven/eight/nine and local DAGs**. Normal and
optimized runs agree on topology, full liveness, binary counts, expected
degree transcription and SHA256. Its result is
[reviews/wave9-circuits.json](reviews/wave9-circuits.json). It does not prove
degrees by propagation or infer unbounded semantic correctness.

The archive/replay receipts are
[arithmetic](data/wave9-review-arithmetic.json) and
[structural](data/wave9-review-structural.json). None supplies an end-to-end
Lean consistency theorem or exported internal ZFC derivation for a new
wave-nine equation.
