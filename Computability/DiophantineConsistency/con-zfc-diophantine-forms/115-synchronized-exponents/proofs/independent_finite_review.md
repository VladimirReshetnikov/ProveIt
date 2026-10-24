# Independent arithmetic review: common exponent and latent-square seed

**Status: PASS for the finite arithmetic and projection claims listed below.**

Reviewed candidate: `analysis-incoming/experiments/common_exponent_latent_square/both`. `ARITHMETIC_REVIEW.json` binds the exact bytes. This review imports no builder or contraction producer. It imports only the separately inherited independent PSD-certificate checker and otherwise reconstructs the relevant calculations directly from the delivered raw rows.

## 1. Complete parent and projected polynomial

The raw record and gate ledger agree in all 1,232 variables and 1,149 quadratic rows. Every definitional gate has an isolated monic output and depends only on earlier variables. The reviewer independently reconstructs all 599 affine restorations, checks that their coefficients are nonnegative, substitutes them through every raw residual and checks that the resulting 633 coordinates and 550 rows exactly match `parent.json`. No dead-gate discard is needed in this candidate.

Independent sum-of-squares expansion matches all 3,552 coefficients in `source_polynomial.json`.

The inherited independent PSD checker then replays every one of the 275 projection steps. Each deleted coordinate has an integer quadratic restoration, with nonnegativity certified by an exact rational weighted sum of squares plus nonnegative monomials. The two restorations with negative coefficients are handled by these actual certificates; their nonnegativity is not inferred from their printed coefficients alone. Substituting every restoration gives all 275 final residuals and all 358 final coordinate names in the stated order.

Independent expansion matches every one of the **8,229 nonzero terms** of the target polynomial. Its exact degree is **4**, and its coefficient height is **9,903,520,314,287,616,167,992,362,844**. These are measured properties of the complete literal equation, not asymptotic or syntax-only estimates.

## 2. Common exponent: exact literal binding

The raw rows specify

- `v4 = t0 + 2`, hence `t >= 2` on the declared natural domain;
- `v6 = 4,194,304 * t`;
- the first power is `(t+1)^v6`;
- the second power is `(2+t+x+y+M0)^v6`.

The two power calls literally share the same exponent atom `v6`. The unchanged label majorant uses exponent `E = 4,194,304 = 2^22`; the unchanged local majorant uses `2E = 8,388,608 = 2^23`. Thus the new common exponent `E*t` is at least the old fixed local exponent, because `t >= 2`.

The carrier power agrees with `((t+1)^t)^E` by the elementary power law. The new majorant power is generally larger than the earlier fixed power; no pointwise equality with the old complete arithmetic source is claimed. The ordinary proof must use majorant domination and horizon padding, as distinguished from the subsequent exact projection.

## 3. Latent seed and shared square: no omitted certification

The raw multiplication row gives `rho = v45 = v44^2`, where `v44` is the first factorial output. Both factorial macros use this exact same radius atom. Their inputs are the majorant `H = v43` and horizon `t = v4`, respectively. The reviewer checks the complete expanded ceiling and remainder rows for both macros directly from the gate ledger.

The extra radius is **not merely added to a metadata list**. Its actual Pell index pair `(v756,v757)` appears in the independent seed list. The global auxiliary divisibility row expands to

`V_aux = (product of all 15 seed Y-coordinates squared) * (quotient_minus1 + 1)`.

The radius seed ordinate `v757` occurs squared in that product. The complete frame row bounds all 22 original power calls. It also bounds `rho`, although `rho` is not itself a power-call exponent: the positive power base `rho+1 = v48` occurs among the bounded atoms. Hence no separate unrecorded frame extension is required for this latent seed.

All three derived index pairs are checked coefficient by coefficient:

- the index `H+rho` is obtained from the certified indices `H` and `rho`;
- the index `t+rho` is obtained from `t` and `rho`;
- the index `t+1` is obtained from `t` and the fixed index one.

The literal exponent-definition rows are checked as well as the pair formulas. The shared discriminant row is exactly `D = A^2 - 1`. Each pair satisfies the exact addition identities

`X_(a+b) = X_a X_b + D Y_a Y_b`,

`Y_(a+b) = X_a Y_b + Y_a X_b`.

There are precisely 18 index pairs: 15 independent seeds and 3 derived pairs.

## 4. Claim boundary and remaining mathematical dependencies

This review proves that the inspected rows encode the intended common-exponent and latent-index formulas, and proves the complete affine and PSD projection/expansion assertions. It does not reprove the inherited Pell positive-power theorem, the factorial fixed-point theorem, the CRT/compiler semantics, the numerical source-calculus equivalence, or an internal ZFC formalization.

The use of positive-power macros must still be justified in the ordinary proof in a noncircular order. In particular, the first factorial output is initially an unrestricted natural coordinate and is later used as a positive power base. The existing route can establish its positivity from the `(rho+1)^H` power and the factorial ceiling/remainder equations before interpreting the power with that factorial output as its base; the separate mathematical review should make that order explicit. No extra positive-domain assumption has been inserted by this arithmetic review.

No proof-critical arithmetic discrepancy was found. The exact finite output is a natural-domain quartic in 358 variables. Its refutation/consistency interpretation remains conditional on the explicitly inherited ordinary semantic theorems, rather than on the success of a finite replay alone.
