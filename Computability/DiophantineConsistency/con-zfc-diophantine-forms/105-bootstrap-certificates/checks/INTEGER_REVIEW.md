# Independent review of the integer sign reduction

Review date: 2026-10-24. Reviewer: the direct-Pell/norm research subtask,
independent of the integer builder's author.

## Scope and conclusion

I reviewed `integer/PROOF.md`, the complete `build_integer.py`, the complete
builder-free `verify_integer.py`, and its retained `projection.py`. I also
inspected the actual parent, sign schedule, guarded equations, projections,
and final coefficient dictionaries in `integer956` and `integer989`.

**No mathematical error or checker gap affecting these supplied equations was
found.** The sign argument is valid over unrestricted integers. Its hypotheses
are discharged by a finite acyclic schedule covering all 781 original
coordinates. The exact monic substitutions preserve the integer zero set,
and summing the remaining quadratic residuals squared gives degree four.

This review concerns the new natural-to-integer reduction. It does not
independently reprove the entire inherited refutation/C222 compiler or claim
an end-to-end proof checked by a proof assistant. The mathematical equivalence
to the parent is unconditional; the interpretation as Con(ZFC) composes it
with the parent's separately documented theorem.

## Points checked

1. **Frame-root orientation has no circular sign assumption.** The norm and
   frame identities give
   \(A^2=1+W^3(W+2)(z+1)^2>W^4\) from \(W\ge2,z\ge0\).
   Since \(A\ge0\), this gives \(A>W^2\ge W\ge n\). Therefore the exact
   row \(X+Yn=YA+m+Tq\) implies \(X\ge0\) using already proved signs of
   \(Y,m,T,q\). No classification of Pell solutions and no prior sign of
   \(X\) is used. The checker verifies the norm, frame sum, base-modulus
   identity, power identity, and every coefficient of \(W-n\). Although the
   margin's dependencies are not separately listed, its positive-coefficient
   support is contained in that of the frame RHS: both the base and margin
   have nonnegative coefficients and their sum equals the frame RHS. Thus
   the recorded frame dependencies suffice. In the actual schedule, \(A\)
   and \(z\) are seed-guarded, and all other dependencies precede each of the
   18 oriented roots.

2. **The quotient identity has the stated sign and constant.** Subtracting
   the three digit rows gives exactly
   \(dQ(h+1)-(N+dt+s+1)=-R_1+dR_3+R_2\).
   The analogous ordinary quotient identity is
   \(d(q+1)-(N+s+1)=-R_{\rm division}+R_{\rm bound}\).
   The checker tests these polynomial equalities after unfolding actual
   backward gate definitions. It then requires nonnegative coefficients
   for the left factor and right side, right-side constant at least one,
   and all odd-power dependencies already proved. Hence a nonpositive
   \(h+1\) or \(q+1\) is impossible. Neither positivity of an unproved
   denominator nor a hidden division operation is assumed.

3. **The centered guard is exact, including its boundary.** For integers
   with \(x+y\ge-1\), nonnegativity of \(2xy+x+y\) implies positivity of
   \((2x+1)(2y+1)\). Both factors cannot be negative, since that would give
   \(x+y\le-2\). The checker authenticates the sum row and its lower bound,
   requires the exact pair guard to be appended, and proves its dependencies
   first. The guard polynomial \(a^2+b^2+c(c+1)\) is nonnegative over all
   integers and represents every nonnegative integer by the three-square
   theorem applied to \(4n+1\). This establishes both directions, rather
   than only soundness of the guard.

4. **Coverage and projection are complete.** The independent schedule
   census found 163 seed guards, 8 pair guards, and 610 rules: 571 polynomial,
   13 shifted-product, 8 centered-pair, and 18 frame-orientation rules.
   Their outputs are disjoint from prior proved coordinates and cover all
   781 parent coordinates. All dependency indices precede their uses.
   Parent variable names and all literal variable indices are valid and
   distinct as applicable; the guarded prefix is byte-equivalent as JSON
   data to the complete parent. Both variants use the same guarded system
   of 1294 coordinates and 848 rows. The projection checker substitutes into
   every retained row, checks each pivot and restoration exactly, prevents
   restoration from using an already deleted coordinate, and verifies every
   final row and collected polynomial coefficient. No unconstrained
   coordinate is removed in either supplied variant.

The checker imports neither builder nor optimizer and uses explicit
exceptions, so Python `-O` does not disable its checks. The root task is
separately running the full checker in normal and optimized modes; this
review additionally performed its own JSON dependency and coverage census
without importing those implementations.

## Independently read final metrics

| Variant | Integer variables | Quadratic rows | Degree | Collected monomials | Coefficient height | Restorations |
|---|---:|---:|---:|---:|---:|---:|
| integer956 | 956 | 510 | 4 | 10,988 | 2,445,790,974,704 | 338 |
| integer989 | 989 | 543 | 4 | 7,705 | 63,910,295 | 305 |

Both final sign certificates and guarded equations match `work_signs/final16`
exactly. The final equation metadata now points to `projection.json`; this
descriptive change does not alter a residual coefficient.

## SHA-256 pins

Paths below are relative to the final integer component except the stated
parent. These pins cover the exact files reviewed, including the final
metadata correction.

```text
parent781/equation.json (agent_alt/result/equations/)
c3d6c12ca8393f01f76f4f375c0a1ec5681c999a39ae421f163341334edf19e0

PROOF.md
c7c73475fa625d9d9a5bd1d7ba237ad438cbafd5a7728505db2aaddb264b26f2
build_integer.py
689ee7a459bfb9832a92babb5c92640f9b30df2b66d531b07a92046b1ed88184
verify_integer.py
359584e149af68348bc9ec08a5454316265093f46f9693a4980423f54dd7561d
projection.py
51c6d185e30bf486fde7622203605ad0e6dfd523229bc746d7011f1554efed95

equations/integer956/sign_certificate.json
equations/integer989/sign_certificate.json
12bf4f710fb558161db1ee4d2bace3439331d0e10f268d3f3d6f907e5d966e2e
equations/integer956/guarded.json
equations/integer989/guarded.json
142063fab7d5737c63ba58e27c3cad28fbb32a1d60cbd6d99bb031977ccf7872

equations/integer956/equation.json
33726b965af8955f64bb259624b606d4e42d1704ea77d46daee2044268bc06a5
equations/integer956/projection.json
fe2aa508abedc8e40a89c601ce8af4cf617c8e46025b4db1e902d9e0d4580913
equations/integer956/metrics.json
25ef7e62450e22f873baa04bde0225cd19c084f529571f3f621501905ef9c5d4
equations/integer956/polynomial.json
25e3a01f387452c8832c52ceb81b17230c35f75c1f205efca346cd63355dd59c

equations/integer989/equation.json
34c711ab06a19cd3842bf1f40c9ba620ce4abff4f77fe3d79d7770605e53e291
equations/integer989/projection.json
624713455952f8573e13123c0ed4c01c42bff29d9f574849ae7db8b839ed24c6
equations/integer989/metrics.json
cd5d3e34136d5d64d59804af38e71f21004b37c0fa97a0215d50c2300e682e04
equations/integer989/polynomial.json
4e13fb0ee2119b80f656379689e37c868c59e39ae23174adb6155daf9976b504
```
