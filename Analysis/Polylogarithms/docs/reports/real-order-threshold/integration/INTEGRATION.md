# Integration notes

## Preferred placement

Copy the entire package to:

`Analysis/Polylogarithms/docs/reports/real-order-threshold/`

The standalone article is the complete proof source. `05-real-order-threshold.tex` is an editorial insertion, not an automatically applied patch. All its labels use the `realorder:` prefix; the editor should choose its final section position and bibliography key.

## Canonical manuscript changes

| Existing location | Recommended action |
|---|---|
| `chapters/05-signed-kernels.tex` | Retain the original a>=1 results. Add the sharp real-order threshold after the kernel construction, with separate absolutely continuous and critical-atomic cases. |
| Signed-kernel angular discussion | Extend the zero-free and unique-angular-zero domain to a+b>=1 using the new measure theorem. At unit radius, use the separate atom-dominance proof on the critical line. |
| Euler certificate section | Add parameter-dependent bounds for 0<a<1. Keep constant one explicitly restricted to a>=1. Include the exact counterexample as a guard against an unqualified extension. |
| Real-order/affine discussions | Distinguish algebraic finite centers from their rational interval enclosures. The new integer-root verifier supports rational noninteger exponents. |
| Angular-zero continuation | Add the critical right-atom and dual left-atom normalized-radius theorems. Do not mark the broader finite-b conjecture solved. |
| Integration / Hurwitz chapters | Cross-reference the critical beta-average identity and its completely monotone normalized Hurwitz expression. |
| Research agenda | Add critical optimal constant, below-threshold zeros, and real-parameter radial phase questions. Keep S6 conjectural. |
| Editorial ledger / validation | Record analytic proof, exact rational computations, exact symbolic checks, numerical diagnostics and PDF review separately. |

## Mandatory qualifications

On a+b=1, the representing measure contains `(1/a) delta_1`. Dropping that atom gives mass `-1/a` rather than zero. Its necessity follows both from the explicit formula and from the limit of the moments.

On a+b=1, the ordinary boundary series diverges; its coefficients tend to `1/a`. Gaussian boundary values and the Euler evaluator mean analytic/Abel values. On a+b<1 coefficients grow without bound and no finite signed Hausdorff measure exists.

The exact counterexample concerns **extending** the old error bound, not refuting it under a>=1. The twelve certified root brackets include one subcritical bracket that asserts existence only.

The package was prepared against a fixed snapshot. No GitHub file, commit, branch or historical certificate was altered. Reconcile newer upstream material before integration.
