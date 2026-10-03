# Release notes

Date: 2 October 2026

## Proven claims

1. All-schema soundness and existential consistent-schema completeness for legal one-step transitions
2. Conditional uniqueness only of the derived U, Y, O and F auxiliaries after fixing numeric source and decorated schedule
3. Exactly V = dK + A + E + B + 3dJ + KJ variables and R = (3d + 2K)J + (d + K)L + Z residuals in the generic dense compiler
4. Residual degree at most two, sum-of-squares degree at most four, and the stated residual coefficient-height bound
5. One constant 18-variable, 30-residual schema for arbitrary positive clone doubling
6. Nested depth-D division producing 2^(D+1)-1 membranes with V = 2D^2+11D+5 and R = 8D^2+15D+7
7. Exact next-population identity by surviving old roots and dividing ancestors, with sharp one-step upper bound 2^n-1 for n old membranes including skin
8. A fixed deterministic four-rule system with 2^T distinct base-4 payloads after 2T steps, implying a lower bound only for identical-subtree quotients

## Finite replay coverage

- 48,621 candidate plans, 2,123 legal plans and 160,332 evaluated residuals on legal cases in the main suite
- 275 rejected single-coordinate derived-auxiliary mutations
- Nested division depths 1 through 10
- A 10,001-bit clone population, without population expansion
- Eight deterministic anti-sharing rounds, giving 256 distinct leaves
- Per-parent resources, mixed schedules among identical source children, old-versus-produced objects, local dissolution/copying and cascaded forest promotion
- Signed-integer zero counterexample showing why the natural domain must be checked
- Duplicate catalogue-index counterexample showing why arbitrary fixed-schema completeness is not asserted
- 228 mixed structural population-identity checks, in addition to the sharp chain family
- Contextual quartic expansion: degree 4, 282 monomials, coefficient height 19, zero at the valid witness and positive at the tested mutation

See the generated JSON receipts for the exact executed outcomes. The tests intentionally use bounded instances; infinite claims are proved in the article.

## Universal frontend status

The source-supported 2006 two-register construction is a candidate effective frontend compiler. It is generative, needs declared display repairs, and needs a skin/inner role-label split to match the implementation. This release does not contain a literal fixed universal program or its external input loader. A separate later frontend construction would need its own proof and accounting.

## Research implementation status

The mathematical theorem assumes a well-formed finite acyclic schema. The Python compiler contains relevant syntax and semantic guards, but it is not a hardened parser for malicious JSON. Its recursive traversals should not be treated as a security boundary. Natural-domain checks are explicit in the replay routines.

## Deliberately excluded

Third-party source PDFs and OCR material, internal reviews, formal-verification claims, priority claims, fixed universal witness counts, universal operation records, and uncharged time-interface equations.
