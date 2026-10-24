# Round 15 source and incoming construction review

Review date: 24 October 2026. Public snapshot: 45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6, committed 22:28:29 UTC. This is a read-only review. No upstream program was executed, repository was changed, or file uploaded.

## Main finding

The incoming Coprime Projection packet already gives an eleven-unrestricted-integer equation at degree 688 with 126 live binary operations, and an alternative at degree 728 with 122 operations. Both improve the delivered round-14 twelve-integer 768/141 point in variables, degree and operations. The eleven-variable arithmetic proof received a focused new review here with no defect found; its inherited native/compiler/refutation calibration is still an imported ordinary mathematical result. The exact operation counts are independently recomputed below; exact degree claims were reviewed through their leading-form arguments but not re-executed through the packet's programs.

Accordingly, a new round-15 twelve-variable result alone should not be advertised as the current compact integer leader. Combining the eleven-variable coprime guard fusion with the powered carrier is a more promising target. The independent research lanes have been given these sources.

## Snapshot and provenance

The newest commit only adds eight ZIP files to docs/incoming. It does not integrate or accept their results into active source, and the catalogue README still covers the earlier eighty packages through source 110.

Source: https://github.com/VladimirReshetnikov/ProveIt/commit/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6

The immediately preceding source work includes:
- cf9ee33f4bd0d9b32e4151a15811c7cd740d6e36: a complete constant recipe 50 nonwhite characters shorter, with a coherent selector permutation and fresh calibration; the canonical equation itself is unchanged.
- 87f7caadc0c3bc4f76b30595243155b1c51a3332: a complete 569-integer direct quartic, 363 residuals, 7,197 terms, height 2,445,790,974,704.
- e6ef991ae17076c3c6302594eb17fdfa413a134f: ten-positive 97/368 and 102/344 square-weight alternatives.
- cf4cb122c7588387be577bece802735c724ef443: current ten-positive 98-operation/degree-360 page and 103/332 direct-coordinate sibling.

Full commit messages are retained in recent_commits.json. The eight ZIP filenames and Git blob identifiers are in public_main_commit.json. Four additional archives were recovered here from their public pinned raw URLs after Library search found none and the connector could not transfer binary content. Every acquired byte stream matched its exact Git blob SHA-1. new_archive_acquisition.json records SHA-256, member count and extraction path. Extraction rejected traversing or symbolic-link members. The parent recovered the other four archives.

## Current public source versus delivered packages

CURRENT_EQUATION.json at the pin declares 10 strictly positive integer unknowns, exact degree 360, 98 live binary operations, and 295,388 raw coefficient bytes. Its scope explicitly preserves ordinary native/controller calibration, while Lean is paused and no new internal object-ZFC derivation or assertion of consistency is made.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/Computability/DiophantineConsistency/CURRENT_EQUATION.json

The active README records 569-integer quartics and 574-variable height-964,213 and 573-variable height-45,769,613 alternatives. Those figures supersede stale 610/604-variable descriptions in historical catalogues, but do not supersede our separately delivered 517/519-variable round-14 constructions.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/Computability/DiophantineConsistency/README.md

The placed collection already contains a quartic in 37 unrestricted integers, albeit with enormous coefficients. It also records eleven-integer constructions without Sun's reduction, previously degree 2,240/206, and ten-integer constructions using a cited Sun reduction. Thus eleven variables are not an absolute variable-count record and a 500-variable direct quartic is not a global quartic-variable record.

Source: https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/Computability/DiophantineConsistency/con-zfc-diophantine-forms/README.md

## Incoming integer norm comparison

Numbers below are degree / operations. Z means all integers; positive means strictly positive, never nonnegative.

- Coprime Projection, 11 Z: 688/126, 728/122, 1632/114, and a dominated 1892/114 companion.
- Coprime Projection, 12 Z: 500/148.
- Coprime Projection, 13 Z: 274/129.
- Coprime Projection, 14 Z: 108/119.
- Coprime Projection, 15 Z: 56/110.
- Powered Saturation round 14, 12 Z: 768/141.
- Saturated Pell, 12 Z: 1084/123, with a dominated 1280/123 control.
- Carriers and Even Indices, 12 Z: 1040/140, 816/144, 800/147, 784/154, 768/161.
- Structural Compression, 13 Z: 536/126; 12 Z: 1200/138 and 1456/137.

The 11 Z 688/126 and 728/122 points dominate the round-14 12 Z 768/141 point in these three measures. The 12 Z 500/148 point remains a lower-degree/higher-cost tradeoff. The structural 13 Z 536/126 and coprime 13 Z 274/129 are a cost/degree tradeoff. Do not confuse numeral bit complexity with live arithmetic operations.

Packet source:
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/docs/incoming/ZFC_Diophantine_Coprime_Projection_2026-10-24.zip

## Incoming ten-positive frontier

The newly supplied points are 283/92, 278/93, 266/96, 258/98 and 254/99, all in ten strictly positive integers. They are a degree/operation frontier, not unrestricted-integer equations. The 266/96 packet dominates the new structural 360/96 point and the current public 360/98 page in both arithmetic measures. The quadratic-frames 278/93 result overlaps the saturated-Pell frontier; no independent novelty claim should be made from duplicate metrics alone.

Source packets:
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/docs/incoming/ConZFC_Saturated_Pell_2026-10-24.zip
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/docs/incoming/con-zfc-quadratic-frames-2026-10-24.zip
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/docs/incoming/con-zfc-structural-compression-2026-10-24.zip

## Direct quartic comparison

All rows have degree four. Numbers are variables / residuals / collected terms / coefficient height.

Previously delivered round 14:
- Z: 519 / 321 / 6,253 / 411,060.
- Z: 517 / 310 / 6,774 / 3,904,267.
- Nonnegative integers: 349 / 268 / 12,768 / 86,915,503.

Signed Powers and Height Two:
- Z quotient radius: 577 / 363 / 7,326 / 2,445,790,974,704.
- Z quotient radius low height: 582 / 368 / 6,069 / 964,213.
- Z square-output radius: 586 / 372 / 7,059 / 2,445,790,974,704.
- Z square-output radius low height: 591 / 377 / 5,835 / 964,213.
- Z private units: 3,564 / 3,350 / 14,518 / 2, with exact coefficient alphabet {-2, 1, 2} and constant coefficient one.

Synchronized Exponents:
- Nonnegative integers: 358 / 275 / 8,229 / 9,903,520,314,287,616,167,992,362,844.
- Nonnegative integers: 361 / 278 / 6,759 / 9,903,520,314,287,616,167,799,424,614.

Structural Compression:
- Z: 589 / 371 / 8,156 / 2,445,790,974,704.
- Z: 595 / 377 / 7,595 / 6,956,012.
- Z: 600 / 382 / 7,075 / 964,213.

Carriers and Even Indices:
- Z: 566 / 372 / 6,431 / 2,445,790,974,704.
- Z: 590 / 396 / 4,776 / 964,219.
- Z: 597 / 403 / 4,767 / 938,267.

Quadratic Frames:
- Z: 576 / 368 / 7,172 / 2,445,790,974,704.
- Z: 582 / 374 / 6,200 / 964,213.

The old 519-variable equation dominates the listed large-height principal 566/569/576/577/586/589-variable equations in variables, terms and height, not necessarily in every representation-dependent statistic. The 582/6,069 and 591/5,835 smaller-support equations remain support/variable/height tradeoffs against 519/6,253. The signed-powers 582/6,069 equation dominates the quadratic-frames 582/6,200 equation at equal height. The 358/361-natural synchronized equations have fewer terms but much larger coefficients and more variables than 349/12,768; do not label them globally dominated or translate N-domain figures into Z-domain figures. The height-two construction is a genuinely different coefficient objective.

Sources:
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/docs/incoming/ConZFC_Signed_Powers_Height_Two_2026-10-24.zip
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/docs/incoming/ConZFC_Synchronized_Exponents_2026-10-24.zip
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/docs/incoming/ConZFC_Carriers_and_Even_Indices_2026-10-24.zip
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/docs/incoming/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip

## Focused proof assessment

### Eleven-integer coprime guard fusion

The full new proof is integer/PROOF.md within Coprime Projection; review/integer/INDEPENDENT_REVIEW.md gives its prior independent audit. My additional reading found the important interfaces explicitly handled:

1. Dt=1+ell(ell+1)k^2 is positive and odd; Dg=1+4D Dt s^2 is coprime to Dt. A positive square product recovers the two old roots separately.
2. The scalar intersective quintic has no rational zero. Thus the I=0 degeneration cannot produce a polynomial zero, and division by the later scale is justified.
3. The three positive odd radicands have weights 1,2,4. In each irrational squareclass the unique least 2-adic order cannot cancel. This recovers integral roots without assuming independence of radicands.
4. Main-Pell classification is recovered by absolute signed folding before the congruence projection and orientation; the even strong multiplier is not falsely normalized to an odd one.
5. Completeness first fixes outer data, then guard Pell witnesses, then one strong pair, then selects the intersective auxiliary residue. The stated full-residue interpolation theorem uses the corrected period 4*n0*f modulo f^2, not 4*n0.
6. The all-radicand fusion includes a separate proof that the rational-cleared finalizer only gives the required divisibility after the adjacent-Pell descent. It does not assume an arbitrary rational Pell ordinate is integral.

This is a focused arithmetic/source-interface review, not independent reconstruction of every historical compiler or every transitive Lean theorem.

### Direct and structural mechanisms

The height-two transformation has a transparent unconditional zero-set proof relative to its supplied source: a private unit chain forces each unit to one; shared product variables preserve degree two in each row; private marking prevents collected coefficient collisions. The independent expansion below confirms the advertised coefficient alphabet in the literal final polynomial.

The signed quotient-radius proof must recover signs from an absolute common frame and signed residues before using power semantics; retaining or deleting twelve raw guards requires its exact original-row dependency proof. The synchronized packet's extra latent Pell index is explicitly certified, not free, and its factorial proof orders rho>=1 before the binomial bound and before factorial meaning. These are promising composable lemmas, but this review does not replace the dedicated semantic audits of their full direct sources.

The scalar/norm packets use different coherent fixed tuples: the integer lane retains source34's six coefficients, while the ten-positive lane uses compact44/BFS four coefficients. MF is already shifted where stated. Do not transplant one tuple, its byte-size claim, or its calibration into another equation.

## Refutation scope and formalization boundary

The current H10 README explicitly refutes the shared-projection83 proposal on the inherited modified75 compiler slices; that is not a refutation of the original modified75 compiler itself. It separately refutes the weakened-bound86 relaxation and explicitly says the established75 certificate and87 polynomial remain unchanged. These candidates remove necessary projections or strict positivity/bound interfaces. The two failed relaxations do not refute the source34 ordinary calibration imported here.

Source:
https://github.com/VladimirReshetnikov/ProveIt/blob/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6/Computability/HilbertTenthProblem/README.md

All resulting consistency claims must distinguish:
- the actual finite polynomial and finite coefficient/identity verification;
- the new unbounded ordinary arithmetic proof;
- the imported native/K215 or direct C222/refutation calibration;
- a new end-to-end Lean/Rocq or encoded object-ZFC derivation, which these packets do not supply.

The task asks for an equivalence provable in ZFC, not a proof of Con(ZFC) or an assertion that the equation has no solutions.

## Independent finite work done here

check_new_payloads.py is newly written, imports no upstream code, and reads only JSON payloads. independent_payload_metrics.json records:
- all ten quartics from the four newly acquired packages expanded independently from every squared residual;
- exact agreement with every supplied polynomial coefficient;
- all advertised variables live, exact degree four, term counts and heights;
- topology, variable closure and live arithmetic operation counts for all four eleven-integer DAGs.

These finite checks do not establish zero-existence equivalence, projection inverses, arbitrary witness completeness or the historical calibration. No upstream replay results are represented as fresh executions.

