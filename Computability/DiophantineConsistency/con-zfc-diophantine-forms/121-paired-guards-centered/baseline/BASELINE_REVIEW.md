# Pinned baseline review for the next Diophantine research iteration

Snapshot: https://github.com/VladimirReshetnikov/ProveIt/tree/45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6
Observed at 2026-10-24 22:31–22:35 UTC. This review is read-only.
The snapshot was the latest main commit at lookup, dated 22:28:29 UTC.

## What has been materialized and verified

- 164 files at the root of Computability/DiophantineConsistency.
- Complete selected research packets for ten-positive-index-weight, ten-positive-square-weight-tradeoff, power0/power3 output-square-frame proofs and projected families, and indexed-tile-enumeration.
- The matching index/square-weight and power0/power3 review files.
- Seven newly arrived peer archives, extracted as inert files under arrivals/. The parent recovered our eighth archive separately in ../prior/ZFC_Diophantine_Coprime_Projection.
- BASELINE_CHECKS.json authenticates 521 downloaded files (30,376,368 bytes) against their exact pinned Git blob identifiers and also records SHA-256 hashes.
- No downloaded Python, TeX, shell, compiler, checker, or other program was executed in this review. Existing receipts are attributed reports, not new replay results.
- tree_index.json records the root listing and recursive research/reviews trees. This is a selected source snapshot, not a complete checkout or proof dependency closure.

## New upstream commits after the supplied late pins

1. e6ef991ae17076c3c6302594eb17fdfa413a134f (21:58:25 UTC): complete ten-positive square-weight alternatives, 97 operations / degree 368 and 102 / 344.
2. 87f7caadc0c3bc4f76b30595243155b1c51a3332 (22:18:56 UTC): remove raw106's sign guard after an acyclic signed-output recovery, giving a complete direct quartic with 569 integer variables, 363 residuals, 7,197 terms and height 2,445,790,974,704.
3. cf9ee33f4bd0d9b32e4151a15811c7cd740d6e36 (22:25:54 UTC): directly indexed tile enumeration saves 50 nonwhite printed characters in the complete constant recipe. Arithmetic remains ten positive variables, 98 operations, degree 360.
4. 45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6 (22:28:29 UTC): eight research ZIP arrivals, including our previous coprime-projection release.

## Exact current canonical display

CURRENT_EQUATION.json, not an old narrative paragraph, is the authoritative local pointer:
ten strictly positive variables, 98 live binary operations, exact degree 360.
The canonical PDF and TeX remain the index-weight versions.
PDF SHA-256: a41fdda9c4129f8607b43805ffd2ce0b57d5d3013da7e58c3f4f578322ab8ea1.
TeX SHA-256: 0b540714a5b572dfa319117c90ad5417a63afe5566cf07649c11f500d9db81f9.
The beginning of SIZE_REDUCTION.md still contains an older 101/368 narrative paragraph despite its current comparison table and later sections. Do not quote that paragraph as the current endpoint.

## Most promising combination: transport without a separate majorant

Read arrivals/con-zfc-structural-compression-2026-10-24/con-zfc-structural-compression-2026-10-24/positive_proofs.tex.

Its new unbounded argument uses the ordinary strong/auxiliary folded source:
c=psi_A(p) with p odd, c>=3, hence c>=psi_A(3)=4Delta+3.
The pre-transport mask estimate yields b>c.
For Q=Delta²I² and the auxiliary Pell equation, V>4Q excludes auxiliary indices 1 and 3, so its odd index is at least 5.
Then V>=16Q²-20Q+5>8Q², Df<Q and b=(V+c)/Df imply b>8Q>2HI.
The errors satisfy 0<y−V<b/4 and e/mu²<b/4 even when e is negative.
Thus the transport weight can be W=1+g*b, deleting the separate HI term.
Completeness is fresh positive n reconstruction, not an unjustified inverse positive shear.

The same packet removes weight 9 through a square-gap noncancellation theorem, giving 96/360 and 102/332 before coprime saturation. The b-only estimate is the stronger promising ingredient for composition with our previous saturated two-root kernels. It cannot simply be asserted to dominate the new product root: that product's size and all scaled-ordinate interfaces must be checked explicitly. The positive research worker received this lead.

## Current index and square-weight mechanism

Sources:
Computability/DiophantineConsistency/research/ten-positive-index-weight/PROOF.md
Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/PROOF.md
and their literal JSON graphs, coefficient bindings, source pins and peer reviews.

Before transport, unchanged classification yields k=2psi_(2V0+1)(n0).
The n0=1 branch gives c=2Y+1 strictly between psi_A(1) and psi_A(2), so n0>=2 and k>=8X(muY)²+4>H.
The universal positive old-zero shear n_new=n_old+(k−H)IB replaces HI by kI.
Exact degree is governed by 16 v0² h0², not by omega^4; missing that competing term would falsely suggest degrees 352/328.
The existing-square alternative uses I²>kI and n_square=n_index+I(I−k)B, deleting kI but raising degree.
These proofs are uniform in each coherent source tuple, not permission to mix tuple components.

## New whole-tuple recipe

Read research/indexed-tile-enumeration/PROOF.md, PEER_REVIEW.md and equation.tex.
The 943 tile set is unchanged but selector ordering changes DC and K.
Beta, MC and MF_source remain byte-identical to old BFS components, yet new K requires the supplied whole native/controller calibration and fresh F,C,R words. No pointwise equality with the previous specialized polynomial is asserted.
The recipe count changes 2393 to 2343 nonwhite characters; complete page count 3217 to 3167.
Its K raw SHA-256 is 0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f.
Using the previous coherent tuple remains safer unless the report deliberately adopts and carries this complete new calibration.

## Direct quartic delta and dependency order

Sources:
research/power3-output-square-frame/PROOF.md, FULL_SOURCE.md;
research/power3-square-frame-source-prototype/ and matching review.
Raw106=f^t is replaced by a new square only in the common frame and loses its scalar guard.
Its actual power call remains unchanged.
The delayed values are exactly 106,124,125,130,132,133.
Calls8/9 orient the t and k122 Pell pairs without them.
The signed residue then gives 106=f^t using |106|<W and |106−f^t|<W^W<A<T3.
Only then restore raw130's lower bound, the prefix, shifted-t proof, range outputs and source interpretation.
This is a distinct route from compact native-source norms and does not automatically improve their counts.

## New arrivals: attributed main results and useful dependencies

The following numbers are package claims read from their manuscripts/READMEs, not newly reproduced theorems or measurements here.

- ConZFC_Saturated_Pell_2026-10-24: positive10 points 92/283, 93/278, direct98/258 and99/254; integer12 123/1084. Useful common-factor saturation and two-root noncancellation proof. Root folder con_zfc_saturated_pell_2026-10-24.
- con-zfc-quadratic-frames-2026-10-24: positive10 93/278 and direct576Z quartic. Root folder con-zfc-quadratic-frames.
- ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24: integer12 141/768; direct519Z and517Z quartics; natural349 quartic. Read architecture/FACTORIAL_CARRIER_PROOF.md, HYBRID_PROOF.md, DERIVED_LABEL_RANGE_PROOF.md; radicals/PROOF.md and norm/PROOF.md. Potential direct-source combination: self-bounding factorials, shared factorial Horn flow and derived label ranges.
- ConZFC_Carriers_and_Even_Indices_2026-10-24: integer12 weak/mixed carrier points down to degree768; direct566Z quartic. Even exponents eliminate small-ordinate index exceptions; actual derived t+1 pairs take two Pell steps and must be rewritten, not merely relabeled.
- ConZFC_Synchronized_Exponents_2026-10-24: natural358 quartic, 275 rows, 8,229 terms and94-bit height. Uses shared exponent e=2^22t and an additional certified Pell index for a common square factorial radius. Potential interaction with shared-factorial/direct349 design needs a new full source proof.
- ConZFC_Signed_Powers_Height_Two_2026-10-24: direct577Z quartic; height-two alternative with3564Z,3350 rows,14518 terms. Signed power outputs and private-unit coefficient control.
- con-zfc-structural-compression-2026-10-24: positive transport/gap result above; identical integer norm evaluations at13Z126ops,12Z138/137ops; direct589Z quartic. Read integer/COMPACT_NORM_ADDENDUM.md and integer/PROOF.md for potential exact evaluator reductions, preserving all degeneracies.
- Our prior coprime-projection package remains the strongest inspected few-variable integer baseline: 11Z688/126,13Z274/129,15Z56/110,12Z500/148,14Z108/119. Newly arrived peer reports do not supersede these specific points.

## Novelty check for the proposed double-centered fifteen-integer kernel

The proposed row
Z²+2(2L+k)UZ+U²(k²−4)=0,
with Z=Un+2q²Klo+H(v−q²), U=2q²H,
was not found in current top-level summaries or the new seven manuscripts.
A15Z/degree48 descendant therefore appears new relative to this inspected baseline.
This is not an all-history or literature-wide novelty claim.

## Logical boundary

Every new compact or direct reduction must keep the complete coefficient tuple, solution domain, all exceptional-case arguments and both existence directions.
The ordinary arithmetic proofs compose with the explicitly inherited source/calculus calibration; existing finite receipts or a local symbolic identity do not establish a new end-to-end internal-ZFC or Lean theorem.
No zero, absence of zeros, consistency assertion, global minimum, or optimality is claimed by this review.

