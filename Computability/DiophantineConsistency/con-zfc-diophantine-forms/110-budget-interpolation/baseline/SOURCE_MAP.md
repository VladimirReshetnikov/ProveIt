# Wave 13 pinned source map
Source review and scoped replay: 2026-10-24 03:32–03:42 UTC.
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned main commit: 7e533c33819ee1f703b69f2778a767cdc069940d
Comparison base: 55ca592b2f4201089b3d6d150f3d41fb01762734
GitHub reports 32 commits ahead, no divergence. The pinned commit includes 8f8fac484b976ba0ab75fd173282e838ca5a3b85.

All paths below are relative to /workspace/shared/diophantine_wave13 unless stated otherwise. Archives and 77 selected candidate files have been checked against their pinned Git blob SHA-1; FETCH_LEDGER.json also records SHA-256. After reviewing the execution surface, rootfusion's full normal and optimized release audits, parity's full normal release, and seven standalone parity optimized algebraic auditors were freshly replayed and passed. The parity optimized whole driver was also checked and rejected execution by its stated policy, as expected. Both original source trees stayed byte-unchanged. See replay/results/REPLAY_SUMMARY.json and REPLAY_REVIEW.md. Other upstream verification receipts remain source claims, not fresh local replays. No worldwide or global minimality claim is made.

## Fast navigation

- baseline/README.project.md: pinned project overview.
- baseline/PROPOSAL_REVIEW_LATEST.md: current upstream comparison and review boundaries.
- baseline/PROPOSAL_REVIEW_PARITY_FAMILIES.md: particularly useful ordinary proof synopsis.
- baseline/PROPOSAL_REVIEW_ROOT_FUSION13.md: exact dependency order for guard-first fusion.
- baseline/PROPOSAL_REVIEW_PRIME_SEPARATION.md: signed valuation separation, midpoint-integrality correction, degree108 companion.
- baseline/PROPOSAL_REVIEW_FIXED_PRIME_RADICALS.md: complete signed prime-separation theorem.
- baseline/COMMITS_SINCE_55ca592.json: all 32 intervening commit messages.
- baseline/COMPARE_SINCE_55ca592.json: changed-file map (GitHub compare listing may impose a file cap).
- baseline/FETCH_LEDGER.json: archive and candidate download authentication.
- prior/ZFC_Diophantine_Centered_Compression: recovered authentic wave12 research packet, provided by parent via Library. Do not confuse it with the incoming dependency-only ZIP.

## Relevant small-variable frontier

Numbers below are (variables, exact total degree, live binary operations), separately by domain. Fixed numeral leaves and register reuse cost zero; every binary +, -, multiplication including squares and scalar multiplication costs one.

### Unrestricted integers

- (13,1088,195), (13,1392,186), (13,1408,185): root fusion.
- (14,652,163), (14,664,156), (14,696,150), (14,748,148), (14,792,137): compact fixed-prime and root-fusion tradeoffs.
- (15,204,128), (15,352,124): first parity family. The degree204 point strictly improves wave12 (15,300,132).
- (16,106,123): wave12 centered normalized merger. Retains a lower degree than all currently reviewed upstream16 forms.
- (16,112,119): second parity family, lower operation count but higher degree than wave12 degree106.
- (16,138,122): wave12 SOS alternative, now strictly dominated by upstream (16,112,119).
- (16,160,115): first parity family, further operation/degree tradeoff.
- (17,48,110): wave12 normalized17, strictly dominates upstream quotient (17,88,110).
- Upstream (16,108,132), prime separation, is dominated by wave12 (16,106,123), but its exact53-term norm identity may be useful.
- Larger low-degree upstream rows include (18,32,112), (19,28,116), and20 variables degree18. These do not dominate the above variable/degree tradeoffs.
- Ten-integer high-degree upstream points remain distinct: degree1245324/471ops and degree1179788/475,1114252/478,1080888/512. They use a different original31/H1868 tuple; they are not small-degree13–17 forms.

### Strictly positive integers

- (10,1152,131): four-root radical/residue construction. Complete compact44 polynomial, not norm10 integer shears.
- (11,211,111): both current adaptive-shear candidate and wave12.
- (12,70,100), (13,51,90), and14-positive operation/degree alternatives73/342,74/312,75/293,76/191 appear in the pinned upstream overview, but were not the focus of this source download.
- Nine-positive high-degree alternatives include433ops/1628768,722/1158228,953/999518, on their distinct specified coefficient tuples.

### No K215/Jones dependency

- Complete direct C222 quartic:3443 nonnegative integers,2838 rows,15754 collected monomials, coefficient height127302193.
- Retained-wire alternative:5960 nonnegative integers,5355 rows,16894 monomials, height1992.
- Separate signed-domain prime-lift quartic:8619 unrestricted integers,4619 quadratic rows,39811 monomials, height127285349.
- These are ordinary literal polynomials, not compiler-only interfaces. They retain named ordinary C222↔ZF-refutation and ZF↔ZFC-refutation interfaces; no new internal-ZFC/Lean completion is claimed.

## Exact artifact roots and mathematical dependencies

### 1. Root fusion13 and quotient companions
Root: baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24
- report/report.tex and report/crt1088.tex.
- equations/norm13_crt_degree1088.json, norm13_degree1392.json, norm13_degree1408.json.
- equations/norm14_degree696.json, norm14_degree792.json, norm15_degree344.json.
- companions/quotient_fusion: four lower-degree coordinate companions.
- provenance/upstream_ordinary and provenance/CALIBRATION_STATUS.md.
Mechanism: four roots are real/positive on every integer input; norm zero first forces the fifth, guard radicand nonnegative. Guard consequences establish strictly separated magnitudes, hence signed-subset noncancellation even when squareclasses are dependent. Galois rationality plus integer-square and adjacent-Pell descent restores roots. CRT degree1088 variant recovers cubic Pell scale and main congruence from one coprime carrier. Completeness uses compatible canonical Pell reselection, not a free zero-set bijection.

### 2. Compact fixed-prime evaluators
Root: baseline/candidates/fixed-prime-compact-norms
- PROOF.md, compact_norms.py, build.py (read only so far).
- integer14_degree652_compact.json, integer14_degree664_compact.json, integer14_degree748_compact.json.
- coefficients/BINDING.json and coefficients/payloads: all six whole source34 numerals.
- Exact generic four-root43-op and five-root93-op evaluators replace110/370-op Taylor forms. Entire parent polynomials are identical, not merely existence-equivalent.
- Parent full proof: baseline/ConZFC_FixedPrime_Radicals_2026-10-23/con-zfc-padic-compression/report/report.tex.
Mechanism: pairwise distinct even valuations at3 forbid signed cancellation inside each squareclass, before positivity. Fifth pentagonal guard recovers positivity, then adjacent descent. Four/five norm operation improvements are exact free-radicand identities.

### 3. First parity family: strongest15-variable source
Root: baseline/con-zfc-parity-norms-2026-10-23/con-zfc-parity-norms-2026-10-23
- PROOF15.md: primitive three-root merger and15-variable reduction.
- PROOF.md: odd-carrier two-root lemma.
- parity15_unit_product_dag.json:15/204/128.
- parity15_sos_dag.json:15/352/124.
- parity16_sos_dag.json:16/160/115.
- PARITY_MERGER_REVIEW.md, COMPACT_NORM_REVIEW.md, SOURCE_PROVENANCE.json.
Mechanism: A=4A4+1, B=4b_guard+1, Caux=(Q-1)(QV²-1); weights1,2,4 enforce parity-based squareclass noncancellation. Primitive norm divides the eight-sign polynomial by the fixed integer256, with integral coefficients. Retained strong row proves Q≠1 before the deleted guard is recovered. Q=0 is handled separately. Unit product has degree204 versus SOS352. Every parent zero reconstructs through actual private roots; no new canonical reselection needed for this15-variable endpoint.
Caution: full ordinary driver intentionally requires nonoptimized Python; upstream separately ran seven algebraic auditors under -O. Do not call that a successful optimized whole driver.

### 4. Second parity family: modulus-four16-variable source
Root: baseline/con-zfc-parity-norms-2026-10-23 (2)/con-zfc-parity-norms
- integer-norms/MOD4_PROOF.md, PROOF.md.
- integer-norms/circuits/integer16_mod4_degree112.json.
- CANDIDATES.json and integer-norms/coefficients/BINDING.json.
Mechanism: d=c^4, Q=Delta(f²-1), A=1+m(m+1)k², B0=mk, n=4n0+2, L=n+B0; norm [d(L²-A)+Q]²-4dL²Q. Retained guard makes L≠0. Rational extraction and an odd integral complementary root show omitted strong multiplier is odd; private-root sign chooses the required residue in completeness.
Caution: this distinct arrival is not a replacement copy of the first. Its direct quartic and integer20 components are outside the upstream small-norm review.

### 5. Prime-three separation16/108
Root: baseline/ConZFC_Prime_Separation_13_Integer_2026-10-23/con_zfc_prime_separation_2026-10-23
- new_integer_compression/PROOF.md and fixed3_crt_integer16.json.
- independent_audit/FOUR_ROOT_REVIEW.md.
Mechanism: squared valuations4,2,0,-2v3(H) give unique even minima. Fifth guard has valuation≥6, possibly odd; this does not break subsets containing an old root. Main carrier initially gives only2gamma integral: odd H plus Hgamma integral is needed to infer gamma integral. Explicit16-variable norm identity has53 terms and degree54 before squaring.
Current status: dominated endpoint, useful proof ingredient.

### 6. Ten-positive four-root radical/residue source
Root: baseline/con-zfc-radical-residue-2026-10-23/con-zfc-radical-residue-2026-10-23
- ten_positive/PROOF.md and INDEPENDENT_MATHEMATICAL_REVIEW.md.
- ten_positive/generated/p10_positive.json and p10_natural.json.
- ten_positive/coefficients: complete compact44 tuple.
- report.tex/report.pdf.
Mechanism: every nonempty signed radical subset is nonzero; recover index before residue separation; include noncoprime modulus case. There is no switch to unrestricted integer domain for free.

### 7. Eleven-positive adaptive double-center
Root: baseline/candidates/positive11-adaptive-shears
- PROOF.md and positive11.json.
- Upstream: baseline/ConZFC_Polynomial_Shears_2026-10-23/con_zfc_polynomial_shears/positive11/PROOF.md.
Mechanism: q²Y main carrier, shifted auxiliary root and two root centers. Removed redundant scalar-four gate improves112/211 to111/211. Complete compact44 payloads are available in the incoming polynomial-shears positive11 component and ten_positive source above.

### 8. Wave12 centered budget
Root: prior/ZFC_Diophantine_Centered_Compression
- signs/PROOF.md, normalized/BUDGET_PROOF.md.
- native/PROOF.md and centered_merge_tau_f16_degree106.json, centered_merge_three15_degree300.json.
- normalized/normalized17_degree48_dag.json.
- pell/PROOF.md and p11_positive_degree211.json.
- DEPENDENCIES.md and baseline/BASELINE_REVIEW.md.
Parent authenticated research ZIP SHA256:f68edc30d832d880785c69e2277af1efa1c9b7eca04289eb8b4e3fdf8b3b4885.
Incoming dependency ZIP contains only the prior Joint_Guards ZIP. Its exact local path:
baseline/ZFC_Diophantine_Centered_Compression_2026-10-24_Dependency/ZFC_Diophantine_Centered_Compression/incoming/ZFC_Diophantine_Joint_Guards_2026-10-24.zip
It is also extracted beside it under incoming/extracted_joint_guards. It is not the research deliverable.

### 9. Direct fixed-bound quartics
Root: baseline/candidates/shared-crt-fixed-power-bound
- PROOF.md, README.md, affine/equation.json and expanded_polynomial.json.
- retained/equation.json and expanded_polynomial.json.
- SOURCE_PINS.json, local receipts.
Mechanism: choose common positive-power bound W=n+k rather than an existential W≥n,k. Fresh canonical witnesses permit deletion of W and two bound slacks at each of55 calls. Parent beta-majorant relies on an actual four-edge uncancelled calculus path proving D² positivity; strengthened CRT lifts shared factorial prime powers before cancellation. These prerequisites must not be silently replaced by a global height assertion.

## Good next research directions from this comparison

1. Apply centered shared budget to parity15's primitive norm, retaining Q=0 handling and pre-guard Q≠1. This targets the currently strongest15-variable point rather than the already dominated prime15 form.
2. Combine modulus-four strong-root recovery with wave12 normalized centered main norm; preserve the private-root sign freedom needed for mod4 completeness.
3. Fold the nearest-square guard coordinate into a five-root norm only after proving nondegeneracy/rationality in the correct order; distinct-prime valuation and guard-first realness are alternative tools, not interchangeable assumptions.
4. Reuse43/93-op compact generic norms before evaluating any proposed multi-root improvement. Compare whole DAGs, not local norm costs.
5. Direct C222 work should start at3443/5960 fixed-bound quartics, not the older16036/27916 or3614/6183 arrivals.

## Scope caution

All reviewed small-degree native equations use the entire mixed-parity-unrounded source34 tuple (beta=2^1064921-1; shifted MF; determinant scales2^1113 and2^666104), totaling615883 raw payload bytes. Positive10/11 use the distinct compact44 tuple. Original31/H1868 high-degree norms use still another tuple. Never substitute individual ports across tuples. Existing ordinary native/compiler/Pell/calibration theorems are essential; finite identities, degree/count checks and artifact hashes are not a new end-to-end internal-ZFC or Lean proof. Lean is paused upstream.

