# Round 13: pinned source and literal comparison

Snapshot: `VladimirReshetnikov/ProveIt`, commit `7e533c33819ee1f703b69f2778a767cdc069940d`, authored 2026-10-24 03:32:10 UTC. This is a fixed review snapshot, not a claim that HEAD remains unchanged. The previous round-12 review pinned `9a33342a03d19cf5b061b2083c6b5d3f27f752ed`.

## Result and review scope

The four requested Library archives are now available locally and each matches the exact Git blob of the same `docs/incoming` ZIP at the new pin. There are also 132 authenticated current source, equation and review files under `current/Computability/DiophantineConsistency/`. Every downloaded text was checked against its literal Git blob hash. A single transport-added trailing newline was removed when, and only when, that removal reproduced the expected hash.

The authored, standalone `check_literal_artifacts.py` passes normally and under Python `-O`. It independently re-expands nine complete direct quartics from their quadratic rows and compares every integer coefficient to the supplied collected polynomial. It also checks topology, liveness and all live binary operation counts in 48 supplied DAGs. It imports or executes no upstream code. Direct exact degrees, heights, dimensions, term counts and complete variable support are independently verified. General DAG exact degrees and semantic theorems are source claims supported by the pinned ordinary review, not independently reproved here. Naive degree bounds are separately recorded and are often larger than cancellation-sensitive exact degree claims.

`LITERAL_COUNTS.json` contains the exact verified scope and all literal results. `COMPARE.json` selects the new working points. `FETCH_LEDGER.json` binds all 132 current files. `INCOMING_ARCHIVE_PINS.json` records full incoming archive SHA-256 hashes and member hashes, plus Git hashes for every entry in the pinned incoming directory. `recent_commits.json` records the recent chronology.

## Direct route: complete independently expanded quartics

All entries have exact degree four. N0 means nonnegative integers; Z means unrestricted integers.

| Construction | Domain | Variables | Quadratic rows | Collected monomials | Coefficient height |
|---|---|---:|---:|---:|---:|
| Shared certificates, arrival affine | N0 | 3614 | 2954 | 15996 | 127778545 |
| Shared certificates, arrival retained | N0 | 6183 | 5523 | 17430 | 1993 |
| Prime-power CRT lift, affine | N0 | 3609 | 2949 | 15752 | 127285349 |
| Prime-power CRT lift, retained | N0 | 6180 | 5520 | 17421 | 1992 |
| Beta-row majorant, affine | N0 | 3603 | 2943 | 15670 | 127285252 |
| Beta-row majorant, retained | N0 | 6179 | 5519 | 17417 | 1992 |
| Fixed positive-power bound, affine | N0 | **3443** | **2838** | 15754 | 127302193 |
| Fixed positive-power bound, retained | N0 | **5960** | **5355** | **16894** | **1992** |
| Prime-lift semantic-input guards | Z | **8619** | 4619 | 39811 | 127285349 |

The current 3443-variable baseline already fixes each of 55 positive-power calls at W=n+k, eliminating its free common-bound coordinate and two slacks. This is not merely max(n,k) simplification on old witnesses: the proof reconstructs fresh Pell witnesses for every common bound. Its soundness restores deleted slacks as k,n and derives A>W from the final Pell norm before interpreting the natural subtraction A−n.

The fixed-bound candidate is built from the frozen prime-lift source, not from the separate beta-majorant candidate. The 3603-variable beta-majorant affine point therefore still has fewer monomials and slightly smaller coefficient height. It is not dominated on all metrics by 3443. The 8619-integer lift is likewise frozen to prime-lift, not automatically a lift of 3443 or 3603.

The preceding prime-power CRT lift strengthens periods using their shared factorial prime powers, removes the factorial-size guard, and shrinks private bound m+U to U. Its proof handles noncoprime factorial cancellation explicitly. The beta-majorant branch replaces E+F+t by E+F only after proving the needed endpoint majorant, not by asserting that inequality globally.

## Small unrestricted-integer working points

Operations below were independently counted from literal DAGs, except the explicitly marked parity review rows. Degrees are source-declared exact degrees; this review did not rerun their degree certificates.

| Family | Z variables | Operations | Source exact degree | Comparison |
|---|---:|---:|---:|---|
| Root fusion, coprime CRT | 13 | 195 | 1088 | Current lowest-degree 13-Z point in reviewed set |
| Root fusion, centered | 13 | 186 | 1392 | Cost/degree tradeoff |
| Root fusion, uncentered | 13 | 185 | 1408 | Cost/degree tradeoff |
| Compact fixed-prime | 13 | 198 / 196 | 1392 / 1408 | Dominated by root fusion |
| Prime-separation arrival | 13 | 205 | 1392 | Dominated by root fusion |
| Compact fixed-prime | 14 | 163 / 156 / 148 | 652 / 664 / 748 | Useful new degree/cost tradeoffs |
| Root fusion | 14 | 150 / 137 | 696 / 792 | Useful degree/cost tradeoffs |
| Compact fixed-prime control | 14 | 150 | 700 | Dominated by 150/696 |
| Prime-separation arrival | 14 | 151 | 696 | Dominated by 150/696 |
| Root fusion | 15 | 131 | 344 | Dominated by parity 128/204 |
| Prime-separation arrival | 15 | 137 | 244 | Dominated by parity 128/204 |
| Parity, pinned review only | 15 | 128 / 124 | 204 / 352 | Literal artifacts not recounted here |
| Parity, pinned review only | 16 | 119 / 115 | 112 / 160 | Literal artifacts not recounted here |
| Prime separation | 16 | 132 | 108 | Lower degree, 13 more operations than parity119/112 |
| Root-fusion quotient companion | 17 | 110 | 88 | Four fewer operations than older114/88 |
| Root-fusion quotient companions | 18 / 19 / 20 | 112 / 116 / 120 | 32 / 28 / 24 | Distinct variable/degree tradeoffs |

The compact fixed-prime evaluator replaces four-root and five-root Taylor forms by 43- and 93-operation local evaluators, saving 67 and 277 operations respectively. Those are already in the pin, not new round-13 achievements. Fourteen-variable costs163/156/148 must be compared to the complete current circuits, not the incoming230/223/215 headlines.

The root-fusion 17/88/110 quotient companion uses fresh canonical squared-modulus witnesses. It preserves calibrated existence, not the old free polynomial's entire zero set. A composition must respect this distinction.

## Ten-integer shears

| Literal family | Linear operations/degree | Cubic operations/degree | Six-term operations/degree |
|---|---|---|---|
| Polynomial-shears arrival | 484 / 1179788 | 487 / 1114252 | 521 / 1081125 |
| Current short-guard composition | **475 / 1179788** | **478 / 1114252** | **512 / 1080888** |

The current baseline without those shears is471 operations at degree1245324 according to its pinned proof/review. The arrival's local 481-operation improvements are not the latest complete baseline. Current sources and proof contracts are under `current/Computability/DiophantineConsistency/candidates/short-guard-shears/`.

The broader positive-domain frontier in `PROPOSAL_REVIEW_LATEST.md` includes9-positive433/1628768,722/1158228,953/999518;10-positive131/1152;11-positive111/211. These are pinned upstream review claims, not recounted in this focused review. They must not be conflated with unrestricted-integer counts. The old manuscript-collection README still describes wave10 and is not the current frontier.

## Source contracts for the next auditors

### Direct route

Current full baseline: `current/Computability/DiophantineConsistency/candidates/shared-crt-fixed-power-bound/`, with `source/build_equation.py`, `source/direct_calculus.py`, `source/affine_shared_step.json`, `source/wire_eliminated_source.json`, `affine/equation.json`, `affine/expanded_polynomial.json`, retained counterparts and `PROOF.md`. Sibling directories `shared-crt-prime-lift` and `shared-crt-beta-majorant` provide the separate ordinary proofs and full literal predecessors.

Inherited direct proof root: `library_sources/ConZFC_Shared_Certificates_2026-10-24/con_zfc_shared_certificates/`. Read `report/calculus.tex`, `report/primitives.tex`, `report/crt.tex`, `direct/shared_crt_audit.md` and `PROVENANCE.md`. The `direct/provenance/` files retain actual `Code254.lean`, `KCode222.lean`, `KEndpoint.lean`, `ConstructibleChoice.lean`, `Bridge.lean`, Pell/power/factorial and bounded-forall interfaces. The named calibration is `c222_iff_zf_refutation`, then `zf_refutation_iff_zfc_refutation`, with ConZFC defined by the chosen ZFCax_s proof predicate. This route does not use K215, Jones or native fixed-coefficient tuples. The complete new internal-ZFC derivation remains open; ordinary proof and finite exact verification are distinct.

### Five-radical/CRT route

Root: `library_sources/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/`. Principal sources: `report/report.tex`, `report/crt1088.tex`, `build_equations.py`, `five_square_norm.py`, `equations/norm13_crt_degree1088.json`. Proof contracts: `provenance/CALIBRATION_STATUS.md`, `FORMALIZATION_BOUNDARY.md`, `NORMALIZED_NORMS_PROOF.md`, `SQUARED_MODULUS_PROOF.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, and `upstream_ordinary/`. The pinned external assessment is `current/Computability/DiophantineConsistency/PROPOSAL_REVIEW_ROOT_FUSION13.md`.

Critical proof order: unconditional realness of four radicands; norm zero forces the guard radicand nonnegative; guard supplies strict sign/nonzero bounds; every nonempty signed subset of nonzero roots has nonzero sum; only then the multiquadratic automorphism argument makes all roots rational. Mere separation of the total sum is insufficient, and dependent squareclasses are permitted. Rational auxiliary-root integrality requires adjacent-coefficient Pell descent, not merely an integer-looking norm. CRT1088 initially permits v=0, but the scaled guard forces v nonzero before division. The two recovered residues use gcd(H,2q²)=1 and Lambda=1 modH, not the generally false gcd(H,q−1)=1.

The coherent tuple is `mixed-parity-unrounded-1064921`: beta=2^1064921−1, K0, MC, MF already shifted, and cone_A=2^1113, cone_B=2^666104. All six supplied raw payloads total615883 bytes. Do not substitute compact36, compact44, H2082 or a twice-shifted MF. The unbounded native/refutation correspondence is inherited ordinary mathematics, not established by finite payload reconstruction.

### Prime separation and compact norms

Prime-separation root: `library_sources/ConZFC_Prime_Separation_13_Integer_2026-10-23/con_zfc_prime_separation_2026-10-23/`. Use `report.tex`, `new_integer_compact/`, `new_integer_compression/DEGREE_LOWER_CERTIFICATES.json`, and the pinned `PROPOSAL_REVIEW_PRIME_SEPARATION.md`. The fifth guard need not have even3-adic valuation: every subset containing an old root has a unique even minimum, while a singleton nonzero guard cannot cancel. Keep the midpoint-integrality argument for the main quotient and establish Q>1 before auxiliary descent.

Compact generic norm source: `current/Computability/DiophantineConsistency/candidates/fixed-prime-compact-norms/compact_norms.py`, `PROOF.md`, `build.py`, literal `integer*_compact.json`, and `parent/forms/DEGREE_PROOF.md`. These are exact whole-polynomial evaluator rewrites, unlike witness-reselection transformations.

## No overclaim

This focused review does not prove consistency, assert a global optimum, recompile Lean, or reproduce every upstream release run. It verifies literal finite properties of the selected frozen artifacts and supplies precise local source contracts. New round-13 constructions must be compared against this pin, preserve their stated domain and source tuple, and separately prove every unbounded reconstruction step.
