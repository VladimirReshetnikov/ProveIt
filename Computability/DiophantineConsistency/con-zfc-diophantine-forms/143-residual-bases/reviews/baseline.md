# Round 18 baseline audit — read-only, 25 October 2026

## Decision-useful findings

1. **The accepted compact baseline is newer than the collection frontier.** Root review explicitly accepts ten-positive `(operations, degree)` points **(83,436), (84,328), (80,750), (81,560)**. The maintained page is a different objective: **15 positive / 66 operations / degree157 on radix55**; the old ten-positive85/328 page is preserved, not current. Unshifted `T`, q-cube normalization, absorbed padding, and product-square extraction are therefore predecessors, not new Round 18 discoveries.
2. **Incoming Certificate Reductions raises the provisional compact bar to (78,630), (79,468).** Its new mechanism is staged first-index/denominator recovery, removing `mu=q²+1`; its literal carrier still uses **D=Y²**, `V0=XD`. The proposed Round 18 replacement D=XY or D=q⁴ was not found in the bounded inspection described below.
3. **Cofinal Anchors makes the old Odd Helpers direct headline obsolete as a Pareto claim.** Its `(Z,287,4,197,4313,128446)` point dominates all three Odd Helpers direct points in variables, residuals, collected support and height. Its 282-variable point also dominates the accepted 327-variable quartic and the other incoming principal integer quartics. **It does not dominate the newer accepted V R1 plain/weighted endpoints, whose height is15109 rather than128446.** See the late-source reconciliation below; the old latest-review overview is not authoritative for current display or complete accepted direct frontier.
4. **Odd Helpers' 13-integer degree-156/127-operation and 14-integer degree-88/119-operation points remain the pertinent incoming root-compression baselines.** None of the other five current packages supplies a competing 13- or 14-integer root-compression endpoint. Its eleven-integer 648/115 remains a cost/degree tradeoff, not superseded merely by Cofinal's lower-degree/higher-cost eleven-integer family.
5. **No residual-row lattice/LLL/basis-optimization overlap was found in the inspected prose.** Incoming direct improvements change arithmetic/sign/anchor semantics, eliminate coordinates, and translate coordinates. Existing references to unimodularity concern coordinates, Pell descent or graph flows, not replacing the SOS residual basis. This is a bounded source-inspection conclusion, not a literature-wide novelty result.

## Snapshot, status and conventions

- Checkout: `round18/upstream`, exact HEAD **e0c98c629bf10d30b695884f6b1d2ab361bdf513**.
- Research root below: `U = round18/upstream/Computability/DiophantineConsistency`.
- Incoming root below: `I = round18/intake`; `CA`, `SS`, `CR`, `GD`, `OH`, `LC` abbreviate the six directories listed in the checksum ledger.
- The six ZIPs are still under `docs/incoming/`. Its README explicitly says incoming archives are not repository research material until placed and written into a report. **Placement itself is not mathematical adoption.** Waves 5–14/sources 31–133 are placed; source 131's 324-variable claim is still distinguished from the root-accepted 327-variable equation in active research.
- Direct tuple convention: **(domain, variables, degree, residuals, collected monomials, coefficient height)**. Graph tuples omit residuals because their defining polynomial is not presented as the corresponding direct SOS. Circuit tuple: **(domain, variables, degree, live binary operations)**. Domains `N`, `Z`, `+` mean nonnegative, unrestricted and strictly positive integers.
- Circuit support/expanded height are **unmeasured, not zero**. The positive four-port tuple's largest port is 592,884 bits; this is not expanded coefficient height. Signed source34 circuits use a different coherent six-port tuple (615,883 uncompressed bytes in OH's root family). Never splice these tuples.
- This audit read source/proof/metric text and computed SHA-256 digests with the system utility. **No supplied Python, shell build, checker or proof compiler was executed.** Recorded verification receipts remain author/reviewer claims, not fresh replay results from this audit.

## Accepted active-research endpoints versus placed claims

| Status | Endpoint | Full measured tuple / literal location |
|---|---|---|
| Explicit root acceptance | Unshifted V² | `(+,10,436,83)`; `U/research/ten-positive-unshift-t-finite/data/equation_unsheared_V2.json` |
| Explicit root acceptance | Unshifted bV | `(+,10,328,84)`; same directory, `equation_unsheared_bV.json` |
| Explicit root acceptance | Unshifted q-cube V² | `(+,10,750,80)`; same directory, `equation_qcube_V2.json` |
| Explicit root acceptance | Unshifted q-cube bV | `(+,10,560,81)`; same directory, `equation_qcube_bV.json` |
| Explicit root acceptance | Fused-nine direct quartic | `(Z,327,4,216,5718,128446)`; `U/research/signed-pell-cap-nine-factor-projections/data/centered/equation.json` |
| Explicit root acceptance; newer V R1 | Plain direct quartic | `(Z,316,4,218,5614,15109)`; `U/research/second-pair-sum-gate-shear-r1-verification/data/plain/equation.json` |
| Explicit root acceptance; newer V R1 | Weighted direct quartic | `(Z,315,4,217,5620,15109)`; same parent directory, `data/weighted/equation.json` |
| Placed source 131; adoption separate | Principal / sparse direct quartics | `(Z,324,4,208,5808,128446)` / `(Z,338,4,222,4493,128446)` |
| Placed source 129 | Principal / sparse natural quartics | `(N,233,4,182,50762,88674690)` / `(N,234,4,183,9019,87741134)` |
| Placed source 127 | Height-one graph | `(Z,2215,4,30468,1)`, constant 1 |
| Placed source 116 | Root-norm comparisons | `(Z,13,274,129)` and `(Z,14,108,119)` |

Acceptance evidence: `U/reviews/ten-positive-unshift-t-finite-root-peer.md` explicitly says all four are accepted, describes both proof and full replay boundaries, and retains the old page. `U/reviews/signed-pell-cap-nine-factor-projections-root-peer.md` and the latest review's “Complete fused-nine quartic reaches327 integer variables” establish the direct accepted endpoint. The subsequent Round16 review explicitly leaves source 131's representative-sum/compressed-sign dependency obligation distinct.

The placed positive10 frontier also retains `(ops,degree)` **89/288, 91/283, 92/278, 94/262, 96/258, 97/254, 102/253, 104/252, 121/246**. These lower-degree tradeoffs must not be dropped when advertising a 77–79-operation high-degree result. Placed eleven-integer points include degree/ops **924/109, 840/110, 810/112, 654/117, 488/118, 464/119, 428/123, 416/125, 376/127, 364/131, 352/132**.

## Incoming direct quartics — all degree four

All paths are relative to the corresponding incoming package; each `equation.json` has an adjacent complete `expanded_polynomial.json`.

| Package / chart | Domain | Variables | Rows | Monomials | Height | Equation directory |
|---|---|---:|---:|---:|---:|---|
| CA dimension | Z | 282 | 192 | 5491 | 128446 | `direct/strict_dimension_centered` |
| CA grouped | Z | 287 | 197 | 4313 | 128446 | `direct/strict_grouped_centered` |
| CA sparse | Z | 309 | 219 | 3922 | 128446 | `direct/strict_sparse_centered` |
| CA natural | N | 229 | 179 | 9184 | 83954634 | `architecture/strict_natural229/natural` |
| CA sparse natural | N | 230 | 180 | 6858 | 83954472 | `architecture/strict_natural230/natural` |
| CA high-height projection | N | 228 | 178 | 9866 | 2445412949744 | `architecture/strict_natural228/natural` |
| SS principal | Z | 286 | 196 | 6607 | 128446 | `integer286/principal/centered` |
| SS companion | Z | 319 | 207 | 5779 | 128446 | `integer286/generated/centered` |
| SS natural | N | 235 | 184 | 22185 | 90911633 | `natural235/equations/natural235` |
| SS sparse natural | N | 236 | 185 | 15645 | 88233865 | `natural235/equations/natural236_sparse` |
| CR integer | Z | 314 | 204 | 5721 | 128446 | `direct` |
| CR natural | N | 233 | 182 | 7313 | 86543666 | `natural` |
| GD natural | N | 226 | 175 | 10314 | 87839583 | `direct/equations/natural226` |
| GD sparse natural | N | 227 | 176 | 7905 | 87839583 | `direct/equations/natural227` |
| LC principal | Z | 306 | 206 | 6259 | 128446 | `direct/integer306` |
| OH minimum | Z | 307 | 211 | 22532 | 394412 | `direct/centered307` |
| OH balanced | Z | 308 | 212 | 5364 | 195962 | `direct/centered308` |
| OH low-height | Z | 310 | 214 | 5612 | 128446 | `direct/centered310` |

**Strong comparisons:** CA282 dominates SS286/319, CR314, LC306 and accepted327; CA287 dominates placed338 and all OH direct headlines. CA309 is a real smaller-support tradeoff, with more rows than CA282/287. GD227 dominates CA228 (fewer variables, rows, terms and smaller height), while GD226/227 versus CA229/230 retain support/height tradeoffs. CA230 dominates CR233 and both SS natural endpoints, but does not dominate GD227 because it has more variables/rows. Preserve older natural low-height/support objectives, e.g. placed source133 `(N,255,4,203,5743,64214623)` and source128 `(N,242,4,190,9308,18049118)`.

## Incoming compact/root and height-one points

| Package | Domain / variables | Exact degree / operations | Literal path(s) |
|---|---|---|---|
| CR | + / 10 | **630/78, 468/79** | `compact/equation78.json`, `equation79.json` |
| SS | + / 10 | 436/83, 560/81, 750/80 | `positive10/equation_83_436.json`, `_81_560.json`, `_80_750.json` |
| GD | + / 10 | **323/87, 318/88** | `compact/equation_87_degree323.json`, `equation_88_degree318.json` |
| OH | + / 10 | 750/81, 560/82 | `positive/equation_81.json`, `equation_82.json` |
| SS | Z / 11 | **924/107, 840/108** | `integer11/parity_saturated11_native.json`, `_short.json` |
| CA | Z / 11 | **328/130, 340/129, 352/125, 398/121** | `scalar/free_cofactor11_sharp.json`, `_simple.json`, `_none.json`, `weak_cofactor11_none.json` |
| OH | Z / 11 | **648/115** | `integer/weak_product11_none.json` |
| OH | Z / 13 | **156/127** | `lowdegree/thirteen/equation.json` |
| OH | Z / 14 | **88/119** | `lowdegree/equation.json` |

CR79/468 dominates both OH positive points and SS80/750, SS81/560. SS83/436 and accepted84/328 retain lower-degree tradeoffs. GD87/323 and88/318 also survive as lower-degree points between accepted84/328 and89/288. Proposed Round18 77/626 and78/464 would improve both metrics against CR78/630 and79/468 respectively, **conditional on completed ordinary proofs, literal graphs and exact degree/cost checks**.

All following graph points have domain Z, degree four, height one, constant one, and permit individual fourth powers:

| Package | Variables / monomials | Literal polynomial path |
|---|---|---|
| CA | **793/51982, 806/23719, 994/11744** | `height_one/endpoints/{compact793,balanced806,sparse994}/polynomial.json` |
| GD | 951/56916, 984/30076, 1050/21766 | `graph/equations/{unit951,unit984,unit1050}/polynomial.json` |
| GD matched source442 | **1137/23105** | `graph/equations/matched1137/polynomial.json` |
| LC | 985/95609, 1122/25922; matched442 1252/27738 | `graph/{principal985,sparse1122,matched1252}/polynomial.json` |

CA793 dominates GD951 and LC985; CA806 dominates GD984; CA994 dominates GD1050, GD1137, LC1122 and LC1252. **Compiler-only comparisons must hold the source fixed:** GD's source442 matched1137/23105 beats CA's recorded matched1254/27714 and LC's1252/27738. CA's stronger final graph endpoints additionally use better direct sources (287/309) and affine refactorization; do not attribute all improvement to its graph compiler.

## Mathematical dependency and novelty boundaries

- **Direct C222 lineage:** ordinary arithmetic transformation → numerical C222 derivation → `KEndpoint.c222_iff_zf_refutation` → `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. No K215, Jones, Sun or enormous fixed tuple is used. CA's `CLOSURE_MAP.md` identifies full active proofs: semantic one-row anchor, orientation-first signed bootstrap, strict `K=x` budget, inherited factorial/CRT/radix semantics and restoration. SS already recovers signs from integral encoded powers, handles zero/negative index cases, uses even frame/odd anchor and sharpens the cofinal modulus. CR adds the polynomial comparison center `A+(1-A)H²` and descending-binomial factorial fixed point. LC uses linear trace-orientation defects in an existing bounded residue pool. These are not residual-basis changes.
- **Positive compact lineage:** fixed indexed BFS943 native/K215/compiler/refutation calibration. Accepted unshifted-T proofs already supply the absolute-value transport and positive completeness; an algebraic `T-alpha` substitution alone does not preserve the positive domain. CR's new staged denominator proof recovers roots and rank first, obtains `q⁶ | e` from `Y² | hHe` without false `gcd(Y,h)=1`, bounds the first index to force equality, and only then recovers full `Y² | e`. D=XY/D=q⁴ changes must reprove this chronology, all denominator bounds, positive witnesses, and exact degrees—not just substitute in the graph.
- **Signed root lineage:** OH's 13-variable polynomial uses source34's full six-number calibration, positive strong/weak radicands before guard extraction, and common-squareclass coefficient valuations **1,2,4** to exclude cancellation. It eliminates strong root `f` and triangular coordinate `p3`; maps `n_new=n_old+(2p3+1)+4f`. The unit-product finalizer relies on `N` being a square modulo four, excluding N=-2. Any further compression must preserve every sign/denominator case and old-zero maps. CA's cofactor11 work is a separate signed interpolation/carrier route, not a new thirteen-variable root norm.
- **Residual-basis opportunity:** an invertible rational or integer linear transformation of a real residual vector preserves its simultaneous zero set, but usually changes its sum-of-squares polynomial. A new quartic should authenticate its full exact transformation/inverse (or rank certificate), collect all coefficients anew, and disclose metrics for that new polynomial. Non-unimodular rational changes may require denominator clearing, affecting height. None of these steps establishes global optimality.
- **Proof scope:** all packages claim ordinary unbounded proofs formalizable in ZFC, composed with named inherited calibration. Finite algebra checks authenticate equations, coefficients, restorations and gates; they do not prove Con(ZFC), decide zero existence, or create a fresh end-to-end Lean/Rocq/object-ZFC proof. “Independent” package reviews are separate agents within the AI-assisted workflow, not outside peer review.

## Source identity ledger

Full local paths are `round18/intake/<directory>` and archive paths are `round18/upstream/docs/incoming/<archive>`. The short names used above expand as follows; each archive SHA-256 was freshly measured:

| Key | Directory / archive stem | Archive SHA-256 |
|---|---|---|
| CA | `ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25` | `1efcb1831b7b57f34385e4171923dd801573b74b4529346b9d153246cd0294e6` |
| SS | `ConZFC_Semantic_Signs_2026-10-24` | `422f84d2733c78121a48a52d3eaee5052647ddfd3641680a14b205406f20b0c9` |
| CR | `ConZFC_Certificate_Reductions_2026-10-25` | `a647b011ffdbc7e3626aa4daf35feb678c2ffa766067edc0d586ef846600b2a1` |
| GD | `conzfc_graph_digits_2026-10-24` | `79151e5694a8cde3661091fbfabc9d8f95f6d13c250a8c6b6e244e60ceb7858a` |
| OH | `ConZFC_Odd_Helpers_Saturated_Carriers` (ZIP adds `_2026-10-25`) | `af8d00306937c8e5f678efd09f11ed97eb1087b3cc972294dbfed58098ecd8d5` |
| LC | `ConZFC_Local_Certificates_2026-10-24` | `40ee7b02195837107a68b7312b742cf6f14aedb50ac5b8bfe4ffbac5e3252a9e` |

Authoritative metric/index files, freshly measured SHA-256:

```text
U/PROPOSAL_REVIEW_LATEST.md
 f1446c558b0664ed44fbf9caaa4108e22897037f101f123266da5397ff76cab7
U/con-zfc-diophantine-forms/README.md
 fcf82fa57c01507362ecf806a471f50d72214862cef47a5619e4a5b589c56770
CA/ENDPOINTS.json
 870097efb3f747ef5f9b5d4c7870fea05ea63ec3579c3591e4930c31599d6a5c
SS/ENDPOINTS.json
 6e62c7f5d1a8687498ca5441ddcf545455bc9580006ca9c3efa1a978712935db
CR/METRICS.json
 dc965a676d33fcfa1c2fe952e3a8775d7b0d8d45357cd4cf7f0c1e4439216b38
GD/RESULTS.json
 0a61822317c83950711fd5e4bd61690f9eefa64c8317bc1c467f088870166d4d
OH/RESULTS.json
 48354fdf7d7bc730c246f94e5d894f14bba72aa1bf254eaf388203d8a2c7322e
LC/EQUATION_IDENTITIES.json
 cf5e860be2c8dc380aadb7493761f28297d3adace85b8642107894ad75920f92
```

CA/SS endpoint catalogs bind every selected equation/polynomial with full SHA-256; OH RESULTS binds each selected equation. Selected additional literal identities freshly measured here:

```text
accepted327 equation: d01d259727d2bb89cc6b9390da32ad2f5f4af4a72223f880a9a7faa161d87fe4
accepted327 polynomial: 2a7d11287dfe04e3bd0e1c4e152014b9cc9df85b39b2f1c2a39b7f023d06701c
CR/compact/equation78.json: f34d0a8e7f2aa953f960e42714747f8aa8e25fe8f565a6cf1ecad588a5ce1e80
CR/compact/equation79.json: fdd63f2769214cb53c312b60c8831c135e7daba4b2feef74507b7625adcc29f8
CR/direct/equation.json: a36f15ae645d6e79f51ba6d8628effc141b4a7957a3c47d0864dd3e6d2711e67
CR/natural/equation.json: 2075ea1cc4bdaf09a00a5610512234f9599029dd9bd80493c50dcaa066025368
GD/direct/equations/natural226/equation.json: b212e401c60e61392014a7a94070a7b08494f8295d17170442d82652808c15df
GD/direct/equations/natural227/equation.json: d445798990c26a37ea7eb4406c80690d23947632ee39970059fe686c398d9218
```

No access denial or authorization blocker occurred. The one `find | head` pipeline emitted its expected broken-pipe diagnostic after the requested output limit; no supplied code was launched.

## Late-source reconciliation, independently checked at 20:47 UTC

The parent's heartbeat notification identified a newer public placement. Its `/agent_notes/.../20-43-40Z.md` file was absent in this executor, but the named commit object and exact repository acceptance records were directly readable. I inspected them without checking out another commit, changing HEAD, replacing pinned inputs, or running their programs. This also exposed stale summary-page statements already present at the original pin; the corrections above use explicit decisions, not the overview.

- **V R1 is accepted**, not merely a held source. `U/reviews/second-pair-sum-gate-shear-r1-finite-endpoint-acceptance.json` says `ACCEPT_EXACT_R1_FINITE_ENDPOINT` and binds both full profiles: plain `(Z,316,4,218,5614,15109)` and weighted `(Z,315,4,217,5620,15109)`, residual height 72. Its SHA-256 is `382d802d8c6dd570270db1fe2bbcc1473faad42fec78e1a9f199fa4cdbc6a1a1`. The source-folder README deliberately preserves its earlier HOLD state; do not mistake it for the later decision. The corrected coordinate-25 shear preserves the failed original and wrong-minus-24 history. This is still a **coordinate** shear, not an optimized residual basis. The lower height makes it a genuine tradeoff against incoming CA282/287/309.
- **Radix53 is an accepted finite checkpoint, not the maintained display.** `U/reviews/compact66-radix53-page-finite-endpoint-acceptance.json` says `ACCEPT_REVIEWED_RADIX53_CHECKPOINT_KEEP_RADIX55_MAINTAINED`. Full tuple `(+,15,157,66)` with 38 products/15 sums/13 differences; four raw ports total 233666 bytes, largest 468998 bits. The page has 2770 nonwhite characters versus maintained radix55's 2764, despite fewer raw bytes (242484→233666). `U/CURRENT_EQUATION.json` explicitly retains `candidates/one-page-compact66-radix55`, 15+/66/157. The decision SHA-256 is `6ffd48634d2cb6f1be7f71bb0be140d8cf6d306140103b02e1fb90538c882c8f`. These are coherent **different tuples/specialized polynomials**; none authorizes substituting isolated radix53 ports into this iteration's BFS943 compact10 circuits.
- **Placement changed, not mathematical acceptance.** Commit **1eed4b48cd34bc1896466395c4efd337db0c4b58**, dated 2026-10-25T20:43:04Z, places the six original e0c98c6 archives as sources **134 certificate-reductions, 135 cofinal-anchors-round17, 136 local-certificates, 137 odd-helpers-saturated-carriers, 138 semantic-signs, 139 graph-digits**. It records 3468 members = 1258 staged + 2205 copies omitted + 5 ignored, retires the six ZIPs, and explicitly says “Nothing was edited and nothing was run”; reconciliation/catalogue follow. Thus the baseline's incoming label is correct **at the frozen pin**, and the same six claims are newly placed but still not independently mathematically adopted by this placement. Their literal input bytes and this task's dependency pin remain unchanged.
