# Round 19 read-only comparison baseline

Snapshot: ProveIt `3ecd6a6cf53d47519228328567f45fb7ee9781d9`, inspected 25 October 2026. All paths below are relative to `/workspace/scratch/416780682817/round19/`. This comparison concerns the seven other latest incoming packages; the author's own `Residual_Bases_Denominator_Engineering` remains a separately attributed predecessor, not a new result.

## Evidence and status

- `baseline_recollect.py` is a new independent, standard-library-only, read-only census. It imports no incoming code. `baseline_metrics.json` records full paths and SHA256s for all checked literal equations and expansions: **8 archive/extraction byte bindings, 51 exact sum-of-squares expansions, 4 height-one literal coefficient censuses, 38 supplied live arithmetic DAG censuses** (including retained controls/parents). Quartic degree/terms/height and circuit operation counts are independently recollected. Circuit exact degrees are **source-proof/receipt claims**, not re-established by this census.
- `baseline_radix47.py` independently reconstructs all 3297 Phi coefficients from the literal 943-tile table, all four entire radix47 coefficient integers, mask populations/boxes, the numeric carry inequalities, prime/exact-order/unit/lift facts. All pass; receipt `baseline_radix47.json`. This does not independently regenerate the tile decoder, replay all 51 native geometry identities, or constitute an unbounded proof.
- The seven packages supply literal artifacts, ordinary new proofs, retained calibration boundaries and finite receipts, rather than merely plans. Main new proof mechanisms were read. Their ordinary theorem remains dependent on the named inherited C222/refutation or native/Pell/refutation calibration. No new end-to-end Lean/Rocq proof, consistency assertion, global minimum, or external human review is established here.
- **Incoming placement is not repository acceptance.** At this exact checkout, the maintained page is coherent radix55: 15 positive variables / 66 operations / degree157 / 242,484 raw coefficient bytes. The separately accepted radix53 checkpoint has 233,666 bytes but is not promoted. README still describes whole radix49 acceptance as pending. Incoming Common supplies completed radix49 and radix47 independently; label them incoming completed candidates, not the maintained page.

## Package aliases

`C` = `intake/ConZFC_Centered_Residues_2026-10-25/`  
`P` = `intake/ConZFC_Coprime_Products_and_Positive_Centers_2026-10-25/`  
`S` = `intake/ConZFC_Shared_Certificates_Round18_2026-10-25/`  
`B` = `intake/ConZFC_Shared_Residue_Bounds_2026-10-25/`  
`R` = `intake/ConZFC_Symmetric_Remainders_2026-10-25/`  
`Y` = `intake/ConZFC_Symmetric_Residue_Budgets_2026-10-25/`  
`M` = `intake/conzfc_common_remainders_20261025/`.

## Literal direct quartic comparison

All entries below are unrestricted integers, exact degree4, and newly recollected from every residual square. Columns are `(variables, quadratic residuals, collected terms, coefficient height)`; paths append `/equation.json`.

| Source and directory | Exact tuple |
|---|---:|
| M `direct/equation` | **(252,182,5340,128446)** |
| Y `equations/P258` | **(258,186,5319,47281)** |
| Y `equations/P261` | (261,185,5332,47281) |
| C `arithmetic/signed258` | (258,186,5366,128446) |
| C `arithmetic/signed259` | (259,185,5361,128446) |
| S `signed/sphere_dimension_centered_merged_odd` | (258,186,5364,128446) |
| S `signed/sphere_dimension_centered_odd` | (259,185,5356,128446) |
| S `signed/sphere_grouped_centered_merged_odd` | **(263,191,4141,128446)** |
| S `signed/sphere_grouped_centered_odd` | (264,190,4135,128446) |
| S `signed/sphere_sparse_centered_merged_odd` | **(285,213,3750,128446)** |
| S `signed/sphere_sparse_centered_odd` | (286,212,3744,128446) |
| B `equations/principal` | **(260,186,4770,9191)** |
| B `certificate/merged_cap32_centered` | (259,185,23960,240653) |
| R `direct/equations/symmetric_caps` | **(260,185,5099,128446)** |
| R `direct/equations/dimension259` | (259,184,21287,240653) |

The own round18 278-variable record is obsolete as a *dimension* comparator; use M252. Its 279/189/5483/7200 lower-height tradeoff remains distinct from B260/H9191, and the smaller-support 284/194/4270/H10864 also remains a tradeoff. No total ordering is justified. Several 258-variable competitors are dominated by Y on these four metrics, while M252 buys smaller dimension with greater height than Y/B.

### Natural-domain quartics

These variables range over **N including zero**, not all Z. Same four-column tuple, degree4, independently recollected:

| Source/directory (`equation.json`) | Exact tuple |
|---|---:|
| P `natural/equations/natural221` | **(221,172,9536,83954186)** |
| P `natural/equations/natural222` | **(222,173,6821,83954028)** |
| C `arithmetic/natural221_high` | (221,171,10216,2445412949744) |
| C `arithmetic/natural222` | (222,172,9522,83954186) |
| C `arithmetic/natural223_sparse` | (223,173,6858,83953724) |
| S `natural/endpoints/natural221/natural` | (221,171,13935,118464197) |
| S `natural/endpoints/natural222/natural` | (222,172,9917,83954634) |
| S `natural/endpoints/natural223/natural` | (223,173,7202,83954472) |
| S `natural/endpoints/natural224_sparse/natural` | (224,174,6527,83953869) |

Thus 228 natural variables is no longer an adequate current dimension benchmark. Keep residual count, support and height explicit: C221 saves a row but has enormous height; P221 is the stronger balanced 221-variable baseline. S221 is another 171-row alternative with far smaller height than C221 but more support.

### Height one

S `height_one/endpoints/{compact571,balanced593,sparse646,sparser742}/polynomial.json` gives `(variables,terms)=(571,19833),(593,12027),(646,8368),(742,7226)`, all exact degree4, constant1 and coefficient height1. Full literal coefficient metrics were independently checked, but this census did not replay their graph/lift certificates. Their ordinary proof is `S/height_one/proof.tex`: signed row orientations, opposite-occurrence fusion, constructor sharing and exact incidence energy. Do not call these simple SOS residual-count records; the polynomial is a half-incidence energy plus equality/unit penalties.

## Few-variable literal circuits

Every operation/witness count below was independently checked for topological validity and liveness; exact degrees are supported by the supplied ordinary degree proofs/receipts. Inputs are strictly positive unless marked Z. All coefficient ports are fixed, supplied integers, not unknowns.

| Path | Variables | Operations / exact degree |
|---|---:|---:|
| C `compact/equation_XY_V2.json` | 10 | **75 / 626** |
| C `compact/equation_XY_bV.json` | 10 | **76 / 464** |
| C `compact/equation_q4_bV.json` | 10 | **77 / 460** |
| P `compact_xy/equation_80_382_partial.json` | 10 | **80 / 382** |
| P `products/equation_14_raw.json` | 14 | **70 / 189** |
| P `products/equation_14_reduced.json` | 14 | **71 / 157** |
| P `products/equation_13_anchored.json` | 13 | **72 / 433** |
| S `scalar/free_whole_center11_c316.json` | 11 Z | **133 / 316** |
| S `scalar/free_whole_center11_c308.json` | 11 Z | **140 / 308** |
| S `scalar/free_whole_center11_c304.json` | 11 Z | **144 / 304** |
| S `scalar/free_whole_center11_c300.json` | 11 Z | **148 / 300** |
| M `radix47/radix47/polynomial.json` | 15 | **66 / 157** |
| M `radix49/radix49/polynomial.json` | 15 | **66 / 157** |

C improves the own round18 matched ten-positive circuits by two operations. The maintained 15-positive66/157 is still cheaper than 13/14-positive products. Lower-degree ten-positive forms (e.g. maintained84/328,89/288,96/258 and97/254) and nine-positive forms remain other tradeoffs. Never compare the eleven-Z source34 six-port tuple with the four-port indexed943 tuple as if it were one specialization.

## What is mathematically new in these seven packages

1. **M common normalization:** replace every `U_i=L_i Q_i+r_i` by `v_i U_i=M Q_i+R_i`, with `L_i v_i=M=q^x`. Divisibility recovers integral `r_i=R_i/v_i`. One centered norm bounds all eleven normalized residues; genuine low tails are `<L_i/32`. Three ratio coordinates and three norm witnesses replace33 private sign witnesses, and sharing four old `Nq^k` products as `NM` removes3 more coordinates: net30, giving252. The factorial low tail is bounded *before* identifying `F=t!`.
2. **Y/C/S/B centered budgets:** small canonical low residues plus congruence and a symmetric norm recover signs. Y/C use factor4 (radius below1/2); S/B use factor2 with a `<3/4` radius and `<1/8` canonical margin. Adjacent q-power groups share one certificate at the cost of2 quadratic wires. C/Y/S additionally use an odd-square radix and an acyclic bootstrap, with compatible even-x/odd-H CRT choices. Y's30 reversible residual-row operations reduce height; B's76 invertible coordinate shears reduce height and support.
3. **R deterministic center and orientation:** `D=A+(1-A)H^2`, but only modulus C (not4C) is needed. It handles the exceptional unit ordinate explicitly; nine selectively oriented abscissas suffice because true positive power requests orient the remaining five. This is more than the shared-radius substitution and may compose with it, but must retain its separate exceptional-index proof.
4. **P positive center:** natural-domain `C=A+(4y+1-A)u^2`, with auxiliary ordinate `v=2y^2(e+1)`, restores the old two center congruences and nonnegative quotients. It composes with four natural remainder pools and a derived output bound. This is not the signed negative-center theorem silently reused on N.
5. **S other branches:** natural weighted three-pool/output-bound absorption; height-one opposite-occurrence fusion; eleven-Z even radical weights and integral polynomial center shears reduce exact degree to300. The scalar proof gives explicit projected-zero-set maps, addresses zero/sign cases and keeps the old supported-modulus interpolation fixed.
6. **Compact arithmetic:** C's `XY`/`kY` sharing gives the75/626 endpoint. Smaller denominators first recover a q-power congruence and the bounded Pell index, then full denominator divisibility. P's coprime-product construction recovers one square before excluding the bad Pell-unit sign, and obtains two roots from a single product square. These are distinct from a new logical encoding.
7. **M radix47 is genuinely a new coherent encoding:** complement horizontal8-bit/vertical9-bit labels bijectively, share seven marker weights2^44, reduce predecode carry29 then decoded carry12, prove local predecessor resets, supply new padding and a fresh actual-rank controller. All four ports change together. Its raw tuple207214 bytes beats completed49's216030, verified53's233666 and maintained55's242484; this is storage, not an established shorter printed-page record.

## Recommended comparison and research boundaries

- Start new integer direct work at M252, not own278. The compatible odd-square change is an immediately plausible composition (not already emitted in M); the four new affine projections found in round19 are *new work*, not baseline facts.
- Start new natural work at P221 (and preserve C/S171-row corners). Check nonnegative restoration rather than transferring Z eliminations unchecked.
- Start ten-positive arithmetic at C75/626,76/464,77/460 and P80/382. No new supplied `X=q^2w,Y=qs,D=q^6` endpoint was found; own round18 explicitly labels an older low-Y q6 attempt rejected. A repaired attempt needs a new proof, not revival of the rejected metric claim.
- Radix47 is a complete incoming specialization with a new finite tuple and proof; it is not equality of polynomials with radix67/55. Any use in another compiler requires a uniform specialization/completeness argument and an entire coherent tuple replacement.
- Do not count future questions, heuristic search proposals, the original failed second-pair-shear namespace, conditional51/57/59/65 adapters, or upstream radix47 clause-alias obstruction as achieved new equations. The new complemented radix47 proof changes the selector coefficients and carry cap, so that old unchanged-coefficient alias is not a counterexample to it.
- New source theorem claims should retain the exact ordinary inherited calibration and clearly state that formalization remains paused. This audit found no substantive gap in the selected new elementary mechanisms, but is not a fresh full transitive-calibration formal verification.

## Exact byte pins

Full checked equation/expansion pins are in `baseline_metrics.json`; full radix47 raw/compressed port pins and controller values are in `baseline_radix47.json`. The following archive hashes bind the complete seven-source closure and the own predecessor.

- `upstream/docs/incoming/ConZFC_Centered_Residues_2026-10-25.zip`  
  SHA256 `3a505f10a5a533572577c7489af9ad84d092ef62f0e134deabd29b277bcc4d31`; 377 extracted files byte-matched.

- `upstream/docs/incoming/ConZFC_Common_Remainders_Radix47_2026-10-25.zip`  
  SHA256 `6066058ae0e269a5b4fff66634d412915066f7b52f8e515259845fd102e018fc`; 275 extracted files byte-matched.

- `upstream/docs/incoming/ConZFC_Coprime_Products_and_Positive_Centers_2026-10-25.zip`  
  SHA256 `b9e20289c01a3608561a46d4d1a0abd44565f79a5d40de473912f3661be37c38`; 240 extracted files byte-matched.

- `upstream/docs/incoming/ConZFC_Residual_Bases_Denominator_Engineering_2026-10-25.zip`  
  SHA256 `f02c30fd6455f618db0f654691887975a933f2200dafa9be7696135dc229058b`; 524 extracted files byte-matched.

- `upstream/docs/incoming/ConZFC_Shared_Certificates_Round18_2026-10-25.zip`  
  SHA256 `593aaa444c2f7b9b6d0fd439ef2dfdfc266d8782e10fcdd049a673668c36f1a7`; 635 extracted files byte-matched.

- `upstream/docs/incoming/ConZFC_Shared_Residue_Bounds_2026-10-25.zip`  
  SHA256 `f4c0c3a7c3290a30cb3d357c32fca9bb09c7e15481669e868de7bcf3750a41c1`; 243 extracted files byte-matched.

- `upstream/docs/incoming/ConZFC_Symmetric_Remainders_2026-10-25.zip`  
  SHA256 `d5f7129eb1a81d1e043b554dc4b42bc4fcb8cebe3a1c5e13f3d28b6f4b4eaaa5`; 164 extracted files byte-matched.

- `upstream/docs/incoming/ConZFC_Symmetric_Residue_Budgets_2026-10-25.zip`  
  SHA256 `3c7341d8ce04cf369f827c98cd7254d3a0433968fda9d298395655351f53d215`; 207 extracted files byte-matched.

### Selected exact artifact pins

- `intake/conzfc_common_remainders_20261025/direct/equation/equation.json`  
  SHA256 `359a38d9ba49f94e1fff7697ff1af7c5b8a6273d56096f6405fc67f212e8d31d`.

- `intake/ConZFC_Symmetric_Residue_Budgets_2026-10-25/equations/P258/equation.json`  
  SHA256 `f72ef7a7f62793e9170bc2df2bcbbe0e70c962409d4c791f45bbd7a51f5711b5`.

- `intake/ConZFC_Shared_Residue_Bounds_2026-10-25/equations/principal/equation.json`  
  SHA256 `500cb73f06e880bfa8585a28985219229464d7f097156219c80e2032ce28539e`.

- `intake/ConZFC_Coprime_Products_and_Positive_Centers_2026-10-25/natural/equations/natural221/equation.json`  
  SHA256 `76b39481b623a8a47b74fc9faa2127073786278416b63e871aedecf3871e8584`.

- `intake/ConZFC_Centered_Residues_2026-10-25/compact/equation_XY_V2.json`  
  SHA256 `ef76bb270defbc007566b90efb5afff24f3e003dcc480449ace04cf31043bef3`.

- `intake/conzfc_common_remainders_20261025/radix47/radix47/polynomial.json`  
  SHA256 `174057a94e7f440a5caba35e30e4d8ea1713cefb6b6541f3102342ee1260839d`.

- `intake/conzfc_common_remainders_20261025/radix47/radix47/radix47_proof.md`  
  SHA256 `3c854e9fb951f030f9d5b9dc7186c3be98f65cf4b94c63810869add08ec2c224`.

- `intake/ConZFC_Shared_Certificates_Round18_2026-10-25/scalar/free_whole_center11_c300.json`  
  SHA256 `e997ab4529cfd983e52603ea68dec4250650da800790fe40576955a8edce20a5`.

- `baseline_recollect.py` SHA256 `208f3f4874ae27762911d836d4170caf5c30fb71bfc00e42158500c28ef25fd0`.

- `baseline_metrics.json` SHA256 `96d55cb17b73596709e0fb11a07f4f7540aaa108862ecc40a1a6eb88657bb97c`.

- `baseline_radix47.py` SHA256 `79dd7d2134fec72766a6ce09344c5a9b6d320933fb39d0dfd85d17d9b350d97d`.

- `baseline_radix47.json` SHA256 `98c54bf563e3e838a52963682eb10e33659ddf773dfc187be430216a57d9dea3`.
