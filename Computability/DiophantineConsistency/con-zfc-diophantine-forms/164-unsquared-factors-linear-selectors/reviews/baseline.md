# Round 20 baseline: inspected source, incoming equations, and acceptance boundaries

Inspection snapshot: ProveIt `7a8da414376a80b90ecf799f37ceb26fb9ac674e`, read locally on 25 October 2026. No remote writes or incoming executable code was run for this baseline. The independently authored scripts in this directory parse inert ZIP/JSON data only.

## Findings useful for the next article

- The strongest selected direct dimension is **240 unrestricted integers**, 177 quadratic residuals, degree 4, 21,482 collected terms, height 6,144 (Shared Factorial Error). This is not the smallest-variable quartic across all coefficient architectures: the repository includes separate 37-integer quartics with large fixed coefficients.
- The principal Factorial-Free endpoint **(242,178,4,5018,7968)** and Normalized balanced **(244,176,4,5212,3968)** are meaningful low-support/low-height baselines, not merely their older 252-variable shared parent. The 241-variable Factorial-Free companion retains only 177 rows.
- Across the selected seven incoming packages, all three Lucas direct quartics and both Nearest direct quartics are dominated componentwise on variables/rows/collected support/height. Their arithmetic mechanisms remain useful; dominance does not invalidate their proofs.
- Cofinal sparse and balanced integer247 profiles retain frontier status on support. Its natural219 and both natural221 profiles remain separate same-domain tradeoffs.
- Lucas gives a new positive10 degree304/87-operation tradeoff. Nearest gives signed (14,82,113), (14,90,111), (13,152,126), (11,298,150), in variables/degree/live-operations order. No scalar expansion height or support was supplied for these, and none is inferred from fixed-port bit lengths.
- The current maintained upstream one-page equation is still **15 strictly positive variables, exact degree157, 66 operations, coherent radix55 tuple**. Seven new ZIPs are incoming, not maintained or accepted new endpoints.

## Source status: do not conflate these levels

1. `docs/incoming` contains exactly the seven archives below at the inspected pin. Its introductory rule says arrivals are not research material until placement and written reconciliation. Its older “queue is clear” paragraph predates these files and is not evidence of acceptance.
2. Numbered placed sources currently extend through **147**: 140 Centered Residues, 141 Common Remainders–Radix47, 142 Coprime Products/Positive Centers, 143 Residual Bases, 144 Shared Certificates Round18, 145 Shared Residue Bounds, 146 Symmetric Remainders, 147 Symmetric Residue Budgets. Placement is not endpoint acceptance. The collection README still has earlier-wave front matter; actual tree and active review scopes control.
3. `research/incoming-3ecd6a6cf5-codefree-intake/README.md` explicitly labels the preceding eight packages’ metrics reported/unverified in that upstream intake. Its ordinary incoming47 review does not authenticate the claimed numeric47 tuple or page.
4. The active README accepts separate direct315/316-variable height15109 quartics and preserves their failed predecessor evidence. It does not adopt the latest 240/241/242-variable arrivals.
5. Upstream numerical53 whole-page endpoint is independently accepted but not promoted because smaller raw coefficient storage is not a shorter printed page. Numerical49 finite controller conditions are discharged separately, without a complete accepted49 tuple/page. The complete three-anchor47 proposal is conditional, with new bracket values and admissible-prime existence unknown. That proposal is not the incoming complemented-label seven-marker47 specialization.
6. All new packages supply ordinary arithmetic proofs composed with named inherited calibration interfaces, plus exact finite artifacts; none claims a newly rebuilt end-to-end Lean/Rocq or encoded object-ZFC derivation. “Independently reviewed” in incoming archives denotes separate AI-assisted internal review, not external human peer review.

### Maintained display identity

`CURRENT_EQUATION.json` SHA-256: `3b689b3c355c5237e1a1170215b7a7430cc3a008714b2aa8187e87a496b71dd9`.
Its equation PDF SHA-256: `4681aa56300883fab83d1c1d47f65ee969bd0a4f68156de6455f74b8f828c302`; TeX: `440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`; polynomial: `058c48168f242f3b9aae8fd86cbe6d2b0f6fb1f336ae8082567a5edb24528066`.

## Exact archive binding

All **2,424 non-directory members** in the seven ZIPs were compared byte-for-byte with their extraction. Every match passed. This checks delivery identity, not mathematical truth.

| Archive | SHA-256 | Members |
|---|---|---:|
| `ConZFC_Cofinal_Witnesses_Centered_Carriers_2026-10-25.zip` | `57089f667de4f1b413c264116a9d3444e255d2f4d51ee9c98770cc1975e8a256` | 799 |
| `ConZFC_Digit_Recovery_2026-10-25.zip` | `5f7aa47532534e1723dd0bdd290eb871dd61fa58e228189412ddee0a6fb78da8` | 160 |
| `ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip` | `38dfec4f7db8ba4af921fe101714da6a569a3afce1d916325eb550160372c913` | 168 |
| `ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25.zip` | `02428d2029887eb1b6f2e861f5ec76b8cb3a10e29b3b44b31b8f828e689117c0` | 248 |
| `ConZFC_Nearest_Factorial_2026-10-25.zip` | `c4bb08c06bc5be8aeab5427ace99d03cb6b60c19c5e90322748648a29157b24e` | 399 |
| `ConZFC_Normalized_Residues_Round19_2026-10-25.zip` | `253ae08cf0cb604a98467b8e2fc8c3321a94b29d3c12b90f31220ab789b5c750` | 407 |
| `ConZFC_Shared_Factorial_Error_2026-10-25.zip` | `8c126ebd9982e547f16e86cf65b57dbc85bf72e98032237ab0c324afc1694ef2` | 243 |

## Independently recollected quartics

Tuples are `(domain; variables, residuals, degree, nonzero collected monomials, coefficient height)`. Height is maximum absolute **collected polynomial** coefficient. Every listed residual system was squared and collected by the independent script, exactly matched against the supplied complete expansion, and checked for variable liveness. “Frontier” means only among the selected comparable incoming quartics, not a global or literature frontier.

| Family / selected equation | Domain | n | Rows | Degree | Terms | Height | Selected frontier |
|---|---|---:|---:|---:|---:|---:|---|
| Lucas / `integer248` | ℤ | 248 | 182 | 4 | 5321 | 128446 | dominated |
| Lucas / `integer246` | ℤ | 246 | 180 | 4 | 5048 | 195955 | dominated |
| Lucas / `integer245` | ℤ | 245 | 179 | 4 | 21845 | 314701 | dominated |
| Shared / `equation240` | ℤ | 240 | 177 | 4 | 21482 | 6144 | yes |
| Shared / `equation241_affine_balanced` | ℤ | 241 | 178 | 4 | 5351 | 15107 | yes |
| Shared / `equation241_affine` | ℤ | 241 | 178 | 4 | 9544 | 4512 | yes |
| Shared / `candidate244` | ℤ | 244 | 181 | 4 | 5346 | 128446 | dominated |
| Digit / `quartic247` | ℤ | 247 | 182 | 4 | 4755 | 8815 | yes |
| Free / `principal` | ℤ | 242 | 178 | 4 | 5018 | 7968 | yes |
| Free / `companion` | ℤ | 241 | 177 | 4 | 12774 | 7968 | yes |
| Nearest / `P242` | ℤ | 242 | 178 | 4 | 17026 | 38432 | dominated |
| Nearest / `P243` | ℤ | 243 | 179 | 4 | 6877 | 11856 | dominated |
| Normalized / `balanced244` | ℤ | 244 | 176 | 4 | 5212 | 3968 | yes |
| Normalized / `dimension243` | ℤ | 243 | 175 | 4 | 19517 | 7680 | yes |
| Normalized / `sparse250` | ℤ | 250 | 182 | 4 | 4770 | 6709 | yes |
| Normalized / `dimension246` | ℤ | 246 | 178 | 4 | 21537 | 6144 | dominated |
| Normalized / `lowheight247` | ℤ | 247 | 179 | 4 | 10422 | 3840 | yes |
| Normalized / `exposed247` | ℤ | 247 | 179 | 4 | 4889 | 170496 | dominated |
| Normalized / `balanced247` | ℤ | 247 | 179 | 4 | 5328 | 3968 | dominated |
| Cofinal / `integer246` | ℤ | 246 | 178 | 4 | 12541 | 12227 | dominated |
| Cofinal / `integer247_sparse` | ℤ | 247 | 179 | 4 | 4352 | 23316 | yes |
| Cofinal / `integer247_balanced` | ℤ | 247 | 179 | 4 | 4432 | 17235 | yes |
| Cofinal / `integer247_lowheight` | ℤ | 247 | 179 | 4 | 5648 | 6144 | dominated |
| Cofinal / `natural219` | ℕ₀ | 219 | 171 | 4 | 8267 | 130686428 | yes |
| Cofinal / `sparse221` | ℕ₀ | 221 | 173 | 4 | 5253 | 65867916 | yes |
| Cofinal / `balanced221` | ℕ₀ | 221 | 172 | 4 | 5586 | 65892620 | yes |

### Literal equation and full-expansion hashes

- `intake/ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25/direct_quartics/equations/integer248/equation.json`
  - equation SHA-256 `c51ebc12534db042bd1c7bf7c59f84602f51625e2d952dffa82fa054b5d92192`
  - full expansion SHA-256 `b479a80535ceb0d563261474fde8acd31cdfccdfd25afbe3936b2420dccf650a`
- `intake/ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25/direct_quartics/equations/integer246/equation.json`
  - equation SHA-256 `70f78f521c8e659c1335ad75f9faea68f30e030ac4f0bd4ba953a182b3d1c5ee`
  - full expansion SHA-256 `4ec2a932355df81e5d9d157e8fcc4338f64eda8221456fa00d7d9720c3a8debd`
- `intake/ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25/direct_quartics/equations/integer245/equation.json`
  - equation SHA-256 `c784406998f2d1666b9c460ba6802cd320ff95848af226ea88d9f23cb480f16b`
  - full expansion SHA-256 `3369c7255e254ed4363498f97221b854a6f0eaf3279a5414262d86418112ef64`
- `intake/conzfc_shared_factorial_error_20261025/equations/equation240/equation.json`
  - equation SHA-256 `5d6b3b447dae75969bce826c30a61d216df784a396d5fed221983e1b23728cc0`
  - full expansion SHA-256 `7157dd5606375b05477caba49ddfee02eb340c2acb365da3185eb7c5d3d05d30`
- `intake/conzfc_shared_factorial_error_20261025/equations/equation241_affine_balanced/equation.json`
  - equation SHA-256 `17340c6a2c251bb488a0cf66c2b8437573f7483d0f405e7d3ba72944180a70c8`
  - full expansion SHA-256 `f4acdc4a187c8e6ee91210dfa21eb1e3925ad999089236c47c8c7845109adfd1`
- `intake/conzfc_shared_factorial_error_20261025/equations/equation241_affine/equation.json`
  - equation SHA-256 `6510d159325dcf51835d837047e7ae71dd3e70fe098435c49f8e9ac1f7544838`
  - full expansion SHA-256 `ebe97d7921ae17932d0d04b603050ae1d3b6ad1015c1836f8e48c3bf6bf0632f`
- `intake/conzfc_shared_factorial_error_20261025/equations/candidate244/equation.json`
  - equation SHA-256 `9a661665b1de2e95c4e0970492ec5bd901187c65be88e0cc01519730cf294a16`
  - full expansion SHA-256 `c29cdd3d4dc1c0e17468df7a1e0c0e792f70faf5278493bf967a31323a056a20`
- `intake/ConZFC_Digit_Recovery_2026-10-25/equations/quartic247/equation.json`
  - equation SHA-256 `6df8f7de8b389084d6ce000f777f27ffc962e05b51217662e680201cffd1578d`
  - full expansion SHA-256 `19b2bc4e8cbb8d112feed0b88ca6c91884a40985745026eed020a78eee35187f`
- `intake/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct/principal/equation.json`
  - equation SHA-256 `3970268165d2dea4914550913d1e882f9c6f108008de677a919fc2a01b8740a5`
  - full expansion SHA-256 `3ce5295378c26fdc16a2f4ca1da123cf8c1f411478df56fbe5ff668ab5dfc2fd`
- `intake/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct/companion/equation.json`
  - equation SHA-256 `4ac1f58659deee06fdd8d956ebc1f38f72543135759f1174b145e3d8f5b4f9fb`
  - full expansion SHA-256 `a739798455ab3606d2d740e038b05aef18e59ff1bd746b52f0ad7f01cc74b11d`
- `intake/ConZFC_Nearest_Factorial_2026-10-25/direct/equations/P242/equation.json`
  - equation SHA-256 `91cf517ce3e86293ea65f141d0dbb842bc3164f71126887611a2b8a59caf754d`
  - full expansion SHA-256 `47b547c4eaa8d6b2f03b2ad9de5bd690182569ac8db4b65c181c49f8b49310fd`
- `intake/ConZFC_Nearest_Factorial_2026-10-25/direct/equations/P243/equation.json`
  - equation SHA-256 `c925dc417ad78baedfe045203a6d710d08710d8da57e0fe39b0fb45073ed82a2`
  - full expansion SHA-256 `a34af9a417ef2db7b6b4ed4f7f0577c088b74a1270a7719a0d24c4f5b9c0545e`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/signed/balanced244/equation.json`
  - equation SHA-256 `f8c5218efa673edaa11074de9adbac14d41c0e0614766e85c668b85b788bb9cf`
  - full expansion SHA-256 `7cf51697551e57d9c7ce5ae9fe61a91e2616d0493ff88337b755406655c43554`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/signed/dimension243/equation.json`
  - equation SHA-256 `37e834830520d2637bab0422b4fcb909ff2c48a9f979b2257c0ac944fc37803c`
  - full expansion SHA-256 `d7114552e27506bed37ff1f1a54c341fd04ace27ed1a1f3c1742b080970c8e5e`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/signed/sparse250/equation.json`
  - equation SHA-256 `77c12733c91a9ba7cc1ab75ffe7cde76adfe93ee80c9753fbff510783e95f2e5`
  - full expansion SHA-256 `37f6ba06a0de0950af3294dce283c98fc7c9b31fa9e4a13448ff607433e25713`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/signed/dimension246/equation.json`
  - equation SHA-256 `ae2b9b78aaa0230b4beffac5bf31d519f85975cbb73528b9e04daa383b39b40a`
  - full expansion SHA-256 `98d3fab044f3f90fc1c0e11e1c3371e429920400d3c881a626fda87018739f79`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/signed/lowheight247/equation.json`
  - equation SHA-256 `3eae001b2bedf7284641754878f87e6d17f7a3af296379dc972ce3ca0052b98d`
  - full expansion SHA-256 `bf2c36e6507de6501f2fd7fe0b726f856e9fabc267d3b46cbaac88f008a88882`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/signed/exposed247/equation.json`
  - equation SHA-256 `749f7e6958fbdc0f9bcbac98d9fe5dedea02a016a0cd76571ca033c5f9f3e877`
  - full expansion SHA-256 `1172ed339931a694f498dbf5dc01489ac1b995957cd83b85456da627a86034bc`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/signed/balanced247/equation.json`
  - equation SHA-256 `9e46b1429c6a816badd4e26b23fe91639e8c01f9ab19651fcbcd9c1ce37deea2`
  - full expansion SHA-256 `4d4e79806a8ef5ae7370cecf30cef90a92311c64fd1af27d92d19914b6c63f84`
- `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/quartic/integer246/equation.json`
  - equation SHA-256 `c11b5090d727e289ce0d8ac37a15d3b0a653f1e4494d35bf478fb672b4b4dd8a`
  - full expansion SHA-256 `0f57980e4a3de477159154cd722df29b039efab3e12536cf8ba5974153a6ca0e`
- `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/quartic/integer247_sparse/equation.json`
  - equation SHA-256 `a3a26997be9328f313b2fdb4257fcbbecaa7688f0a7ae15db0946770d01d2040`
  - full expansion SHA-256 `37cccaae1ab0b991b8b1d584284372438ee1edf50dc1c25d544fb22dbb2b62a0`
- `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/quartic/integer247_balanced/equation.json`
  - equation SHA-256 `ee8cf677106080ea23f74e4903d92a6e79e346d9abdc22e4f5f0014377bb01ab`
  - full expansion SHA-256 `0fed4450fa66c07a19ad767a5931ea924ac13809eb697322eb1372e4172a6d31`
- `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/quartic/integer247_lowheight/equation.json`
  - equation SHA-256 `6fb392ad080093ca1b6b73ad3087905b8fdd080f6a0b1a6fe314ac8fc9df543b`
  - full expansion SHA-256 `e081197c178a4bf9684f0f4ff43ad405905b684856375edd580c9cc933364553`
- `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/natural/natural219/equation.json`
  - equation SHA-256 `0f1d3f46062a717fff2229146c4eb82e89c81912d2c53e20db531cc662714895`
  - full expansion SHA-256 `545ce66e110d76c076caedec1778ff7432aa0966f2f098cf06e050d048e95691`
- `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/natural/sparse221/equation.json`
  - equation SHA-256 `e1f5716c1c463f254fd520956e32c4f19aa27d39406a271d01fa378fe7cd5790`
  - full expansion SHA-256 `47b3f9d579b438721339d4631e79108beefb7762c1d4e2e6887f8e35658b6f84`
- `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/natural/balanced221/equation.json`
  - equation SHA-256 `6249702f42930d20630a0a4fa4a8e125c0477875295d5b886acdf6e523d6d8d2`
  - full expansion SHA-256 `55a45230ae48407eb5198f278407a027aae08dbf4708dc84ba5117413690710e`

## Small-variable scalar endpoints

Live gates and coordinate liveness below were independently counted from actual DAGs. Exact degree is supplied by the corresponding ordinary/leading-form proof; our separate data-only census records a syntactic upper bound, not an independent degree-exactness theorem. In particular the 11-integer 298/300 endpoints both have naive upper bound352 and require their nontrivial center-cancellation identities. Unmeasured expansion size/height is not zero.

| Literal file | Domain | n | Claimed exact degree | Independent live operations | Syntactic degree bound |
|---|---|---:|---:|---:|---:|
| `intake/ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25/compact/equation_bV.json` | strictly positive integers | 10 | 304 | 87 | 304 |
| `intake/ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25/compact/equation_V2.json` | strictly positive integers | 10 | 410 | 86 | 410 |
| `intake/ConZFC_Nearest_Factorial_2026-10-25/signed/integer14_degree82.json` | unrestricted integers | 14 | 82 | 113 | 82 |
| `intake/ConZFC_Nearest_Factorial_2026-10-25/signed/integer14_degree90.json` | unrestricted integers | 14 | 90 | 111 | 90 |
| `intake/ConZFC_Nearest_Factorial_2026-10-25/signed/integer13_degree152.json` | unrestricted integers | 13 | 152 | 126 | 152 |
| `intake/ConZFC_Nearest_Factorial_2026-10-25/signed/integer11_degree298.json` | unrestricted integers | 11 | 298 | 150 | 352 |
| `intake/ConZFC_Nearest_Factorial_2026-10-25/compact/equation79_degree382.json` | strictly positive integers | 10 | 382 | 79 | 382 |
| `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/scalar/free_whole_center11_c300.json` | unrestricted integers | 11 | 300 | 148 | 352 |
| `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/positive/q1_bv.json` | strictly positive integers | 10 | 338 | 80 | 338 |
| `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/positive/q2_bv.json` | strictly positive integers | 10 | 382 | 79 | 382 |
| `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/roots/integer14_degree88_ops110.json` | unrestricted integers | 14 | 88 | 110 | 88 |
| `intake/ConZFC_Cofinal_Witnesses_Centered_Carriers/roots/integer13_degree156_ops117.json` | unrestricted integers | 13 | 156 | 117 | 156 |

Scalar SHA-256 identities:

- `equation_bV.json`: `228ba5cdc2ac9c5f96b1d354e0050be7225534d3f2d6a58802d2431168937ead`
- `equation_V2.json`: `1ce029a1af821936e46064be35fe21528fc83301863e2bec8953bdf270c7a6b8`
- `integer14_degree82.json`: `e65e2ad32ec613a89f0404aa01ef7d05567306e0a1f757ba4929853a5243eb78`
- `integer14_degree90.json`: `c983daea1493e9bf7b2629cc8182c253b753545cfc96113597a2defb7f8780ce`
- `integer13_degree152.json`: `44c6c004e4252574c793ba2574540bdafb58187da96d0d7b4a9f8a6a0543869a`
- `integer11_degree298.json`: `6c1fecc3e01806ed3090bb6ebbc538e86f6b11eae385f4f34a23fba0d0db1b5e`
- `equation79_degree382.json`: `86cff2b5880b96811bddff8d638f85a4ba376083701ae0069ca7d654ca825cf7`
- `free_whole_center11_c300.json`: `e997ab4529cfd983e52603ea68dec4250650da800790fe40576955a8edce20a5`
- `q1_bv.json`: `bfe24b67669f3dce988246d2f69d427ecc5f9c9db492f13402dae777f56ac442`
- `q2_bv.json`: `92c820b982b2a89f8d6b494ca24f1f959fca12f532e09c96945df477cba9982b`
- `integer14_degree88_ops110.json`: `86082ac57f64e6d6ad7a5010baece1893ab132d2ebd03dfe528dd35cf7b0046a`
- `integer13_degree156_ops117.json`: `9087a1b72cba4cd9db8b94ed2ce6cddbb24324d357141662f0dc4973210d5f92`

## Height-one polynomials

These are collected quartics, not residual-list encodings. Every supplied coefficient was independently collected, all variables were live, height was exactly1 and constant exactly1. Their zero-set proof additionally depends on the incidence/alias certificates, not rechecked by this narrow census.

| Endpoint | Domain | n | Degree | Terms | Height | Polynomial SHA-256 |
|---|---|---:|---:|---:|---:|---|
| balanced580 | ℤ | 580 | 4 | 12001 | 1 | `b990d397782d321b183fec1829e573a2e91f2ab248e9bf2820f57960382e6476` |
| compact534 | ℤ | 534 | 4 | 18543 | 1 | `53085a590f83edd755ec12df31558395124aae8f02dcf271ced9b212a002e363` |
| minimum528 | ℤ | 528 | 4 | 20816 | 1 | `6a117a2933fdd74da841ec6ce08b7fea4763b391a264afc97898852b2a180a22` |
| sparse620 | ℤ | 620 | 4 | 8318 | 1 | `31b1d0c61f04ca1ad45a8f0d1357bf100252dc5e82acfce6b272dc0498f8bcff` |
| sparser717 | ℤ | 717 | 4 | 7176 | 1 | `f2a4b81d1bf2a28b6f1054d97f8ba017a93f3f043b37d4e9db6d58d4ecede8c7` |

## Genuine mechanisms, required proof order, and boundaries

### Factorial-Free Binomial CRT

`report/main.tex` proves two distinct binomial-modulus lemmas. For `R≥lcm(1,…,t)²`, every row `R+i` has a full prime-power divisor of `B=binom(R+t,t)` exceeding `t`. Conversely every prime power exactly dividing B has some compatible row, even if it was not selected for row-by-row soundness. The latter is required for completeness at all primes. Valuation calculation uses the classical divisor `t*binom(t−1,i−1) | lcm(1,…,t)`. No pairwise coprimality of consecutive factors is assumed.
Label multiplicity is recovered by evaluation uniqueness, not coprimality of values `1+jF`: first force equal nonunit factor counts, then use coefficient sum `<F` and unique factorization over Q[z]. The actual choice `F=[2(t+1)]^t`, `y=F(2v+1)²`, `H=2+sum actual representatives`, `q=(2z+1)²` reuses the existing power request. F need not be a factorial; factorials may still occur when constructing a divisible beta parameter in completeness. The algebraic boundary y=F is excluded only after local-row decoding by propagation of initial zero accumulator against final one. This is a substantive new compiler argument, not only a coordinate shear.
### Nearest Factorial and Shared Factorial Error

Both packages use the sign-free common error mechanism `Bv=M`, `MF=vV+S` and a common norm bounding S and the eleven modular remainders. It yields `|BF−V|<|B|/2` before signs. A nearest-integer fixed-point theorem then forces `F=t!` once B is authenticated. Its proof first obtains F>t² from the lower bound `2^t/(t+1)`, then excludes all other integer values through a product-error estimate; completeness has the stronger error `<1/32`.
Nearest keeps an odd-square radix; Shared goes further to the signed affine odd radix `q=2z+1`. Shared excludes both unit radices by `Bv=M` and |B|≥2, allows q<0 through the bootstrap, uses the signed low polynomial Σ binom(n,j)q^j with absolute-value remainder bounds, then recovers B>0, F>0 and q>0. Its final beta is the original `y=V(V−1)`. Augmented-beta alternatives in review history are NOT final premises. The authoritative final proof is `Shared/report/paper_main.tex`; `Shared/equations/PROOF.md` describes only its older250-variable square-radix ancestor. Both retain full14-pair orientation: a nine-term selective orientation proof cannot silently be reused while B is signed.
Nearest signed-native scalar changes are separate: the first-index modulus grows from XY to XY², enabling the guard q⁸→q⁶. It changes the frame and thus does not contradict Normalized’s degree300 lower bound for the previous fixed frame. Its compact79-operation degree382 result is only a reassociation of the same old polynomial, not a newly lower-degree polynomial.
### Normalized Residues

The new common sphere is `M²−2ΣRi²=G(a,b,c)` rather than `M²−4ΣRi²−1=G`. Under recovered M>0 it gives |ri|<3Li/4. The canonical binomial low tails are <Li/32, so congruent lifts differ by strictly less than Li; half-radius uniqueness is unnecessary. Exact row/coordinate changes then expose affine variables and reduce coefficient height.
Its height-one improvement polarizes a same-logical square a² into ab, replaces a three-alias equality cycle with `Q(a,b)=(a−b)²(a²+ab+b²)`, and removes its equality dummy. Nonnegative incidence energy plus equality/unit penalties proves zero-set equivalence; each selected final whole polynomial still needs exact coefficient collection, since polarization can cause collisions. The universal off-zero canonical lift is `(ΣRj²+(Σδj Rj)²)/2`, NOT automatically the bare original SOS.
The scalar degree300 theorem is limited to the precisely fixed frame, constant nonzero radical weight and integer polynomial center independent of the carrier variable n. It is not a global11-variable lower bound, and the supplied degree300/148 graph is unchanged.
### Digit Recovery

Uses `q=(6z+3)²≥9`, early exponent bound x≥t+1 from an existing denominator ratio, and self-radix q≥2^x to recover the positive factorial binomial digit BEFORE ceiling signs. The retained beta endpoint gives F²+t≤x−1, making every digit small. Then `rs=G` and `r+s=B−1≥0` recover both signs. Completeness requires actual cofinal representative choices giving H≡3 mod6 and an even beta exponent; this is not a natural-coordinate bijection. The separately supplied K,S,Peirce231-nonnegative-variable experiment is explicitly unsuccessful against its229-variable parent.
### Lucas Corrections and Witness Elimination

The direct branch uses `(r+1)(s+1)=1+G` to reduce three front sign triples to one ternary guard plus odd-square radix. It treats both r,s≥0 and r,s≤−2 branches before binomial authentication. Its direct metrics are now dominated by concurrent alternatives.
The genuinely new compact mechanism takes Y=qs and a second-order Lucas correction `e6=6(k−R−1)−v(R+1)(R−1)(R+3)`, v=XY², denominator6q⁶. It recovers the bounded index from q⁴ divisibility before restoring full q⁶ divisibility, and only then recovers q²|s. The proof does not invert6 moduloq; prime valuations handle2 and3 explicitly. The signed transport proof has separate adverse-correction cases R≤−4 and R=0. Omitting those would leave a soundness gap. Degree304/87ops is a new tradeoff, while degree410/86ops is a dominated control.
Its higher-degree witness elimination is exact monic substitution with explicit restoration. Reported selected tuples include153 integers,87 residuals,degree8,188579 collected monomials,height750273658864,2290 live operations; this full octic expansion was not independently recollected in the current narrow census. Higher cases report proved power-of-two height bounds, not measured exact heights, and should not be compared as though the bounds were exact.
### Cofinal Witnesses / Centered Carriers

Natural cofinal construction uses even descending horizon t=2t0+4 and y=V−1; its divisibility and pending-state bounds are the mathematical change. The signed direct branch composes common remainders, odd-square bootstrap, affine exposures and row-basis transformations. Compact projection-before-full-denominator recovery and root-coordinate polynomial shears are separate mechanisms. Alternate radix47 fixed ports change the whole coherent tuple and do not constitute promotion of the upstream conditional three-anchor47 proposal.

## Finite scope and reproducibility

Run `python -B round20/audit_baseline.py` and `python -B round20/audit_scalar_baseline.py` from the workspace root. These scripts read archive/equation data and write only their receipts beside themselves. They import no incoming producer, checker, evaluator or AST helper; no incoming subprocess is launched.

`baseline_census.json` records all26 equation/expansion hashes, exact metrics, archive binding and selected dominance relations. `baseline_scalars.json` records12 literal DAG hashes/costs and five height-one polynomial hashes. Their mathematical scope is deliberately narrower than a complete replay of all inherited transformations and unbounded proofs. No consistency decision, global minimum, new kernel proof, repository acceptance or external peer endorsement follows from these finite checks.

## Proof-source SHA-256 pins

- `intake/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/report/main.tex`: `dc4e07fe132e256cf591dfd50624226af1e1bfc5d9c086974c7a15f72e6cddbb`
- `intake/ConZFC_Nearest_Factorial_2026-10-25/direct/proofs/NEAREST_FACTORIAL_PROOF.md`: `d40f734d6b736303b5baec7a0e0768d9ebb8d757038c85baf21ecc62783ce82a`
- `intake/ConZFC_Nearest_Factorial_2026-10-25/signed/PROOF.md`: `eacf11a456b06c9b277dc6253f52beee63d6cd333f1f5726d8966830cf591bf7`
- `intake/conzfc_shared_factorial_error_20261025/report/paper_main.tex`: `d9cf03c92db7d68bffb1e51d81af58777ddec8b3cd4d1d681bfabdb9a55ad74e`
- `intake/conzfc_shared_factorial_error_20261025/verification/SIGNED_POWER_AND_BETA_REVIEW.md`: `7f440fbf27bfdc7598a259613ba99ce98af45da7814286818fef288aa5536a0d`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/signed/PROOF.md`: `18dfa6e71476081f8a64284e2ac05d20d4a0f1c13b397a96bd961201a49ac63e`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/height_one/PROOF.md`: `8dfb1a4ad4d175fb2da28531c9c8303261be6fa612d23a53c2e9a21fb4856690`
- `intake/ConZFC_Normalized_Residues_Round19_2026-10-25/scalar/SCALAR_FIXED_FRAME_DEGREE_FLOOR.md`: `9ee05fc4c7757aad72a136fe04d82d3557302e6b45ad803a0b9664021286b0dc`
- `intake/ConZFC_Digit_Recovery_2026-10-25/proofs/NEW_ARGUMENT.md`: `6bd08c8143ff690350509d8530323e628c827a3d6c4bd039f7d7e47a7af4d02f`
- `intake/ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25/compact/PROOF.md`: `c3551f76855c4d492129b7933fc7bce9661795a2572f25a9866283e18b979037`
- `intake/ConZFC_Lucas_Corrections_and_Witness_Elimination_2026-10-25/direct_quartics/PROOF.md`: `969916b42890fb45e911a48f0bcff526abf125ec4e529ee4174dadfda3947671`
