# Signed caps and free scales: independent inert ordinary review

Reviewed 2026-10-24. This record closes an ordinary proof/data review of placed package `132-signed-caps-free-scales`. No incoming program was imported, compiled or executed; no source/compiler replay, circuit census or quartic collection is approved by this record. No delivered or frozen parent file was changed.

The free-scale first-root proof contains a repairable error in its claimed complete leading form. The exact degree-44 witness survives the correction. No further new ordinary gap was found in the arguments read, conditional on their stated inherited signed-rank, step-down, divisibility, interpolation, canonical-family and native calibration contracts; those inherited contracts and all executable bindings were not independently re-proved here.

## Authentication and read scope

Original arrival commit: `fd3e384e92ed4813a5536f877c5cd835ca4c75d2`.
Original path: `docs/incoming/ConZFC_Signed_Caps_Free_Scales_2026-10-25.zip`.
Git blob: `493957e8b40e0b2eb857f1b7f7d9b31a168aa848`.
Whole ZIP SHA256: `333fcb482099832d9d4827722226d4c26c229700ee793155cecc9a911c8cfd89` (1593 members).

The original Git blob was recovered only to `/tmp`. The following proofs and endpoint ledger were read and authenticated byte for byte against the original ZIP. Paths are relative to `con-zfc-diophantine-forms/132-signed-caps-free-scales/`.

| Member | SHA256 |
| --- | --- |
| `README.md` | `da4daab995b6eb0c747d8872c46fa0cb90607f3172beb6aee597f713acd2b2c2` |
| `alternative/PROOF.md` | `67d294420df2a1648313570b1081922164501975f79788ea6c0c01a17558fa2b` |
| `lowdegree/PROOF.md` | `527b916ff3f8f150069c715ce8d176ed0e20a2914913aa8d511eca54ed737ca6` |
| `integer/source/FREE_SCALE_PROOF.md` | `8657bcf6ee42ae876b669b8b86ca0682d8be218f0a076885019b9865e1d790f8` |
| `integer/PROOF.md` | `a79a042f37ff959131278a5e557e8dbe456fb803172fb058cf6f27eeace7c57d` |
| `integer_lowops/PROOF.md` | `a828b2d62f7e2862efc78d0303fb295475dbc301829b16f0bba620744ab7bd9f` |
| `positive/PROOF.md` | `ad97812045054ab5a4a20771910e9c314324a0afc223bf548aed931c167cb165` |
| `RESULTS.json` | `dd55e35565b38df047baf58ed1adf1022acce52df6b34b545f8f996a31997cc9` |

The alternative README was also read. The complete lowdegree artifact and its metrics were authenticated as original ZIP members, without evaluating their DAG:

| Member | SHA256 |
| --- | --- |
| `lowdegree/equation.json` | `17aff7a98d0bcd36c1db0abd3bcc71de4d2e4075ac01316eec95ab0358ab8d69` |
| `lowdegree/METRICS.json` | `0d23b095217c310591269e7cf016cc1d3866531b055d35e3c7aba201362b7f87` |

## Exact leading-form correction

Section 8 of both `lowdegree/PROOF.md` and the copied `integer/source/FREE_SCALE_PROOF.md` states that only `4ULZ` contributes in degree 22 to

    A=(Z+Uk)^2+4U(LZ-U),    P=A^2+B^2+Caux^2+G^2.

That assertion is false: `deg(U)=6` and `deg(k)=5`, so `(Uk)^2` also has degree 22. With the displayed leading forms and `k_0=R_0`, the corrected complete forms are

    [A]_22 = U_0^2 R_0^2 + 4 U_0 L_0 Z_0,
    [P]_44 = (U_0^2 R_0^2 + 4 U_0 L_0 Z_0)^2.

Here `Z_0=U_0 n+4q_0^3 X_0^2`. The omitted term is independent of `n`, so the coefficient of `n^2` in the corrected top form is still exactly `16U_0^4 L_0^2`. Substitution of

    q_0=6 beta j,  X_0=12q_0 w,  Y_0=v,
    R_0=-q_0^3(12wC-q_0z),
    U_0=8q_0^3 X_0Y_0,  L_0=X_0Y_0^2R_0

therefore still gives

    [j^26 w^6 v^8 z^2 n^2] P = 2^54 3^32 beta^26 > 0.

The exponents sum to 44, and all other squared residuals have lower degree. This establishes the advertised exact degree despite the incorrect full-leading-form sentence. It is not a degree counterexample or a refutation of the zero-existence theorem. The delivered lowdegree ledger records 111 gates: 63 multiplications, 26 additions and 22 subtractions.

## Ordinary dependencies examined

The first-root release of `Y` does not cancel a nonunit modulo `H`. Monicity first gives integral `Z/U`, the 2-primary divisibility gives the required parity, and the strengthened budget yields `|Y|>|q|^3`. The signed bootstrap then supplies the stronger growth estimate. The retained divisibility is of the whole product `q^3(x_0-2^R)(2^R x_0+1)`; its bound forces the product to vanish before scale recovery. Only after `H|Klo` does the proof cancel the nonzero integer `H` from an integer divisibility and recover `Y=(2v_scale+1)q^3`. Soundness constructs a literal predecessor zero; completeness uses the canonical predecessor family and a fresh strengthened-budget triple. It is not a bijection on arbitrary predecessor zeros.

The eleven-variable saturation proof treats the independent radical classes and late scale recovery separately; the stronger divisible product is bounded before invoking the recovered cubic scale. The product-guard low-operation proof obtains the early main root before splitting its remaining factors, avoiding the apparent circular use of that split. Its completeness fixes a single strong pair before the supported modulus interpolation. In the positive variants, the polynomial center shift is proved positive before using kernel meanings; the later gap estimate restores a fresh positive transport coordinate. These are the proof-use boundaries checked in this read, not approval of all literal source tuples, native ports or gates.

The alternative 352/355 signed-cap proof is based on a different inherited body and request set. Its arithmetic cannot be identified with the accepted 327 complete body by matching a cap formula. Full actual source, witness reconstruction, Horn/projection/free-coordinate/translation and coefficient bindings remain a separate obligation.

## Delivered comparisons and scope

The authenticated `RESULTS.json` reports integer quartics 352/219/9355/15020718 and 355/220/9370/15020718, in variables/rows/terms/height order. The accepted 327/216/5718/128446 endpoint is smaller in all four metrics. The fifteen-variable degree-44, eleven-variable saturation/product and ten-positive degree-253/252 routes are different degree/operation tradeoffs, not competing quartic counts. None of these delivered censuses was independently regenerated in this review.

Complete gate and four-port coefficient binding, every global leading form, the authentic native compiler chain, all actual source/guard maps, executable closure and deterministic reproduction remain required before accepting any new endpoint. The concrete correction above should accompany any future reuse of the first-root degree proof; the delivered files remain untouched.
