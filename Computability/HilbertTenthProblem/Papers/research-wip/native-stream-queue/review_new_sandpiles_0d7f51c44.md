# Scoped intake of four sandpile packages at 0d7f51c44

This is a bounded text and inert-source review at arrival commit `0d7f51c442f5736f35d9de14d4c1b1f7cc1c2bbf`. No concrete defect was found in the selected mathematical text. Fresh checks confirm the four supplied DAGs' counts, closure, liveness, literal sum-of-squares assembly and exact degree 18. This is not a reconstruction of every mathematical macro or an independent certification of the imported universality simulations.

The accompanying `review_new_sandpiles_0d7f51c44.json` inventories all 320 regular members of the four archives, including nested baseline/replay copies. Each archive has its commit, Git blob, byte count and SHA256; each member has its byte count, SHA256 and explicit coverage. Inclusive read spans have normalized UTF-8 span hashes, with the raw member hash retained separately. No supplied builder, checker, adapter, copied program or Lean file was executed or imported; no PDF was rendered or built.

| Report | Archive basename | ZIP SHA256 | Members |
|---|---|---|---:|
| 50 | A_Fixed_Arity_Integer_Certificate_for_Binary_Sandpile_Stabilization_Package.zip | `298dc832e14adb87eaad7afa778ebe2c23d85f71906c34b8feb2775bda122508` | 59 |
| 52 | Finite_Legal_Binary_Target_Firing_in_Periodic_Sandpiles_Package.zip | `2d9da85ef5be71fdae56182890da283e916b7073419790f60e51d081623d0803` | 102 |
| 53 | Repeated_Legal_Target_Firing_in_Periodic_Sandpiles_Package.zip | `f45cabb3d129dd366166f9fd6bf0b401abc27c62fcb8d3eb0055c580359b5f47` | 84 |
| 54 | Unrestricted_Finite_Global_Sandpile_Stabilization_Package.zip | `c8dd5b47dbefa45ce83fa566333cdbf152d91382c803af7f1cedac369ab3f545` | 75 |

## What the certificates represent

These are fixed-arity integer certificates with unbounded existential witness values, not merely fixed-duration or fixed-box families. Their one ordinary positive input is a Cantor code of a physical sandpile instance; that decoding is included in the arithmetic. Periodic tile digits are 0–5 and finite-patch digits 0–15 in the original base 32 encoding. All witness coordinates are strictly positive, with natural values represented by shifts where needed. None of the statements is an equivalence for arbitrary real witnesses or a finite-fold representation.

| Report | Represented physical event | Gates | Multiplications | Additions/subtractions | Positive witnesses | Squared residuals |
|---|---|---:|---:|---:|---:|---:|
| 50 | Finite legal global stabilization with binary true odometer | 11,469 | 4,518 | 6,951 | 2,566 | 1,491 |
| 52 | A finite legal binary prefix firing the target | 14,778 | 5,810 | 8,968 | 3,308 | 1,923 |
| 53 | A finite legal prefix firing the target, allowing repeated firing | 17,275 | 6,788 | 10,487 | 3,865 | 2,251 |
| 54 | Finite total global stabilization, allowing arbitrary finite firing multiplicities | 14,571 | 5,734 | 8,837 | 3,262 | 1,897 |

Report 50 uses a finite binary stabilizing supersolution and least action. The supplied count vector need not equal the true odometer: an already stable adjacent pair of height 5 can admit a nonzero binary stabilizing supersolution. Its support therefore cannot be used to certify target firing. The unknown prism and its zero shell provide finite support without a supplied time horizon.

Report 52 explicitly supplies chronology for a binary firing prefix. It need not end in a stable configuration and says nothing about subsequent infinite activity. The population recurrence and event masks prevent a second firing of a site, while the selected available-height constraints make each layer serializable. The stated two-site example with initial heights 12 and 4 separates ordinary repeated target firing from this binary restriction.

Report 53 removes that binary restriction by an existential radix `b=32^L` and two paid conversions of the original raw tile and patch. Its chronology argument first bounds cumulative counts inductively and then justifies carry-free digit equations; it does not assume a no-carry conclusion to obtain the count bound. The selected target event is a firing bit, rather than the low bit of a final cumulative count. The parameter bound `b >= 64(K+1)` keeps the selected legality balance below one radix. Finite target firing remains different from global stabilization.

Report 54 has no time tableau. It bounds arbitrary finite count digits by `b/16−1`, uses a carry-free stable balance and a finite zero shell, and invokes least action. The inequalities `20+6(b/16−1) < b` and `6(b/16−1)+5 < b` justify the local balance; an actual finite odometer can be accommodated by choosing a sufficiently large `L`. “Finite global” means finitely many firings in total, including the empty sequence when already stable. It does not mean an infinite evolution with finitely many firings at each vertex. The height-12 point and uniform-height-5-plus-one examples in the read text separate this event from binary stabilization and from target firing.

## Compiler and dependency boundary

The arithmetic sources expand POWER, subset, AND and spreading interfaces into a finite polynomial source. The main imported arithmetic theorem is the constructive Pell characterization of exponentiation, pinned by the packages to mathlib commit `ac77769fabe23cb237559e7f56578dbead91499f`, `PellMatiyasevic.lean` SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. That Lean proof was not reread or executed in this intake.

The Report 53 target-firing hardness discussion imports an alarm/vertex simulation and explicitly describes corrections to its published initialization. Report 54 instead pins the finite-total Report 35/U15 interface and distinguishes finite global activity from locally finite infinite activity. Its hardness-interface notes also record proposed corrections to published sandpile arguments. These are disclosed source dependencies, not newly verified primary-source corrections in this review. The conditional transfer requires the stipulated physical simulation, finite active-region and partial-gate bounds.

An effective machine-input-to-physical-code reduction is not a separately paid arithmetic compiler for the ordinary raw machine input. These high-count physical-input polynomials therefore do not improve the repository's 84/85-operation or U21 arithmetic programs. Conversely, their large counts do not negate their fixed-arity result: the raw physical-input packing and unbounded existential box/radix are explicitly paid. No optimality claim is supported by this review.

## Exact read and fresh-check scope

All 13 README entries were covered: ten unique full texts were read, and the three Report 50 README copies inside Report 52 were authenticated byte-identical and inherit the same full read. The following additional texts were read completely:

- Report 50: `science/PROOF.md` 1–144 and `science/SCOPE.md` 1–13.
- Report 52: `science/ARCHITECTURE.md` 1–96 and `independent_audit/SEMANTICS.md` 1–88.
- Report 53: `science/ARCHITECTURE.md` 1–204 and `universality/REVIEW.md` 1–121.
- Report 54: `science/PROOF.md` 1–259; `hardness-interface/REVIEW.md` 1–145, `CORRECTIONS.md` 1–41 and `PRIMARY_LOCATORS.md` 1–42.

The article spans read were Report 50 lines 120–169, 664–780 and 887–926; Report 52 lines 105–190, 808–932 and 1092–1157; Report 53 lines 71–82 and 430–575; Report 54 `article/Report54.tex` lines 114–129 and 486–643. The JSON gives the exact member paths and span hashes. Other members have hash-only coverage, except the explicitly identified arithmetic JSON checks. Supplied audit PASS reports and portability claims are historical evidence, not executions performed here.

The fresh standard-library checker `review_new_sandpiles_checks.py` inspects all 58,093 literal rows. It independently checks legal binary operations, token closure, acyclicity, all-gate/all-witness/input liveness, the operation census, and every row of the literal residual-square/sum suffix. It propagates degree bounds and independently evaluates the whole source as an exact univariate polynomial, setting the six dimension ports and three prism-size ports to one common indeterminate and every other supplied port to zero. Each source has degree at most 18 and this line has degree 18 with coefficient 48, proving exact degree 18. This line is an algebraic degree witness, not a positive zero tuple or a finite physical simulation.

The checker does not reconstruct each residual against the POWER/AND/spreading mathematical specifications. Its normal and `-O` executions agree byte-for-byte; no archived helper was executed. Checker SHA256: `585c4d46dc56e4eacda71b0439fa123c083d9470d69483f368ae221de15da4d9`. Separate check receipt SHA256: `245549c9b6825f3538cd99d11605eeee5678c7fd27fd8969457f0afc69e06f27`. Main inventory/read-scope JSON SHA256: `251808b08219a0d04a5cb41d128cca81fa52bdeef3f2219bef7450c74cba4a13`.
