# Round 16: pinned comparison frontier

Snapshot: `f4d8db99e060339f3306a04d507c35bc1d0d68c5`, main at 2026-10-24 23:45:29 UTC.
Commit URL: https://github.com/VladimirReshetnikov/ProveIt/commit/f4d8db99e060339f3306a04d507c35bc1d0d68c5

The last prior local comparison was `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`. This snapshot is much newer than that baseline and includes all eight new incoming archives from commit `5f3379063df18910a981d2e6cae6aee91b79cf4d`.

## What genuinely changed

- `18a04bee9e8d84166151f464f08b9ffc1c334080` adds `candidates/ten-positive-gap-fusion`: six complete positive equations, at operations/degree 89/288, 91/283, 92/278, 94/262, 96/258, 97/254. These coincide in metrics, and largely in the underlying constructions, with the previous delivered Paired Guards / Centered Carriers family. The commit explicitly attributes overlap. Do not repackage these as a fresh round-16 mathematical advance.
- `aaa1051053d506097bfcd33b0061d4599d00fd74` changes five direct circuits by the exact identity `(q^3*q)*(q-1)=q^3*(q*(q-1))`, reusing an already-live product. One multiplication is saved. Their new operations/degree pairs are 97/258, 98/254, 96/258, 97/254, 94/262; the polynomial itself does not change.
- `0ca3812ae91720265cc808586d0789c24ea6c7b6` preserves a complete 89/288 one-page alternative. The canonical CURRENT_EQUATION still describes the 92/283 display, not the entire current frontier. Do not take this convenient landing page as the newest or best result in every metric.
- New incoming natural quartic and unrestricted-integer families substantially supersede the round-15 comparison points. All source provenance below uses this new pin, even though the incoming packages' own comparison snapshots were the prior pin.

## Actual inspected frontier

These are branch-specific comparisons, not global minimality claims.

### Direct natural quartics

| Source | Variables | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| Shared Pell Bound, primary | 261 | 194 | 4 | 31,679 | 85,566,955 |
| Shared Pell Bound, sparse | 292 | 225 | 4 | 6,140 | 83,933,334 |
| Shared Binomial, selected | 319 | 254 | 4 | 10,283 | 86,842,335 |
| Shared Binomial, lower height | 320 | 255 | 4 | 13,828 | 15,248,812 |
| Unified Binomial, Cantor | 329 | 253 | 4 | 12,210 | 86,844,780 |
| Residue Compiler | 332 | 263 | 4 | 11,823 | 85,243,454 |
| Residue Compiler, sparse/even | 333 | 264 | 4 | 4,357 | 209,508,384 |

Nonnegative means zero is allowed. 261 is not an unrestricted-integer count. The primary 261 point trades density for fewer variables. The 292 point strictly dominates the 319, 329 and 332 points in all listed varying metrics, but the latter remain important as source architectures.

### Direct unrestricted-integer quartics

| Source | Variables | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| Unified Binomial / Even Indices | 442 | 290 | 4 | 4,652 | 128,446 |
| Weak Carriers / Shared Signs | 478 | 305 | 4 | 5,484 | 511,326 |
| Cofinal Witnesses | 508 | 308 | 4 | 6,545 | 996,521 |

The 442 point dominates both other incoming direct integer points and the prior local 489/493 points. It is still not a global minimum-variable quartic: separate native coefficient architectures have much smaller variable counts and enormous fixed constants.

### Eleven unrestricted-integer circuit frontier

Operations count live binary additions, subtractions and multiplications, including squaring and multiplication by fixed integers. Intermediate registers are abbreviations, not extra unknowns.

| Source and circuit | Operations | Exact degree stated/proved in source |
|---|---:|---:|
| Shared Binomial, lowops/product11_degree966.json | 111 | 966 |
| Shared Binomial, lowops/product11_degree882.json | 112 | 882 |
| Unified Binomial, norm/integral_direct_paired.json | 118 | 488 |
| Unified Binomial, norm/integral_centered_paired.json | 119 | 464 |
| Unified Binomial, norm_weak/weak_integral_direct_paired.json | 124 | 456 |
| Unified Binomial, norm_weak/weak_integral_centered_paired.json | 125 | 416 |

Shared Binomial's 126/440 and Height One's 122/464 are dominated by the above existing points. Their constructions may nevertheless enable new cross-combinations. The complete six-port native tuple must remain coherent; source34 and compact44/indexed tuples are not interchangeable coefficient-by-coefficient.

### Height one

`ConZFC_Height_One_and_Degree_464` supplies a 7,431-variable unrestricted-integer quartic, 34,086 monomials, constant 1, with every nonzero coefficient ±1. This is a different objective and already reaches the least positive possible coefficient height. No smaller-variable assertion follows.

## Verification performed for this review

`BASELINE_CHECKS.json`: 381 selected source files and incoming artifacts verified against pinned Git blob SHA-1, with SHA-256 also recorded. All eight ZIPs were safely extracted after rejecting traversal/symlink entries. `INCOMING_CHECKS.json` isolates the archive receipts.

`audit_incoming_data.py` is newly written, data-only audit code. It imports no downloaded source. Its receipt `INDEPENDENT_INCOMING_DATA_AUDIT.json` records exact re-expansion of every coefficient for ten incoming quartics, exact degree four, all occurring variables, and the live operation census of 22 circuits. All checked identities pass. Circuit degree values were read from their exact source proofs and data but not independently replayed by this audit. No downloaded producer, checker or verifier was executed.

Written cap, self-radix, modular-residue and shared-binomial arguments were inspected. This is not an end-to-end re-verification of every inherited logical/Pell calibration. No refutation search, solvability claim, or consistency assertion is made.

## Local artifact map

Archive files: `docs/incoming/ConZFC_*_2026-10-24.zip`.
Extracted package root: `extracted/<archive stem>/<package root>/`.
All roots equal the archive stem except:
- Residue Compiler inner root is `con_zfc_residue_compiler_2026-10-24`.
- Paired Guards inner root is `ConZFC_Paired_Guards_Centered_Carriers`.

Source formulas and exact interface cautions are collected in `MATHEMATICAL_OPPORTUNITIES.md`. The authoritative original source artifacts remain unmodified.
