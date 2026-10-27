# Arithmetic Pell strong divisibility: author validation

The frozen 196-line main and 46-line Checks pass fresh private compilation. This is author validation, pending ROOT's independent source review and replay. Every index and parameter is an element of an arbitrary `ORingStructure V` satisfying IΣ1. No standard-index induction, externally classified fundamental unit, supplied coprimality, or desired index divisibility is assumed.

The only direct imports are `ArithmeticPellRecurrence` and `ArithmeticGcdNormalization`. With the actual represented ordinate `ycoord` and actual represented `gcdValue`, the main proves

- `strong_divisibility`: `gcdValue (ycoord m b) (ycoord n b) = ycoord (gcdValue m n) b`;
- `y_dvd_iff`: `ycoord m b ∣ ycoord n b ↔ m ∣ n`, including either index zero;
- `scaled_common_divisor`: divisibility of both `T*ycoord m b` and `T*ycoord n b` implies divisibility of `T*ycoord (gcdValue m n) b`, with no positivity premise on `T` or the common divisor.

The actual norm gives a natural Bezout unit certificate for `xcoord m b` against any divisor of `ycoord m b`, including divisor zero when permitted. Addition and that certificate yield the additive Euclidean reduction for common divisors. A bounded two-variable Σ1 invariant is proved by internal order induction on the sum of the indices; both subtraction branches retain their order justifications. Actual addition/growth yields strict monotonicity and then index divisibility reflection. The scaled result multiplies the gcd certificate rather than cancelling a possibly zero scale.

The focused checks cover zero/one indices, the diagonal, the zero-divisor norm certificate, zero scale, and arbitrary scale/common divisor. Large-c index forcing, the relaxed-integrality endpoint, and HA equivalence are outside this packet.

## Exact frozen sources and outputs

| Artifact | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/ArithmeticPellStrongDivisibility.lean` | `a98ec37a7c16151236e8dacdd433c6ecd2e7d870c7a58c4b710267f6c9fd6c92` |
| `Lean/DiophantineConsistency/ArithmeticPellStrongDivisibilityChecks.lean` | `589bd12f7607f6f462d15427796dfb9e161452fe213434e776169fe3dc215ab6` |
| main `.olean` | `51fe8bb3ed563268ec08c8e00a42a46825daac58f58874228713895b71de2385` |
| Checks `.olean` | `96e243fff405cb5f9fc4a933f68a431cf3d9f9a6535422b4b241ca426236ee45` |
| replay JSON | `c85cf2c33f09b8aef36719430cffefcc8a1c4d51a19f3aabd8feaae1457dc4c7` |
| 24-file `author-replay/FILES.json` | `16d21f1046d0fd0040530a4326dffd7507c2fe62cbcab8f55190b01d5505900e` |
| executed author driver | `e2db5af0d125a6bb91559cdfae87e41d47b051dd97fe341706468cb91508617c` |
| freeze driver | `bf8f2b01141273c26e5ca4bc549cc50adac735cbdf04581de1b2292e944d8d8c` |

The successful private provider is `/tmp/arithmetic-pell-strong-divisibility-author-rkedmwpb/lib`. Both new outputs are regular files. No shared object was changed.

## Authentication and execution

The unchanged approved proposal is `research/arithmetic-pell-strong-divisibility-plan.md` (`0f72dbf8ff86770d83c8564fcc86c59bfe9e053cd219d81e88e2c3976250eb8a`). The unchanged exact cache plan is `research/arithmetic-pell-strong-divisibility-cache-plan.json` (`6540842617bdadcad5f9d28b42447ff6b3ed9b3ad28d225b323a808997bd4015`). Its separate first-provider map is `37335c562ed6c82eba945bcfa1e04033828d047aa668dce415f5de16cb082a08`.

The selected closure contains 97 custom modules (95 Foundation), 382 custom artifacts, 38 explicit boundary modules and 114 total boundary artifacts (38 primary objects plus 76 companions). Thus 496 actual first-provider artifacts were rehashed. No prerequisite was refreshed. The driver re-parses all selected source headers, checks the exact reachable DAG and boundary names including implicit Init, checks every selected source/object and inherited plan pin, and verifies the actual LEAN_PATH first providers. The Gcd object is the accepted ROOT object at `/tmp/arithmetic-gcd-normalization-root-pnbeaddq/lib`; the Recurrence object is its accepted independent peer object. Their exact pins/provenance remain in the plan. This reuses authenticated package-boundary objects; it does not claim a fresh whole-Foundation build.

The compiler is `/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`, SHA `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Each command uses `-M6000 -j1 -DElab.async=false -o <fresh-private-output> <source>`, with `LEAN_NUM_THREADS=1` and only the private selected overlay plus recorded boundary paths. The full driver and both inputs were read before each attempt. Both source snapshots were saved before its first compiler command. The driver enforces 512MiB free reserve before and after execution; final free space was 1,253,371,904 bytes.

Successful main/Checks times were 7.072/2.475 seconds, with peak RSS 1,820,252/1,789,528 KiB. Both exit codes are zero, the main log is empty, and Checks contains exactly seven reports, each listing only `propext`, `Classical.choice`, and `Quot.sound`. No warnings, errors, `sorryAx`, extra imports, or increased caps occurred in the successful attempt. Final execution rehashed 1,060 observed paths. The independent freeze verification made 2,166 comparisons over 1,481 actual paths.

## Preserved attempt history

Attempt 1, `/tmp/arithmetic-pell-strong-divisibility-author-uug3229j`, failed only in the final `gcd_scale` quotient witnesses: rewriting `x` or `y` globally also rewrote an argument of `gcdValue`. Its main log and both input snapshots, including the unexecuted Checks, are preserved. Attempt 2 replaces those two global rewrites with multiplication applied by `congrArg`, then ring associativity. No statement, premise, import, induction invariant, or resource cap changed. The second pair passes cleanly.

`arithmetic-pell-strong-divisibility-author-replay/` preserves both attempts' drivers, source snapshots, states, input/authentication/provider metadata, logs/timings, the approved plan/proposal, freeze driver, and freeze-authentication observations. The replay JSON pins the original regular outputs, all final reports, and this durable manifest. Frozen accepted dependencies, shared documentation, and Git were not edited.
