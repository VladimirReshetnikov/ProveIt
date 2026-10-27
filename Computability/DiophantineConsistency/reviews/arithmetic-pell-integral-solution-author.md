# Arithmetic Pell integral solution: author validation

The frozen 169-line main and 41-line Checks pass fresh private compilation. This is author validation, pending ROOT's independent review/replay. All parameters and indices are elements of an arbitrary `ORingStructure V` satisfying IΣ1. The only imports are `ArithmeticPellCommonUnit` and `ArithmeticPellStrongDivisibility`.

The actual public `integral_solution` theorem assumes `p,i,f>0`, `c=ycoord p a`, the additive relaxed norm `(i*c*c)²+delta a=delta a*f²`, and `(a+2)*delta a*delta a<c`. It derives a positive internal `m` with `p∣m`, `f=xcoord m a`, and `i*c*c=delta a*ycoord m a`. `integral_solution_tsub` accepts the literal truncated norm and derives the justified additive form from `f>0`.

The proof invokes actual common-unit classification/composition once. It derives `e*p∣n` before constructing `m=p*k`. The intermediate `large_index_multiple` uses actual gcd/strong divisibility, proves positivity of the gcd index, excludes a proper divisor by `2*g≤e*p`, and combines actual doubling growth with the large-c bound. There is no supplied common unit, index multiple, coprimality, minimality, or standard-Nat classification premise. The same original-base coordinates are recovered by the already proved all-internal composition identities.

The further `c∣m` conclusion, cubic congruence, full relaxed auxiliary theorem and HA endpoint remain outside this packet. `y_lt_x` includes index zero; strict doubling retains a positive-index premise. Checks exercise these, the intermediate theorem at `M=1` under its complete premises, and both actual norm endpoints.

## Exact frozen pins

| Artifact | SHA-256 |
| --- | --- |
| `ArithmeticPellIntegralSolution.lean` | `358d56e418a32843cd93c58266f406d49db3ae9373561ffb879307d7a0e927d1` |
| `ArithmeticPellIntegralSolutionChecks.lean` | `e6b121a8e0188dd1f689dddbf72e8cf1330822ffe01c3ec8a4277d01b08ef0d2` |
| main `.olean` | `7814dd0443e0438a5f110beca8dee926e32a5104fa96f279936aeeaa9f29a1af` |
| Checks `.olean` | `e74b9b5ba112d456b5138d1054b6a0f02fd6d62bf92c99707094ebd530df79e6` |
| replay JSON | `7c71696cfc3682163f91bedeedd2e4c26f757cd887e196234d000934e1b33110` |
| 25-file `author-replay/FILES.json` | `7fc8c5e8f8a707603278db924eedf50ed81b9e3cc8c58d983b080c1061059ff1` |
| executed author driver | `4012bb3e08657b68de04d554235139daa29135e023ff9bff5a5cd4793f12cedb` |
| freeze driver | `9ea77c9c8a2eedeaffb751678397e80e3d3ae152a967ac2c2964260e500a4fe2` |

The successful provider is `/tmp/arithmetic-pell-integral-solution-author-4aqhmxqy/lib`; both new outputs are regular files. Frozen dependencies and shared objects were not modified.

## Complete selected cache and execution

The original approved proposal SHA is `a99ddd196895b3dfabf41a976d9628e69481c308ab0dcef31a7abdcfda7e98a8`; the original cache-plan SHA is `27b365f34e47feeaaaa6e32c3987ed2cebbb3a6e333673c4d4717b52b3afcee2`. Both remain unchanged. The separate accepted-StrongDivisibility supplement `05fefd83261e8d29c8dd652190f92e0f952f049cfad6cc9f00dbfd1509168aa9` replaces only that provisional provider path in memory with `/tmp/arithmetic-pell-strong-divisibility-root-mljfsamm/lib`, whose source/object bytes equal the planned author bytes. CommonUnit uses its accepted ROOT provider `m1m65ryx`; Gcd uses accepted ROOT `pnbeaddq`. All exact provider paths and source/object records are in the inputs and provider metadata.

The exact selected closure is 101 custom modules, including 95 Foundation modules, with 386 custom artifacts and 38 explicit boundary modules. The latter have 114 total artifacts: 38 primaries plus 76 companions. All 500 actual first providers are authenticated. No dependency was refreshed. The driver checks all original and supplement pins, selected source headers, the exact reachable import graph including implicit Init, every source/object pair, and actual LEAN_PATH first-provider precedence. Reusing authenticated boundary objects is not a claim of a fresh whole-Foundation build.

The fully read driver `/tmp/arithmetic-pell-integral-solution-author.py` uses Lean4.32 at `/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean` (SHA `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`) with `-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`, and fresh private outputs. Both complete inputs and driver were read before each attempt. Both source snapshots were saved before each attempt's first compiler invocation. The 512MiB reserve was checked before and after compilation; final free space was 1,206,079,488 bytes.

Final main/Checks took 4.460/1.927 seconds with peak RSS 1,810,160/1,795,648 KiB. Both exit codes are zero. The main log is empty; Checks has exactly five reports, each containing only `propext`, `Classical.choice`, and `Quot.sound`. The successful logs contain no warnings/errors/`sorryAx`. The execution rehashed 1,220 observed paths; the separate freeze checked 2,487 comparisons over 1,646 actual paths.

## Preserved attempt history

Attempt 1 (`/tmp/arithmetic-pell-integral-solution-author-rr0u8ij6`) failed after 4.305 seconds only because simplification retained the internal numeral `1+1` when the goal used `2` in the proper-divisor quotient bound. Attempt 2 explicitly uses `one_add_one_eq_two` there and passes both files. No theorem statement, premise, import, cap, or mathematical argument changed.

The durable `arithmetic-pell-integral-solution-author-replay/` bundle contains both attempts' source snapshots (including the first unused Checks), drivers, input/authentication/provider metadata, states, logs/timings, unchanged proposal/plan, accepted provider supplement, freeze driver and freeze-authentication observations. The replay JSON records exact final source/object/log pins and all five reports. No Git or shared documentation was changed.
