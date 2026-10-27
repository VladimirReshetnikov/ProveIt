# Arithmetic Pell index divisibility: author validation

The frozen 143-line main and 49-line Checks passed their first fresh private compilation, with no failed attempt or diagnostics. This is author validation, pending ROOT's independent review/replay. The sole direct import is `ArithmeticPellIntegralSolution`; all parameters and indices are in an arbitrary `ORingStructure V` satisfying IΣ1.

`quotient_alternatives` proves a genuine Σ1 successor-induction invariant for the actual represented recurrence: exact nonnegative quotients have either the shape `X_j=1+D*u, Y_j=A*j+D*v` or `X_j=A+D*u, Y_j=j+D*v`, with `A=a+2`, `D=delta a`. The two successor cases swap those shapes using literal nonnegative coefficient formulas. This supplies `index_certificate : Bez (Y_j) D j` at every internal index, including zero; no parity oracle or standard-natural induction is used.

Two elementary scaling lemmas preserve the actual natural Bezout equations, including zero scales. They prove `ordinate_divides_index`: from `p∣m` and `Y_p²∣D*Y_m`, derive `Y_p∣m`. Both zero indices are retained. The `p=0` branch precedes construction of `B=X_p−2`; in the other branch the proof derives `X_p≥2` before the subtraction and `Y_p>0` before cancellation. Actual composition gives `Y_(p*k)=Y_k(B)*Y_p`, and the actual norm gives `delta B=D*Y_p²`. The first scaled certificate gives `Y_p∣D*k`; the second gives `Y_p∣p*k=m`.

The public `relaxed_auxiliary` and `relaxed_auxiliary_tsub` endpoints derive a positive internal `m` with **both** `p∣m` and `c∣m`, `f=xcoord m a`, and `i*c*c=delta a*ycoord m a`, from the actual positive norm, `c=ycoord p a`, and `(a+2)*delta a*delta a<c`. They retain the same `m` returned by IntegralSolution. No desired divisibility, coprimality, cubic congruence, power theorem, squarefree factorization, or external Pell oracle is assumed. Later target-index identities, simultaneous carrier witnesses and HA equation equivalence remain outside this packet.

Checks cover both quotient shapes, indices zero/one, both zero-scale certificate lemmas, `p=0`, `m=0`, and both actual norm input forms.

## Frozen source and replay pins

| Artifact | SHA-256 |
| --- | --- |
| `ArithmeticPellIndexDivisibility.lean` | `c2d78a3fe1176faeed285dcf0946c7ce64483663c6a3f8d1903152349b8ae226` |
| `ArithmeticPellIndexDivisibilityChecks.lean` | `bbfeb73a763a6954ed04176dfa8e21485aa27650511d7d982e02b923e58b3ca4` |
| main `.olean` | `72c5c900c413090db7674b4b7832b5d530e820b45a9bc1c817f4abbb22351986` |
| Checks `.olean` | `58b46128482a46cadea47c8ce8a4fe1378080815b667543fd708661721b6c97f` |
| replay JSON | `3479e25fd6ff0c15bf33cf32d00e1ac5d741fe4c9ed09fa8e84e66a0b7deebba` |
| 16-file `author-replay/FILES.json` | `81dfc99c6c98bc782327522c9c5442846677933541615d536c9a19a2c5a386db` |
| executed author driver | `d3ed7d59f3171584a893f0cb67f7a00847f157c8ff875812041a68db9fce4c61` |
| freeze driver | `c3d89134993655839f22f847addb3d435962050110c971afa881c701a8733e68` |

The private provider is `/tmp/arithmetic-pell-index-divisibility-author-kvlg002p/lib`. Both new outputs are regular files; shared objects and accepted sources were not modified.

## Exact cache and execution scope

The unchanged approved proposal SHA is `9d6884265c4302389403316f795c7d37d5a27acdd36ac40ce8067919dc3d3a4b`; original inventory SHA is `ab6f041ac993f09ef46965feb906c3445da26d9c509a13ca7522c1b4a57a8274`. The accepted IntegralSolution supplement `1733d27dc9af570a50fc5983afdfb9b63c1c1ef8531f0419a547be23758dc60a` selects the byte-identical ROOT provider `/tmp/arithmetic-pell-integral-solution-root-awcmdrel/lib` only in memory. The original proposal/inventory and all accepted dependency bytes remain unchanged.

The exact selected closure has 102 custom modules (95 Foundation), 387 custom artifacts, and 38 boundary modules with 114 total artifacts (38 primaries plus 76 companions). All 501 actual first-provider artifacts are authenticated; zero prerequisites were refreshed. The driver checks original/supplement pins, exact selected source headers and reachable DAG, implicit Init and all boundary names, and actual LEAN_PATH first-provider precedence. This reuses authenticated package-boundary objects and does not claim a fresh whole-Foundation build.

Both complete sources and the executed driver `/tmp/arithmetic-pell-index-divisibility-author.py` were read before execution. Both input snapshots were saved before its first compiler command. The compiler is Lean4.32 at `/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`, SHA `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`, using `-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1` and fresh private outputs. The 512MiB reserve was enforced before and after; final free space was 1,167,011,840 bytes.

Main/Checks passed in 7.801/2.341 seconds with peak RSS 1,835,100/1,795,680 KiB. The main log is empty; Checks contains exactly seven reports, each listing only `propext`, `Classical.choice`, and `Quot.sound`. Both exit codes are zero and no warnings/errors/`sorryAx` occurred. The execution finally rehashed 1,293 observed paths; the separate freeze checked 1,324 comparisons over 1,318 actual paths.

The durable `arithmetic-pell-index-divisibility-author-replay/` bundle preserves the sole attempt's full sources, driver, input/authentication/provider metadata, state, logs/timings, original plan/proposal, accepted supplement, freeze driver and freeze-authentication observations. No failed compiler attempts occurred. No Git or shared documentation was changed.
