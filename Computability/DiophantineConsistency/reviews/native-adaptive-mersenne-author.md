# Adaptive Mersenne base recovery: frozen author checkpoint

2026-10-26, author `/root/complemented47_review`. The complete final main,
focused checks and driver were read before execution. Final private two-leaf
replay passes; independent review/acceptance is separate. No accepted source,
shared object, equation, coefficient tuple, documentation index or Git state
was changed.

New files under `Lean/DiophantineConsistency`:

- `NativeAdaptiveMersenne.lean`, 181 lines, SHA256
  `555c1c5cf659d00499b1f7d0952483e9269754fd965f4f56aaa06d7e875a978c`.
- `NativeAdaptiveMersenneChecks.lean`, 38 lines, SHA256
  `0e14bc6f9534cc79e5bc2df40ad396daa21f948b2060df4bd6a5f4fad97627c4`.

The sole main import is frozen `NativeAdaptivePowerRecovery`. The original
four Power sources remain unchanged.

## Exact proof scope

For natural `d≥4`, the generic theorem proves
`¬ ((2:ℤ)^d−1) ∣ (3*2^u−1)` for every natural u. Exponent division is an
actual geometric-sum divisibility identity. For `r=u%d≤d−2`, the residual
`3*2^r−1` lies strictly in `(0,2^d−1)`. For `r=d−1`, subtracting the modulus
leaves exactly `2^r`, again strictly in that interval. The r=0 and high
remainder branches are both retained.

Given integer `q>1`, `(2^d−1)∣q−1`, and `q∣3*2^R`, the next theorem
first excludes `3∣q`: writing q=3m permits cancellation of the *literal*
nonzero factor 3, and positive m is classified as a power of two. The
Mersenne lemma then contradicts the q−1 congruence. Only after that exclusion
does the accepted explicit `bezout_three` identity give `q∣2^R`.
`Nat.dvd_prime_pow Nat.prime_two` supplies a positive exponent u≤R, and the
actual remainder theorem proves d∣u. Thus q is the positive radix power
`(2^d)^N` with N>0 and d*N≤R. Positive integer-to-natural casts and the
u=0 boundary are explicit.

`adaptive_q_power_radix` retains every original positive literal cut and
`PortBox`, adding only the actual Mersenne width identity. It derives beta≥15
from d≥4 and invokes the accepted all-positive power-recovery theorem; it
does not receive X=2^R, q|X, an index equality, oddness or a restored source
as a premise. It concludes

```
X=(2:ℤ)^R.toNat ∧ ¬(3:ℤ)∣q ∧ q∣X ∧
∃N:ℕ, 0<N ∧ q=((2:ℤ)^d)^N ∧ d*N≤R.toNat.
```

`current_width_q_power_radix` fixes the current width **47*2011=94517**,
retaining `ports 0=(2:ℤ)^(47*2011)−1`. The other ports remain the same
arbitrary `PortBox` inputs, with MF once shifted at `ports 3`. This is an
actual-width arithmetic specialization, not a fresh proof of the concrete
four-port constants. It uses no historical compact44 tuple or old source
client. Source restoration, canonical converse, full low-degree graph
binding, metrics and internal HA/PA equivalence remain separate.

Focused checks cover u=0, high remainder, a repeated-period high remainder,
the necessary q>1 boundary, impossibility at exponent zero, the actual
94517 positive-radix/exponent-bound client and d|u. Eight principal theorem
axiom audits are included.

## Cache and replay

Approved proposal SHA256
`6435d941d6a7beebc5fdb90d18db24e8e24d0e4be39f1c1ec56b952f1ab77b39`
and read-only cache audit
`235165731675608064bfc92aa916b45cfecb6981016e9e3b6cf213a0673b9c3e`
remain frozen. The provider is root's accepted Power replay,
`/tmp/native-adaptive-power-root-hgpurypn/lib`, record
`9473432e98100b64f511acd679717a4ada8ccf4089d9ecfa206b40f66d51f495`.

The new private replay authenticates **32 cached custom source/object pairs,
22 explicit external names including Init, and 66 external companions**.
The two Power main objects are independently accepted inputs. There are 171
execution pins, checked before and after; source import headers and the
custom/external boundary are checked. API sources read as guides are pinned
as well. No Foundation, prerequisite or external package build occurred.

Final private directory: `/tmp/native-adaptive-mersenne-8cbwhqb1`.
Both commands use the pinned Lean4.32 compiler with
`-M6000 -j1 -DElab.async=false`, one Lean thread, no `LEAN_SRC_PATH`, private
regular non-symlink output files and the 512 MiB reserve guard. Main/checks
pass in **4.639 / 2.827 seconds**, main output empty, no warnings/errors.
Main peak RSS was 3,238,444 KiB. All eight reports use only `propext`,
`Classical.choice`, `Quot.sound`.

Final objects:

- Main: `66e0eb6f9a8838fb32110c3046a5615418588b9237050aaf12c7551c3dc6020b`.
- Checks: `46b8823acef0069afeaece29d6ab1ac89e41bd8944a99ab92a6032b2e2ab7f47`.

Driver `/tmp/native-adaptive-mersenne-driver.py`, SHA256
`86cfe20f42642ec33c4fea3e43b48f075aad767478b17eb3b98e2c3d058ca1a7`.
Final inputs SHA256
`35df4842f5d22f6da1ea18c2cf8c2ef605887dc2ac4c8c0b8a6ae1f08a6e116e`;
final state
`19bd13aabbf6edbd38705da187a478050379d4fc6f0c950105c6927eace24273`.

Durable replay `native-adaptive-mersenne-replay.json`, SHA256
`3f04a37e270510b97caba9f4c208158ee4ccdf6d83594f0a7e393600c41a99fd`,
contains full inputs, commands, output/axiom pins and both attempts. The
17-file manifest `native-adaptive-mersenne-replay-files.json`, SHA256
`583934a7e03fd071ad4f330a1bc449481aa30a1eabd36a61c808f78cfbf61c7c`,
binds the durable `native-adaptive-mersenne-replay/` bundle: both source
states, inputs/state files, logs/timings, proposal/audit and complete drivers.

The first main attempt `/tmp/native-adaptive-mersenne-hp9isu2s` failed on
unwanted divisibility-instance goals from `convert`, a wrong sign in a
`linear_combination` proof command, and unspaced `<i` parsing. It also
reported the unused generic width binder. Corrections use explicit integer
divisibility witnesses, the correct Bézout equality combination, spacing,
and an underscored unused binder. Public mathematical statements were
unchanged. The failed log/source state is retained; it is not accepted as
a compiled proof. The second main and first executed Checks both pass.
