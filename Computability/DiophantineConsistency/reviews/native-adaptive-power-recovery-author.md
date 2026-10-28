# Literal adaptive power recovery — author receipt

PASS. I authored and fully read both new modules, their focused checks,
the private replay driver, and the final proof delta before the successful
run. This is author validation, pending independent review. Root authorized
the split into first-index/projection and growth/recovery pairs. No accepted
source, shared object, umbrella, coefficient, display, or Git state was edited.

## Exact proved scope

`NativeAdaptivePowerProjection.adaptive_projection` uses the original
positive integer inputs, `PortBox`, beta>=15, literal q/target/transport,
A0=A1=0 and Fs=Fa=1. It derives the same actual classified main ordinate,
first index n>=25 with **2n=R+1**, 4XY²|v, q²Y|v, q|3X, and
H|3(X−2^R), where v=k−R−1 and H=4Y(X+1)+3. The explicit ring witnesses
retain the case 3|q. No assumed nonnegative quotient or first index is used.

`NativeAdaptivePowerRecovery.adaptive_X_eq_two_pow` adds precisely the
actual k=eta+zeta relation with both inputs positive. It derives
**X=(2:Int)^R.toNat**, retains q|3X, and returns the first-index and
divisibility data above. The ratio proof retains its factor two. For X>=2
it derives 2^R<Y using 9^16>6*8^16; for X=1 it derives 2^R<=4Y and a
contradiction modulo eight. It never uses a source certificate, supplied
classification/index, oddness, q|X, X>=2, or power premise. MF remains the
already once-shifted port from the original target.

This proves an all-positive soundness step from the literal cuts. It does
not yet derive those four unit equalities from the complete graph product,
exclude the exceptional factor three via a Mersenne coefficient, restore
all source coordinates, prove canonical completeness, or establish a new
polynomial/HA endpoint or operation/degree metric. Those are separate tasks.

## Frozen sources and fresh objects

| New source (under `Lean/DiophantineConsistency`) | Lines | SHA-256 |
| --- | ---: | --- |
| `NativeAdaptivePowerProjection.lean` | 153 | `92a4d01435c031ea51706162503e5e51239c39eb5eebdfcaac587c933ef09c84` |
| `NativeAdaptivePowerProjectionChecks.lean` | 35 | `12c4e4757338c5b724e913226f8d9086664b04650d68a385ee535b8bf22bb29d` |
| `NativeAdaptivePowerRecovery.lean` | 233 | `cd97a608e86cefcba299f53f76150112c63898327f82460c7daf78b229d6f0ae` |
| `NativeAdaptivePowerRecoveryChecks.lean` | 44 | `4ee03a473e71b017204ae98440f09659dd832e9a6251031d36becfbec61d8c3d` |

Final private library: `/tmp/native-adaptive-power-tr0wfda0/lib`.
Objects in the same order have hashes:

```
cb92cdc6231cfd7a4299424f2476aa4bb15a271cf4bf6e667b575fb15ac52c8b
c0c988661de8228940aae29a1068c39438a9507ffab0876d5585bcc0ec187db0
66b65a620d5e293de29abe9fff4da5b88d4023a47c647f8e97cf0ec9458450e4
efe9d00179befb52dabf05ad9d8d24b54cb1960314db2a5a00e9906285fc2f8f
```

All four outputs were absent before compilation and are regular files,
not symlinks. The final durations were 5.553, 2.715, 13.216, and 2.621
seconds; maximum RSS was 3,278,448 KiB. Both main logs are empty. All
four exit codes are zero. The checks report 14 declarations: only
`propext`, `Classical.choice`, and `Quot.sound` occur (two elementary
growth lemmas use only `propext` and `Quot.sound`).

## Authentication, commands, and preserved attempts

The exact driver is preserved in
`native-adaptive-power-recovery-replay/driver.py`, SHA
`6e70e8e9200de0b5c71498b4b0e941f478971e734e08e32b6ed898ae7ccc2c87`.
It uses the pinned Lean 4.32.0 binary with
`-M6000 -j1 -DElab.async=false -o PRIVATE/module.olean SOURCE.lean`.
There was no prerequisite or Foundation build. The 512 MiB reserve was
checked before every command and after completion; final freeze retained
2,137,047,040 free bytes.

The original approved Strong author provider remains explicitly recorded,
including source/object hashes and root's separately reported byte-identical
independent acceptance. The imported cache has 30 custom source/object
pairs and 22 actual external names including Init, with all 66 companion
objects. All 157 selected input pins were checked before and after the
run. Recovery uses this run's freshly author-validated Projection object;
that is not represented as a previously independently accepted cache item.
Reused custom modules are symlinks to the immutable authenticated providers;
the four new outputs are private regular files. The scope is these four
leaves, not a new package-wide dependency rebuild.

All three attempts are preserved in the durable bundle:

1. `ervsqrik`: Projection failed after 5.527 seconds due to a nested tactic
   scope in the Pell positivity proof inside its statement. The explicit
   `mul_pos` proof repaired this elaboration issue.
2. `xalobwgr`: Projection and its checks passed. Recovery failed after
   35.804 seconds on explicit cast/congruence/exponent normalization and
   a missing local positive-Q fact, then a broad final `nlinarith` reached
   the ordinary heartbeat limit. The log and source snapshot are intact.
3. `tr0wfda0`: all four passed cleanly after explicit casts, dependent
   `simp only` congruences, exponent normalization, correct `dvd_abs`
   arguments, and narrowly scoped arithmetic. No mathematical premise,
   resource cap, or theorem objective was weakened.

The driver provider-path typo was caught in the mandatory source read and
corrected before any execution; it produced no failed run. No source
changes followed the final successful run.

The full packet `native-adaptive-power-recovery-replay.json` has SHA
`480e34f77e08ca6d26a9c1ead6839a58baec7b36e9ac8c11f0019aba0384d056`.
The 34-file durable text bundle plus packet are pinned by
`native-adaptive-power-recovery-replay-files.json`, SHA
`23a7b5fe1a733023b4c0dc18c3f3341d3c3570f63fec36f9957cb1240e9369ff`.
It includes all inputs, states, exact source snapshots, command records,
stdout logs, timing files, driver, frozen proposal/cache audit, and freeze
script. Final source/object/log hashes were rechecked while freezing.
