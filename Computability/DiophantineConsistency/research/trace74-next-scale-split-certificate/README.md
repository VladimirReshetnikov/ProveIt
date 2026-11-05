# Attempted serial B=65537 split certificate

This packet derives 34 Lean sources from the exact pinned
[B=65537 certificate and trace](../trace74-next-scale-kernel-certificate/README.md):
one common module, 32 predecessor-linked transition modules, and a final
module intended to prove the initial state, the 32-bit index, the full
folded transition chain, and the Bézout-derived `Nat.Coprime` result. The
deriver checks that all state and transition declarations agree with both
the parent source and trace; [`manifest.json`](manifest.json) pins every
generated source and extracted declaration.

The sole serial run stopped at its **first stage**, `Trace74SplitCommon`,
after the stage's 30-second wall timeout. Lean emitted no output and no
object was produced. The receipt records 30.078 seconds, 852,728 KiB
Lean child peak RSS, an actually observed 2 GiB cgroup limit with zero
swap, zero OOM/max events, and passing post-run source/input guards.
The [stage receipt](observations/Trace74SplitCommon/result.json), empty
[Lean log](observations/Trace74SplitCommon/lean.log),
[outer log](observations/outer/Trace74SplitCommon.log) and
[outer state](observations/outer-state.json) preserve the failure.

As instructed, the runner did not attempt any later stage after that
timeout. Consequently no split transition, final chain, or full
`Nat.Coprime` theorem was checked in this run. The timeout is not a
mathematical failure; its precise cause was not diagnosed. In particular,
the successful [isolated transition checks](../trace74-next-scale-transition-bench/README.md)
do not establish this common module or the complete chain.

## Guards and scope

For every attempted stage, `stage.py` verifies the cgroup's actual memory
and swap limits, pins the Lean binary and direct Mathlib import, checks
the parent source and trace, all 34 generated source hashes, the exact
direct import and its first matching path, and all prior fresh output hashes
before and after Lean. It imposes `-M1800 -j1` and a 30-second subprocess
timeout, records the result, and accepts only exit 0 without warning,
error, or `sorryAx`. `run.py` launches stages serially and stops at the
first non-passing result. These guards do not authenticate the full
transitive package or dynamic-library ancestry and cannot exclude changes
between observations.

The generated sources and scripts are retained for inspection; this is
an attempt receipt, not an instruction to rerun without coordinating
the shared Lean slot. The runner refuses to overwrite its existing
observations and temporary output. Even a future successful closed Nat
certificate would still need symbolic coefficient/modulus bindings and
transfer to represented model arithmetic; it would not itself prove the
actual `B=590069` gcd, graph zero, or iPRA endpoint.

```text
7c2ee2ed8c416e0702aaae201370e963e8d8a5874e6d6c1bd3a4cffe36d8a70b  derive.py
f8651b24e180f95e356d3cff6f6d7a4126e40c5d935adcecdfeeda30d8ff80c2  stage.py
42269e3233c2964194cca621d1f907859ae22641304cbed58fd0db2d0276f776  run.py
714dfabeeddd3d3f5311fa6f86bdd777eebf373a4719348688ed06b5a8939099  manifest.json
c3e0ab27519c408cc7499f2c87fbd59a479c2a5f3c335fe6533ec2bb75969be9  src/Trace74SplitCommon.lean
```
