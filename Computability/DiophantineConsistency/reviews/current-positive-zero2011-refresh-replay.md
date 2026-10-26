# Scoped refresh after the five incoming proof changes

PASS for the authorized fifteen-command refresh at source snapshot
`8d1729b5d58e338308f2a6521c7416bd24ebef55`. Every selected source was compared
against that exact Git snapshot, and its SHA-256 was verified before and after
execution. Later HA files and documentation added outside this graph were not
part of this run. This is a **limited changed-source refresh**, separate from
[the completed 361-module validation at 09eaa](current-positive-zero2011-closure-replay.md).
It is not a fresh validation of the entire merged dependency closure.

The reviewer fully read all fifteen selected Lean sources/checks and the new
refresh driver before executing it. The five changed modules preserve the
existing relevant theorem statements and arithmetic data. The kernel now proves
one common-modulus residue and projects it to the three required factors;
`K_cast_common` is an additional public theorem. The physical-order simplification
adds the installed `Mathlib.Data.Finset.Sort` import. No incoming executable was run.

## Exact scope and reuse

The private overlay contains 370 custom modules: **15 freshly compiled** and
**355 reused from the completed private 09eaa overlay**. Each reused module has
an unchanged current source hash matching the original manifest and an object
hash matching the original terminal PASS state. There is no reuse of an
unbound shared project object. The shared `.lake/build/lib/lean` directory was
removed from `LEAN_PATH`. Its replacement contains links to the original
validated objects and the fifteen fresh outputs. The original validation
folder and durable bundle were not modified.

Reuse deliberately includes unchanged intermediate clients of the changed
proofs. The direct clients are `CurrentAuxiliaryOrder2011`,
`CurrentControllerSubsets2011`, and `CurrentControllerUnits2011`; their
transitive unchanged clients were also retained. Consequently the endpoint
replay checks composition with these previously validated objects, rather
than freshly re-elaborating all their current dependency paths. All three
clients have unchanged source bytes; their prior dependency provenance stays
in the original manifest and state.

`ArithmeticNonzero` lies outside the original 361-module graph, so its four
custom prerequisites (`Representation`, `ArithmeticRepresentation`,
`ComposeRepresentation`, `DirectComposition`) were freshly compiled too.
There is no existing `ArithmeticNonzeroChecks` file, and none was invented
for this run. The four other changed modules have their existing checks.
The installed package/toolchain boundary consists of 64 direct external
imports with recorded source/object/companion hashes; those package objects
remain trusted precompiled inputs. This refresh does not establish a new
transitive external-package source replay.

## Commands and results

The exact driver command was:

```text
python3 -u /tmp/current-positive-zero2011-refresh-plan/refresh.py run \
  1aa0d66e626bff9e03ef1b6317c61518bb520b0eadaf336ff8abfc45357a2e72 \
  /tmp/current-positive-zero2011-refresh-validation-20261026b
```

Every compiler invocation was serial and used the pinned Lean executable with
`-M6000 -j1 -DElab.async=false -o <private-object> <actual-source>`.
The complete commands appear in `driver.log`; each command has a separate
stdout/stderr log and `/usr/bin/time` receipt. No source edits, shared object
writes, retries, cap increases or resumptions were needed.

UTC interval: `2026-10-26T20:16:06.387615+00:00` through `2026-10-26T20:17:19.719480+00:00`;
wall-clock execution 73.332 seconds.
Maximum compiler RSS was 3,824,420 KiB (`CurrentPowerCoordinates2011`).
All ten main-module logs are empty; the five check logs contain only their
expected axiom reports. All 54 reports use at most `propext`,
`Classical.choice`, and `Quot.sound`; two reports use no axioms.

| Module, in execution order | Exit | Seconds | Axiom reports |
| --- | ---: | ---: | ---: |
| `Representation` | 0 | 4.282 | 0 |
| `ArithmeticRepresentation` | 0 | 2.550 | 0 |
| `ComposeRepresentation` | 0 | 1.983 | 0 |
| `DirectComposition` | 0 | 2.322 | 0 |
| `ArithmeticNonzero` | 0 | 2.348 | 0 |
| `PrimePowerOrder` | 0 | 2.242 | 0 |
| `PrimePowerOrderChecks` | 0 | 2.157 | 6 |
| `CurrentPowerCoordinates2011` | 0 | 10.651 | 0 |
| `CurrentPowerCoordinates2011Checks` | 0 | 3.659 | 13 |
| `WangTiles942PhysicalOrder` | 0 | 5.651 | 0 |
| `WangTiles942PhysicalOrderChecks` | 0 | 10.400 | 16 |
| `CurrentKernelResidues2011` | 0 | 12.669 | 0 |
| `CurrentKernelResidues2011Checks` | 0 | 3.890 | 13 |
| `CurrentPositiveZero2011` | 0 | 4.247 | 0 |
| `CurrentPositiveZero2011Checks` | 0 | 3.251 | 6 |

The endpoint sources are unchanged:
`CurrentPositiveZero2011.lean`
`cdbd33de5ccb176c253d1cfca41f1d34b8d0121790a4b06c5d38d461b72b648c`,
and its checks
`79a6dc417560cec163767f9d5af69c4ef647fb081b433ab0abd830dbf41ee44b`.
Their freshly generated objects are byte-identical to the prior completed
run: respectively `629d9b6e21a33c0ddaa9d61e067a3c47e0435cb146fb30f6bab259b4026b68c0`
and `c74a78cec6457027befbf2219859e18df01117875ba4dff0c11a8b5ed34524b3`.
This equality is an observed result, not a substitute for the fresh compilation.

## Changed source pins

| Current source | SHA-256 |
| --- | --- |
| `ArithmeticNonzero.lean` | `38aff54429a2df3bf722d6225ac18f0c15d84b8112000af1f9ab35d25c0100a2` |
| `PrimePowerOrder.lean` | `72c0c999cc47c961b2801e74ebe2328c840477b67805f9a9c72f152e9e389917` |
| `CurrentPowerCoordinates2011.lean` | `0682e3263153369d5694b3dcf0942e0b4a5cdd2b48b2c25199e4989cbe3896c3` |
| `WangTiles942PhysicalOrder.lean` | `e4c47779d350f7ec34ed3cd15a17a584e23077a2a56a8c8a0c2a53f8376ddddf` |
| `CurrentKernelResidues2011.lean` | `f16f792f4449e423bfa6165f81a6b6e3d8c872531b4e428aaf0bebafd178a659` |

## Durable evidence

The bundle preserves the reviewed driver, complete source/object manifest,
terminal state, driver output, and all thirty text log/timing files. It contains
no Lean objects. All fifteen source/object/log/timing hashes were independently
recomputed after the driver terminated; the compressed text archive was checked
entry by entry and passed ZIP integrity verification. The driver also rechecked
all 370 source and selected object hashes, the toolchain, original evidence,
and the external boundary before reporting PASS.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| [driver.log](current-positive-zero2011-refresh/driver.log) | 13902 | `ffd4369300c3a12e0e5f0afb396311b8f7d19d651d480504b14cf10e060bbd72` |
| [execution-logs.zip](current-positive-zero2011-refresh/execution-logs.zip) | 7194 | `42e44fb4855907b0b6e62a11a5775c5482effda5eb8cd1bde8fed59c2d97e1a1` |
| [execution-state.json](current-positive-zero2011-refresh/execution-state.json) | 28460 | `d299eb7e7c213b3db2dc795a85c6c54c872fbc554bef1839002037ba245999a3` |
| [manifest.json](current-positive-zero2011-refresh/manifest.json) | 358228 | `1aa0d66e626bff9e03ef1b6317c61518bb520b0eadaf336ff8abfc45357a2e72` |
| [refresh.py](current-positive-zero2011-refresh/refresh.py) | 9954 | `10ffa1cfffbfc05461838cc2a17c8a7cb4789d112bc6a82e3e90b9c80adbbd0b` |

## Mathematical and formal scope

The unchanged endpoint proves the external Lean equivalence for the actual
fixed positive fourteen-variable polynomial and the accepted positive
thirteen-variable forms, using the actual `DiophantineConsistency.ConZFC`
predicate. The six endpoint audits remain standard-axiom-only. This receipt
adds no claim of an encoded internal ZFC derivation, an HA derivation, a
fresh whole-project build, or global minimality of the equation.

The reviewer authored earlier versions of substantial native/controller
prerequisites, including several of these changed modules. This is a source
read and reproducible build/provenance receipt, not an independent review of
all of the reviewer's original mathematics. Root and other agents supplied
separate earlier mathematical reviews. No central source, documentation,
umbrella, Git state or accepted object was edited by this refresh.
