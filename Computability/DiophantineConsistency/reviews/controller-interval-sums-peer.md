# Modular interval subset sums: independent peer review

Date: 2026-10-26. Reviewer: `controller_certificate`. Author of the
reviewed packet: `circuit_reduction`. Result: **PASS**, with no source
changes requested. This review covers the finite interval-coordinate
construction, not the entire native controller.

## Reviewed bindings

All paths below are relative to `Computability/DiophantineConsistency/`.

| Source | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/ControllerIntervalSums.lean` | 83 | `aecbb4d39a0f6efc6173d9f38ced30e131cff421dd89d5a747a1e94ba530461a` |
| `Lean/DiophantineConsistency/ControllerIntervalSumsChecks.lean` | 90 | `79668160d975e1e8b5bf6c872e24213cea3880af187e3b7bcc6560f5056efaf3` |
| `reviews/controller-interval-sums-author.md` | — | `fc92928cb6edf869bd06f3d1107aeeca8df1fdfb0c7c2008b58649b115751fb0` |

I read both complete sources and the entire author receipt before
execution. The main imports only `Mathlib.Data.ZMod.Basic`,
`Mathlib.Algebra.BigOperators.Intervals`, and `Mathlib.Tactic`.
I inspected the actual pinned definitions of `unitOfCoprime`, its value,
`isUnit_iff_coprime`, `Units.mul_inv_cancel_left`, and the natural
Gauss-sum proof. The three relevant API source hashes match the author
receipt. No local machine, kernel, carry, tile, or controller module is
imported. I authored none of these sources or their mathlib dependencies;
my earlier local arithmetic work is not used by this packet.

## Mathematical review

The actual subset is the image of `range a` under translation of natural
coordinates into `ZMod T`. From `a≤T`, two source indices in the range
both lie strictly below `T`; equality of translated residues therefore
implies equality of canonical natural representatives. This proves
injectivity and exact cardinality, including wraparound and full length.

The image-sum theorem uses that same proved injectivity before changing
the sum to a range sum. The resulting constant term is `a*start`, and
the triangular term is computed as `a*(a-1)/2` in `Nat`, then cast.
There is no illicit cancellation or inverse of two in an even residue
ring. Natural subtraction also handles the empty interval correctly.

`startFor` explicitly uses the inverse of the unit corresponding to
`a`, justified by the supplied `Nat.Coprime a T`. Unit cancellation
solves the coefficient equation exactly. `targetInterval` then gives
the actual finite subset, its cardinality and its target sum; the final
existence theorems merely package this construction. No desired subset
or target-sum witness is assumed.

The edge cases are coherent. `T=1` is allowed, including both `a=0`
and `a=1`; `NeZero T` excludes `T=0` where bounded cyclic-coordinate
injectivity would have a different meaning. The general coefficient
equation itself does not need the finite-coordinate assumptions.
The endpoint assumes exactly positive modulus, `a≤T` and coprimality.

The checks exercise wrapped and full intervals, the explicit inverse
start, both zero-ring endpoints, and failure of cardinality above the
length bound. The noncoprime example correctly distinguishes failure
of consecutive intervals from failure of arbitrary subsets: two-term
intervals in `ZMod 4` cannot sum to zero, while `{1,3}` does.

The receipt accurately leaves the power-orbit identification, CRT,
the auxiliary Boolean choice, safe dummy placement, and transport of
arithmetic witnesses open. This packet proves no complete controller,
positive polynomial witness, or consistency equivalence.

## Independent fresh replay

I compiled the main and checks sequentially into the isolated directory
`/tmp/controller-interval-sums-controller-peer/`, prepending that directory
to `LEAN_PATH`. No target object was copied into the overlay: the checks
imported the freshly produced main object. Both sources were run with
`-M6000 -j1` and their declared `Elab.async false`, using pinned
`leanprover/lean4:v4.32.0`. Existing mathlib objects were reused; this is
not a full fresh mathlib dependency build.

| Replay | Result | Seconds | Peak KiB |
| --- | --- | ---: | ---: |
| Main | PASS, no Lean diagnostics | 3.44 | 3178988 |
| Checks | PASS, eight intended axiom reports | 3.01 | 3177452 |

The eight reports use only `propext`, `Classical.choice`, and/or
`Quot.sound`. No `sorry`, `admit`, `native_decide`, or added axiom occurs
in either reviewed source. The main replay object is byte-identical to
the existing author object. No original checks object existed, so no
check-object byte-identity claim is made.

Fifteen selected source, toolchain, package-manifest, imported-object and
target-object paths were hashed before and after replay; all were
unchanged, including the continued absence of the shared checks object.
The isolated evidence is:

| Evidence | SHA-256 |
| --- | --- |
| `inputs-before.json` | `39eb064081564d40ca2b7331dd5c001d281814e1759aa863e22fc30ff75f41a0` |
| `main.log` | `aa01744ea5c05164f241af869338d3f251489359fd9ff8a131739f59b68ef7c5` |
| `checks.log` | `ed4ed96e79c32a74039f48a51999be67d60ff6b77b1832fa8cb54fd7a1014d2e` |
| Main `.olean` | `833345ce36bcab09fd09ddfa824c4afaca60de68d9bba90516cc246ffb585963` |
| Checks `.olean` | `de19fedf317a19a413ea8a983b05e34c82751d28f91bf89036e56045a6a46850` |
| `results.json` | `93cbc1ecfba6ad52776c7ab79bcffcfa1e4accb12fda0701e2ad0186c21d2a0c` |

Only this new peer receipt was added to the repository. No reviewed
source, shared document, shared object, or git operation was changed.
