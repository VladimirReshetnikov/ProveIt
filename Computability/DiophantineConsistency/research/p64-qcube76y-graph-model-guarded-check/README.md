# Guarded 76Y model split and main-root check

The corrected `IndependentYGraphDraft.lean` passed a bounded Lean check for
arbitrary natural ports in the stated IΣ₁ models. `residuals` proves that a
positive 76Y zero has first and auxiliary residuals 1 and main, strong and
transport residuals 0. `main_root` then obtains the natural Pell root from
the main and transport residuals using the lifted q-cube coordinate. These
are prerequisites, not yet a positive-zero equivalence or iPRA endpoint.

The [second attempt](observations/attempt02/result.json) exited 0 with both
expected `[propext, Classical.choice, Quot.sound]` reports, no warnings or
`sorryAx`, and stable source, Lean and three direct-provider guards. Its
object `/tmp/p64-qcube76y-graph-model-priority-check02/IndependentYGraphDraft.olean`
has SHA-256 `6ecb0bab486ceb1184c6417dca31ac1f9d22e65a37b58c8ac30fb1e130d60742`.
The corrected source SHA-256 is
`edefc1fcb8dc1140ad403bef8d21060d9477f3dc7356fc22a01ea9a901c93467`.
The [first attempt](observations/attempt01/compile.log) exited 1 on a cast
of one and reported `sorryAx` in both unresolved declarations; its source and
receipt are retained. The correction adds `Nat.cast_one` to the simplifier.

The successful check ran beside the current14 rebuild with `-M2400`, nice 19,
idle I/O, a 120-second limit, and sampled stops at 3.5 GiB process-group RSS
and 10 GiB `MemAvailable`. It recorded 23 group-RSS samples, sampled maximum
2,118,221,824 bytes and minimum available memory 18,823,389,184 bytes, with no
stop. Sampling is not a hard RSS reservation; full transitive and dynamic
provider ancestry remains inherited. The
[graph check packet](../p64-qcube76-independent-y-guarded-check/README.md)
records the shared missing-child monitor controls.
