# Guarded actual-zero 76Y size bound

`IndependentYSizeDraft.actual_f_bound` proves that `f²>c+1` for every
positive 76Y zero, at arbitrary natural ports in the stated IΣ₁ models. It
binds the checked generic Pell/strong-norm inequality to the actual graph's
checked residual split and main root. The stronger `V<y` guard, positive
witness maps, zero-equivalence and iPRA endpoint remain separate.

The [sixth check](observations/attempt06/result.json) exited 0 with the
expected `[propext, Classical.choice, Quot.sound]` report, no warnings or
`sorryAx`, and stable source, Lean executable and direct graph-model provider
guards. The object
`/tmp/p64-qcube76y-size-priority-check06/IndependentYSizeDraft.olean` has
SHA-256 `194262091b270d8f4c7e75610166b2c36b26ff7aac448a20b904edc447e90463`.
The corrected source SHA-256 is
`f422f35611f0d802e1c8cbe443d64b57517eb541920378a7fe9c35bacda67a58`.

The check ran alongside the current14 rebuild with `-M2400`, nice 19, idle
I/O, a 120-second limit, and sampled stops at 3.5 GiB process-group RSS and
10 GiB `MemAvailable`. It recorded 26 group-RSS samples, sampled maximum
2,129,989,632 bytes and minimum available memory 18,825,805,824 bytes; no
stop fired. Sampling is not a hard RSS reservation. Captured-provider
transitive and dynamic ancestry remains inherited; the shared missing-child
monitor controls are in the [graph packet](../p64-qcube76-independent-y-guarded-check/README.md).

The [first four diagnostics](observations/) exited 1 on the strong evaluator
tactic, including cast/propositional-goal issues. The [fifth](observations/attempt05/result.json)
had Lean exit 0 without `sorryAx`, but the strict runner marked it FAILED for
two tactic-style warnings. All prior exact sources, logs and receipts are
retained; the sixth check removed those warnings. The accepted runner SHA-256
is `645384d7f39f8ffcd869b6fa5a737cdc98dc9f2d4363f437f3167e669d9513e5`.
