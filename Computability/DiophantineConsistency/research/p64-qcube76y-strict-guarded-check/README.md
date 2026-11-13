# Guarded actual-zero strict-root check

`IndependentYStrictDraft.actual_strict` proves that the evaluated signed
carrier `V` is strictly below the positive `y` coordinate at every positive
76Y zero, for arbitrary natural ports in the stated IΣ₁ models. It binds the
auxiliary evaluator to the checked graph residuals, the actual `f²>c+1` size
bound and the generic auxiliary inequality. This is the new→old witness
guard, not by itself a witness map, zero-existence equivalence or iPRA
endpoint.

The [guarded check](observations/attempt01/result.json) exited 0; both
ring-level evaluator reports used `[propext]`, and `actual_strict` reported
`[propext, Classical.choice, Quot.sound]`, with no warnings or `sorryAx`.
Source, Lean executable and both direct captured-provider objects and
companions remained stable. The object
`/tmp/p64-qcube76y-strict-priority-check01/IndependentYStrictDraft.olean` has
SHA-256 `8d656cea923e20d2966581c7af9410f6d63ae0cdab7e8b091aa9252898ac8fc2`.
The source and runner SHA-256 values are respectively
`c959e856d4554e735c57ef91f9255633a5ff899639f0222a2e8a11a02e61ad2a` and
`3b694e731395431bd752c0e09e6cb27ea7808e3a16749e898be61b547a02fe99`.

The run used `-M2400`, nice 19, idle I/O, a 120-second limit, and sampled
stops at 3.5 GiB process-group RSS and 10 GiB `MemAvailable`, alongside the
current14 rebuild. It recorded 30 group-RSS samples, sampled maximum
2,120,261,632 bytes and minimum available memory 18,804,523,008 bytes; no
stop fired. Sampling is not a hard RSS reservation. Captured-provider
transitive and dynamic ancestry remains inherited; shared monitor controls
are in the [graph packet](../p64-qcube76-independent-y-guarded-check/README.md).
