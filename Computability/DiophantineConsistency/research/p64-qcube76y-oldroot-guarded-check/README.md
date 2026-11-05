# Guarded actual-zero old-root nonzero check

`IndependentYOldRootDraft.old_root_ne_zero` proves that the 77 graph's signed
auxiliary root `V+e` is nonzero at every positive 77 zero, for arbitrary
natural ports in the stated IΣ₁ models. It is the old→new positive-magnitude
witness guard; the witness map and positive-zero equivalence are separate.

The [third guarded check](observations/attempt03/result.json) exited 0 with
two expected `[propext, Classical.choice, Quot.sound]` reports, no warnings
or `sorryAx`, and stable source, Lean and both direct-provider guards. Its
object `/tmp/p64-qcube76y-oldroot-priority-check03/IndependentYOldRootDraft.olean`
has SHA-256 `24ac7fe3ed34e031cc2c67a7ba6c4bd4f1886d335524d993bf08f6d6d9a45534`;
the corrected source SHA-256 is
`9e557f49eace846edfdc9caeb2283ccf67f4c6c930147679fc2ab390e1aa2ef7`.
The first two attempts exited 1 on namespace and evaluator-elaboration
errors; their exact sources, logs and receipts are retained under
[`observations/`](observations/).

The successful run used `-M2400`, nice 19, idle I/O, a 120-second limit,
and sampled stops at 3.5 GiB process-group RSS and 10 GiB `MemAvailable`,
alongside the current14 rebuild. It recorded 24 group-RSS samples, sampled
maximum 2,128,343,040 bytes and minimum available memory 18,891,677,696 bytes;
no stop fired. Sampling is not a hard RSS reservation. Captured-provider
transitive and dynamic ancestry remains inherited; shared monitor controls
are in the [graph packet](../p64-qcube76-independent-y-guarded-check/README.md).
