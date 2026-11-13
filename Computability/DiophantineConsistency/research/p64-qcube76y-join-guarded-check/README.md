# Guarded 76Y/77 positive-zero model join

`IndependentYFullJoinDraft.positive_zero_iff` proves both directions of
positive-zero existence between the independent-`y` 76Y graph and the 77
graph, for arbitrary natural ports in every stated IΣ₁ model. It applies the
checked conditional witness join to the separately checked old-root
nonzero and new-root strict guards. This is a model equivalence for Lean
graph definitions; the iPRA proof-existence client and external payload or
display identification are separate.

The [conditional check](observations/conditional01/result.json) and
[full check](observations/full01/result.json) both exited 0 with their
expected `[propext, Classical.choice, Quot.sound]` reports, no warnings or
`sorryAx`, and stable direct source/provider guards. Their objects are:

| Module | Object SHA-256 |
| --- | --- |
| `/tmp/p64-qcube76y-conditional-join-priority-check01/IndependentYJoinDraft.olean` | `4eb10cce4b795b980805086f4fb9b1b8171eb9060cacc60f744ff90c814906c7` |
| `/tmp/p64-qcube76y-full-join-priority-check01/IndependentYFullJoinDraft.olean` | `0031cc6f24bed9ddeb19bb05818cd32b343a074d6263482644567e26e54879c4` |

The full check used `-M2400`, nice 19, idle I/O, a 120-second limit, and
sampled stops at 3.5 GiB process-group RSS and 10 GiB `MemAvailable`, alongside
the current14 rebuild. It recorded 11 RSS samples, sampled maximum
2,097,836,032 bytes and minimum available memory 17,486,356,480 bytes; no
stop fired. Sampling is not a hard RSS reservation. The guarded checks use
captured providers; transitive, dynamic and complete historical ancestry is
inherited. The shared monitor controls are in the
[graph check packet](../p64-qcube76-independent-y-guarded-check/README.md).
