# ArithmeticBinaryPopulation — independent review and replay

27 October 2026. Reviewer: `complemented47_review`. Result: **PASS; no finding or requested correction**.

I read the complete final 227-line main and 40-line Checks, the proposal and exact prerequisite contracts, the author receipt, the complete executed author driver, the independent driver, and the preserved source changes. I independently authenticated the complete selected source/header DAG, provenance evidence and all first providers before replaying only these two leaves.

## Exact sources and evidence

- Main SHA256: `5ca0171ebc2525a1ac6f2fc3dbcd42c6793e935cd27f194b09501772511e6219`.
- Checks SHA256: `b1e882c8d79b3070d5a3ae638b0f11b412f8bc8af7f0517d3e648b036456bc38`.
- Author packet: `arithmetic-binary-population-replay.json`, SHA256 `ee47d164549eb378ed52ca616cc121ff50fc90f9e812f11f4419cd6616416677`.
- Author receipt: `arithmetic-binary-population-author.md`, SHA256 `77c2473a8b515006c7e64aa04cde1d463327192262f7c85a4b189dde9962e35d`.
- Author 25-file manifest: SHA256 `a7599395145ec4cbbe10aa7249aeb112e46cd12f0d60889ac5c2a07df17a0d1f`.
- Independent replay packet: [arithmetic-binary-population-peer-replay.json](arithmetic-binary-population-peer-replay.json), SHA256 `808afd07ae24a76f2c8e86754e6d0b7d118362913da54c97a3f8aac78dfaea23`.
- Independent 14-file manifest: [FILES.json](arithmetic-binary-population-peer-replay/FILES.json), SHA256 `356a675a62a9c0eca25754271200a7e2ea735554373c4b23e37f020034c0706d`.
- Executed 143-line independent driver: `/tmp/arithmetic-binary-population-peer.py`, SHA256 `e1ff07f996a25aa3eb02a3542138e990032968820db64ed2e903aebd90f4c540`; durable identical copy in the bundle.
- Freeze driver SHA256: `78c3c953d579ef43229aba4f32019cc0b5a9b3aeb75584e1225c6eb7fc9b870d`.

The author packet and author receipt are pinned explicitly outside the author's manifest. The independent packet and this receipt likewise remain outside the independent manifest to avoid cyclic hashing.

## Mathematical review

The fixed PR blueprint represents a genuine prefix count over every internal index. Its zero and successor graph arities and argument order match `PR.Construction`; the successor adds the actual Foundation `fbit`. Both the Sigma1 and Delta1 graph definitions are fixed syntax, and the population graph composes the prefix graph with the actual binary length. Totality and uniqueness come from represented primitive recursion, not an external finite sum or standard-natural oracle.

The prefix bound, stability, binary shift and population recurrences use the actual bit/length APIs. The even-length case isolates zero before using the positive-even length identity. Concatenation fixes the upper block before a genuine Sigma1 induction with a bounded universal lower block. Complement uses the same bounded induction, derives the quotient bound before subtraction, and proves the additive candidate identity before identifying the truncated complement. Both endpoints include zero length, zero value and leading-zero cases, and quantify over arbitrary internal elements of an IΣ1 model.

The final source repairs preserve these statements: attempt 1 to 2 renames the reserved identifier `prefix` to `prefixCount` and corrects two subtraction rewrite directions; attempt 2 to 3 replaces a failing zero-case simplification with the explicit `prefix_succ (0 : V)` specializations. The historical snapshots, diagnostics and exact deltas of all three author attempts were authenticated. Checks bytes remained unchanged.

## Replay and cache boundary

The selected prerequisite profile is exactly **95 custom modules, all 95 Foundation; 380 custom artifacts; 38 external boundaries containing 114 total artifacts (38 primaries and 76 companions); 494 actual first providers; zero refreshes**. The exact approved plan and its entire provenance chain were authenticated. No Foundation or other prerequisite was rebuilt, and no unrestricted shared project cache was added to resolution.

Fresh private provider: `/tmp/arithmetic-binary-population-peer-199go8sf/lib`.

| Leaf | Exit | Seconds | Peak RSS KiB | Object SHA256 |
| --- | ---: | ---: | ---: | --- |
| Main | 0 | 12.757 | 1825404 | `6fd26c3bb8b07acbb212aa75eb5db824fe285c4d118a1c93b74122a9de2b7760` |
| Checks | 0 | 2.102 | 1785676 | `80b25b8bf2884523fe254212cc7142c54e8a282aac5d9e335181e64163ae6f58` |

Both objects and full logs are byte-identical to the author outputs. Main has no diagnostic output. All **14** Checks reports match exactly and contain only `propext`, `Classical.choice`, and `Quot.sound`.

There was one independent attempt and exactly two compiler invocations, both successful. Commands used pinned Lean 4.32, `-M6000 -j1 -DElab.async=false`, one thread, explicit package boundaries and a 512 MiB pre-command reserve guard. Both source inputs were snapshotted before main. Outputs are fresh regular files with independent inodes, not symlinks or aliases of author objects. Pre/post authentication recorded 13,276 comparisons over 2,634 paths; final freeze reauthenticated 3,651 comparisons over 2,656 paths. The bundle preserves immutable terminal metadata, both source snapshots, commands, driver, logs, timings and outputs using regular hardlinks, retaining every original path.

## Independence and limitations

I previously reviewed the plan and challenged the draft source; I did not author either Population leaf or any of its 95 Foundation prerequisites. My earlier Pell/current-source authorship and peer reviews do not occur as mathematical prerequisites in this selected DAG. This is an independent source/provenance review and two-leaf kernel replay, not a fresh Foundation rebuild. It establishes the stated internal population, concatenation and complement results only; NoCarry/subadditivity, binomial extraction, maintained equation soundness and HA equivalence remain separate work. No accepted source, shared object, shared documentation or Git state was changed.
