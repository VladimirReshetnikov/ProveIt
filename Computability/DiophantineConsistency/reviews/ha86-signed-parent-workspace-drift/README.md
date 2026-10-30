# Signed HA parent snapshot versus later workspace sources

This is a read-only comparison of the 732 distinct source guard entries reported by the in-flight 85-module 87 HA peer `/tmp/ha87-focused-validator-rebase-q6geuvc7` against the workspace. The peer compiles from preserved source snapshots; the comparison neither runs Lean nor authenticates any provider object. At the observation recorded in `observed.json`, six guarded source files had changed after that snapshot. This does not invalidate the peer's snapshot replay, but a direct 86 extension that requires those parent guards to match the current workspace cannot claim to compile the later source graph from this parent.

`guards.json` freezes the module-to-source mapping and expected SHA-256 values from the peer state, plus the observed running-state and source-graph hashes. Its own SHA-256 is `14e7af0510c92a26a1f230d048a7a11f9140a15b682e66749705293bd9805ee9`. `observed.json` records expected and then-current hashes for the six changed files. Reproduce a comparison against whatever files are present at replay time with:

```sh
python3 Computability/DiophantineConsistency/reviews/ha86-signed-parent-workspace-drift/check.py
```

The peer state later changes as compilation progresses, and additional workspace merges can change the comparison; differing later output is not by itself a contradiction of this recorded observation. This does not assert that differing sources or objects are semantically incompatible, nor does it cover any source outside the recorded guard set.
