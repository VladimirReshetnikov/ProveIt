# Independent review: retry05 continuation design

The [continuation design](../../research/current14-carrier65-retry05-continuation-design/README.md) is a bounded, fail-closed proposal rather than a runnable or certified continuation. Its saved-record projection is internally consistent within the stated abstract layout; both projection receipts reproduce. This review does not authorize a build or establish that retained prefix objects are compatible with any particular Lean environment.

The independent checker reconstructs 1,000 proposed base `.olean` links and 239 proposed links to the retained prefix outputs from the pinned failed state. Those links are reused inputs; they are not newly compiled outputs. Their relative names are distinct and do not overlap the 290 remaining planned `.olean` names or the separate final audit client. The stage-240 row is still an unexecuted stub. A real implementation must use a fresh output/state root and apply separate acceptance rules for input links and newly produced regular files; the prior runner's output postflight cannot simply be reused unchanged.

The checker independently projects all 9,308 recorded old-root guard entries onto hypothetical `@NEW_LIB@` labels and compares their recorded presence, realpath and hash with the abstract input map. It preserves 18,616 external guard entries as saved records, and confirms 373 dependency paths would be relabelled while 343 retain their recorded external spelling. It also rechecks the stated point-in-time byte totals for the 239 old prefix objects, 1,000 base-link targets and 530 retained source snapshots. These totals exclude package/toolchain dependencies, new outputs and filesystem overhead; they are not a space reservation. The projection does not create files or links, reauthenticate external guards, invoke `lean --deps`, or show what Lean would load through a new root.

The blockers in the design are material: the exact transitive package/toolchain/runtime and companion closure remains unauthenticated; changing search roots can alter provider and companion selection; symlinks and hard links do not freeze their target bytes; previously recorded guards cannot be assumed to certify a new path; and a real exclusive resource boundary and monitored disk/memory limits must be established. Future stages need fresh guarded dependency and compile checks, and the final postflight must distinguish original reused evidence from new outputs and inspect the actual axiom reports. The design also counts the prior 2,487.332 seconds toward its proposed six-hour deadline. This review's AST inspection of the projection script is bounded and is not a general Python safety proof.

No Lean process was run and no retained retry05 evidence was changed. The existing disk-floor, monitoring, provider and physical TeX/PDF binding limitations remain in force.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current14-carrier65-retry05-continuation-design-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/current14-carrier65-retry05-continuation-design-independent/result.json
```
