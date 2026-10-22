# Phase11 Lean evidence

The direct 58-step generic derivation, with two single-use aliases inlined into their public theorems, passed the Lean checks. The maintained generic core is 13,723 bytes / 287 lines: 1,016 bytes / 43 lines shorter than phase10. Its unchanged Nat adapter brings the pair to 16,403 bytes / 360 lines. The reviewed data-only producer reproduces both exact files; two unused maintained templates are retired with their original bytes retained.

The combined check contains 197 providers: the 192-module endpoint closure plus five decoder-prefix modules. Eight modules were freshly compiled and 189 were reused from phase10 after exact transitive source/import checks. Both unchanged endpoint clients passed, with ten standard axiom reports and no audit warnings. The 21 project warning occurrences include inherited logs. All nine site batches retain their phase10 bindings; they were not recompiled here.

The separate 16-provider isolated check freshly compiled five modules. Its 17 fresh reports comprise seven empty-axiom generic reports and ten numeric reports using only `propext` and `Quot.sound`; those invocations had no warnings. Two inherited KCode222 reports and six inherited TarskiComplete warnings are recorded separately. Both compiler-run outer processes exited zero. The initial isolated saved-record reviewer counted fresh and inherited reports together; its failed assertion and corrected reader are preserved. It was not a proof/compiler failure.

`execution.tar.gz` contains exact new raw records, source/log aliases, producer history and the two retired template blobs. `basis-reference.json` pins the local [phase10 packet](../../phase10/lean/README.md), which supplies unchanged evidence in place. No compiled objects or ancestor archives are copied. The reader uses pinned local predecessor validators; it never runs code extracted from an archive. Historical `before.inputs` are retained unchanged: the five producer inputs resolve to their saved phase10 bytes. The two current writes and two current absences are checked separately.

From a repository containing this packet and its predecessors:

```sh
python -B review_saved.py --basis-repo /path/to/Proofs --repo /path/to/Proofs --output /tmp/phase11-saved-review.json
```

Omit `--repo` to check only the saved evidence. The reader validates source, dependency, command, log and recorded object-hash provenance; it does not invoke Lean or claim to recheck live compiled objects. The collector's separate postcheck rehashed the live objects, logs, sources and original input pins at capture time. Raw execution and producer statuses remain historical records. This packet adds no machine-state reduction, runtime execution, Rocq check or internal PA theorem.
