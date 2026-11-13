# Independent single-union review

The v6 attempt failed before producing a stage-01 object. Its retained
pre-scan found `DiophantineConsistency.IPRAOpenDisjunctionWitness` in the
canonical library, but the Lean invocation searched for it in the fresh
upper `DiophantineConsistency` directory and reported it missing. The v6
scanner's per-file fallback therefore did not model the namespace resolution
observed during compilation.

The reviewed v7 runner has SHA-256
`4fd1c8ea506edeb5e468b59a7367efd7e759681a70a283f1c30d0278774ec79c`.
It builds one fresh project union from the canonical inventory and selected
supplemental companions, then removes only checked union symlinks for the four
affected modules before recompiling. It snapshots the union and validates it
after replacements. The pinned historical adapter preflight ties the affected
sources to their serialized direct imports and orders those imports so no
later affected object is used stale. The other v6 fail-closed checks remain.

The captured, independent no-Lean simulation built a temporary 2,681-file
union and checked the selected object and companion hashes for all 1,605
project modules in the retained v6 pre-scan. It found no top-level project and
package namespace directory overlap. Unlinking the four affected union
symlinks left the canonical library unchanged. The observation exited zero
with empty stderr.

This simulation does not prove the subsequent Lean compilation succeeds or
authenticate package-transitive and dynamic ancestry. The actual v7 run must
perform its own guarded header scans and compilation.
