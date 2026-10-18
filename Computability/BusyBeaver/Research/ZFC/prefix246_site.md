# Instruction checks for prefix246

`SitePrefix246.lean` connects each accepted instruction check to strictly positive execution on the exact 246-state table. It checks a consumed path of length at most 40, the logical-to-physical register assignment and both decrement branches. Every accepted trace applies to arbitrary natural gap parameters, register values and nonempty finite spare suffixes.

The target keeps the full tape. Positive decrement increases the header distance by one; overflow can independently add another cell. Increment's value-one spare and zero decrement's old112 return are inherited from the checked symbolic executor. Internal-node edges and register indices outside the nine primaries are rejected.

Root's first source/audit run passed: 12 named axiom probes and 13 typed callers, standard Lean axioms only, zero warnings. Source took 0.756 seconds and audit 0.485 seconds. The guard uses one thread, 4,096 MiB, a shared 120-second budget and default proof limits, with no dependency builds or version query. Final evidence review rechecked all 50 input identities, the complete 17-project import closure, Init/Omega boundaries, actual first providers and fresh source object saved before audit.

The sole successful attempt and exact raw snapshots are retained; the history archive was assembled after success from those bytes. Publication changes only the guard's source/audit default paths. The original record retains the actual scratch Symbolic evidence path; the identical maintained evidence is accepted below.

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix246_site.py \
  --repo "$PWD" \
  --symbolic-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-symbolic-verification.json \
  --output /tmp/zfc-prefix246-site-check --prepare-only
```

Use a new external output directory. Preparation invokes no compiler or version query; removing `--prepare-only` requests the bounded source/audit run.

This unit proves soundness when a check succeeds. Complete acceptance of the 8,391 cases, dispatch-frame preservation, actual blank startup, binary consistency and PA internalization remain separate. Attribution follows the checked 250-state port and the Mira-Cult, Jeff Ketchersid and Wade framework described in the source.
