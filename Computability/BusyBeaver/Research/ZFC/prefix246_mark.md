# Exact prefix246 marking

`RegisterMarkPrefix246.lean` proves all nine physical selector entries and the marking excursion for arbitrary natural register values, finite left contexts and terminal words. It returns in exactly `2 * width(pre) + 3` transitions, through old2 for physical register0 and old6 otherwise. The selected ordinary `01` header becomes `00`; every other tape cell is preserved. The unpadded file contracts match the direct246 carry boxes.

The contextual selector fold enters retained old20 after the separator. The ordinary unary block supplies the required next one, so only old20/read-one is used. The proof assumes no old20/read-zero behavior or global startup invariant. Generic encodings and the machine-parametric return scanner come from the maintained permutation252 proof; actual finite row premises are checked on `machinePrefix246`.

The second root-run check passed the170-line source and its audit, with10 axiom probes,6 downstream callers and no warnings. The first attempt passed the identical source, then failed audit client53 because `restoreZero` named two imported definitions. Qualifying it as `RegisterMarkPrefix246.restoreZero` repaired that client. Both full attempts, source objects recorded before their audits, raw logs and exact source/audit/guard bytes are preserved. The second attempt recompiled both source and audit. Archival copies were made after their terminal outcomes and rehashed against the original records.

Successful record SHA256: `e8b9aac9ad117eadbf63efbac49d8e35e326d1b270a5796b7abbd9434a1d8328`.
Fresh object SHA256: `2714d3848cacba252a2ba31696489e755ce4ff3a3d40696a9e0f63d5db3293e9`.

The checker selects seven exact project providers, with supplied Init/Omega toolchain boundaries. Only the marking source and audit are compiled, serially, under default proof limits, one thread,4096MiB and a shared120-second bound. Preparation invokes neither compiler nor version query:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_prefix246_mark.py \
  --repo "$PWD" \
  --table-evidence Computability/BusyBeaver/Research/ZFC/results/table-prefix246-verification.json \
  --output /tmp/prefix246-mark-fresh-preparation --prepare-only
```

Mira-Cult, Jeff Ketchersid and Andrew James Wade retain the original machine, marking, verification and compiler attribution. The earlier prefix250/247 selector saving remains attributed to the prior reports; source63 supplies this exact246 context and pulse fold. The independent source/interface review is included unchanged, alongside the separate author evidence review. This local contract does not prove full instruction coverage, blank bootstrap, nonhalting/consistency equivalence or PA internalization.
