# First 1,024 steps of the exact 246-state machine

`BootPrefix246First.lean` proves the complete blank-run configuration at step 1,024 for `machinePrefix246`: state 88, head −2, and every cell of the infinite tape. The finite checkpoint has 11 left cells, 25 right cells, and 13 ones. Its omitted exterior is zero. The module also proves `advance_checkpoint`, which composes a kernel-checked finite zipper block with an already proved blank-run checkpoint.

The source imports the exact balanced lookup for the [246-state candidate](candidate-prefix246/README.md) and the existing finite-zipper semantics. Its numeric block is checked using `decide +kernel`, and the lookup equality transfers it to the original table. Generated checkpoint data are untrusted input to that equality. This result does not establish the final 410,735-step bootstrap, a dispatch frame, arbitrary runtime simulation, or equivalence with ZFC consistency; those are separate modules.

The [exact executed record](results/boot-prefix246-first-verification.json) reports source and audit PASS, seven named axiom probes, nine caller checks, and zero warnings. The block theorem uses `propext`; the remaining probes use `propext` and `Quot.sound`. There is no `sorryAx` or native-computation axiom. The one-thread guard uses a shared 120-second source/audit budget, `-j1 -M4096`, and default proof limits for this new unit. Imported Core, Table, FastTable and FiniteZipper objects are explicit prior checked boundaries; they were not rebuilt by this check.

The [history](results/boot-prefix246-first-history.json) preserves the executed source, audit, guard, generator, checkpoint data, both logs, evidence record, independent reviews and portable deltas. Its archive copies were made after PASS and checked against the guard's original snapshots and input hashes. A preliminary unsupported `--fast-evidence` argument was rejected by argparse before compilation; this is retained as a parent-agent report, because no raw transcript was saved. It is not counted as a proof attempt.

The [maintained-default preparation](results/boot-prefix246-first-maintained-prepare.json) checks the placed files and providers without invoking Lean or a version query. The [publication record](results/boot-prefix246-first-publication.json) binds the published files to these records. Historical absolute scratch paths in exact execution evidence are provenance, not portable output locations.

From this research directory, a source-only regeneration comparison is:

```sh
python3 -B generate_boot_prefix246_first.py --check
```

The guard accepts a new external output directory. Preparation performs no compilation; removing `--prepare-only` performs the bounded source and audit run once:

```sh
python3 -B check_boot_prefix246_first.py --prepare-only --output /tmp/prefix246-first-prepare
python3 -B check_boot_prefix246_first.py --output /tmp/prefix246-first-check
```

The selected prior checked object files must still be available at their recorded paths. These commands do not rebuild missing dependencies. The generator and data are included as `generate_boot_prefix246_first.py` and `bootstrap-prefix246/first/data.json`.

Attribution: the transition table and reported endpoint come from the source63 246-state submission by Mira-Cult/Jeff/Wade's lineage, catalogued in the maintained incoming reports. The checked zipper semantics and sequential checkpoint method build on the repository's prior Lean verification work. No supplied report instruction is treated as a user authorization.
