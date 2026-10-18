# Exact 246-state blank-tape bootstrap

All eight continuation groups passed. The final theorem, `BootPrefix246Chunk008.bootstrap410735`, states that the complete infinite-tape configuration of `machinePrefix246.run 410735` is represented by `BootPrefix246Probe16384.finish`. Its state is 88 and its head is −5. `bootstrap_tape` specifies every tape coordinate, including the zero exterior; `bootstrap_active_through` proves that no earlier step halts.

The proof starts with the separately checked [first 1,024 steps](boot_prefix246_first.md). Six continuation modules each add four 16,384-step blocks, reaching step 394,240. Two smaller modules add 111 transitions. The final module then applies the separately checked local 16,384-step calculation to reach 410,735. Every local equality is immediately composed with a theorem about the actual blank run. The local calculation alone is conditional on its explicit start configuration.

Expected checkpoints come from a deterministic generator using both sparse-tape and finite-zipper calculations. They are untrusted inputs. Lean checks each local `zipBlock` equality using `decide +kernel`; the equality of the balanced lookup with the exact canonical table transfers the result to `machinePrefix246`. The generic `ZipRep` lemmas provide the whole-tape interpretation and compose elapsed time.

The finite final configuration has 11 left cells, 707 right cells and 351 ones. Its marker is at −6 and its header at 176. The dispatch interpretation of this literal tape and its logical seed `(3,0,0,0,3,0,0,0,0)` with 167 spare value-one blocks belongs to a separate frame module. Arbitrary instruction simulation and equivalence with ZFC consistency are also separate from this bootstrap module.

The [manifest](bootstrap-prefix246/manifest.json) lists the exact checked modules, ordered dependency records, axiom reports, warnings and timings. Each source, audit, raw guard, data file and log is stored once. Historical source/snapshot paths are aliases to those same bytes. Existing Table, FastTable and First-checkpoint publications are referenced by hash. Raw execution records retain their original paths; cached `.olean` files remain explicit prerequisites and are not committed.

Every source/audit pair uses one Lean process at a time with `-j1 -M4096`, a shared 120-second wall budget and the default proof limits for the new unit. No dependency build, download, native evaluator or compiler-version query is part of these checks. Imported Core and FiniteZipper objects are existing checked boundaries with the exact source/object identities recorded by the guards.

The portable coordinator stages byte-identical sources, audits and data in a new external directory. Its reviewed adaptation changes repository/default paths and successor parent-record bindings; it preserves each guard's proof, provider, audit and resource checks. Preparation uses the recorded successful parents and invokes no proof command. Full replay checks each unit serially, requires a successful fresh parent before its successor, and stops on a failure.

```sh
python3 -B check_boot_prefix246_chain.py --prepare-only --output /tmp/prefix246-bootstrap-prepare
python3 -B check_boot_prefix246_chain.py --output /tmp/prefix246-bootstrap-check
```

The recorded checked boundary objects and their input paths must still be present. The coordinator does not rebuild missing dependencies. Exact historical guards are retained separately from the portable coordinator, and new replay records are not represented as the original runs.

Attribution follows the [exact candidate's notices](candidate-prefix246/README.md): Mira-Cult's calculus and machine, Jeff Ketchersid's verification and symbolic machinery, Andrew James Wade's compiler framework, and the later reductions and ProveIt research. The 246-state submission supplies the new pulse fold and startup; the Lean checkpoint proof certifies this exact table and blank run.
