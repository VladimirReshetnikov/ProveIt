# Matched encoded-controller and physical step at site 31

`PA194SourceSite31Physical.sourcePhysical` proves a matched source/physical step in every model of PRA. The actual resolved source instruction at site 31 is increment logical register 0 and go to site 32. The encoded source controller takes that step while preserving its independent controller tail. The literal PA194 machine takes the corresponding physical site-31→32 source-frame step, with the same incremented register file, one appended one-valued spare, and gap changing from `(k+1)+1` to `k+1`. The physical run is given by the explicit first-phase clock and the nested `runAfter` clocks.

The input condition is that physical suffix position 10 equals `repeatOutput(count,0)`, representing a model-valued number of one-valued spares followed by blank tape. Logical register values, the physical spare, `k`, `count`, and the independent controller tail are arbitrary model elements. The source-controller state and physical-frame definitions in these two standalone modules are definitionally the same as the existing site-25 bridge definitions.

This theorem handles one matched source instruction. It does not yet supply a single PR-coded total physical clock, a native iPRA sentence for this matched step, arbitrary model-length synchronization of the complete machine, or either consistency implication.

From the repository root, choose a fresh nonexistent output directory:

```sh
env -u LEAN_PATH Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-matched.sh \
  "$PWD" /dev/shm/pa194-site27-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip \
  /dev/shm/pa194-fetch-coherent-full-v2 \
  /dev/shm/pa194-site31-matched-coherent
```

The checker extends the physical source-frame replay, then traverses the pinned source-closure manifest and rebuilds every missing controller-specific dependency into the **same fresh output**, against the physical baseline. It never adds the fetch machine-object root to `LEAN_PATH`. In particular, both sides use the physical baseline's single `PA194SourceProgram` object, rather than combining it with the byte-different fetch object. The source manifest supplies source paths and SHA-256 hashes; a retained `site31-controller-closure-receipt.json` records built source modules and the baseline objects used. The checker refuses missing machine-specific dependencies, source hash changes, and `sorryAx` in module output, and checks the named controller and conjunction axiom reports.

The physical baseline, the two selected physical tail stages, the fetch root's `foundation-view`, and the general foundation roots are prebuilt. The baseline's selected source-program and controller-import objects are pinned including their available `.private` and `.server` companions; the source graph builder records the baseline objects it actually uses. This is a single shared staged source build on that prebuilt baseline, not a fresh reconstruction or independent certification of every transitive imported foundation or baseline object.

The repository replay also exited 0 (`/tmp/pa194-site31-matched-repo.log`). Its
`site31-controller-closure-receipt.json` is included as a snapshot of source and
used baseline hashes; its absolute paths describe this replay and are not portable.
